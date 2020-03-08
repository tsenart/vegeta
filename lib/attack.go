package vegeta

import (
	"bytes"
	"context"
	"crypto/tls"
	"errors"
	"io"
	"io/ioutil"
	"math"
	"net"
	"net/http"
	"net/url"
	"strconv"
	"sync"
	"time"

	"github.com/valyala/fasthttp"
)

// Attacker is an attack executor which wraps an http.Client
type Attacker struct {
	Hitter Hitter
	Workers    uint64
	MaxWorkers uint64

	stopch     chan struct{}
	seqmu      sync.Mutex
	seq        uint64
	began      time.Time
}

// Attack reads its Targets from the passed Targeter and attacks them at
// the rate specified by the Pacer. When the duration is zero the attack
// runs until Stop is called. Results are sent to the returned channel as soon
// as they arrive and will have their Attack field set to the given name.
func (a *Attacker) Attack(tr Targeter, p Pacer, du time.Duration, name string) <-chan *Result {
	var wg sync.WaitGroup

	workers := a.Workers
	if workers > a.MaxWorkers {
		workers = a.MaxWorkers
	}

	results := make(chan *Result)
	ticks := make(chan struct{})
	for i := uint64(0); i < workers; i++ {
		wg.Add(1)
		go a.attack(tr, name, &wg, ticks, results)
	}

	go func() {
		defer close(results)
		defer wg.Wait()
		defer close(ticks)

		began, count := time.Now(), uint64(0)
		for {
			elapsed := time.Since(began)
			if du > 0 && elapsed > du {
				return
			}

			wait, stop := p.Pace(elapsed, count)
			if stop {
				return
			}

			time.Sleep(wait)

			if workers < a.MaxWorkers {
				select {
				case ticks <- struct{}{}:
					count++
					continue
				case <-a.stopch:
					return
				default:
					// all workers are blocked. start one more and try again
					workers++
					wg.Add(1)
					go a.attack(tr, name, &wg, ticks, results)
				}
			}

			select {
			case ticks <- struct{}{}:
				count++
			case <-a.stopch:
				return
			}
		}
	}()

	return results
}

// Stop stops the current attack.
func (a *Attacker) Stop() {
	select {
	case <-a.stopch:
		return
	default:
		close(a.stopch)
	}
}

func (a *Attacker) attack(tr Targeter, name string, workers *sync.WaitGroup, ticks <-chan struct{}, results chan<- *Result) {
	defer workers.Done()
	for range ticks {
		results <- a.hit(tr, name)
	}
}

var ErrNoResult = errors.New("no result returned from hitter")

func (a *Attacker) hit(tr Targeter, name string) *Result {
	var t Target
	if err := tr(&t); err != nil {
		a.Stop()
		return &Result{Attack: name, Error: err.Error()}
	}

	if name != "" {
		t.Header.Set("X-Vegeta-Attack", name)
	}

	t.Header.Set("X-Vegeta-Seq", strconv.FormatUint(seq, 10))

	a.seqmu.Lock()
	timestamp := a.began.Add(time.Since(a.began))
	seq := a.seq
	a.seq++
	a.seqmu.Unlock()

	r := a.Hitter.Hit(&t)
	if r == nil {
		r = &Result{Error: ErrNoResult.Error()}
	}

	r.Attack = name
	r.Timestamp = timestamp
	r.Seq = seq

	return r
}

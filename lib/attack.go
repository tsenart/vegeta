package vegeta

import (
	"errors"
	"net/http"
	"strconv"
	"sync"
	"time"
)

type Attack struct {
	Hitter   Hitter
	Targeter Targeter
	Pacer    Pacer

	Name       string
	Duration   time.Duration
	Workers    uint64
	MaxWorkers uint64

	init   sync.Once
	stopch chan struct{}
	seqmu  sync.Mutex
	seq    uint64
	began  time.Time
}

// Run runs the Attack, reading its Targets from the specified Targeter,
// hitting those Targets at a pace determined by the given Pacer.
// When the Duration is zero the attack runs until the passed context.Context is cancelled.
// Results are sent to the passed channel as soon as they are returned by the
// given Hitter and will have their Attack field set to the given Name.
func (a *Attack) Run(results chan *Result) {
	a.began = time.Now()
	a.stopch = make(chan struct{})

	var wg sync.WaitGroup

	workers := a.Workers
	if workers > a.MaxWorkers {
		workers = a.MaxWorkers
	}

	hits := make(chan struct{})
	for i := uint64(0); i < workers; i++ {
		wg.Add(1)
		go a.run(&wg, hits, results)
	}

	defer a.Stop()
	defer wg.Wait()
	defer close(hits)

	began, count := time.Now(), uint64(0)
	for {
		elapsed := time.Since(began)
		if a.Duration > 0 && elapsed > a.Duration {
			return
		}

		wait, stop := a.Pacer.Pace(elapsed, count)
		if stop {
			return
		}

		time.Sleep(wait)

		if workers < a.MaxWorkers {
			select {
			case hits <- struct{}{}:
				count++
				continue
			case <-a.stopch:
				return
			default:
				// all workers are blocked. start one more and try again
				workers++
				wg.Add(1)
				go a.run(&wg, hits, results)
			}
		}

		select {
		case hits <- struct{}{}:
			count++
		case <-a.stopch:
			return
		}
	}
}

// Stop stops the current attack if its running.
func (a *Attack) Stop() {
	select {
	case <-a.stopch:
		return
	default:
		close(a.stopch)
	}
}

func (a *Attack) Done() chan struct{} {
	return a.stopch
}

func (a *Attack) run(workers *sync.WaitGroup, ticks <-chan struct{}, results chan<- *Result) {
	defer workers.Done()
	for range ticks {
		results <- a.hit()
	}
}

var ErrNoResult = errors.New("no result returned from hitter")

func (a *Attack) hit() *Result {
	var t Target
	if err := a.Targeter(&t); err != nil {
		a.Stop()
		return &Result{Attack: a.Name, Error: err.Error()}
	}

	if t.Header == nil {
		t.Header = make(http.Header, 2)
	} else {
		t.Header = t.Header.Clone()
	}

	if a.Name != "" {
		t.Header["X-Vegeta-Attack"] = []string{a.Name}
	}

	a.seqmu.Lock()
	timestamp := a.began.Add(time.Since(a.began))
	seq := a.seq
	a.seq++
	a.seqmu.Unlock()

	t.Header["X-Vegeta-Seq"] = []string{strconv.FormatUint(seq, 10)}

	r := a.Hitter.Hit(&t)
	if r == nil {
		r = &Result{Error: ErrNoResult.Error()}
	}

	r.Latency = time.Since(timestamp)
	r.Attack = a.Name
	r.Timestamp = timestamp
	r.Seq = seq

	return r
}

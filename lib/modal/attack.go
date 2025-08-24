package modal

import (
	"context"
	"crypto/tls"
	"math"
	"net"
	"sync"
	"time"

	"github.com/modal-labs/libmodal/modal-go"
	"github.com/tsenart/vegeta/v12/lib"
)

// Attacker is an attack executor which wraps an http.Client
type Attacker struct {
	stopch     chan struct{}
	stopOnce   sync.Once
	workers    uint64
	maxWorkers uint64
	maxBody    int64
	seqmu      sync.Mutex
	seq        uint64
	began      time.Time
	chunked    bool
	functions  map[string]*modal.Function
}

const (
	// DefaultTimeout is the default amount of time an Attacker waits for a request
	// before it times out.
	DefaultTimeout = 30 * time.Second
	// DefaultWorkers is the default initial number of workers used to carry an attack.
	DefaultWorkers = 10
	// DefaultMaxWorkers is the default maximum number of workers used to carry an attack.
	DefaultMaxWorkers = math.MaxUint64
	// DefaultMaxBody is the default max number of bytes to be read from response bodies.
	// Defaults to no limit.
	DefaultMaxBody = int64(-1)
)

var (
	// DefaultLocalAddr is the default local IP address an Attacker uses.
	DefaultLocalAddr = net.IPAddr{IP: net.IPv4zero}
	// DefaultTLSConfig is the default tls.Config an Attacker uses.
	DefaultTLSConfig = &tls.Config{InsecureSkipVerify: false}
)

// NewAttacker returns a new Attacker with default options which are overridden
// by the optionally provided opts.
func NewAttacker(targets []Target, opts ...func(*Attacker)) (*Attacker, error) {
	a := &Attacker{
		stopch:     make(chan struct{}),
		stopOnce:   sync.Once{},
		workers:    DefaultWorkers,
		maxWorkers: DefaultMaxWorkers,
		maxBody:    DefaultMaxBody,
		functions:  make(map[string]*modal.Function),
	}

	for _, opt := range opts {
		opt(a)
	}

	ctx := context.Background()
	for _, t := range targets {
		function, err := modal.FunctionLookup(ctx, t.AppName, t.FunctionName, nil)
		if err != nil {
			return nil, err
		}
		a.functions[t.FunctionName] = function
	}

	return a, nil
}

// Workers returns a functional option which sets the initial number of workers
// an Attacker uses to hit its targets. More workers may be spawned dynamically
// to sustain the requested rate in the face of slow responses and errors.
func Workers(n uint64) func(*Attacker) {
	return func(a *Attacker) { a.workers = n }
}

// MaxWorkers returns a functional option which sets the maximum number of workers
// an Attacker can use to hit its targets.
func MaxWorkers(n uint64) func(*Attacker) {
	return func(a *Attacker) { a.maxWorkers = n }
}

// Timeout returns a functional option which sets the maximum amount of time
// an Attacker will wait for a request to be responded to and completely read.
//func Timeout(d time.Duration) func(*Attacker) {
//	return func(a *Attacker) {
//		a.client.Timeout = d
//	}
//}

// MaxBody returns a functional option which limits the max number of bytes
// read from response bodies. Set to -1 to disable any limits.
func MaxBody(n int64) func(*Attacker) {
	return func(a *Attacker) { a.maxBody = n }
}

type attack struct {
	name  string
	began time.Time

	seqmu sync.Mutex
	seq   uint64
}

// Attack reads its Targets from the passed Targeter and attacks them at
// the rate specified by the Pacer. When the duration is zero the attack
// runs until Stop is called. Results are sent to the returned channel as soon
// as they arrive and will have their Attack field set to the given name.
func (a *Attacker) Attack(tr Targeter, p vegeta.Pacer, du time.Duration, name string) <-chan *vegeta.Result {
	var wg sync.WaitGroup

	workers := a.workers
	if workers > a.maxWorkers {
		workers = a.maxWorkers
	}

	atk := &attack{
		name:  name,
		began: time.Now(),
	}

	results := make(chan *vegeta.Result)
	ticks := make(chan struct{})
	for i := uint64(0); i < workers; i++ {
		wg.Add(1)
		go a.attack(tr, atk, &wg, ticks, results)
	}

	go func() {
		defer func() {
			close(ticks)
			wg.Wait()
			close(results)
			a.Stop()
		}()

		count := uint64(0)
		for {
			elapsed := time.Since(atk.began)
			if du > 0 && elapsed > du {
				return
			}

			wait, stop := p.Pace(elapsed, count)
			if stop {
				return
			}

			time.Sleep(wait)

			if workers < a.maxWorkers {
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
					go a.attack(tr, atk, &wg, ticks, results)
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

// Stop stops the current attack. The return value indicates whether this call
// has signalled the attack to stop (`true` for the first call) or whether it
// was a noop because it has been previously signalled to stop (`false` for any
// subsequent calls).
func (a *Attacker) Stop() bool {
	select {
	case <-a.stopch:
		return false
	default:
		a.stopOnce.Do(func() { close(a.stopch) })
		return true
	}
}

func (a *Attacker) attack(tr Targeter, atk *attack, workers *sync.WaitGroup, ticks <-chan struct{}, results chan<- *vegeta.Result) {
	defer workers.Done()
	for range ticks {
		results <- a.hit(tr, atk)
	}
}

func (a *Attacker) hit(tr Targeter, atk *attack) *vegeta.Result {
	var (
		res = vegeta.Result{Attack: atk.name}
		tgt Target
		err error
	)

	//
	// Subtleness ahead! We need to compute the result timestamp in
	// the same critical section that protects the increment of the sequence
	// number because we want the same total ordering of timestamps and sequence
	// numbers. That is, we wouldn't want two results A and B where A.seq > B.seq
	// but A.timestamp < B.timestamp.
	//
	// Additionally, we calculate the result timestamp based on the same beginning
	// timestamp using the Add method, which will use monotonic time calculations.
	//
	atk.seqmu.Lock()
	res.Timestamp = atk.began.Add(time.Since(atk.began))
	res.Seq = atk.seq
	atk.seq++
	atk.seqmu.Unlock()

	defer func() {
		res.Latency = time.Since(res.Timestamp)
		if err != nil {
			res.Error = err.Error()
		}
	}()

	if err = tr(&tgt); err != nil {
		a.Stop()
		return &res
	}

	res.Method = tgt.FunctionName
	res.URL = tgt.AppName
	function := a.functions[tgt.FunctionName]

	_, err = function.Remote(nil, nil)
	if err == nil {
		res.Code = 200
	} else {
		res.Code = 500
		res.Error = err.Error()
	}
	res.BytesIn = 0  // TODO: payload size in response
	res.BytesOut = 0 // TODO: payload size in request

	return &res
}

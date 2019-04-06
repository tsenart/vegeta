package vegeta

import (
	"context"
	"crypto/tls"
	"fmt"
	"io"
	"io/ioutil"
	"net"
	"net/http"
	"net/url"
	"sync"
	"time"

	"golang.org/x/net/http2"
)

// Attacker is an attack executor which wraps an http.Client
type Attacker struct {
	dialer    *net.Dialer
	client    http.Client
	stopch    chan struct{}
	workers   uint64
	maxBody   int64
	redirects int
	seqmu     sync.Mutex
	seq       uint64
	began     time.Time
}

const (
	// DefaultRedirects is the default number of times an Attacker follows
	// redirects.
	DefaultRedirects = 10
	// DefaultTimeout is the default amount of time an Attacker waits for a request
	// before it times out.
	DefaultTimeout = 30 * time.Second
	// DefaultConnections is the default amount of max open idle connections per
	// target host.
	DefaultConnections = 10000
	// DefaultWorkers is the default initial number of workers used to carry an attack.
	DefaultWorkers = 10
	// DefaultMaxBody is the default max number of bytes to be read from response bodies.
	// Defaults to no limit.
	DefaultMaxBody = int64(-1)
	// NoFollow is the value when redirects are not followed but marked successful
	NoFollow = -1
)

var (
	// DefaultLocalAddr is the default local IP address an Attacker uses.
	DefaultLocalAddr = net.IPAddr{IP: net.IPv4zero}
	// DefaultTLSConfig is the default tls.Config an Attacker uses.
	DefaultTLSConfig = &tls.Config{InsecureSkipVerify: true}
)

// NewAttacker returns a new Attacker with default options which are overridden
// by the optionally provided opts.
func NewAttacker(opts ...func(*Attacker)) *Attacker {
	a := &Attacker{
		stopch:  make(chan struct{}),
		workers: DefaultWorkers,
		maxBody: DefaultMaxBody,
		began:   time.Now(),
	}

	a.dialer = &net.Dialer{
		LocalAddr: &net.TCPAddr{IP: DefaultLocalAddr.IP, Zone: DefaultLocalAddr.Zone},
		KeepAlive: 30 * time.Second,
	}

	a.client = http.Client{
		Timeout: DefaultTimeout,
		Transport: &http.Transport{
			Proxy:               http.ProxyFromEnvironment,
			Dial:                a.dialer.Dial,
			TLSClientConfig:     DefaultTLSConfig,
			MaxIdleConnsPerHost: DefaultConnections,
		},
	}

	for _, opt := range opts {
		opt(a)
	}

	return a
}

// Workers returns a functional option which sets the initial number of workers
// an Attacker uses to hit its targets. More workers may be spawned dynamically
// to sustain the requested rate in the face of slow responses and errors.
func Workers(n uint64) func(*Attacker) {
	return func(a *Attacker) { a.workers = n }
}

// Connections returns a functional option which sets the number of maximum idle
// open connections per target host.
func Connections(n int) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.MaxIdleConnsPerHost = n
	}
}

// Redirects returns a functional option which sets the maximum
// number of redirects an Attacker will follow.
func Redirects(n int) func(*Attacker) {
	return func(a *Attacker) {
		a.redirects = n
		a.client.CheckRedirect = func(_ *http.Request, via []*http.Request) error {
			switch {
			case n == NoFollow:
				return http.ErrUseLastResponse
			case n < len(via):
				return fmt.Errorf("stopped after %d redirects", n)
			default:
				return nil
			}
		}
	}
}

// Proxy returns a functional option which sets the `Proxy` field on
// the http.Client's Transport
func Proxy(proxy func(*http.Request) (*url.URL, error)) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.Proxy = proxy
	}
}

// Timeout returns a functional option which sets the maximum amount of time
// an Attacker will wait for a request to be responded to and completely read.
func Timeout(d time.Duration) func(*Attacker) {
	return func(a *Attacker) {
		a.client.Timeout = d
	}
}

// LocalAddr returns a functional option which sets the local address
// an Attacker will use with its requests.
func LocalAddr(addr net.IPAddr) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		a.dialer.LocalAddr = &net.TCPAddr{IP: addr.IP, Zone: addr.Zone}
		tr.Dial = a.dialer.Dial
	}
}

// KeepAlive returns a functional option which toggles KeepAlive
// connections on the dialer and transport.
func KeepAlive(keepalive bool) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.DisableKeepAlives = !keepalive
		if !keepalive {
			a.dialer.KeepAlive = 0
			tr.Dial = a.dialer.Dial
		}
	}
}

// TLSConfig returns a functional option which sets the *tls.Config for a
// Attacker to use with its requests.
func TLSConfig(c *tls.Config) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.TLSClientConfig = c
	}
}

// HTTP2 returns a functional option which enables or disables HTTP/2 support
// on requests performed by an Attacker.
func HTTP2(enabled bool) func(*Attacker) {
	return func(a *Attacker) {
		if tr := a.client.Transport.(*http.Transport); enabled {
			http2.ConfigureTransport(tr)
		} else {
			tr.TLSNextProto = map[string]func(string, *tls.Conn) http.RoundTripper{}
		}
	}
}

// H2C returns a functional option which enables H2C support on requests
// performed by an Attacker
func H2C(enabled bool) func(*Attacker) {
	return func(a *Attacker) {
		if tr := a.client.Transport.(*http.Transport); enabled {
			a.client.Transport = &http2.Transport{
				AllowHTTP: true,
				DialTLS: func(network, addr string, cfg *tls.Config) (net.Conn, error) {
					return tr.Dial(network, addr)
				},
			}
		}
	}
}

// MaxBody returns a functional option which limits the max number of bytes
// read from response bodies. Set to -1 to disable any limits.
func MaxBody(n int64) func(*Attacker) {
	return func(a *Attacker) { a.maxBody = n }
}

// UnixSocket changes the dialer for the attacker to use the specified unix socket file
func UnixSocket(socket string) func(*Attacker) {
	return func(a *Attacker) {
		if tr, ok := a.client.Transport.(*http.Transport); socket != "" && ok {
			tr.DialContext = func(_ context.Context, _, _ string) (net.Conn, error) {
				return net.Dial("unix", socket)
			}
		}
	}
}

// Client returns a functional option that allows you to bring your own http.Client
func Client(c *http.Client) func(*Attacker) {
	return func(a *Attacker) { a.client = *c }
}

// A Rater defines the rate of hits during an Attack by
// returning the duration an Attacker should wait until hiting
// the next Target. When a negative value time is returned,
// an Attacker will stop.
type Rater interface {
	Wait(began, now time.Time) time.Duration
}

// A RaterFunc is a function adapter type that implements the
// Rater interface.
type RaterFunc func(began, now time.Time) time.Duration

// Wait implements the Rater interface.
func (f RaterFunc) Wait(began, now time.Time) time.Duration {
	return f(began, now)
}

// A FixedRater is a Rater that produces hits at a fixed rate
// for a given duration. It is not safe for concurrent use.
type FixedRater struct {
	rate  Rate
	hits  uint64
	count uint64
}

// NewFixedRater returns a new FixedRater with the given Rate and duration.
// When duration is zero, the rater will never stop.
func NewFixedRater(rate Rate, du time.Duration) *FixedRater {
	r := FixedRater{rate: rate}
	if du != 0 && !rate.IsZero() {
		r.hits = uint64(du) /
			(uint64(rate.Per.Nanoseconds() / int64(rate.Freq)))
	}
	return &r
}

// Wait is an utility method that calls the rater function itself.
// It's meant to aid readability.
func (r *FixedRater) Wait(began, now time.Time) time.Duration {
	if r.hits != 0 && r.count == r.hits {
		return -1
	}

	r.count++
	interval := uint64(r.rate.Per.Nanoseconds() / int64(r.rate.Freq))
	delta := time.Duration(r.count * interval)

	if wait := began.Add(delta).Sub(now); wait > 0 {
		return wait
	}

	return 0
}

// Rate sends a constant rate of hits to the target.
type Rate struct {
	Freq int           // Frequency (number of occurrences) per ...
	Per  time.Duration // Time unit, usually 1s
}

// IsZero returns true if either Freq or Per are zero valued.
func (r Rate) IsZero() bool {
	return r.Freq == 0 || r.Per == 0
}

// String returns a pretty-printed description of the rate, e.g.:
//   Rate{1 hits/1s} for Rate{Freq:1, Per: time.Second}
func (r Rate) String() string {
	return fmt.Sprintf("Rate{%d hits/%s}", r.Freq, r.Per)
}

// Attack reads its Targets from the passed Targeter and attacks them at
// the rate produced by the given Rater. Results are sent to the returned
// channel as soon as they arrive and will have their Attack field set to
// the given name.
func (a *Attacker) Attack(tr Targeter, r Rater, name string) <-chan *Result {
	var workers sync.WaitGroup
	results := make(chan *Result)
	ticks := make(chan struct{})
	for i := uint64(0); i < a.workers; i++ {
		workers.Add(1)
		go a.attack(tr, name, &workers, ticks, results)
	}

	go func() {
		defer close(results)
		defer workers.Wait()
		defer close(ticks)
		began := time.Now()
		for {
			wait := r.Wait(began, time.Now())
			if wait < 0 {
				return
			}
			time.Sleep(wait)

			select {
			case ticks <- struct{}{}:
			case <-a.stopch:
				return
			default: // all workers are blocked. start one more and try again
				workers.Add(1)
				go a.attack(tr, name, &workers, ticks, results)
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

func (a *Attacker) hit(tr Targeter, name string) *Result {
	var (
		res = Result{Attack: name}
		tgt Target
		err error
	)

	defer func() {
		if err != nil {
			res.Error = err.Error()
		}
	}()

	a.seqmu.Lock()
	res.Timestamp = a.began.Add(time.Since(a.began))
	res.Seq = a.seq
	a.seq++
	a.seqmu.Unlock()

	if err = tr(&tgt); err != nil {
		a.Stop()
		return &res
	}

	req, err := tgt.Request()
	if err != nil {
		return &res
	}

	r, err := a.client.Do(req)
	if err != nil {
		return &res
	}
	defer r.Body.Close()

	body := io.Reader(r.Body)
	if a.maxBody >= 0 {
		body = io.LimitReader(r.Body, a.maxBody)
	}

	if res.Body, err = ioutil.ReadAll(body); err != nil {
		return &res
	} else if _, err = io.Copy(ioutil.Discard, r.Body); err != nil {
		return &res
	}

	res.Latency = time.Since(res.Timestamp)
	res.BytesIn = uint64(len(res.Body))

	if req.ContentLength != -1 {
		res.BytesOut = uint64(req.ContentLength)
	}

	if res.Code = uint16(r.StatusCode); res.Code < 200 || res.Code >= 400 {
		res.Error = r.Status
	}

	return &res
}

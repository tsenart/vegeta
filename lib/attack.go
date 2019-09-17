package vegeta

import (
	"context"
	"crypto/tls"
	"fmt"
	"io"
	"io/ioutil"
	"math"
	"net"
	"net/http"
	"net/url"
	"sync"
	"time"

	"golang.org/x/net/http2"
)

// Attacker is an attack executor which wraps an http.Client
type Attacker struct {
	dialer     *net.Dialer
	client     http.Client
	stopch     chan struct{}
	workers    uint64
	maxWorkers uint64
	maxBody    int64
	redirects  int
	seqmu      sync.Mutex
	seq        uint64
	began      time.Time
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
	// DefaultMaxWorkers is the default maximum number of workers used to carry an attack.
	DefaultMaxWorkers = math.MaxUint64
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
		stopch:     make(chan struct{}),
		workers:    DefaultWorkers,
		maxWorkers: DefaultMaxWorkers,
		maxBody:    DefaultMaxBody,
		began:      time.Now(),
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

// MaxWorkers returns a functional option which sets the maximum number of workers
// an Attacker can use to hit its targets.
func MaxWorkers(n uint64) func(*Attacker) {
	return func(a *Attacker) { a.maxWorkers = n }
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

// ProxyHeader returns a functional option that allows you to add your own
// Proxy CONNECT headers
func ProxyHeader(h http.Header) func(*Attacker) {
	return func(a *Attacker) {
		if tr, ok := a.client.Transport.(*http.Transport); ok {
			tr.ProxyConnectHeader = h
		}
	}
}

// Attack reads its Targets from the passed Targeter and attacks them at
// the rate specified by the Pacer. When the duration is zero the attack
// runs until Stop is called. Results are sent to the returned channel as soon
// as they arrive and will have their Attack field set to the given name.
func (a *Attacker) Attack(tr Targeter, p Pacer, du time.Duration, name string) <-chan *Result {
	var wg sync.WaitGroup

	workers := a.workers
	if workers > a.maxWorkers {
		workers = a.maxWorkers
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

func (a *Attacker) hit(tr Targeter, name string) *Result {
	var (
		res = Result{Attack: name}
		tgt Target
		err error
	)

	a.seqmu.Lock()
	res.Timestamp = a.began.Add(time.Since(a.began))
	res.Seq = a.seq
	a.seq++
	a.seqmu.Unlock()

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

	res.Method = tgt.Method
	res.URL = tgt.URL

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

	res.BytesIn = uint64(len(res.Body))

	if req.ContentLength != -1 {
		res.BytesOut = uint64(req.ContentLength)
	}

	if res.Code = uint16(r.StatusCode); res.Code < 200 || res.Code >= 400 {
		res.Error = r.Status
	}

	return &res
}

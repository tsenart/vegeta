package vegeta

import (
	"crypto/tls"
	"fmt"
	"io/ioutil"
	"net"
	"net/http"
	"sync"
	"time"
)

// Attacker is an attack executor which wraps an http.Client
type Attacker struct {
	dialer  *net.Dialer
	client  http.Client
	stop    chan struct{}
	workers uint64
}

var (
	// DefaultRedirects is the default number of times an Attacker follows
	// redirects.
	DefaultRedirects = 10
	// DefaultTimeout is the default amount of time an Attacker waits for a request
	// before it times out.
	DefaultTimeout = 30 * time.Second
	// DefaultLocalAddr is the default local IP address an Attacker uses.
	DefaultLocalAddr = net.IPAddr{IP: net.IPv4zero}
	// DefaultTLSConfig is the default tls.Config an Attacker uses.
	DefaultTLSConfig = &tls.Config{InsecureSkipVerify: true}
)

// NewAttacker returns a new Attacker with default options which are overridden
// by the optionally provided opts.
func NewAttacker(opts ...func(*Attacker)) *Attacker {
	a := &Attacker{stop: make(chan struct{})}
	a.dialer = &net.Dialer{
		LocalAddr: &net.TCPAddr{IP: DefaultLocalAddr.IP, Zone: DefaultLocalAddr.Zone},
		KeepAlive: 30 * time.Second,
		Timeout:   DefaultTimeout,
	}
	a.client = http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyFromEnvironment,
			Dial:  a.dialer.Dial,
			ResponseHeaderTimeout: DefaultTimeout,
			TLSClientConfig:       DefaultTLSConfig,
			TLSHandshakeTimeout:   10 * time.Second,
		},
	}
	for _, opt := range opts {
		opt(a)
	}
	return a
}

// Workers returns a functional option which sets the number of workers
// an Attacker uses to hit its targets.
// If zero or greater than the total number of hits, workers will be capped
// to that maximum.
func Workers(n uint64) func(*Attacker) {
	return func(a *Attacker) { a.workers = n }
}

// Redirects returns a functional option which sets the maximum
// number of redirects an Attacker will follow.
func Redirects(n int) func(*Attacker) {
	return func(a *Attacker) {
		a.client.CheckRedirect = func(_ *http.Request, via []*http.Request) error {
			if len(via) > n {
				return fmt.Errorf("stopped after %d redirects", n)
			}
			return nil
		}
	}
}

// Timeout returns a functional option which sets the maximum amount of time
// an Attacker will wait for a request to be responded to.
func Timeout(d time.Duration) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.ResponseHeaderTimeout = d
		a.dialer.Timeout = d
		tr.Dial = a.dialer.Dial
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

// Attack reads its Targets from the passed Targeter and attacks them at
// the rate specified for duration time. Results are put into the returned channel
// as soon as they arrive.
func (a *Attacker) Attack(tr Targeter, rate uint64, du time.Duration) chan *Result {
	resc := make(chan *Result)
	hits := rate * uint64(du.Seconds())
	wrk := a.workers
	if wrk == 0 || wrk > hits {
		wrk = hits
	}
	share := hits / wrk
	throttle := time.NewTicker(time.Duration(1e9 / rate))

	var wg sync.WaitGroup
	for i := uint64(0); i < wrk; i++ {
		wg.Add(1)
		go func(share uint64) {
			defer wg.Done()
			for j := uint64(0); j < share; j++ {
				select {
				case tm := <-throttle.C:
					resc <- a.hit(tr, tm)
				case <-a.stop:
					return
				}
			}
		}(share)
	}

	go func() {
		wg.Wait()
		close(resc)
		throttle.Stop()
	}()

	return resc
}

// Stop stops the current attack.
func (a *Attacker) Stop() { close(a.stop) }

func (a *Attacker) hit(tr Targeter, tm time.Time) *Result {
	res := Result{Timestamp: tm}
	defer func() { res.Latency = time.Since(tm) }()

	tgt, err := tr()
	if err != nil {
		res.Error = err.Error()
		return &res
	}

	req, err := tgt.Request()
	if err != nil {
		res.Error = err.Error()
		return &res
	}

	r, err := a.client.Do(req)
	if err != nil {
		res.Error = err.Error()
		return &res
	}
	defer r.Body.Close()

	res.BytesOut = uint64(req.ContentLength)
	res.Code = uint16(r.StatusCode)
	if body, err := ioutil.ReadAll(r.Body); err != nil {
		if res.Code < 200 || res.Code >= 400 {
			res.Error = string(body)
		}
	} else {
		res.BytesIn = uint64(len(body))
	}
	return &res
}

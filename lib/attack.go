package vegeta

import (
	"crypto/tls"
	"fmt"
	"io/ioutil"
	"net"
	"net/http"
	"sync/atomic"
	"time"
)

// Attacker is an attack executor which wraps an http.Client
type Attacker struct {
	dialer *net.Dialer
	client http.Client
}

var (
	// DefaultRedirects represents the number of times the DefaultAttacker
	// follows redirects
	DefaultRedirects = 10
	// DefaultTimeout represents the amount of time the DefaultAttacker waits
	// for a request before it times out
	DefaultTimeout = 30 * time.Second
	// DefaultLocalAddr is the local IP address the DefaultAttacker uses in its
	// requests
	DefaultLocalAddr = net.IPAddr{IP: net.IPv4zero}
	// DefaultTLSConfig is the default tls.Config the DefaultAttacker uses in its
	// requests
	DefaultTLSConfig = &tls.Config{InsecureSkipVerify: true}
)

// NewAttacker returns a new Attacker with default options which are overridden
// by the optionally provided opts.
func NewAttacker(opts ...func(*Attacker)) *Attacker {
	a := &Attacker{}
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
		a.client.Transport = tr
	}
}

// LocalAddr returns a functional option which sets the local address
// an Attacker will use with its requests.
func LocalAddr(addr net.IPAddr) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		a.dialer.LocalAddr = &net.TCPAddr{IP: addr.IP, Zone: addr.Zone}
		tr.Dial = a.dialer.Dial
		a.client.Transport = tr
	}
}

// TLSConfig returns a functional option which sets the *tls.Config for a
// Attacker to use with its requests.
func TLSConfig(c *tls.Config) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.TLSClientConfig = c
		a.client.Transport = tr
	}
}

// Attack reads its Targets from the passed Targeter and attacks them at
// the rate specified for duration time. Results are put into the returned channel
// as soon as they arrive.
//
// If the passed Targeter doesn't provided enough Targets, ErrNoTargets
// is returned.
func (a *Attacker) Attack(tr Targeter, rate uint64, du time.Duration) chan *Result {
	hits := rate * uint64(du.Seconds())
	resc := make(chan *Result)
	throttle := time.NewTicker(time.Duration(1e9 / rate))

	var done, i uint64
	for ; i < hits; i++ {
		go func() {
			<-throttle.C
			resc <- a.hit(tr)
			if atomic.AddUint64(&done, 1) == hits {
				close(resc)
				throttle.Stop()
			}
		}()
	}

	return resc
}

func (a *Attacker) hit(tr Targeter) *Result {
	tgt, err := tr()
	if err != nil {
		return &Result{Error: err.Error()}
	}

	res := new(Result)
	req, err := tgt.Request()
	if err != nil {
		res.Error = err.Error()
		return res
	}

	res.Timestamp = time.Now()
	r, err := a.client.Do(req)
	res.Latency = time.Since(res.Timestamp)
	if err != nil {
		res.Error = err.Error()
		return res
	}
	defer r.Body.Close()

	res.BytesOut = uint64(req.ContentLength)
	res.Code = uint16(r.StatusCode)
	if body, err := ioutil.ReadAll(r.Body); err != nil {
		if res.Code < 200 || res.Code >= 300 {
			res.Error = string(body)
		}
	} else {
		res.BytesIn = uint64(len(body))
	}
	res.Latency = time.Since(res.Timestamp)

	return res
}

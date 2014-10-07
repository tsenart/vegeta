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
type Attacker struct{ client http.Client }

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

// NewAttacker returns a pointer to a new Attacker
//
// redirects is the max amount of redirects the attacker will follow.
// Use DefaultRedirects for a sensible default.
//
// timeout is the client side timeout for each request.
// Use DefaultTimeout for a sensible default.
//
// laddr is the local IP address used for each request.
// Use DefaultLocalAddr for a sensible default.
//
// tlsc is the *tls.Config used for each HTTPS request.
// Use DefaultTLSConfig for a sensible default.
func NewAttacker(redirects int, timeout time.Duration, laddr net.IPAddr, tlsc *tls.Config) *Attacker {
	return &Attacker{http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyFromEnvironment,
			Dial: (&net.Dialer{
				Timeout:   timeout,
				KeepAlive: 30 * time.Second,
				LocalAddr: &net.TCPAddr{IP: laddr.IP, Zone: laddr.Zone},
			}).Dial,
			ResponseHeaderTimeout: timeout,
			TLSClientConfig:       tlsc,
			TLSHandshakeTimeout:   10 * time.Second,
		},
		CheckRedirect: func(_ *http.Request, via []*http.Request) error {
			if len(via) > redirects {
				return fmt.Errorf("stopped after %d redirects", redirects)
			}
			return nil
		},
	}}
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

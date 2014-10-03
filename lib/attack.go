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
type Attacker struct{ http.Client }

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

// DefaultAttacker is the default Attacker used by Attack
var DefaultAttacker = NewAttacker(DefaultRedirects, DefaultTimeout, DefaultLocalAddr, DefaultTLSConfig)

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

// Attack hits the passed Targets (http.Requests) at the rate specified for
// duration time and then waits for all the requests to come back.
// The results of the attack are put into a slice which is returned.
//
// Attack is a wrapper around DefaultAttacker.Attack
func Attack(tch <-chan *Target, maxreqs uint64) Results {
	return DefaultAttacker.Attack(tch, maxreqs)
}

// Attack attacks the passed Targets (http.Requests) at the rate specified for
// duration time and then waits for all the requests to come back.
// The results of the attack are put into a slice which is returned.
func (a *Attacker) Attack(targetCh <-chan *Target, maxreqs uint64) Results {
	resc := make(chan *Result)

	var wg sync.WaitGroup

	go func() {

		// fire up the request pool
		for i := uint64(0); i < maxreqs; i++ {
			wg.Add(1)

			go func() {
				for t := range targetCh {
					resc <- a.hit(t)
				}
				wg.Done()
			}()
		}

		wg.Wait()
		close(resc)
	}()

	var results []*Result
	for r := range resc {
		results = append(results, r)
	}

	return Results(results).Sort()
}

func (a *Attacker) hit(tgt *Target) (res *Result) {
	req, err := tgt.Request()
	if err != nil {
		res.Error = err.Error()
		return res
	}

	res = &Result{}
	res.Timestamp = time.Now()
	r, err := a.Do(req)
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

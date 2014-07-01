package vegeta

import (
	"crypto/tls"
	"fmt"
	"io/ioutil"
	"net"
	"net/http"
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
)

// DefaultAttacker is the default Attacker used by Attack
var DefaultAttacker = NewAttacker(DefaultRedirects, DefaultTimeout, DefaultLocalAddr)

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
func NewAttacker(redirects int, timeout time.Duration, laddr net.IPAddr) *Attacker {
	return &Attacker{http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyFromEnvironment,
			Dial: (&net.Dialer{
				Timeout:   timeout,
				KeepAlive: 30 * time.Second,
				LocalAddr: &net.TCPAddr{IP: laddr.IP, Zone: laddr.Zone},
			}).Dial,
			ResponseHeaderTimeout: timeout,
			TLSClientConfig: &tls.Config{
				InsecureSkipVerify: true,
			},
			TLSHandshakeTimeout: 10 * time.Second,
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
func Attack(tgts Targets, rate uint64, du time.Duration) Results {
	return DefaultAttacker.Attack(tgts, rate, du)
}

// Attack attacks the passed Targets (http.Requests) at the rate specified for
// duration time and then waits for all the requests to come back.
// The results of the attack are put into a slice which is returned.
func (a *Attacker) Attack(tgts Targets, rate uint64, du time.Duration) Results {
	hits := int(rate * uint64(du.Seconds()))
	resc := make(chan Result)
	throttle := time.NewTicker(time.Duration(1e9 / rate))
	defer throttle.Stop()

	for i := 0; i < hits; i++ {
		<-throttle.C
		go func(tgt Target) { resc <- a.hit(tgt) }(tgts[i%len(tgts)])
	}

	results := make(Results, 0, hits)
	for len(results) < cap(results) {
		results = append(results, <-resc)
	}

	return results.Sort()
}

func (a *Attacker) hit(tgt Target) (res Result) {
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

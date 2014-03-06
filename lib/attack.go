package vegeta

import (
	"crypto/tls"
	"fmt"
	"io/ioutil"
	"net/http"
	"time"
)

// Attacker is an attack executor, wrapping an http.Client
type Attacker struct{ client http.Client }

// DefaultAttacker is the default Attacker used by Attack
var DefaultAttacker = NewAttacker()

// NewAttacker returns a pointer to a new Attacker
func NewAttacker() *Attacker {
	return &Attacker{http.Client{Transport: &defaultTransport}}
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
func (a Attacker) Attack(tgts Targets, rate uint64, du time.Duration) Results {
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

// SetRedirects sets the max amount of redirects the attacker's http client
// will follow.
func (a *Attacker) SetRedirects(redirects int) {
	a.client.CheckRedirect = func(_ *http.Request, via []*http.Request) error {
		if len(via) > redirects {
			return fmt.Errorf("Stopped after %d redirects", redirects)
		}
		return nil
	}
}

// SetTimeout sets the client side timeout for each request the attacker makes.
func (a *Attacker) SetTimeout(timeout time.Duration) {
	tr := a.client.Transport.(*http.Transport)
	tr.ResponseHeaderTimeout = timeout
	a.client.Transport = tr
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

	return res
}

var defaultTransport = http.Transport{
	TLSClientConfig: &tls.Config{
		InsecureSkipVerify: true,
	},
}

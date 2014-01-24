package vegeta

import (
	"crypto/tls"
	"io/ioutil"
	"net/http"
	"time"
)

// Attacker is an attack executor, wrapping an *http.Client
type Attacker struct{ client *http.Client }

// DefaultAttacker is the default Attacker used by Attack
var DefaultAttacker = Attacker{&http.Client{
	Transport: &http.Transport{
		TLSClientConfig: &tls.Config{
			InsecureSkipVerify: true,
		},
	},
}}

// NewAttacker returns an *Attacker wrapping an *http.Client
func NewAttacker(client *http.Client) *Attacker {
  return &Attacker{client}
}

// Attack hits the passed Targets (http.Requests) at the rate specified for
// duration time and then waits for all the requests to come back.
// The results of the attack are put into a slice which is returned.
//
// Attack is a wrapper around DefaultAttacker.Attack
func Attack(tgts Targets, rate uint64, du time.Duration) Results {
	return DefaultAttacker.Attack(tgts, rate, du)
}

// Attack hits the passed Targets (http.Requests) at the rate specified for
// duration time and then waits for all the requests to come back.
// The results of the attack are put into a slice which is returned.
func (a Attacker) Attack(tgts Targets, rate uint64, du time.Duration) Results {
	total := rate * uint64(du.Seconds())
	hits := make(chan *http.Request, total)
	resc := make(chan Result, total)
	results := make(Results, total)

	go a.drill(rate, hits, resc)
	for i := 0; i < cap(hits); i++ {
		hits <- tgts[i%len(tgts)]
	}
	close(hits)

	for i := 0; i < cap(resc); i++ {
		results[i] = <-resc
	}
	close(resc)

	return results.Sort()
}

// drill loops over the passed reqs channel and executes each request.
// It is throttled to the rate specified.
func (a Attacker) drill(rt uint64, reqs chan *http.Request, resc chan Result) {
	throttle := time.Tick(time.Duration(1e9 / rt))
	for req := range reqs {
		<-throttle
		go a.hit(req, resc)
	}
}

// hit executes the passed http.Request and puts the result into results.
// Both transport errors and unsucessfull requests (non {2xx,3xx}) are
// considered errors.
func (a Attacker) hit(req *http.Request, res chan Result) {
	began := time.Now()
	r, err := a.client.Do(req)
	result := Result{
		Timestamp: began,
		Latency:   time.Since(began),
		BytesOut:  uint64(req.ContentLength),
	}
	if err != nil {
		result.Error = err.Error()
	} else {
		result.Code = uint16(r.StatusCode)
		if body, err := ioutil.ReadAll(r.Body); err != nil {
			if result.Code < 200 || result.Code >= 300 {
				result.Error = string(body)
			}
		} else {
			result.BytesIn = uint64(len(body))
		}
	}
	res <- result
}

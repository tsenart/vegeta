package vegeta

import (
	"crypto/tls"
	"io/ioutil"
	"net/http"
	"time"
)

// Attack hits the passed Targets (http.Requests) at the rate specified for
// duration time and then waits for all the requests to come back.
// The results of the attack are put into a slice which is returned.
func Attack(targets Targets, rate uint64, duration time.Duration) Results {
	total := rate * uint64(duration.Seconds())
	hits := make(chan *http.Request, total)
	res := make(chan Result, total)
	results := make(Results, total)
	// Scatter
	go drill(rate, hits, res)
	for i := 0; i < cap(hits); i++ {
		hits <- targets[i%len(targets)]
	}
	close(hits)
	// Gather
	for i := 0; i < cap(res); i++ {
		results[i] = <-res
	}
	close(res)

	return results.Sort()
}

// drill loops over the passed reqs channel and executes each request.
// It is throttled to the rate specified.
func drill(rate uint64, reqs chan *http.Request, res chan Result) {
	throttle := time.Tick(time.Duration(1e9 / rate))
	for req := range reqs {
		<-throttle
		go hit(req, res)
	}
}

var client = &http.Client{
	Transport: &http.Transport{
		TLSClientConfig: &tls.Config{
			InsecureSkipVerify: true,
		},
	},
}

// hit executes the passed http.Request and puts the result into results.
// Both transport errors and unsucessfull requests (non {2xx,3xx}) are
// considered errors.
func hit(req *http.Request, res chan Result) {
	began := time.Now()
	r, err := client.Do(req)
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

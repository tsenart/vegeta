package vegeta

import (
	"errors"
	"io/ioutil"
	"net/http"
	"time"
)

// Attack hits the passed Targets (http.Requests) at the rate specified for
// duration time and then waits for all the requests to come back.
// The results of the attack are put into the rep Reporter.
func Attack(targets Targets, rate uint64, duration time.Duration, rep Reporter) {
	hits := make(chan *http.Request, rate*uint64((duration).Seconds()))
	defer close(hits)
	results := make(chan *Result, cap(hits))
	defer close(results)
	go drill(rate, hits, results) // Attack!
	for i := 0; i < cap(hits); i++ {
		hits <- targets[i%len(targets)]
	}
	// Wait for all requests to finish
	for i := 0; i < cap(results); i++ {
		rep.add(<-results)
	}
}

// Result represents the metrics we want out of an http.Response
type Result struct {
	Code      uint64
	Timestamp time.Time
	Timing    time.Duration
	BytesOut  uint64
	BytesIn   uint64
	Error     error
}

// drill loops over the passed reqs channel and executes each request.
// It is throttled to the rate specified.
func drill(rate uint64, reqs chan *http.Request, res chan *Result) {
	throttle := time.Tick(time.Duration(1e9 / rate))
	for req := range reqs {
		<-throttle
		go hit(req, res)
	}
}

// hit executes the passed http.Request and puts a generated *result into res.
// Both transport errors and unsucessfull requests (non {2xx,3xx}) are
// considered errors which are set in the Response.
func hit(req *http.Request, res chan *Result) {
	began := time.Now()
	r, err := http.DefaultClient.Do(req)
	result := &Result{
		Timestamp: began,
		Timing:    time.Since(began),
		BytesOut:  uint64(req.ContentLength),
		Error:     err,
	}
	if err == nil {
		result.BytesIn, result.Code = uint64(r.ContentLength), uint64(r.StatusCode)
		if body, err := ioutil.ReadAll(r.Body); err != nil && (result.Code < 200 || result.Code >= 300) {
			result.Error = errors.New(string(body))
		}
	}

	res <- result
}

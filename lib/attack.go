package vegeta

import (
	"errors"
	"io/ioutil"
	"net/http"
	"sort"
	"time"
)

// Attack hits the passed Targets (http.Requests) at the rate specified for
// duration time and then waits for all the requests to come back.
// The results of the attack are put into a slice which is returned.
func Attack(targets Targets, rate uint64, duration time.Duration) []Result {
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

	sort.Sort(results)

	return results
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

// Results is a slice of Result defined only to be sortable with sort.Interface
type Results []Result

func (r Results) Len() int           { return len(r) }
func (r Results) Less(i, j int) bool { return r[i].Timestamp.Before(r[j].Timestamp) }
func (r Results) Swap(i, j int)      { r[i], r[j] = r[j], r[i] }

// drill loops over the passed reqs channel and executes each request.
// It is throttled to the rate specified.
func drill(rate uint64, reqs chan *http.Request, res chan Result) {
	throttle := time.Tick(time.Duration(1e9 / rate))
	for req := range reqs {
		<-throttle
		go hit(req, res)
	}
}

// hit executes the passed http.Request and puts the result into results.
// Both transport errors and unsucessfull requests (non {2xx,3xx}) are
// considered errors.
func hit(req *http.Request, res chan Result) {
	began := time.Now()
	r, err := http.DefaultClient.Do(req)
	result := Result{
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

package vegeta

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"math/rand"
	"net/http"
	"time"
)

// Target is a HTTP request blueprint
type Target struct {
	Method string
	URL    string
	Body   []byte
	Header http.Header
}

// Request creates an *http.Request out of Target and returns it along with an
// error in case of failure.
func (t *Target) Request() (*http.Request, error) {
	req, err := http.NewRequest(t.Method, t.URL, bytes.NewBuffer(t.Body))
	if err != nil {
		return nil, err
	}
	for k, vs := range t.Header {
		req.Header[k] = make([]string, len(vs))
		copy(req.Header[k], vs)
	}
	if host := req.Header.Get("Host"); host != "" {
		req.Host = host
	}
	return req, nil
}

// Targets is a slice of Targets which can be shuffled
type Targets []Target

// Shuffle randomly alters the order of Targets with the provided seed
func (t Targets) Shuffle(seed int64) {
	rand.Seed(seed)
	for i, rnd := range rand.Perm(len(t)) {
		t[i], t[rnd] = t[rnd], t[i]
	}
}

// TargetGenerator generates a target at each invocation
type TargetGenerator func(chan<- *Target) error

// NewFileTargetGenerator returns a TargetGenerator
func NewStreamTargetGenerator(r io.Reader, body []byte, header http.Header) TargetGenerator {
	return func(tch chan<- *Target) error {
		sc := bufio.NewScanner(r)
		for sc.Scan() {
			line := bytes.TrimSpace(sc.Bytes())
			if len(line) == 0 || bytes.HasPrefix(line, []byte("//")) {
				// Skipping comments or blank lines
				continue
			}

			ps := bytes.Split(line, []byte(" "))

			if len(ps) != 2 {
				return fmt.Errorf("invalid request format: `%s`", line)
			}

			tch <- &Target{
				Method: string(ps[0]),
				URL:    string(ps[1]),
				Body:   body,
				Header: header,
			}

		}

		if err := sc.Err(); err != nil {
			return err
		}
		return nil
	}
}

// NewTargetProducer parses a line-separated byte src and returns Targets.
// It sets the passed body and http.Header on all targets.
func NewTargetProducer(rate uint64, du time.Duration, f TargetGenerator) (<-chan *Target, <-chan error) {
	errCh := make(chan error, 1) // 1 so it can complete without a reader
	hits := int(rate * uint64(du.Seconds()))
	tgtCh := make(chan *Target, hits)

	go func() {
		defer close(errCh)
		defer close(tgtCh)

		throttle := time.NewTicker(time.Duration(1e9 / rate))
		defer throttle.Stop()
		for hits > 0 {
			<-throttle.C
			if err := f(tgtCh); err != nil {
				errCh <- err
				return
			}
			hits--
		}
	}()

	return tgtCh, errCh
}

package vegeta

import (
	"bufio"
	"bytes"
	"fmt"
	"math/rand"
	"net/http"
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

// NewTargets parses a line-separated byte src and returns Targets.
// It sets the passed body and http.Header on all targets.
func NewTargets(src []byte, body []byte, header http.Header) (Targets, error) {
	var tgts Targets

	sc := bufio.NewScanner(bytes.NewReader(src))
	for sc.Scan() {
		line := bytes.TrimSpace(sc.Bytes())
		if len(line) == 0 || bytes.HasPrefix(line, []byte("//")) {
			// Skipping comments or blank lines
			continue
		}

		ps := bytes.Split(line, []byte(" "))
		if len(ps) != 2 {
			return nil, fmt.Errorf("invalid request format: `%s`", line)
		}

		tgts = append(tgts, Target{
			Method: string(ps[0]),
			URL:    string(ps[1]),
			Body:   body,
			Header: header,
		})
	}

	if err := sc.Err(); err != nil {
		return nil, err
	}

	return tgts, nil
}

// Shuffle randomly alters the order of Targets with the provided seed
func (t Targets) Shuffle(seed int64) {
	rand.Seed(seed)
	for i, rnd := range rand.Perm(len(t)) {
		t[i], t[rnd] = t[rnd], t[i]
	}
}

package vegeta

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
	"net/http"
	"sync"
	"sync/atomic"
)

// Target is an HTTP request blueprint.
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

// ErrNoTargets is returned when not enough Targets are available.
var ErrNoTargets = errors.New("no targets to attack")

// Targeter is a generator function which returns a new Target
// or an error on every invocation. It is safe for concurrent use.
type Targeter func() (*Target, error)

// NewStaticTargeter returns a Targeter which round-robins over the passed
// Targets.
func NewStaticTargeter(tgts ...*Target) Targeter {
	i := int64(-1)
	return func() (*Target, error) {
		return tgts[atomic.AddInt64(&i, 1)%int64(len(tgts))], nil
	}
}

// NewEagerTargeter eagerly reads all Targets out of the provided io.Reader and
// returns a NewStaticTargeter with them.
// The targets' bodies and headers will be set to the passed body and header arguments.
func NewEagerTargeter(src io.Reader, body []byte, header http.Header) (Targeter, error) {
	var (
		sc   = NewLazyTargeter(src, body, header)
		tgts []*Target
		tgt  *Target
		err  error
	)
	for {
		if tgt, err = sc(); err == ErrNoTargets {
			break
		} else if err != nil {
			return nil, err
		}
		tgts = append(tgts, tgt)
	}
	if len(tgts) == 0 {
		return nil, ErrNoTargets
	}
	return NewStaticTargeter(tgts...), nil
}

// NewLazyTargeter returns a new Targeter that lazily scans Targets from the
// provided io.Reader on every invocation.
// The targets' bodies and headers will be set to the passed body and header arguments.
func NewLazyTargeter(src io.Reader, body []byte, hdr http.Header) Targeter {
	var mu sync.Mutex
	sc := bufio.NewScanner(src)
	return func() (*Target, error) {
		mu.Lock()
		defer mu.Unlock()
		for sc.Scan() {
			line := bytes.TrimSpace(sc.Bytes())
			if len(line) == 0 || bytes.HasPrefix(line, []byte("//")) {
				// Skipping comments or blank lines
				continue
			}
			ps := bytes.Split(line, []byte(" "))
			if len(ps) != 2 {
				return nil, fmt.Errorf("invalid target: `%s`", line)
			}
			return &Target{
				Method: string(ps[0]),
				URL:    string(ps[1]),
				Body:   body,
				Header: hdr,
			}, nil
		}
		return nil, ErrNoTargets
	}
}

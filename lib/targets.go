package vegeta

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"net/http"
	"net/url"
	"regexp"
	"strings"
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
	req, err := http.NewRequest(t.Method, t.URL, bytes.NewReader(t.Body))
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

var (
	// ErrNoTargets is returned when not enough Targets are available.
	ErrNoTargets = errors.New("no targets to attack")
	// ErrNilTarget is returned when the passed Target pointer is nil.
	ErrNilTarget = errors.New("nil target")
)

// A Targeter decodes a Target or returns an error in case of failure.
// Implementations must be safe for concurrent use.
type Targeter func(*Target) error

// NewStaticTargeter returns a Targeter which round-robins over the passed
// Targets.
func NewStaticTargeter(tgts ...Target) Targeter {
	i := int64(-1)
	return func(tgt *Target) error {
		if tgt == nil {
			return ErrNilTarget
		}
		*tgt = tgts[atomic.AddInt64(&i, 1)%int64(len(tgts))]
		return nil
	}
}

// NewEagerTargeter eagerly reads all Targets out of the provided io.Reader and
// returns a NewStaticTargeter with them.
//
// body will be set as the Target's body if no body is provided.
// hdr will be merged with the each Target's headers.
func NewEagerTargeter(src io.Reader, body []byte, header http.Header) (Targeter, error) {
	var (
		sc   = NewLazyTargeter(src, body, header)
		tgts []Target
		tgt  Target
		err  error
	)
	for {
		if err = sc(&tgt); err == ErrNoTargets {
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
//
// body will be set as the Target's body if no body is provided.
// hdr will be merged with the each Target's headers.
func NewLazyTargeter(src io.Reader, body []byte, hdr http.Header) Targeter {
	var mu sync.Mutex
	sc := peekingScanner{src: bufio.NewScanner(src)}
	return func(tgt *Target) (err error) {
		mu.Lock()
		defer mu.Unlock()

		if tgt == nil {
			return ErrNilTarget
		}

		var line string
		for {
			if !sc.Scan() {
				return ErrNoTargets
			}
			line = strings.TrimSpace(sc.Text())
			if len(line) != 0 {
				break
			}
		}

		tgt.Body = body
		tgt.Header = http.Header{}
		for k, vs := range hdr {
			tgt.Header[k] = vs
		}

		tokens := strings.SplitN(line, " ", 2)
		if len(tokens) < 2 {
			return fmt.Errorf("bad target: %s", line)
		}
		if !startsWithHTTPMethod(line) {
			return fmt.Errorf("bad method: %s", tokens[0])
		}
		tgt.Method = tokens[0]
		if _, err = url.ParseRequestURI(tokens[1]); err != nil {
			return fmt.Errorf("bad URL: %s", tokens[1])
		}
		tgt.URL = tokens[1]
		line = strings.TrimSpace(sc.Peek())
		if line == "" || startsWithHTTPMethod(line) {
			return nil
		}
		for sc.Scan() {
			if line = strings.TrimSpace(sc.Text()); line == "" {
				break
			} else if strings.HasPrefix(line, "@") {
				if tgt.Body, err = ioutil.ReadFile(line[1:]); err != nil {
					return fmt.Errorf("bad body: %s", err)
				}
				break
			}
			tokens = strings.SplitN(line, ":", 2)
			if len(tokens) < 2 {
				return fmt.Errorf("bad header: %s", line)
			}
			for i := range tokens {
				if tokens[i] = strings.TrimSpace(tokens[i]); tokens[i] == "" {
					return fmt.Errorf("bad header: %s", line)
				}
			}
			// Add key/value directly to the http.Header (map[string][]string).
			// http.Header.Add() canonicalizes keys but vegeta is used
			// to test systems that require case-sensitive headers.
			tgt.Header[tokens[0]] = append(tgt.Header[tokens[0]], tokens[1])
		}
		if err = sc.Err(); err != nil {
			return ErrNoTargets
		}
		return nil
	}
}

var httpMethodChecker = regexp.MustCompile("^[A-Z]+\\s")

// A line starts with an http method when the first word is uppercase ascii
// followed by a space.
func startsWithHTTPMethod(t string) bool {
	return httpMethodChecker.MatchString(t)
}

// Wrap a Scanner so we can cheat and look at the next value and react accordingly,
// but still have it be around the next time we Scan() + Text()
type peekingScanner struct {
	src    *bufio.Scanner
	peeked string
}

func (s *peekingScanner) Err() error {
	return s.src.Err()
}

func (s *peekingScanner) Peek() string {
	if !s.src.Scan() {
		return ""
	}
	s.peeked = s.src.Text()
	return s.peeked
}

func (s *peekingScanner) Scan() bool {
	if s.peeked == "" {
		return s.src.Scan()
	}
	return true
}

func (s *peekingScanner) Text() string {
	if s.peeked == "" {
		return s.src.Text()
	}
	t := s.peeked
	s.peeked = ""
	return t
}

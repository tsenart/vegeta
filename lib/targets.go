package vegeta

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"net/http"
	"os"
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
var ErrNoBody = errors.New("No body referenced by file")

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
				continue // skip comments or blank lines
			}
			ps := bytes.Split(line, []byte(" "))
			if len(ps) < 2 {
				return nil, fmt.Errorf("invalid target: `%s`", line)
			}

			method := string(ps[0])
			url := string(ps[1])

			var (
				err       error
				useBody   []byte
				useHeader http.Header
			)

			// Standard target - {METHOD} {url} + body + header from params
			if len(ps) == 2 {
				useBody = body
				useHeader = hdr

				// Enhanced target:
				//   Headers only, including one with an embedded space:
				//     GET {url} -HFoo:Bar -HX-Do-Not-Do:true -HSome-Name:Token[SPACE]ABCDEFG
				//   Headers + body file reference
				//     POST {url} -HFlavor:Cotton-Candy -HContent-Type:application/json <post_data/foo.json
				//   Body file reference only
				//     PATCH {url} <patch_data/foo.json
			} else {
				if useBody, useHeader, err = augmentTarget(ps[2:], body, hdr); err != nil {
					continue
				}
			}
			return &Target{
				Method: method,
				URL:    url,
				Body:   useBody,
				Header: useHeader,
			}, nil
		}
		return nil, ErrNoTargets
	}
}

func augmentTarget(additionalArgs [][]byte, body []byte, hdr http.Header) ([]byte, http.Header, error) {
	targetHeaders := http.Header{}
	for _, arg := range additionalArgs {
		if bytes.HasPrefix(arg, []byte("-H")) {
			pair := bytes.SplitN(arg[2:], []byte(":"), 2)
			if len(pair) == 2 {
				targetHeaders.Set(string(pair[0]), strings.Replace(string(pair[1]), "[SPACE]", " ", -1))
			}
		} else if bytes.HasPrefix(arg, []byte("<")) {
			path := string(arg[1:])
			if contents, err := slurp(strings.TrimSpace(path)); err != nil {
				return nil, nil, ErrNoBody
			} else {
				body = *contents
			}
		}
	}

	// only use the new header object if we assigned any
	// TODO: merge?
	useHeader := targetHeaders
	if len(targetHeaders) == 0 {
		useHeader = hdr
	}
	return body, useHeader, nil
}

func slurp(path string) (*[]byte, error) {
	file, err := os.Open(path)
	if err != nil {
		os.Stderr.WriteString(fmt.Sprintf("Skipping line, cannot open referenced file [Path: %s] [Error: %s]\n", path, err))
		return nil, err
	}
	defer file.Close()
	contents, err := ioutil.ReadAll(file)
	if err != nil {
		os.Stderr.WriteString(fmt.Sprintf("Skipping line, error reading referenced file [Path: %s] [Error: %s]\n", path, err))
		return nil, err
	}
	return &contents, nil
}

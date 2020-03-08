package vegeta

import (
	"bytes"
	"crypto/tls"
	"io"
	"io/ioutil"
	"math"
	"net"
	"net/http"
	"time"

	"github.com/valyala/fasthttp"
)

type Hitter interface {
	Hit(*Target) *Result
}

const (
	// DefaultRedirects is the default number of times an Attacker follows
	// redirects.
	DefaultRedirects = 10
	// DefaultTimeout is the default amount of time an Attacker waits for a request
	// before it times out.
	DefaultTimeout = 30 * time.Second
	// DefaultConnections is the default amount of max open idle connections per
	// target host.
	DefaultConnections = 10000
	// DefaultMaxConnections is the default amount of connections per target
	// host.
	DefaultMaxConnections = 0
	// DefaultWorkers is the default initial number of workers used to carry an attack.
	DefaultWorkers = 10
	// DefaultMaxWorkers is the default maximum number of workers used to carry an attack.
	DefaultMaxWorkers = math.MaxUint64
	// DefaultMaxBody is the default max number of bytes to be read from response bodies.
	// Defaults to no limit.
	DefaultMaxBody = int64(-1)
	// NoFollow is the value when redirects are not followed but marked successful
	NoFollow = -1
)

var (
	// DefaultLocalAddr is the default local IP address an Attacker uses.
	DefaultLocalAddr = net.IPAddr{IP: net.IPv4zero}
	// DefaultTLSConfig is the default tls.Config an Attacker uses.
	DefaultTLSConfig = &tls.Config{InsecureSkipVerify: true}
	// DefaultHitter is the default Hitter an Attacker uses.
	DefaultHitter = &FastHTTPHitter{
		MaxBody: DefaultMaxBody,
		Client: &fasthttp.Client{
			ReadTimeout:                   DefaultTimeout,
			TLSConfig:                     DefaultTLSConfig,
			MaxConnsPerHost:               DefaultMaxConnections,
			DisableHeaderNamesNormalizing: true,
		},
	}
)

var _ Hitter = (*NetHTTPHitter)(nil)

type NetHTTPHitter struct {
	Client  *http.Client
	Chunked bool
	MaxBody int64
}

func (h *NetHTTPHitter) Hit(t *Target) *Result {
	var (
		r   = &Result{Method: t.Method, URL: t.URL}
		err error
	)

	defer func() {
		if err != nil {
			r.Error = err.Error()
		}
	}()

	req, err := http.NewRequest(t.Method, t.URL, bytes.NewReader(t.Body))
	if err != nil {
		return r
	}

	for k, vs := range t.Header {
		req.Header[k] = make([]string, len(vs))
		copy(req.Header[k], vs)
	}

	if host := req.Header.Get("Host"); host != "" {
		req.Host = host
	}

	if h.Chunked {
		req.TransferEncoding = append(req.TransferEncoding, "chunked")
	}

	resp, err := h.Client.Do(req)
	if err != nil {
		return r
	}
	defer func() { _ = resp.Body.Close() }()

	body := io.Reader(resp.Body)
	if h.MaxBody >= 0 {
		body = io.LimitReader(resp.Body, h.MaxBody)
	}

	if r.Body, err = ioutil.ReadAll(body); err != nil {
		return r
	} else if _, err = io.Copy(ioutil.Discard, resp.Body); err != nil {
		return r
	}

	r.BytesIn = uint64(len(r.Body))

	if req.ContentLength != -1 {
		r.BytesOut = uint64(req.ContentLength)
	}

	if r.Code = uint16(resp.StatusCode); r.Code < 200 || r.Code >= 400 {
		r.Error = resp.Status
	}

	r.Headers = resp.Header

	return r
}

type FastHTTPHitter struct {
	Client  *fasthttp.Client
	Chunked bool
	MaxBody int64
}

var _ Hitter = (*FastHTTPHitter)(nil)

func (h *FastHTTPHitter) Hit(t *Target) *Result {
	var (
		r    = &Result{Method: t.Method, URL: t.URL}
		req  = fasthttp.AcquireRequest()
		resp = fasthttp.AcquireResponse()
		err  error
	)

	defer func() {
		fasthttp.ReleaseRequest(req)
		fasthttp.ReleaseResponse(resp)

		if err != nil {
			r.Error = err.Error()
		}
	}()

	req.Header.SetMethod(t.Method)
	req.SetRequestURI(t.URL)

	for k, vs := range t.Header {
		for _, v := range vs {
			req.Header.Add(k, v)
		}
	}

	if host := t.Header.Get("Host"); host != "" {
		req.Header.SetHost(host)
	}

	r.Method = t.Method
	r.URL = t.URL

	if h.Chunked {
		req.SetBodyStream(bytes.NewReader(t.Body), -1)
	} else {
		req.SetBody(t.Body)
	}

	err = h.Client.Do(req, resp)
	if err != nil {
		return r
	}

	r.Body = resp.Body()
	if h.MaxBody >= 0 {
		// TODO(tsenart): Contribute a change to fasthttp that permits reading only n bytes from the response body.
		r.Body = r.Body[:h.MaxBody]
	}

	r.BytesIn = uint64(len(r.Body))
	r.BytesOut = uint64(len(req.Body()))
	r.Code = uint16(resp.StatusCode())

	if r.Code < 200 || r.Code >= 400 {
		r.Error = http.StatusText(resp.StatusCode())
	}

	r.Headers = make(http.Header)
	resp.Header.VisitAll(func(k, v []byte) {
		r.Headers.Add(string(k), string(v))
	})

	return r
}

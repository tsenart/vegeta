package main

import (
	"errors"
	"io/ioutil"
	"net/http"
	"time"
)

// Client is an http.Client with rate limiting
// TODO: Add timeouts
type Client struct {
	http.Client
	rate uint
}

// Response represents the metrics we want out of an http.Response
type Response struct {
	code      uint64
	timestamp time.Time
	timing    time.Duration
	bytesOut  uint64
	bytesIn   uint64
	err       error
}

// NewClient returns an initialized Client
func NewClient(rate uint) *Client {
	return &Client{http.Client{}, rate}
}

// Drill loops over the passed reqs channel and executes each request.
// It is throttled to the qps specified in the initializer
func (c *Client) Drill(reqs chan *http.Request, res chan *Response) {
	throttle := time.Tick(time.Duration(1e9 / c.rate))
	for req := range reqs {
		<-throttle
		go c.Do(req, res)
	}
}

// Do executes the passed http.Request and puts a generated *Response into res.
func (c *Client) Do(req *http.Request, res chan *Response) {
	began := time.Now()
	r, err := c.Client.Do(req)
	resp := &Response{
		timestamp: began,
		timing:    time.Since(began),
		bytesOut:  uint64(req.ContentLength),
		err:       err,
	}
	if err == nil {
		resp.bytesIn, resp.code = uint64(r.ContentLength), uint64(r.StatusCode)
		if body, err := ioutil.ReadAll(r.Body); err != nil && resp.code < 200 || resp.code >= 300 {
			resp.err = errors.New(string(body))
		}
	}

	res <- resp
}

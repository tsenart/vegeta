package main

import (
	"net/http"
	"time"
)

// Client is an http.Client with rate limiting and time series instrumentation.
type Client struct {
	cli      http.Client
	qps      uint
	codes    []uint64
	timings  []time.Duration
	bytesOut []int64
	bytesIn  []int64
}

func NewClient(qps uint) *Client {
	return &Client{
		cli:      http.Client{},
		qps:      qps,
		codes:    []uint64{},
		timings:  []time.Duration{},
		bytesOut: []int64{},
		bytesIn:  []int64{},
	}
}

// Drill loops over the passed reqs channel and executes each request.
// It is throttled to the qps specified in the initializer
func (c *Client) Drill(reqs chan *http.Request) {
	throttle := time.Tick(time.Duration(1e9 / c.qps))
	for req := range reqs {
		<-throttle
		go c.Do(req)
	}
}

// Do executes the passed http.Request and saves some metrics
// (timings, bytesIn, bytesOut, codes)
func (c *Client) Do(req *http.Request) (*http.Response, error) {
	began := time.Now()
	resp, err := c.cli.Do(req)
	c.timings = append(c.timings, time.Since(began))
	c.bytesOut = append(c.bytesOut, req.ContentLength)
	c.bytesIn = append(c.bytesIn, resp.ContentLength)
	c.codes[resp.StatusCode]++
	return resp, err
}

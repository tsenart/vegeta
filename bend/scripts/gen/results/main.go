// Writes bend/tests/golden/results.{csv,json} with Go Vegeta's encoders
// for six results that exercise the formats' edges, and results.metrics
// with the metrics tests/metrics.bend prints for them (Go's Metrics for
// everything but p50, which is exact nearest rank, as the port computes).
package main

import (
	"bytes"
	"fmt"
	"net/http"
	"os"
	"sort"
	"time"

	vegeta "github.com/tsenart/vegeta/v12/lib"
)

func results() []vegeta.Result {
	plus2 := time.FixedZone("", 2*3600)
	t0 := time.Date(2026, 9, 23, 2, 9, 47, 935870875, time.UTC)
	return []vegeta.Result{
		{Attack: "a", Seq: 0, Code: 200, Timestamp: t0, Latency: 1500 * time.Microsecond, BytesOut: 0, BytesIn: 2,
			Body: []byte("ok"), Method: "GET", URL: "http://127.0.0.1:8080/",
			Headers: http.Header{"Content-Type": {"text/plain"}}},
		{Attack: "a", Seq: 1, Code: 0, Timestamp: t0.Add(time.Millisecond), Latency: 300 * time.Microsecond,
			Error: `Get "http://127.0.0.1:1/": dial tcp 127.0.0.1:1: connect: connection refused`, Method: "GET", URL: "http://127.0.0.1:1/"},
		{Attack: "a", Seq: 2, Code: 500, Timestamp: t0.Add(2 * time.Millisecond), Latency: 25 * time.Millisecond, BytesIn: 4,
			Error: "500 Internal Server Error", Body: []byte("boom"), Method: "POST", URL: "http://h/x", BytesOut: 3,
			Headers: http.Header{"Set-Cookie": {"a=1", "b=2"}}},
		{Attack: "", Seq: 3, Code: 200, Timestamp: t0.Add(3 * time.Millisecond), Latency: 7 * time.Millisecond,
			Error: "", Body: []byte{}, Method: "GET", URL: "http://h/q?x=\"1\",2", Headers: http.Header{}},
		{Attack: "b", Seq: 4294967296, Code: 404, Timestamp: t0.Add(4 * time.Millisecond).In(plus2), Latency: 999 * time.Microsecond,
			Error: "404 Not Found", Body: []byte("a,b\n\"c\""), Method: "GET", URL: "http://h/"},
		{Attack: "c", Seq: 5, Code: 302, Timestamp: time.Unix(0, 999).UTC(), Latency: 1, Method: "GET", URL: "http://h/r",
			Body: []byte{}, Headers: http.Header{"Location": {"/x"}}},
	}
}

func main() {
	rs := results()
	var csvb, jsonb bytes.Buffer
	ce, je := vegeta.NewCSVEncoder(&csvb), vegeta.NewJSONEncoder(&jsonb)
	for i := range rs {
		ce.Encode(&rs[i])
		je.Encode(&rs[i])
	}
	must(os.WriteFile("bend/tests/golden/results.csv", csvb.Bytes(), 0o644))
	must(os.WriteFile("bend/tests/golden/results.json", jsonb.Bytes(), 0o644))

	var m vegeta.Metrics
	m.Histogram = &vegeta.Histogram{Buckets: []time.Duration{0, time.Millisecond, 10 * time.Millisecond}}
	var lats []int64
	for i := range rs {
		m.Add(&rs[i])
		lats = append(lats, int64(rs[i].Latency))
	}
	m.Close()
	sort.Slice(lats, func(i, j int) bool { return lats[i] < lats[j] })
	k := (50*len(lats)+99)/100 - 1
	var out bytes.Buffer
	fmt.Fprintf(&out, "requests %d\nsuccess %d\n", m.Requests, int(m.Success*float64(m.Requests)+0.5))
	codes := make([]string, 0)
	for c := range m.StatusCodes {
		codes = append(codes, c)
	}
	sort.Strings(codes)
	for _, c := range codes {
		fmt.Fprintf(&out, "code %s %d\n", c, m.StatusCodes[c])
	}
	errs := append([]string(nil), m.Errors...)
	sort.Strings(errs)
	for _, e := range errs {
		fmt.Fprintf(&out, "error %s\n", e)
	}
	fmt.Fprintf(&out, "p50 %d\nmax %d\nmin %d\n", lats[k], int64(m.Latencies.Max), int64(m.Latencies.Min))
	for i, c := range m.Histogram.Counts {
		fmt.Fprintf(&out, "bucket %d %d\n", i, c)
	}
	must(os.WriteFile("bend/tests/golden/results.metrics", out.Bytes(), 0o644))
}

func must(err error) {
	if err != nil {
		panic(err)
	}
}

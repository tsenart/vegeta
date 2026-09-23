// Writes bend/tests/golden/report-<case>.{csv,text,json,hist} with Go
// Vegeta's encoder and reporters, and report-<case>.pct with the exact
// nearest-rank p50/p90/p95/p99 the port computes (Go's are t-digest
// estimates). Run with TZ=UTC so report times are in UTC.
package main

import (
	"bytes"
	"fmt"
	"os"
	"sort"
	"time"

	vegeta "github.com/tsenart/vegeta/v12/lib"
)

var t0 = time.Date(2026, 9, 23, 10, 0, 0, 0, time.UTC)

func cases() map[string][]vegeta.Result {
	cs := map[string][]vegeta.Result{"empty": nil}
	cs["single"] = []vegeta.Result{{Code: 200, Timestamp: t0, Latency: 3 * time.Millisecond, BytesIn: 10, BytesOut: 5, Method: "GET", URL: "http://h/", Body: []byte{}}}
	var mixed []vegeta.Result
	errs := []string{"500 Internal Server Error", "", "Get \"http://h/\": EOF", "", "503 Service Unavailable"}
	for i := 0; i < 100; i++ {
		code := uint16(200)
		switch i % 5 {
		case 0:
			code = 500
		case 2:
			code = 0
		case 4:
			code = 503
		}
		mixed = append(mixed, vegeta.Result{Seq: uint64(i), Code: code, Timestamp: t0.Add(time.Duration(i) * 10 * time.Millisecond),
			Latency: time.Duration(i+1) * time.Millisecond, BytesIn: uint64(i * 3), BytesOut: 7, Error: errs[i%5], Method: "GET", URL: "http://h/", Body: []byte{}})
	}
	cs["mixed"] = mixed
	var huge []vegeta.Result
	for i := 0; i < 3; i++ {
		huge = append(huge, vegeta.Result{Seq: uint64(i), Code: 200, Timestamp: t0.Add(time.Duration(i) * time.Second),
			Latency: 70 * time.Hour, BytesIn: 1 << 47, BytesOut: 1 << 47, Method: "GET", URL: "http://h/", Body: []byte{}})
	}
	cs["huge-sums"] = huge
	plus2 := time.FixedZone("", 2*3600)
	cs["two-zones"] = []vegeta.Result{
		{Code: 200, Timestamp: t0, Latency: time.Millisecond, Method: "GET", URL: "http://h/", Body: []byte{}},
		{Code: 204, Timestamp: t0.Add(1500 * time.Millisecond).In(plus2), Latency: 2 * time.Millisecond, Method: "GET", URL: "http://h/", Body: []byte{}},
	}
	return cs
}

func main() {
	buckets := []time.Duration{0, time.Millisecond, 10 * time.Millisecond, 100 * time.Millisecond}
	for name, rs := range cases() {
		var csvb bytes.Buffer
		enc := vegeta.NewCSVEncoder(&csvb)
		for i := range rs {
			enc.Encode(&rs[i])
		}
		write(name, "csv", csvb.Bytes())

		// reread through the CSV decoder, as `vegeta report` would
		dec := vegeta.NewCSVDecoder(bytes.NewReader(csvb.Bytes()))
		var m vegeta.Metrics
		h := vegeta.Histogram{Buckets: buckets}
		var lats []int64
		for {
			var r vegeta.Result
			if err := dec(&r); err != nil {
				break
			}
			m.Add(&r)
			h.Add(&r)
			lats = append(lats, int64(r.Latency))
		}
		m.Close()
		var text, js, hist bytes.Buffer
		vegeta.NewTextReporter(&m).Report(&text)
		vegeta.NewJSONReporter(&m).Report(&js)
		write(name, "text", text.Bytes())
		write(name, "json", js.Bytes())
		if len(lats) > 0 {
			vegeta.NewHistogramReporter(&h).Report(&hist)
			write(name, "hist", hist.Bytes())
		}
		sort.Slice(lats, func(i, j int) bool { return lats[i] < lats[j] })
		var pct bytes.Buffer
		for _, q := range []int{50, 90, 95, 99} {
			v := int64(0)
			if n := len(lats); n > 0 {
				k := (q*n+99)/100 - 1
				v = lats[k]
			}
			fmt.Fprintf(&pct, "%d %d\n", q, v)
		}
		write(name, "pct", pct.Bytes())
	}
}

func write(name, ext string, b []byte) {
	if err := os.WriteFile(fmt.Sprintf("bend/tests/golden/report-%s.%s", name, ext), b, 0o644); err != nil {
		panic(err)
	}
}

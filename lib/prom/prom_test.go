package prom

import (
	"io"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"

	"github.com/prometheus/client_golang/prometheus"
	dto "github.com/prometheus/client_model/go"
	"github.com/prometheus/prometheus/model/textparse"
	vegeta "github.com/tsenart/vegeta/v12/lib"
)

func TestMetrics_Observe(t *testing.T) {
	reg := prometheus.NewRegistry()
	pm := NewMetrics()

	if err := pm.Register(reg); err != nil {
		t.Fatal("error registering metrics", err)
	}

	srv := httptest.NewServer(NewHandler(reg, time.Now().UTC()))
	defer srv.Close()

	// XXX: Result timestamps are ignored, since Prometheus aggregates metrics
	// and only assigns timestamps to series in the server once it scrapes.
	// To have accurate timestamps we'd have to implement a remote write integration.

	r := &vegeta.Result{
		URL:      "http://test.com/test1",
		Method:   "GET",
		Code:     500,
		Error:    "Internal Server Error",
		Latency:  100 * time.Millisecond,
		BytesIn:  1000,
		BytesOut: 50,
	}

	pm.Observe(r)

	resp, err := http.Get(srv.URL)
	if err != nil {
		t.Fatalf("failed to get prometheus metrics. err=%s", err)
	}

	if resp.StatusCode != 200 {
		t.Fatalf("status code should be 200. code=%d", resp.StatusCode)
	}

	data, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Errorf("error reading response body: err=%v", err)
	}

	p, err := textparse.New(data, resp.Header.Get("Content-Type"), true, nil)
	if err != nil {
		t.Fatalf("error creating prometheus metrics parser. err=%v", err)
	}

	want := map[string]struct{}{
		"request_seconds":    struct{}{},
		"request_bytes_in":   struct{}{},
		"request_bytes_out":  struct{}{},
		"request_fail_count": struct{}{},
	}

	t.Log(string(data))

	for len(want) > 0 {
		_, err := p.Next()
		if err != nil {
			if err == io.EOF {
				break
			}
			t.Fatalf("error parsing prometheus metrics. err=%v", err)
		}

		name, _ := p.Help()
		nameStr := string(name)

		if _, ok := want[nameStr]; ok {
			delete(want, nameStr)
		}
	}

	if len(want) > 0 {
		t.Errorf("missing metrics: %v", want)
	}
}

func TestMetrics_Observe_FailCounterIncremented(t *testing.T) {
	pm := NewMetrics()
	reg := prometheus.NewRegistry()

	if err := pm.Register(reg); err != nil {
		t.Fatal("error registering metrics", err)
	}

	pm.Observe(&vegeta.Result{
		URL:     "http://example.com/fail",
		Method:  "GET",
		Code:    500,
		Error:   "Internal Server Error",
		Latency: 100 * time.Millisecond,
	})
	pm.Observe(&vegeta.Result{
		URL:     "http://example.com/fail",
		Method:  "GET",
		Code:    500,
		Error:   "Internal Server Error",
		Latency: 200 * time.Millisecond,
	})
	pm.Observe(&vegeta.Result{
		URL:     "http://example.com/ok",
		Method:  "GET",
		Code:    200,
		Latency: 50 * time.Millisecond,
	})

	var m dto.Metric
	failCounter := pm.requestFailCounter.WithLabelValues("GET", "http://example.com/fail", "500", "Internal Server Error")
	if err := failCounter.Write(&m); err != nil {
		t.Fatalf("error writing metric: %v", err)
	}

	if got, want := m.GetCounter().GetValue(), float64(2); got != want {
		t.Errorf("request_fail_count: got %v, want %v", got, want)
	}
}

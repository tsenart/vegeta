package prom

import (
	"context"
	"io"
	"net/http"
	"strings"
	"testing"
	"time"

	"github.com/prometheus/client_golang/prometheus"
	vegeta "github.com/tsenart/vegeta/v12/lib"
)

func TestPromMetrics1(t *testing.T) {
	pm, err := NewMetrics(nil)
	if err != nil {
		t.Errorf("Error creating metrics. err=%s", err)
	}

	err = pm.Unregister()
	if err != nil {
		t.Errorf("Cannot unregister metrics. err=%s", err)
	}
}

func TestPromMetrics2(t *testing.T) {
	reg := prometheus.NewRegistry()

	pm, err := NewMetrics(reg)
	if err != nil {
		t.Errorf("Error creating metrics. err=%s", err)
	}

	err = pm.Unregister()
	if err != nil {
		t.Errorf("Cannot unregister metrics. err=%s", err)
	}

	// register again to check if registry was cleared correctly
	pm, err = NewMetrics(reg)
	if err != nil {
		t.Errorf("Error creating metrics. err=%s", err)
	}

	err = pm.Unregister()
	if err != nil {
		t.Errorf("Cannot unregister metrics. err=%s", err)
	}

	// register again to check if registry was cleared correctly
	pm, err = NewMetrics(reg)
	if err != nil {
		t.Errorf("Error creating metrics. err=%s", err)
	}

	err = pm.Unregister()
	if err != nil {
		t.Errorf("Cannot unregister metrics. err=%s", err)
	}

}

func TestPromServerBasic1(t *testing.T) {
	r := prometheus.NewRegistry()
	pm, err := NewMetrics(r)
	if err != nil {
		t.Errorf("Error creating metrics. err=%s", err)
	}

	srv, err := StartPromServer("0.0.0.0:8880", r)
	if err != nil {
		t.Errorf("Error starting server. err=%s", err)
	}

	err = srv.Shutdown(context.Background())
	if err != nil {
		t.Errorf("Error shutting down server. err=%s", err)
	}
	pm.Unregister()
}

func TestPromServerBasic2(t *testing.T) {
	reg := prometheus.NewRegistry()

	pm, err := NewMetrics(reg)
	if err != nil {
		t.Errorf("Error creating metrics. err=%s", err)
	}

	// start/stop 1
	srv, err := StartPromServer("0.0.0.0:8880", reg)
	if err != nil {
		t.Errorf("Error starting server. err=%s", err)
	}
	err = srv.Shutdown(context.Background())
	if err != nil {
		t.Errorf("Error shutting down server. err=%s", err)
	}

	// start/stop 2
	srv, err = StartPromServer("0.0.0.0:8880", reg)
	if err != nil {
		t.Errorf("Error starting server. err=%s", err)
	}
	err = srv.Shutdown(context.Background())
	if err != nil {
		t.Errorf("Error shutting down server. err=%s", err)
	}

	pm.Unregister()

	// start server again after reusing the same registry (sanity check)
	_, err = NewMetrics(reg)
	if err != nil {
		t.Errorf("Error creating metrics. err=%s", err)
	}
	// start/stop 1
	srv, err = StartPromServer("0.0.0.0:8880", reg)
	if err != nil {
		t.Errorf("Error starting server. err=%s", err)
	}
	err = srv.Shutdown(context.Background())
	if err != nil {
		t.Errorf("Error shutting down server. err=%s", err)
	}

}

func TestPromServerObserve(t *testing.T) {
	reg := prometheus.NewRegistry()
	pm, err := NewMetrics(reg)
	if err != nil {
		if err != nil {
			t.Errorf("Error launching Prometheus http server. err=%s", err)
		}
	}

	srv, err := StartPromServer("0.0.0.0:8880", reg)
	if err != nil {
		t.Errorf("Error starting server. err=%s", err)
	}

	r := &vegeta.Result{
		URL:      "http://test.com/test1",
		Method:   "GET",
		Code:     200,
		Error:    "",
		Latency:  100 * time.Millisecond,
		BytesIn:  1000,
		BytesOut: 50,
	}
	pm.Observe(r)
	pm.Observe(r)
	pm.Observe(r)
	pm.Observe(r)

	time.Sleep(3 * time.Second)
	resp, err := http.Get("http://localhost:8880")
	if err != nil {
		t.Errorf("Error calling prometheus metrics. err=%s", err)
	}
	if resp.StatusCode != 200 {
		t.Errorf("Status code should be 200")
	}

	data, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Errorf("Error calling prometheus metrics. err=%s", err)
	}
	str := string(data)
	if len(str) == 0 {
		t.Errorf("Body not empty. body=%s", str)
	}
	if !strings.Contains(str, "request_seconds") {
		t.Error("Metrics should contain request_seconds")
	}
	if !strings.Contains(str, "request_bytes_in") {
		t.Error("Metrics should contain request_bytes_in")
	}
	if !strings.Contains(str, "request_bytes_out") {
		t.Error("Metrics should contain request_bytes_out")
	}
	if strings.Contains(str, "request_fail_count") {
		t.Error("Metrics should contain request_fail_count")
	}

	r.Code = 500
	r.Error = "REQUEST FAILED"
	pm.Observe(r)

	resp, err = http.Get("http://localhost:8880")
	if err != nil {
		t.Errorf("Error calling prometheus metrics. err=%s", err)
	}
	if resp.StatusCode != 200 {
		t.Errorf("Status code should be 200")
	}

	data, err = io.ReadAll(resp.Body)
	if err != nil {
		t.Errorf("Error calling prometheus metrics. err=%s", err)
	}
	str = string(data)

	if !strings.Contains(str, "request_fail_count") {
		t.Error("Metrics should contain request_fail_count")
	}

	err = srv.Shutdown(context.Background())
	if err != nil {
		t.Errorf("Error shutting down server. err=%s", err)
	}
	pm.Unregister()
}

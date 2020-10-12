package prom

import (
	"io/ioutil"
	"net/http"
	"strings"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	vegeta "github.com/tsenart/vegeta/v12/lib"
)

func TestPromServerBasic1(t *testing.T) {
	pm, err := NewPrometheusMetrics()
	if err != nil {
		t.Errorf("Error launching Prometheus http server. err=%s", err)
	}

	err = pm.Close()
	if err != nil {
		t.Errorf("Error stopping Prometheus http server. err=%s", err)
	}
}

func TestPromServerBasic2(t *testing.T) {
	pm, err := NewPrometheusMetrics()
	if err != nil {
		t.Errorf("Error launching Prometheus metrics. err=%s", err)
	}
	err = pm.Close()
	if err != nil {
		t.Errorf("Error stopping Prometheus http server. err=%s", err)
	}

	pm, err = NewPrometheusMetrics()
	if err != nil {
		t.Errorf("Error launching Prometheus metrics. err=%s", err)
	}
	err = pm.Close()
	if err != nil {
		t.Errorf("Error stopping Prometheus http server. err=%s", err)
	}

	pm, err = NewPrometheusMetrics()
	if err != nil {
		t.Errorf("Error launching Prometheus metrics. err=%s", err)
	}
	err = pm.Close()
	if err != nil {
		t.Errorf("Error stopping Prometheus http server. err=%s", err)
	}
}

func TestPromServerObserve(t *testing.T) {
	pm, err := NewPrometheusMetrics()
	assert.Nil(t, err, "Error launching Prometheus http server. err=%s", err)

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

	data, err := ioutil.ReadAll(resp.Body)
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

	data, err = ioutil.ReadAll(resp.Body)
	if err != nil {
		t.Errorf("Error calling prometheus metrics. err=%s", err)
	}
	str = string(data)

	if !strings.Contains(str, "request_fail_count") {
		t.Error("Metrics should contain request_fail_count")
	}

	err = pm.Close()
	if err != nil {
		t.Errorf("Error stopping Prometheus http server. err=%s", err)
	}
}

package prom

import (
	"fmt"
	"net/http"
	"strconv"
	"time"

	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/promhttp"

	vegeta "github.com/tsenart/vegeta/v12/lib"
)

// Metrics encapsulates Prometheus metrics of an attack.
type Metrics struct {
	requestLatencyHistogram *prometheus.HistogramVec
	requestBytesInCounter   *prometheus.CounterVec
	requestBytesOutCounter  *prometheus.CounterVec
	requestFailCounter      *prometheus.CounterVec
}

// NewMetrics returns a new Metrics instance that must be
// registered in a Prometheus registry with Register.
func NewMetrics() *Metrics {
	baseLabels := []string{"method", "url", "status"}
	return &Metrics{
		requestLatencyHistogram: prometheus.NewHistogramVec(prometheus.HistogramOpts{
			Name:    "request_seconds",
			Help:    "Request latency",
			Buckets: prometheus.DefBuckets,
		}, baseLabels),
		requestBytesInCounter: prometheus.NewCounterVec(prometheus.CounterOpts{
			Name: "request_bytes_in",
			Help: "Bytes received from servers as response to requests",
		}, baseLabels),
		requestBytesOutCounter: prometheus.NewCounterVec(prometheus.CounterOpts{
			Name: "request_bytes_out",
			Help: "Bytes sent to servers during requests",
		}, baseLabels),
		requestFailCounter: prometheus.NewCounterVec(prometheus.CounterOpts{
			Name: "request_fail_count",
			Help: "Count of failed requests",
		}, append(baseLabels[:len(baseLabels):len(baseLabels)], "message")),
	}
}

// Register registers all Prometheus metrics in r.
func (pm *Metrics) Register(r prometheus.Registerer) error {
	for _, c := range []prometheus.Collector{
		pm.requestLatencyHistogram,
		pm.requestBytesInCounter,
		pm.requestBytesOutCounter,
		pm.requestFailCounter,
	} {
		if err := r.Register(c); err != nil {
			return fmt.Errorf("failed to register metric %v: %w", c, err)
		}
	}
	return nil
}

// Observe metrics given a vegeta.Result.
func (pm *Metrics) Observe(res *vegeta.Result) {
	code := strconv.FormatUint(uint64(res.Code), 10)
	pm.requestBytesInCounter.WithLabelValues(res.Method, res.URL, code).Add(float64(res.BytesIn))
	pm.requestBytesOutCounter.WithLabelValues(res.Method, res.URL, code).Add(float64(res.BytesOut))
	pm.requestLatencyHistogram.WithLabelValues(res.Method, res.URL, code).Observe(res.Latency.Seconds())
	if res.Error != "" {
		pm.requestFailCounter.WithLabelValues(res.Method, res.URL, code, res.Error)
	}
}

// NewHandler returns a new http.Handler that exposes Prometheus
// metrics registed in r in the OpenMetrics format.
func NewHandler(r *prometheus.Registry, startTime time.Time) http.Handler {
	return promhttp.HandlerFor(r, promhttp.HandlerOpts{
		Registry:          r,
		EnableOpenMetrics: true,
		ProcessStartTime:  startTime,
	})
}

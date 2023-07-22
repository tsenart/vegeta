package prom

import (
	"errors"
	"net/http"
	"strconv"
	"time"

	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/promhttp"

	vegeta "github.com/tsenart/vegeta/v12/lib"
)

// Metrics encapsulates Prometheus metrics of an attack.
type Metrics struct {
	RequestSecondsHistogram *prometheus.HistogramVec
	RequestBytesInCounter   *prometheus.CounterVec
	RequestBytesOutCounter  *prometheus.CounterVec
	RequestFailCounter      *prometheus.CounterVec
	Registry                prometheus.Registerer
}

// NewMetrics returns a new Metrics instance and registers all of them in the given Registry.
func NewMetrics(registry prometheus.Registerer) (*Metrics, error) {
	if registry == nil {
		registry = prometheus.DefaultRegisterer
	}

	pm := &Metrics{Registry: registry}

	pm.RequestSecondsHistogram = prometheus.NewHistogramVec(prometheus.HistogramOpts{
		Name:    "request_seconds",
		Help:    "Request latency",
		Buckets: prometheus.DefBuckets,
	}, []string{
		"method",
		"url",
		"status",
	})
	err := pm.Registry.Register(pm.RequestSecondsHistogram)
	if err != nil {
		return nil, err
	}

	pm.RequestBytesInCounter = prometheus.NewCounterVec(prometheus.CounterOpts{
		Name: "request_bytes_in",
		Help: "Bytes received from servers as response to requests",
	}, []string{
		"method",
		"url",
		"status",
	})
	err = pm.Registry.Register(pm.RequestBytesInCounter)
	if err != nil {
		return nil, err
	}

	pm.RequestBytesOutCounter = prometheus.NewCounterVec(prometheus.CounterOpts{
		Name: "request_bytes_out",
		Help: "Bytes sent to servers during requests",
	}, []string{
		"method",
		"url",
		"status",
	})
	err = pm.Registry.Register(pm.RequestBytesOutCounter)
	if err != nil {
		return nil, err
	}

	pm.RequestFailCounter = prometheus.NewCounterVec(prometheus.CounterOpts{
		Name: "request_fail_count",
		Help: "Internal failures that prevented a hit to the target server",
	}, []string{
		"method",
		"url",
		"code",
		"message",
	})
	err = pm.Registry.Register(pm.RequestFailCounter)
	if err != nil {
		return nil, err
	}

	return pm, nil
}

// Unregister all prometheus collectors
func (pm *Metrics) Unregister() error {
	exists := pm.Registry.Unregister(pm.RequestSecondsHistogram)
	if !exists {
		return errors.New("'RequestSecondsHistogram' cannot be unregistered because it was not found")
	}

	exists = pm.Registry.Unregister(pm.RequestBytesInCounter)
	if !exists {
		return errors.New("'RequestBytesInCounter' cannot be unregistered because it was not found")
	}

	exists = pm.Registry.Unregister(pm.RequestBytesOutCounter)
	if !exists {
		return errors.New("'RequestBytesOutCounter' cannot be unregistered because it was not found")
	}

	exists = pm.Registry.Unregister(pm.RequestFailCounter)
	if !exists {
		return errors.New("'RequestFailCounter' cannot be unregistered because it was not found")
	}

	return nil
}

// Observe metrics with hit results
func (pm *Metrics) Observe(res *vegeta.Result) {
	code := strconv.FormatUint(uint64(res.Code), 10)
	pm.RequestBytesInCounter.WithLabelValues(res.Method, res.URL, code).Add(float64(res.BytesIn))
	pm.RequestBytesOutCounter.WithLabelValues(res.Method, res.URL, code).Add(float64(res.BytesOut))
	pm.RequestSecondsHistogram.WithLabelValues(res.Method, res.URL, code).Observe(float64(res.Latency) / float64(time.Second))
	if res.Error != "" {
		pm.RequestFailCounter.WithLabelValues(res.Method, res.URL, code, res.Error)
	}
}

// StartPromServer starts a new Prometheus server with metrics present in promRegistry
// launches a http server in a new goroutine and returns the http.Server instance
func StartPromServer(bindAddr string, promRegistry *prometheus.Registry) (*http.Server, error) {
	srv := http.Server{
		Addr:    bindAddr,
		Handler: promhttp.HandlerFor(promRegistry, promhttp.HandlerOpts{}),
	}

	go srv.ListenAndServe()

	return &srv, nil
}

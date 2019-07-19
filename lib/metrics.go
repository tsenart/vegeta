package vegeta

import (
	"strconv"
	"time"

	"github.com/influxdata/tdigest"
)

// Metrics holds metrics computed out of a slice of Results which are used
// in some of the Reporters
type Metrics struct {
	// Latencies holds computed request latency metrics.
	Latencies LatencyMetrics `json:"latencies"`
	// Histogram, only if requested
	Histogram *Histogram `json:"buckets,omitempty"`
	// BytesIn holds computed incoming byte metrics.
	BytesIn ByteMetrics `json:"bytes_in"`
	// BytesOut holds computed outgoing byte metrics.
	BytesOut ByteMetrics `json:"bytes_out"`
	// Earliest is the earliest timestamp in a Result set.
	Earliest time.Time `json:"earliest"`
	// Latest is the latest timestamp in a Result set.
	Latest time.Time `json:"latest"`
	// End is the latest timestamp in a Result set plus its latency.
	End time.Time `json:"end"`
	// Duration is the duration of the attack.
	Duration time.Duration `json:"duration"`
	// Wait is the extra time waiting for responses from targets.
	Wait time.Duration `json:"wait"`
	// Requests is the total number of requests executed.
	Requests uint64 `json:"requests"`
	// Rate is the rate of sent requests per second.
	Rate float64 `json:"rate"`
	// Throughput is the rate of successful requests per second.
	Throughput float64 `json:"throughput"`
	// Success is the percentage of non-error responses.
	Success float64 `json:"success"`
	// StatusCodes is a histogram of the responses' status codes.
	StatusCodes map[string]int `json:"status_codes"`
	// Errors is a set of unique errors returned by the targets during the attack.
	Errors []string `json:"errors"`

	errors  map[string]struct{}
	success uint64
}

// Add implements the Add method of the Report interface by adding the given
// Result to Metrics.
func (m *Metrics) Add(r *Result) {
	m.init()

	m.Requests++
	m.StatusCodes[strconv.Itoa(int(r.Code))]++
	m.BytesOut.Total += r.BytesOut
	m.BytesIn.Total += r.BytesIn

	m.Latencies.Add(r.Latency)

	if m.Earliest.IsZero() || m.Earliest.After(r.Timestamp) {
		m.Earliest = r.Timestamp
	}

	if r.Timestamp.After(m.Latest) {
		m.Latest = r.Timestamp
	}

	if end := r.End(); end.After(m.End) {
		m.End = end
	}

	if r.Code >= 200 && r.Code < 400 {
		m.success++
	}

	if r.Error != "" {
		if _, ok := m.errors[r.Error]; !ok {
			m.errors[r.Error] = struct{}{}
			m.Errors = append(m.Errors, r.Error)
		}
	}

	if m.Histogram != nil {
		m.Histogram.Add(r)
	}
}

// Close implements the Close method of the Report interface by computing
// derived summary metrics which don't need to be run on every Add call.
func (m *Metrics) Close() {
	m.init()
	m.Rate = float64(m.Requests)
	m.Throughput = float64(m.success)
	m.Duration = m.Latest.Sub(m.Earliest)
	m.Wait = m.End.Sub(m.Latest)
	if secs := m.Duration.Seconds(); secs > 0 {
		m.Rate /= secs
		// No need to check for zero because we know m.Duration > 0
		m.Throughput /= (m.Duration + m.Wait).Seconds()
	}

	m.BytesIn.Mean = float64(m.BytesIn.Total) / float64(m.Requests)
	m.BytesOut.Mean = float64(m.BytesOut.Total) / float64(m.Requests)
	m.Success = float64(m.success) / float64(m.Requests)
	m.Latencies.Mean = time.Duration(float64(m.Latencies.Total) / float64(m.Requests))
	m.Latencies.P50 = m.Latencies.Quantile(0.50)
	m.Latencies.P95 = m.Latencies.Quantile(0.95)
	m.Latencies.P99 = m.Latencies.Quantile(0.99)
}

func (m *Metrics) init() {
	if m.StatusCodes == nil {
		m.StatusCodes = map[string]int{}
	}

	if m.errors == nil {
		m.errors = map[string]struct{}{}
	}

	if m.Errors == nil {
		m.Errors = make([]string, 0)
	}
}

// LatencyMetrics holds computed request latency metrics.
type LatencyMetrics struct {
	// Total is the total latency sum of all requests in an attack.
	Total time.Duration `json:"total"`
	// Mean is the mean request latency.
	Mean time.Duration `json:"mean"`
	// P50 is the 50th percentile request latency.
	P50 time.Duration `json:"50th"`
	// P95 is the 95th percentile request latency.
	P95 time.Duration `json:"95th"`
	// P99 is the 99th percentile request latency.
	P99 time.Duration `json:"99th"`
	// Max is the maximum observed request latency.
	Max time.Duration `json:"max"`

	estimator estimator
}

// Add adds the given latency to the latency metrics.
func (l *LatencyMetrics) Add(latency time.Duration) {
	l.init()
	if l.Total += latency; latency > l.Max {
		l.Max = latency
	}
	l.estimator.Add(float64(latency))
}

// Quantile returns the nth quantile from the latency summary.
func (l LatencyMetrics) Quantile(nth float64) time.Duration {
	l.init()
	return time.Duration(l.estimator.Get(nth))
}

func (l *LatencyMetrics) init() {
	if l.estimator == nil {
		// This compression parameter value is the recommended value
		// for normal uses as per http://javadox.com/com.tdunning/t-digest/3.0/com/tdunning/math/stats/TDigest.html
		l.estimator = newTdigestEstimator(100)
	}
}

// ByteMetrics holds computed byte flow metrics.
type ByteMetrics struct {
	// Total is the total number of flowing bytes in an attack.
	Total uint64 `json:"total"`
	// Mean is the mean number of flowing bytes per hit.
	Mean float64 `json:"mean"`
}

type estimator interface {
	Add(sample float64)
	Get(quantile float64) float64
}

type tdigestEstimator struct{ *tdigest.TDigest }

func newTdigestEstimator(compression float64) *tdigestEstimator {
	return &tdigestEstimator{TDigest: tdigest.NewWithCompression(compression)}
}

func (e *tdigestEstimator) Add(s float64) { e.TDigest.Add(s, 1) }
func (e *tdigestEstimator) Get(q float64) float64 {
	return e.TDigest.Quantile(q)
}

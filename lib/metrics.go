package vegeta

import (
	"strconv"
	"time"

	"github.com/streadway/quantile"
)

type (
	// Metrics holds metrics computed out of a slice of Results which are used
	// in some of the Reporters
	Metrics struct {
		// Latencies holds computed request latency metrics.
		Latencies LatencyMetrics `json:"latencies"`
		// BytesIn holds computed incoming byte metrics.
		BytesIn ByteMetrics `json:"bytes_in"`
		// BytesOut holds computed outgoing byte metrics.
		BytesOut ByteMetrics `json:"bytes_out"`
		// First is the earliest timestamp in a Result set.
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
		// Rate is the rate of requests per second.
		Rate float64 `json:"rate"`
		// Success is the percentage of non-error responses.
		Success float64 `json:"success"`
		// StatusCodes is a histogram of the responses' status codes.
		StatusCodes map[string]int `json:"status_codes"`
		// Errors is a set of unique errors returned by the targets during the attack.
		Errors []string `json:"errors"`

		errors    map[string]struct{}
		success   uint64
		latencies *quantile.Estimator
	}

	// LatencyMetrics holds computed request latency metrics.
	LatencyMetrics struct {
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
	}

	// ByteMetrics holds computed byte flow metrics.
	ByteMetrics struct {
		// Total is the total number of flowing bytes in an attack.
		Total uint64 `json:"total"`
		// Mean is the mean number of flowing bytes per hit.
		Mean float64 `json:"mean"`
	}
)

// Add implements the Add method of the Report interface by adding the given
// Result to Metrics.
func (m *Metrics) Add(r *Result) {
	m.init()

	m.Requests++
	m.StatusCodes[strconv.Itoa(int(r.Code))]++
	m.Latencies.Total += r.Latency
	m.BytesOut.Total += r.BytesOut
	m.BytesIn.Total += r.BytesIn

	m.latencies.Add(float64(r.Latency))

	if m.Earliest.IsZero() || m.Earliest.After(r.Timestamp) {
		m.Earliest = r.Timestamp
	}

	if r.Timestamp.After(m.Latest) {
		m.Latest = r.Timestamp
	}

	if end := r.End(); end.After(m.End) {
		m.End = end
	}

	if r.Latency > m.Latencies.Max {
		m.Latencies.Max = r.Latency
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
}

// Close implements the Close method of the Report interface by computing
// derived summary metrics which don't need to be run on every Add call.
func (m *Metrics) Close() {
	m.init()
	m.Rate = float64(m.Requests)
	m.Duration = m.Latest.Sub(m.Earliest)
	if secs := m.Duration.Seconds(); secs > 0 {
		m.Rate /= secs
	}
	m.Wait = m.End.Sub(m.Latest)
	m.BytesIn.Mean = float64(m.BytesIn.Total) / float64(m.Requests)
	m.BytesOut.Mean = float64(m.BytesOut.Total) / float64(m.Requests)
	m.Success = float64(m.success) / float64(m.Requests)
	m.Latencies.Mean = time.Duration(float64(m.Latencies.Total) / float64(m.Requests))
	m.Latencies.P50 = time.Duration(m.latencies.Get(0.50))
	m.Latencies.P95 = time.Duration(m.latencies.Get(0.95))
	m.Latencies.P99 = time.Duration(m.latencies.Get(0.99))
}

func (m *Metrics) init() {
	if m.StatusCodes == nil {
		m.StatusCodes = map[string]int{}
	}

	if m.errors == nil {
		m.errors = map[string]struct{}{}
	}

	if m.latencies == nil {
		m.latencies = quantile.New(
			quantile.Known(0.50, 0.01),
			quantile.Known(0.95, 0.001),
			quantile.Known(0.99, 0.0005),
		)
	}
}

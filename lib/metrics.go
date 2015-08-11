package vegeta

import (
	"math"
	"sort"
	"strconv"
	"time"
)

type (
	// Metrics holds metrics computed out of a slice of Results which are used
	// in some of the Reporters
	Metrics struct {
		// Latencies holds computed latency metrics.
		Latencies LatencyMetrics `json:"latencies"`
		// BytesIn holds computed incoming byte metrics.
		BytesIn ByteMetrics `json:"bytes_in"`
		// BytesOut holds computed outgoing byte metrics.
		BytesOut ByteMetrics `json:"bytes_out"`
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
	}

	// LatencyMetrics holds computed request latency metrics.
	LatencyMetrics struct {
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

// NewMetrics computes and returns a Metrics struct out of a slice of Results
// pre-sorted by timestamp.
func NewMetrics(r Results) *Metrics {
	m := &Metrics{StatusCodes: map[string]int{}}

	if len(r) == 0 {
		return m
	}

	var (
		errorSet       = map[string]struct{}{}
		latencies      = make([]float64, len(r))
		totalSuccess   int
		totalLatencies time.Duration
		latest         time.Time
	)

	for i, result := range r {
		latencies[i] = float64(result.Latency)
		m.StatusCodes[strconv.Itoa(int(result.Code))]++
		totalLatencies += result.Latency
		m.BytesOut.Total += result.BytesOut
		m.BytesIn.Total += result.BytesIn
		if end := result.Timestamp.Add(result.Latency); end.After(latest) {
			latest = end
		}
		if result.Code >= 200 && result.Code < 400 {
			totalSuccess++
		}
		if result.Error != "" {
			errorSet[result.Error] = struct{}{}
		}
	}

	m.Requests = uint64(len(r))
	m.Duration = r[len(r)-1].Timestamp.Sub(r[0].Timestamp)
	m.Rate = float64(m.Requests) / m.Duration.Seconds()
	m.Wait = latest.Sub(r[len(r)-1].Timestamp)
	m.Latencies.Mean = time.Duration(float64(totalLatencies) / float64(m.Requests))
	m.BytesIn.Mean = float64(m.BytesIn.Total) / float64(m.Requests)
	m.BytesOut.Mean = float64(m.BytesOut.Total) / float64(m.Requests)
	m.Success = float64(totalSuccess) / float64(m.Requests)

	sort.Float64s(latencies)
	m.Latencies.P50 = time.Duration(.5 + quantileR8(0.50, latencies))
	m.Latencies.P95 = time.Duration(.5 + quantileR8(0.95, latencies))
	m.Latencies.P99 = time.Duration(.5 + quantileR8(0.99, latencies))
	m.Latencies.Max = time.Duration(latencies[len(latencies)-1])

	m.Errors = make([]string, 0, len(errorSet))
	for err := range errorSet {
		m.Errors = append(m.Errors, err)
	}

	return m
}

// quantileR8 computes the quantile p with R's type 8 estimation method.
// The resulting quantile estimates are approximately median-unbiased
// regardless of the distribution of x.
func quantileR8(p float64, x []float64) float64 {
	return quantile(p, 1/3.0, 1/3.0, x)
}

// quantile computes empirical quantiles for a slice of sorted float64s.
// The implementation is an adaptation of scipy.stats.mstats.mquantiles. See:
// http://docs.scipy.org/doc/scipy-0.15.1/reference/generated/scipy.stats.mstats.mquantiles.html
func quantile(p, alphap, betap float64, x []float64) float64 {
	switch len(x) {
	case 0:
		return 0
	case 1:
		return x[0]
	}
	m := alphap + p*(1-alphap-betap)
	n := float64(len(x))
	aleph := n*p + m
	k := math.Floor(clip(aleph, 1, n-1))
	gamma := clip(aleph-k, 0, 1)
	return (1-gamma)*x[int(k)-1] + gamma*x[int(k)]
}

// clip clips a number n to the range [lo, hi]
func clip(n, lo, hi float64) float64 {
	switch {
	case n < lo:
		return lo
	case n > hi:
		return hi
	default:
		return n
	}
}

package vegeta

import (
	"strconv"
	"time"

	hdr "github.com/codahale/hdrhistogram"
)

// Metrics holds the stats computed out of a slice of Results
// that is used for some of the Reporters
type Metrics struct {
	Latencies struct {
		Mean time.Duration `json:"mean"`
		P50  time.Duration `json:"50th"`  // P50 is the 50th percentile upper value
		P95  time.Duration `json:"95th"`  // P95 is the 95th percentile upper value
		P99  time.Duration `json:"99th"`  // P99 is the 99th percentile upper value
		P999 time.Duration `json:"999th"` // P999 is the 99.9th percentile upper value
		Max  time.Duration `json:"max"`
		Min  time.Duration `json:"min"`
	} `json:"latencies"`

	BytesIn struct {
		Total uint64  `json:"total"`
		Mean  float64 `json:"mean"`
	} `json:"bytes_in"`

	BytesOut struct {
		Total uint64  `json:"total"`
		Mean  float64 `json:"mean"`
	} `json:"bytes_out"`

	// Duration is the duration of the attack.
	Duration time.Duration `json:"duration"`
	// Wait is the extra time waiting for responses from targets.
	Wait time.Duration `json:"wait"`
	// Requests is the total number of requests executed.
	Requests uint64 `json:"requests"`
	// Success is the percentage of non-error responses.
	Success float64 `json:"success"`
	// StatusCodes is a histogram of the responses' status codes.
	StatusCodes map[string]int `json:"status_codes"`
	// Errors is a set of unique errors returned by the targets during the attack.
	Errors []string `json:"errors"`
}

// NewMetrics computes and returns a Metrics struct out of a slice of Results.
func NewMetrics(r Results) *Metrics {
	m := &Metrics{StatusCodes: map[string]int{}}

	if len(r) == 0 {
		return m
	}

	var (
		errorSet = map[string]struct{}{}
		success  int
		latest   time.Time
	)

	m.Latencies.Min = r[0].Latency
	m.Latencies.Max = m.Latencies.Min

	for _, result := range r {
		m.StatusCodes[strconv.Itoa(int(result.Code))]++
		m.BytesOut.Total += result.BytesOut
		m.BytesIn.Total += result.BytesIn
		if result.Latency > m.Latencies.Max {
			m.Latencies.Max = result.Latency
		}
		if result.Latency < m.Latencies.Min {
			m.Latencies.Min = result.Latency
		}
		if end := result.Timestamp.Add(result.Latency); end.After(latest) {
			latest = end
		}
		if result.Code >= 200 && result.Code < 400 {
			success++
		}
		if result.Error != "" {
			errorSet[result.Error] = struct{}{}
		}
	}

	hist := hdr.New(int64(m.Latencies.Min), int64(m.Latencies.Max), 5)
	for _, result := range r {
		hist.RecordValue(int64(result.Latency))
	}

	m.Requests = uint64(len(r))
	m.Duration = r[len(r)-1].Timestamp.Sub(r[0].Timestamp)
	m.Wait = latest.Sub(r[len(r)-1].Timestamp)
	m.Latencies.Mean = time.Duration(hist.Mean())
	m.Latencies.P50 = time.Duration(hist.ValueAtQuantile(50))
	m.Latencies.P95 = time.Duration(hist.ValueAtQuantile(95))
	m.Latencies.P99 = time.Duration(hist.ValueAtQuantile(99))
	m.Latencies.P999 = time.Duration(hist.ValueAtQuantile(99.9))
	m.BytesIn.Mean = float64(m.BytesIn.Total) / float64(m.Requests)
	m.BytesOut.Mean = float64(m.BytesOut.Total) / float64(m.Requests)
	m.Success = float64(success) / float64(m.Requests)

	m.Errors = make([]string, 0, len(errorSet))
	for err := range errorSet {
		m.Errors = append(m.Errors, err)
	}
	return m
}

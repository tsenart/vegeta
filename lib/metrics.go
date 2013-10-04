package vegeta

import (
	"strconv"
	"time"

	"github.com/bmizerany/perks/quantile"
)

// Metrics holds the stats computed out of a slice of Results
// that is used for some of the Reporters
type Metrics struct {
	Latencies struct {
		Total  time.Duration `json:"total"`
		Max    time.Duration `json:"max"`
		Mean   time.Duration `json:"mean"`
		Mean95 time.Duration `json:"mean_95"`
		Mean99 time.Duration `json:"mean_99"`
	} `json:"latencies"`

	BytesIn struct {
		Total uint64  `json:"total"`
		Mean  float64 `json:"mean"`
	} `json:"bytes_in"`

	BytesOut struct {
		Total uint64  `json:"total"`
		Mean  float64 `json:"mean"`
	} `json:"bytes_out"`

	Requests    uint64         `json:"requests"`
	Success     float64        `json:"success"`
	StatusCodes map[string]int `json:"status_codes"`
	Errors      []string       `json:"errors"`
}

// NewMetrics computes and returns a Metrics struct out of a slice of Results
func NewMetrics(results []Result) *Metrics {
	m := &Metrics{
		Requests:    uint64(len(results)),
		StatusCodes: map[string]int{},
	}
	errorSet := map[string]struct{}{}
	quants := quantile.NewTargeted(0.95, 0.99)
	totalSuccess := 0

	for _, result := range results {
		quants.Insert(float64(result.Latency))
		m.StatusCodes[strconv.Itoa(int(result.Code))]++
		m.Latencies.Total += result.Latency
		m.BytesOut.Total += result.BytesOut
		m.BytesIn.Total += result.BytesIn
		if result.Latency > m.Latencies.Max {
			m.Latencies.Max = result.Latency
		}
		if result.Code >= 200 && result.Code < 300 {
			totalSuccess++
		}
		if result.Error != "" {
			errorSet[result.Error] = struct{}{}
		}
	}

	m.Latencies.Mean = time.Duration(float64(m.Latencies.Total) / float64(m.Requests))
	m.Latencies.Mean95 = time.Duration(quants.Query(0.95))
	m.Latencies.Mean99 = time.Duration(quants.Query(0.99))
	m.BytesIn.Mean = float64(m.BytesIn.Total) / float64(m.Requests)
	m.BytesOut.Mean = float64(m.BytesOut.Total) / float64(m.Requests)
	m.Success = float64(totalSuccess) / float64(m.Requests)

	m.Errors = make([]string, 0, len(errorSet))
	for err := range errorSet {
		m.Errors = append(m.Errors, err)
	}

	return m
}

package vegeta

import (
	"strconv"
	"time"
	"github.com/bmizerany/perks/quantile"
	"fmt"
	"strings"
)

// Metrics holds the stats computed out of a slice of Results
// that is used for some of the Reporters
type Metrics struct {
	Latencies struct {
		Mean time.Duration `json:"mean"`
		P95  time.Duration `json:"95th"` // P95 is the 95th percentile upper value
		P99  time.Duration `json:"99th"` // P99 is the 99th percentile upper value
		Max  time.Duration `json:"max"`
	} `json:"latencies"`

	BytesIn struct {
		Total uint64  `json:"total"`
		Mean  float64 `json:"mean"`
	} `json:"bytes_in"`

	BytesOut struct {
		Total uint64  `json:"total"`
		Mean  float64 `json:"mean"`
	} `json:"bytes_out"`

	Duration    time.Duration  `json:"duration"`
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
	totalSuccess, totalLatencies := 0, time.Duration(0)

	for _, result := range results {
		quants.Insert(float64(result.Latency))
		m.StatusCodes[strconv.Itoa(int(result.Code))]++
		totalLatencies += result.Latency
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

	m.Duration = results[len(results)-1].Timestamp.Sub(results[0].Timestamp)
	m.Latencies.Mean = time.Duration(float64(totalLatencies) / float64(m.Requests))
	m.Latencies.P95 = time.Duration(quants.Query(0.95))
	m.Latencies.P99 = time.Duration(quants.Query(0.99))
	m.BytesIn.Mean = float64(m.BytesIn.Total) / float64(m.Requests)
	m.BytesOut.Mean = float64(m.BytesOut.Total) / float64(m.Requests)
	m.Success = float64(totalSuccess) / float64(m.Requests)

	m.Errors = make([]string, 0, len(errorSet))
	for err := range errorSet {
		m.Errors = append(m.Errors, err)
	}

	return m
}


func csvString(d time.Duration) string { 
	var result float64 =  float64(d.Nanoseconds()   / 1000.0 / 1000.0)  // in miliseconds 
	return strconv.FormatFloat(result,  'f', -1, 64)
}

func(m *Metrics) Csv(rate uint64) []string {
		result := fmt.Sprintf("%d req/s,%s,%s,%s,%s,%f,%f,%.2f",rate,
			  csvString(m.Latencies.Mean), csvString(m.Latencies.P95), csvString(m.Latencies.P99), csvString(m.Latencies.Max),
			  m.BytesIn.Mean, m.BytesOut.Mean, m.Success * 100)
        return strings.Split(result, ",")
}


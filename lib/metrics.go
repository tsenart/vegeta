package vegeta

import (
	"strconv"
	"time"
)

// Metrics holds the stats computed out of a slice of Results
// that is used for some of the Reporters
type Metrics struct {
	TotalRequests uint64         `json:"total_requests"`
	TotalTiming   time.Duration  `json:"total_timing"`
	MeanTiming    time.Duration  `json:"mean_timing"`
	TotalBytesIn  uint64         `json:"total_bytes_in"`
	MeanBytesIn   float64        `json:"mean_bytes_in"`
	TotalBytesOut uint64         `json:"total_bytes_out"`
	MeanBytesOut  float64        `json:"mean_bytes_out"`
	TotalSuccess  uint64         `json:"total_success"`
	MeanSuccess   float64        `json:"mean_success"`
	StatusCodes   map[string]int `json:"status_codes"`
	Errors        []string       `json:"errors"`
}

// NewMetrics computes and returns a Metrics struct out of a slice of Results
func NewMetrics(results []Result) *Metrics {
	m := &Metrics{
		TotalRequests: uint64(len(results)),
		StatusCodes:   map[string]int{},
	}
	errorSet := map[string]struct{}{}

	for _, result := range results {
		m.StatusCodes[strconv.Itoa(int(result.Code))]++
		m.TotalTiming += result.Timing
		m.TotalBytesOut += result.BytesOut
		m.TotalBytesIn += result.BytesIn
		if result.Code >= 200 && result.Code < 300 {
			m.TotalSuccess++
		}
		if result.Error != nil {
			errorSet[result.Error.Error()] = struct{}{}
		}
	}

	m.MeanTiming = time.Duration(float64(m.TotalTiming) / float64(m.TotalRequests))
	m.MeanBytesOut = float64(m.TotalBytesOut) / float64(m.TotalRequests)
	m.MeanBytesIn = float64(m.TotalBytesIn) / float64(m.TotalRequests)
	m.MeanSuccess = float64(m.TotalSuccess) / float64(m.TotalRequests)

	m.Errors = make([]string, 0, len(errorSet))
	for err, _ := range errorSet {
		m.Errors = append(m.Errors, err)
	}

	return m
}

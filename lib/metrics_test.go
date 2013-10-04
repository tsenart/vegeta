package vegeta

import (
	"testing"
	"time"
)

func TestNewMetrics(t *testing.T) {
	m := NewMetrics([]Result{
		Result{500, time.Now(), 100 * time.Millisecond, 10, 30, "Internal server error"},
		Result{200, time.Now(), 20 * time.Millisecond, 20, 20, ""},
		Result{200, time.Now(), 30 * time.Millisecond, 30, 10, ""},
	})

	for field, values := range map[string][]float64{
		"BytesIn.Mean":  []float64{m.BytesIn.Mean, 20.0},
		"BytesOut.Mean": []float64{m.BytesOut.Mean, 20.0},
		"Sucess":        []float64{m.Success, 0.6666666666666666},
	} {
		if values[0] != values[1] {
			t.Errorf("%s: want: %f, got: %f", field, values[1], values[0])
		}
	}

	for field, values := range map[string][]time.Duration{
		"Latencies.Total":  []time.Duration{m.Latencies.Total, 150 * time.Millisecond},
		"Latencies.Mean":   []time.Duration{m.Latencies.Mean, 50 * time.Millisecond},
		"Latencies.Mean95": []time.Duration{m.Latencies.Mean95, 30 * time.Millisecond},
		"Latencies.Mean99": []time.Duration{m.Latencies.Mean99, 30 * time.Millisecond},
		"Latencies.Max":    []time.Duration{m.Latencies.Max, 100 * time.Millisecond},
	} {
		if values[0] != values[1] {
			t.Errorf("%s: want: %s, got: %s", field, values[1], values[0])
		}
	}

	for field, values := range map[string][]uint64{
		"BytesOut.Total": []uint64{m.BytesOut.Total, 60},
		"BytesIn.Total":  []uint64{m.BytesIn.Total, 60},
		"Requests":       []uint64{m.Requests, 3},
	} {
		if values[0] != values[1] {
			t.Errorf("%s: want: %d, got: %d", field, values[1], values[0])
		}
	}

	if len(m.StatusCodes) != 2 || m.StatusCodes["200"] != 2 || m.StatusCodes["500"] != 1 {
		t.Errorf("StatusCodes: want: %v, got: %v", map[int]int{200: 2, 500: 1}, m.StatusCodes)
	}

	err := "Internal server error"
	if len(m.Errors) != 1 || m.Errors[0] != err {
		t.Errorf("Errors: want: %v, got: %v", []string{err}, m.Errors)
	}
}

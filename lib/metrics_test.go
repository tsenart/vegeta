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
		"MeanBytesIn":  []float64{m.MeanBytesIn, 20.0},
		"MeanBytesOut": []float64{m.MeanBytesOut, 20.0},
		"MeanSuccess":  []float64{m.MeanSuccess, 0.6666666666666666},
	} {
		if values[0] != values[1] {
			t.Errorf("%s: want: %f, got: %f", field, values[1], values[0])
		}
	}

	for field, values := range map[string][]time.Duration{
		"TotalTiming": []time.Duration{m.TotalTiming, 150 * time.Millisecond},
		"MeanTiming":  []time.Duration{m.MeanTiming, 50 * time.Millisecond},
	} {
		if values[0] != values[1] {
			t.Errorf("%s: want: %s, got: %s", field, values[1], values[0])
		}
	}

	for field, values := range map[string][]uint64{
		"TotalSuccess":  []uint64{m.TotalSuccess, 2},
		"TotalBytesOut": []uint64{m.TotalBytesOut, 60},
		"TotalRequests": []uint64{m.TotalRequests, 3},
		"TotalBytesIn":  []uint64{m.TotalBytesIn, 60},
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

package vegeta

import (
	"testing"
	"time"
)

func TestNewMetrics(t *testing.T) {
	t.Parallel()

	m := NewMetrics(Results{
		&Result{500, time.Unix(0, 0), 100 * time.Millisecond, 10, 30, "Internal server error"},
		&Result{200, time.Unix(1, 0), 20 * time.Millisecond, 20, 20, ""},
		&Result{302, time.Unix(0, 0), 10 * time.Millisecond, 20, 20, ErrTooManyRedirects.Error()},
		&Result{200, time.Unix(2, 0), 30 * time.Millisecond, 30, 10, ""},
	})

	for field, values := range map[string][]float64{
		"BytesIn.Mean":  []float64{m.BytesIn.Mean, 20.0},
		"BytesOut.Mean": []float64{m.BytesOut.Mean, 20.0},
		"Sucess":        []float64{m.Success, 0.750000},
	} {
		if values[0] != values[1] {
			t.Errorf("%s: want: %f, got: %f", field, values[1], values[0])
		}
	}

	for field, values := range map[string][]time.Duration{
		"Latencies.Max":  []time.Duration{m.Latencies.Max, 100 * time.Millisecond},
		"Latencies.Mean": []time.Duration{m.Latencies.Mean, 40 * time.Millisecond},
		"Latencies.P50":  []time.Duration{m.Latencies.P50, 20 * time.Millisecond},
		"Latencies.P95":  []time.Duration{m.Latencies.P95, 30 * time.Millisecond},
		"Latencies.P99":  []time.Duration{m.Latencies.P99, 30 * time.Millisecond},
		"Duration":       []time.Duration{m.Duration, 2 * time.Second},
		"Wait":           []time.Duration{m.Wait, 30 * time.Millisecond},
	} {
		if values[0] != values[1] {
			t.Errorf("%s: want: %s, got: %s", field, values[1], values[0])
		}
	}

	for field, values := range map[string][]uint64{
		"BytesOut.Total": []uint64{m.BytesOut.Total, 80},
		"BytesIn.Total":  []uint64{m.BytesIn.Total, 80},
		"Requests":       []uint64{m.Requests, 4},
	} {
		if values[0] != values[1] {
			t.Errorf("%s: want: %d, got: %d", field, values[1], values[0])
		}
	}

	if len(m.StatusCodes) != 3 || m.StatusCodes["200"] != 2 || m.StatusCodes["500"] != 1 || m.StatusCodes["302"] != 1 {
		t.Errorf("StatusCodes: want: %v, got: %v", map[int]int{200: 2, 500: 1}, m.StatusCodes)
	}

	err := "Internal server error"
	if len(m.Errors) != 1 || m.Errors[0] != err {
		t.Errorf("Errors: want: %v, got: %v", []string{err}, m.Errors)
	}
}

func TestNewMetricsEmptyResults(t *testing.T) {
	_ = NewMetrics(Results{}) // Must not panic
}

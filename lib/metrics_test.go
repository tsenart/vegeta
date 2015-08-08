package vegeta

import (
	"reflect"
	"testing"
	"time"
)

func TestNewMetrics(t *testing.T) {
	t.Parallel()

	want := &Metrics{
		Latencies: LatencyMetrics{
			Mean: 112100000,
			P50:  115000000,
			P95:  200000000,
			P99:  200000000,
			Max:  200000000,
		},
		BytesIn:     ByteMetrics{Total: 170, Mean: 17.00},
		BytesOut:    ByteMetrics{Total: 230, Mean: 23.00},
		Duration:    9 * time.Second,
		Wait:        190 * time.Millisecond,
		Requests:    10,
		Rate:        1.1111111111111112,
		Success:     0.9,
		StatusCodes: map[string]int{"500": 1, "200": 7, "302": 2},
		Errors:      []string{"Internal server error"},
	}

	got := NewMetrics(Results{
		&Result{500, time.Unix(0, 0), 100 * time.Millisecond, 10, 30, "Internal server error"},
		&Result{200, time.Unix(1, 0), 20 * time.Millisecond, 20, 20, ""},
		&Result{302, time.Unix(2, 0), 10 * time.Millisecond, 20, 20, ""},
		&Result{200, time.Unix(3, 0), 75 * time.Millisecond, 30, 10, ""},
		&Result{200, time.Unix(4, 0), 200 * time.Millisecond, 20, 20, ""},
		&Result{200, time.Unix(5, 0), 110 * time.Millisecond, 20, 20, ""},
		&Result{302, time.Unix(6, 0), 120 * time.Millisecond, 20, 20, ""},
		&Result{200, time.Unix(7, 0), 130 * time.Millisecond, 30, 10, ""},
		&Result{200, time.Unix(8, 0), 166 * time.Millisecond, 30, 10, ""},
		&Result{200, time.Unix(9, 0), 190 * time.Millisecond, 30, 10, ""},
	})

	if !reflect.DeepEqual(got, want) {
		t.Errorf("\ngot:  %+v\nwant: %+v", got, want)
	}
}

func TestNewMetricsEmptyResults(t *testing.T) {
	_ = NewMetrics(Results{}) // Must not panic
}

package vegeta

import (
	"reflect"
	"testing"
	"time"
)

func BenchmarkReportPlot(b *testing.B) {
	b.StopTimer()
	// Build result set
	results := make(Results, 50000)
	for began, i := time.Now(), 0; i < len(results); i++ {
		results[i] = &Result{
			Code:      uint16(i % 600),
			Latency:   50 * time.Millisecond,
			Timestamp: began.Add(time.Duration(i) * 50 * time.Millisecond),
		}
		if i%5 == 0 {
			results[i].Error = "Error"
		}
	}
	// Start benchmark
	b.ReportAllocs()
	b.StartTimer()
	for i := 0; i < b.N; i++ {
		ReportPlot(results)
	}
}

func TestHistogramReporter_Set(t *testing.T) {
	for value, want := range map[string]string{
		"":       "bad buckets: ",
		" ":      "bad buckets:  ",
		"{0, 2}": "bad buckets: {0, 2}",
		"[]":     "time: invalid duration ",
		"[0, 2]": "time: missing unit in duration 2",
	} {
		if got := (&HistogramReporter{}).Set(value).Error(); got != want {
			t.Errorf("got: %v, want: %v", got, want)
		}
	}

	for value, want := range map[string][]time.Duration{
		"[0,5ms]":             {0, 5 * time.Millisecond},
		"[0, 5ms]":            {0, 5 * time.Millisecond},
		"[   0,5ms, 10m    ]": {0, 5 * time.Millisecond, 10 * time.Minute},
	} {
		var got []time.Duration
		if err := (*HistogramReporter)(&got).Set(value); err != nil {
			t.Fatal(err)
		} else if !reflect.DeepEqual(got, want) {
			t.Errorf("got: %v, want: %v", got, want)
		}
	}
}

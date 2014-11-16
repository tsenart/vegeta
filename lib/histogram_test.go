package vegeta

import (
	"testing"
	"time"
)

func TestHistogram(t *testing.T) {
	buckets := []time.Duration{
		0,
		10 * time.Millisecond,
		25 * time.Millisecond,
		50 * time.Millisecond,
		100 * time.Millisecond,
		1000 * time.Millisecond,
	}
	results := Results{
		{Latency: 5 * time.Millisecond},
		{Latency: 15 * time.Millisecond},
		{Latency: 30 * time.Millisecond},
		{Latency: 75 * time.Millisecond},
		{Latency: 200 * time.Millisecond},
		{Latency: 2000 * time.Millisecond},
	}
	for _, count := range Histogram(buckets, results) {
		if want, got := uint64(1), count; want != got {
			t.Fatalf("want: %d, got: %d", want, got)
		}
	}
}

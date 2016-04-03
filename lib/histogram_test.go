package vegeta

import (
	"reflect"
	"testing"
	"time"
)

func TestHistogram_Add(t *testing.T) {
	t.Parallel()
	hist := Histogram{
		Buckets: []time.Duration{
			0,
			10 * time.Millisecond,
			25 * time.Millisecond,
			50 * time.Millisecond,
			100 * time.Millisecond,
			1000 * time.Millisecond,
		},
	}

	for _, d := range []time.Duration{
		5 * time.Millisecond,
		15 * time.Millisecond,
		30 * time.Millisecond,
		75 * time.Millisecond,
		200 * time.Millisecond,
		2000 * time.Millisecond,
	} {
		hist.Add(&Result{Latency: d})
	}

	if got, want := hist.Counts, []uint64{1, 1, 1, 1, 1, 1}; !reflect.DeepEqual(got, want) {
		t.Errorf("Counts: got: %v, want: %v", got, want)
	}

	if got, want := hist.Total, uint64(6); got != want {
		t.Errorf("Total: got %v, want: %v", got, want)
	}
}

func TestBuckets_UnmarshalText(t *testing.T) {
	t.Parallel()
	for value, want := range map[string]string{
		"":       "bad buckets: ",
		" ":      "bad buckets:  ",
		"{0, 2}": "bad buckets: {0, 2}",
		"[]":     "time: invalid duration ",
		"[0, 2]": "time: missing unit in duration 2",
	} {
		if got := (&Buckets{}).UnmarshalText([]byte(value)).Error(); got != want {
			t.Errorf("got: %v, want: %v", got, want)
		}
	}

	for value, want := range map[string]Buckets{
		"[0,5ms]":             {0, 5 * time.Millisecond},
		"[0, 5ms]":            {0, 5 * time.Millisecond},
		"[   0,5ms, 10m    ]": {0, 5 * time.Millisecond, 10 * time.Minute},
	} {
		var got Buckets
		if err := got.UnmarshalText([]byte(value)); err != nil {
			t.Fatal(err)
		} else if !reflect.DeepEqual(got, want) {
			t.Errorf("got: %v, want: %v", got, want)
		}
	}
}

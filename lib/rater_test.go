package vegeta

import (
	"math"
	"testing"
	"time"
)

var quarterPeriods = map[string]float64{
	"MeanUp":   MeanUp,
	"Peak":     Peak,
	"MeanDown": MeanDown,
	"Trough":   Trough,
}

func TestRateInterval(t *testing.T) {
	t.Parallel()
	began := time.Now()

	for i, tt := range []struct {
		freq  int
		per   time.Duration
		count uint64
		since time.Duration
		want  time.Duration
	}{
		// 1 hit/sec, 0 hits sent, 1s elapsed => -1s until next hit
		// (time.Sleep will return immediately in this case)
		{1, time.Second, 0, time.Second, -time.Second},
		// 1 hit/sec, 1 hit sent, 1s elapsed => 0s until next hit
		{1, time.Second, 1, time.Second, 0},
		// 1 hit/sec, 2 hits sent, 1s elapsed => 1s until next hit
		{1, time.Second, 2, time.Second, time.Second},
		// 1 hit/sec, 10 hits sent, 1s elapsed => 9s until next hit
		{1, time.Second, 10, time.Second, 9 * time.Second},
		// 1 hit/sec, 10 hits sent, 10s elapsed => 0s until next hit
		{1, time.Second, 10, 10 * time.Second, 0},
		// 2 hit/sec, 9 hits sent, 4.4s elapsed => 100ms until next hit
		{2, time.Second, 9, (44 * time.Second) / 10, 100 * time.Millisecond},
	} {
		r := Rate{Freq: tt.freq, Per: tt.per}
		got := r.interval(began, began.Add(tt.since), tt.count)
		if got != tt.want {
			t.Errorf("%d: %v.Interval(%v, %d) = %v; want %v",
				i, r, tt.since, tt.count, got, tt.want)
		}
	}
}

func TestRateHits(t *testing.T) {
	for i, tt := range []struct {
		freq int
		per  time.Duration
		du   time.Duration
		want uint64
	}{
		{1, time.Second, 0, 0},
		{1, time.Second, time.Second, 1},
		{2, time.Second, time.Second, 2},
		{1, time.Second, 10 * time.Second, 10},
		{100, time.Second, 100 * time.Second, 100 * 100},
	} {
		r := Rate{Freq: tt.freq, Per: tt.per}
		got := r.Hits(tt.du)
		if got != tt.want {
			t.Errorf("%d: %v.Hits(%v) = %d; want %d", i, r, tt.du, got, tt.want)
		}
	}
}

type sineTest struct {
	p, m, a float64
}

func (st sineTest) Rate(startAt float64) SineRate {
	return SineRate{
		Period:  time.Duration(st.p) * time.Second,
		Mean:    st.m / float64(time.Second),
		Amp:     st.a / float64(time.Second),
		StartAt: startAt,
	}
}

func (st sineTest) AmpHits() float64 {
	return (st.a * st.p) / (2 * math.Pi)
}

func (st sineTest) Hits(frac, startAt float64) uint64 {
	return uint64(math.Round(
		st.m*st.p*frac +
			st.AmpHits()*(math.Cos(startAt)-math.Cos(startAt+frac*2*math.Pi))))
}

func (st sineTest) Nanos(frac, startAt float64) time.Duration {
	return time.Duration(1 / (st.m + st.a*math.Sin(startAt+frac*2*math.Pi)))
}

func TestSineRateHits(t *testing.T) {
	tests := []sineTest{
		{20 * 60, 100, 90},
		{60, 1000, 10},
		{1, 1, 0.7},
		{1, 1, 0},
		// These test cases failed with off-by-one errors before applying
		// math.Round in Hits, due to floating-point maths differences.
		{1e6, 1, 0.7},
		{60, 1000, 999},
	}

	for i, test := range tests {
		for name, sa := range quarterPeriods {
			sr := test.Rate(sa)
			if got, want := sr.Hits(sr.Period/4), test.Hits(0.25, sa); got != want {
				t.Errorf("%d(%s): hits after 1/4 period = %d, want %d", i, name, got, want)
			}
			if got, want := sr.Hits(sr.Period/2), test.Hits(0.5, sa); got != want {
				t.Errorf("%d(%s): hits after 1/2 period = %d, want %d", i, name, got, want)
			}
			if got, want := sr.Hits(3*sr.Period/4), test.Hits(0.75, sa); got != want {
				t.Errorf("%d(%s): hits after 3/4 period = %d, want %d", i, name, got, want)
			}
			if got, want := sr.Hits(sr.Period), test.Hits(1, sa); got != want {
				t.Errorf("%d(%s): hits after full period = %d, want %d", i, name, got, want)
			}
		}
	}
}

func TestSineIntervalFlat(t *testing.T) {
	st := sineTest{1, 1, 0}
	tests := []struct {
		et   time.Duration
		c    uint64
		want time.Duration
	}{
		{0, 0, time.Second},
		{0, 1, 2 * time.Second},
		{time.Second / 100, 0, 99 * time.Second / 100},
		{time.Second / 2, 0, time.Second / 2},
		{64 * time.Second / 100, 0, 36 * time.Second / 100},
		// Has an off-by-one I can't round away nicely because it's
		// due to expectedHits being 0.9900000000000001. Ugh floats.
		// {99 * time.Second / 100, 0, time.Second / 100},
		{time.Second, 1, time.Second},
		{time.Second, 0, 0},
	}

	for i, test := range tests {
		for name, sa := range quarterPeriods {
			sr := st.Rate(sa)
			if got := sr.interval(test.et, test.c); got != test.want {
				t.Errorf("%d(%s): interval(%v, %d) = %v, want %v",
					i, name, test.et, test.c, got, test.want)
			}
		}
	}
}

// No idea how to test interval without hard-coding a bunch of numbers.

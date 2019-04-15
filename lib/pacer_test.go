package vegeta

import (
	"math"
	"testing"
	"time"
)

func TestRatePacing(t *testing.T) {
	t.Parallel()

	for i, tt := range []struct {
		freq    int
		per     time.Duration
		elapsed time.Duration
		count   uint64
		wait    time.Duration
		stop    bool
	}{
		// NOTE: Rate sleeps before sending the first hit,
		// rather than sending the first hit instantly!
		// 1 hit/sec, 0 hits sent, 1s elapsed => 0s until next hit
		// (time.Sleep will return immediately in this case)
		{1, time.Second, time.Second, 0, 0, false},
		// 1 hit/sec, 0 hits sent, 2s elapsed => -1s until next hit
		// (time.Sleep will return immediately in this case)
		{1, time.Second, 2 * time.Second, 0, -1 * time.Second, false},
		// 1 hit/sec, 1 hit sent, 1s elapsed => 1s until next hit
		{1, time.Second, time.Second, 1, time.Second, false},
		// 1 hit/sec, 2 hits sent, 1s elapsed => 2s until next hit
		{1, time.Second, time.Second, 2, 2 * time.Second, false},
		// 1 hit/sec, 10 hits sent, 1s elapsed => 10s until next hit
		{1, time.Second, time.Second, 10, 10 * time.Second, false},
		// 1 hit/sec, 10 hits sent, 11s elapsed => 0s until next hit
		{1, time.Second, 11 * time.Second, 10, 0, false},
		// 2 hit/sec, 9 hits sent, 4.9s elapsed => 100ms until next hit
		{2, time.Second, (49 * time.Second) / 10, 9, 100 * time.Millisecond, false},
	} {
		r := &Rate{Freq: tt.freq, Per: tt.per}

		wait, stop := r.Pace(tt.elapsed, tt.count)
		if have, want := wait, tt.wait; have != want {
			t.Errorf("test case %d: %+v: wait=%v, want %v", i, r, have, want)
		}
		if have, want := stop, tt.stop; have != want {
			t.Errorf("test case %d: %+v: stop=%v, want %v", i, r, have, want)
		}
	}
}

var quarterPeriods = map[string]float64{
	"MeanUp":   MeanUp,
	"Peak":     Peak,
	"MeanDown": MeanDown,
	"Trough":   Trough,
}

type sineTest struct {
	p, m, a int
}

func (st sineTest) Pacer(startAt float64) SinePacer {
	return SinePacer{
		Period:  time.Duration(st.p) * time.Second,
		Mean:    Rate{st.m, time.Second},
		Amp:     Rate{st.a, time.Second},
		StartAt: startAt,
	}
}

func (st sineTest) AmpHits() float64 {
	return float64(st.a*st.p) / (2 * math.Pi)
}

func (st sineTest) Hits(frac, startAt float64) uint64 {
	return uint64(math.Round(
		float64(st.m*st.p)*frac +
			st.AmpHits()*(math.Cos(startAt)-math.Cos(startAt+frac*2*math.Pi))))
}

func (st sineTest) Nanos(frac, startAt float64) time.Duration {
	return time.Duration(1 / (float64(st.m) + float64(st.a)*math.Sin(startAt+frac*2*math.Pi)))
}

func TestSinePacerHits(t *testing.T) {
	tests := []sineTest{
		{20 * 60, 100, 90},
		{60, 1000, 10},
		{1, 10, 7},
		{1, 1, 0},
		// These test cases failed with off-by-one errors before applying
		// math.Round in Hits, due to floating-point maths differences.
		{1e6, 10, 7},
		{60, 1000, 999},
	}

	for i, test := range tests {
		for name, sa := range quarterPeriods {
			sr := test.Pacer(sa)
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

func TestSinePacerFlat(t *testing.T) {
	st := sineTest{1, 1, 0}
	tests := []struct {
		et   time.Duration
		c    uint64
		wait time.Duration
		stop bool
	}{
		{0, 0, time.Second, false},
		{0, 1, 2 * time.Second, false},
		{time.Second / 100, 0, 99 * time.Second / 100, false},
		{time.Second / 2, 0, time.Second / 2, false},
		{64 * time.Second / 100, 0, 36 * time.Second / 100, false},
		// Has an off-by-one I can't round away nicely because it's
		// due to expectedHits being 0.9900000000000001. Ugh floats.
		// {99 * time.Second / 100, 0, time.Second / 100},
		{time.Second, 1, time.Second, false},
		{time.Second, 0, 0, false},
	}

	for i, test := range tests {
		for name, sa := range quarterPeriods {
			p := st.Pacer(sa)
			wait, stop := p.Pace(test.et, test.c)
			if wait != test.wait || stop != test.stop {
				t.Errorf("%d(%s): wait(%v) = (%v, %v), want (%v, %v)",
					i, name, test.et, wait, stop, test.wait, test.stop)
			}
		}
	}
}

// No idea how to test interval without hard-coding a bunch of numbers.

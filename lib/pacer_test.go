package vegeta

import (
	"math"
	"testing"
	"time"
)

func TestConstantPacer(t *testing.T) {
	t.Parallel()

	for ti, tt := range []struct {
		freq    int
		per     time.Duration
		elapsed time.Duration
		hits    uint64
		wait    time.Duration
		stop    bool
	}{
		// :-( HAPPY PATH TESTS :-)
		// 1 hit/sec, 0 hits sent, 1s elapsed => 0s until next hit
		// (time.Sleep will return immediately in this case)
		{1, time.Second, time.Second, 0, 0, false},
		// 1 hit/sec, 0 hits sent, 2s elapsed => 0s (-1s) until next hit
		// (time.Sleep will return immediately in this case)
		{1, time.Second, 2 * time.Second, 0, 0, false},
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

		// :-( SAD PATH TESTS :-(
		// Zero frequency.
		{0, time.Second, time.Second, 0, 0, true},
		// Zero per.
		{1, 0, time.Second, 0, 0, true},
		// Zero frequency + per.
		{0, 0, time.Second, 0, 0, true},
		// Negative frequency.
		{-1, time.Second, time.Second, 0, 0, true},
		// Negative per.
		{1, -time.Second, time.Second, 0, 0, true},
		// Negative frequency + per.
		{-1, -time.Second, time.Second, 0, 0, true},
		// Large per, overflow int64.
		{1, time.Duration(math.MaxInt64) / 10, time.Duration(math.MaxInt64), 11, 0, true},
		// Large hits, overflow int64.
		{1, time.Hour, time.Duration(math.MaxInt64), 2562048, 0, true},
	} {
		cp := &ConstantPacer{Freq: tt.freq, Per: tt.per}

		wait, stop := cp.Pace(tt.elapsed, tt.hits)
		if wait != tt.wait || stop != tt.stop {
			t.Errorf("%d: %+v.Pace(%s, %d) = (%s, %t); want (%s, %t)",
				ti, cp, tt.elapsed, tt.hits, wait, stop, tt.wait, tt.stop)
		}
	}
}

// Stolen from https://github.com/google/go-cmp/cmp/cmpopts/equate.go
// to avoid an unwieldy dependency. Both fraction and margin set at 1e-6.
func floatEqual(x, y float64) bool {
	relMarg := 1e-6 * math.Min(math.Abs(x), math.Abs(y))
	return math.Abs(x-y) <= math.Max(1e-6, relMarg)
}

// A similar function to the above because SinePacer.Pace has discrete
// inputs and outputs but uses floats internally, and sometimes the
// floating point imprecision leaks out :-(
func durationEqual(x, y time.Duration) bool {
	diff := x - y
	if diff < 0 {
		diff = -diff
	}
	return diff <= time.Microsecond
}

var quarterPeriods = map[string]float64{
	"MeanUp":   MeanUp,
	"Peak":     Peak,
	"MeanDown": MeanDown,
	"Trough":   Trough,
}

// qpahm == Quarter Period Amp-Hit Multiplier
// These are multipliers that help us integrate our rate equation
// in steps of 𝛑/2 without needing to resort to trig functions.
// This relies on integral in each quarter period being:
//   (Mean * Period) / 4 ± (Amp * Period) / 2𝛑
//
// Put another way, the two shaded areas in the graph below contain
// an equal number of hits -- (Amp * Period) / 2𝛑, or ampHits().
//
//  Mean -|         ,-'''-.
//  +Amp  |      ,-'xxx|   `-.
//        |    ,'xxxxxx|      `.
//        |  ,'xxxxxxxx|        `.
//        | /xxxxxxxxxx|          \
//        |/xxxxxxxxxxx|           \
//  Mean -+-------------------------\--------------------------> t
//        |                          \           |xxxxxxxxxxx/
//        |                           \          |xxxxxxxxxx/
//        |                            `.        |xxxxxxxx,'
//        |                              `.      |xxxxxx,'
//  Mean  |                                `-.   |xxx,-'
//  -Amp -|                                   `-,,,-'
//
// The four multipliers are how many multiples of ampHits() away from
// Mean*t the integral is after 1, 2, 3 and 4 quarter-periods respectively.
var qpahm = map[float64][]float64{
	MeanUp:   {1, 2, 1, 0},
	Peak:     {1, 0, -1, 0},
	MeanDown: {-1, -2, -1, 0},
	Trough:   {-1, 0, 1, 0},
}

// Helper struct type to make creating SinePacers easier
type sineTest struct {
	period int // Period, in seconds
	mean   int // Mean request rate, in hits/sec
	amp    int // Amplitude, in hits/sec
}

func (st sineTest) Pacer(startAt float64) SinePacer {
	return SinePacer{
		Period:  time.Duration(st.period) * time.Second,
		Mean:    Rate{st.mean, time.Second},
		Amp:     Rate{st.amp, time.Second},
		StartAt: startAt,
	}
}

// See comment for qpahm above for why this is useful.
func (st sineTest) ampHits() float64 {
	return float64(st.amp) * float64(st.period) / (2 * math.Pi)
}

func TestSinePacerHits(t *testing.T) {
	tests := []sineTest{
		// {period in secs, mean hits/sec, amp hits/sec}
		{20 * 60, 100, 90},
		{60, 1000, 10},
		{1, 10, 7},
		{1, 1, 0},
		{1e6, 10, 7},
		{60, 1000, 999},
	}

	for ti, tt := range tests {
		for name, startAt := range quarterPeriods {
			sp := tt.Pacer(startAt)
			// See comment for qpahm (quarter-period ampHits multiplier) above.
			for i, mult := range qpahm[startAt] {
				periods := i + 1
				want := float64(tt.mean*periods*tt.period)/4 + tt.ampHits()*mult
				if got := sp.hits(time.Duration(periods) * sp.Period / 4); !floatEqual(got, want) {
					t.Errorf("%d(%s): %+v.hits(%d/4 period) = %g, want %g",
						ti, name, sp, i+1, got, want)
				}
			}
		}
	}

	// TestSinePacerInvalid takes care of most of the sad path.
	sp := sineTest{1, 1, 0}.Pacer(0)
	if got := sp.hits(-1); got != 0 {
		t.Errorf("%d: %+v.hits(-1) = %g, want 0", len(tests), sp, got)
	}
}

func TestSinePacerInvalid(t *testing.T) {
	tests := []sineTest{
		// {period in secs, mean hits/sec, amp hits/sec}
		{0, 100, 90},   // Zero period
		{60, 0, 90},    // Zero mean
		{60, 100, 110}, // Amp > mean
		{-10, 100, 90}, // Negative period
		{60, -10, 90},  // Negative mean
	}

	for ti, tt := range tests {
		sp := tt.Pacer(0)
		if got := sp.hits(sp.Period); got != 0 {
			t.Errorf("%d: %+v.hits(%s) = %g, want 0",
				ti, sp, sp.Period, got)
		}
	}
}

// This function tests SinePacer behaviour when the Amplitude is zero,
// which is ... much more predictable than otherwise.
func TestSinePacerPace_Flat(t *testing.T) {
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
		{99 * time.Second / 100, 0, time.Second / 100, false},
		{time.Second, 1, time.Second, false},
		{time.Second, 0, 0, false},
	}

	for i, test := range tests {
		for name, sa := range quarterPeriods {
			p := st.Pacer(sa)
			wait, stop := p.Pace(test.et, test.c)
			if !durationEqual(wait, test.wait) || stop != test.stop {
				t.Errorf("%d(%s): wait(%v) = (%v, %v), want (%v, %v)",
					i, name, test.et, wait, stop, test.wait, test.stop)
			}
		}
	}
}

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

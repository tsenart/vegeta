package vegeta

import (
	"fmt"
	"math"
	"time"
)

// A Pacer defines the rate of hits during an Attack by
// returning the duration an Attacker should wait until
// hitting the next Target. If the second return value
// is true, the attack will terminate.
type Pacer interface {
	Pace(elapsed time.Duration, hits uint64) (wait time.Duration, stop bool)
}

// A PacerFunc is a function adapter type that implements
// the Pacer interface.
type PacerFunc func(time.Duration, uint64) (time.Duration, bool)

// Pace implements the Pacer interface.
func (pf PacerFunc) Pace(elapsed time.Duration, hits uint64) (time.Duration, bool) {
	return pf(elapsed, hits)
}

// A ConstantPacer defines a constant rate of hits for the target.
type ConstantPacer struct {
	Freq int           // Frequency (number of occurrences) per ...
	Per  time.Duration // Time unit, usually 1s
}

// Rate is a type alias for ConstantPacer for backwards-compatibility.
type Rate = ConstantPacer

// ConstantPacer satisfies the Pacer interface.
var _ Pacer = ConstantPacer{}

// String returns a pretty-printed description of the ConstantPacer's behaviour:
//   ConstantPacer{Freq: 1, Per: time.Second} => Constant{1 hits/1s}
func (cp ConstantPacer) String() string {
	return fmt.Sprintf("Constant{%d hits/%s}", cp.Freq, cp.Per)
}

// Pace determines the length of time to sleep until the next hit is sent.
func (cp ConstantPacer) Pace(elapsed time.Duration, hits uint64) (time.Duration, bool) {
	if cp.Per <= 0 || cp.Freq <= 0 {
		// If pacer configuration is invalid, stop the attack.
		return 0, true
	}
	expectedHits := uint64(cp.Freq) * uint64(elapsed/cp.Per)
	if hits < expectedHits {
		// Running behind, send next hit immediately.
		return 0, false
	}
	interval := uint64(cp.Per.Nanoseconds() / int64(cp.Freq))
	if math.MaxInt64/interval < hits {
		// We would overflow delta if we continued, so stop the attack.
		return 0, true
	}
	delta := time.Duration((hits + 1) * interval)
	// Zero or negative durations cause time.Sleep to return immediately.
	return delta - elapsed, false
}


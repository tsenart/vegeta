package vegeta

import (
	"fmt"
	"math"
	"time"
)

// A Pacer defines the rate of hits during an Attack.
type Pacer interface {
	// Pace returns the duration an Attacker should wait until
	// hitting the next Target, given an already elapsed duration and
	// completed hits. If the second return value is true, an attacker
	// should stop sending hits.
	Pace(elapsed time.Duration, hits uint64) (wait time.Duration, stop bool)

	// Rate returns a Pacer's instantaneous hit rate (per seconds)
	// at the given elapsed duration of an attack.
	Rate(elapsed time.Duration) float64
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
//
//	ConstantPacer{Freq: 1, Per: time.Second} => Constant{1 hits/1s}
func (cp ConstantPacer) String() string {
	return fmt.Sprintf("Constant{%d hits/%s}", cp.Freq, cp.Per)
}

// Pace determines the length of time to sleep until the next hit is sent.
func (cp ConstantPacer) Pace(elapsed time.Duration, hits uint64) (time.Duration, bool) {
	switch {
	case cp.Per == 0 || cp.Freq == 0:
		return 0, false // Zero value = infinite rate
	case cp.Per < 0 || cp.Freq < 0:
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

// Rate returns a ConstantPacer's instantaneous hit rate (i.e. requests per second)
// at the given elapsed duration of an attack. Since it's constant, the return
// value is independent of the given elapsed duration.
func (cp ConstantPacer) Rate(elapsed time.Duration) float64 {
	return cp.hitsPerNs() * 1e9
}

// hitsPerNs returns the attack rate this ConstantPacer represents, in
// fractional hits per nanosecond.
func (cp ConstantPacer) hitsPerNs() float64 {
	return float64(cp.Freq) / float64(cp.Per)
}

const (
	// MeanUp is a SinePacer Offset that causes the attack to start
	// at the Mean attack rate and increase towards the peak.
	MeanUp float64 = 0
	// Peak is a SinePacer Offset that causes the attack to start
	// at the peak (maximum) attack rate and decrease towards the Mean.
	Peak = math.Pi / 2
	// MeanDown is a SinePacer Offset that causes the attack to start
	// at the Mean attack rate and decrease towards the trough.
	MeanDown = math.Pi
	// Trough is a SinePacer Offset that causes the attack to start
	// at the trough (minimum) attack rate and increase towards the Mean.
	Trough = 3 * math.Pi / 2
)

// SinePacer is a Pacer that describes attack request rates with the equation:
//
//	R = MA sin(O+(2𝛑/P)t)
//
// Where:
//
//	R = Instantaneous attack rate at elapsed time t, hits per nanosecond
//	M = Mean attack rate over period P, sp.Mean, hits per nanosecond
//	A = Amplitude of sine wave, sp.Amp, hits per nanosecond
//	O = Offset of sine wave, sp.StartAt, radians
//	P = Period of sine wave, sp.Period, nanoseconds
//	t = Elapsed time since attack start, nanoseconds
//
// Many thanks to http://ascii.co.uk/art/sine and "sps" for the ascii here :-)
//
//	Mean -|         ,-'''-.
//	+Amp  |      ,-'   |   `-.
//	      |    ,'      |      `.       O=𝛑
//	      |  ,'      O=𝛑/2      `.     MeanDown
//	      | /        Peak         \   /
//	      |/                       \ /
//	Mean -+-------------------------\--------------------------> t
//	      |\                         \                       /
//	      | \                         \       O=3𝛑/2        /
//	      |  O=0                       `.     Trough      ,'
//	      |  MeanUp                      `.      |      ,'
//	Mean  |                                `-.   |   ,-'
//	-Amp -|                                   `-,,,-'
//	      |<-------------------- Period --------------------->|
//
// This equation is integrated with respect to time to derive the expected
// number of hits served at time t after the attack began:
//
//	H = Mt - (AP/2𝛑)cos(O+(2𝛑/P)t) + (AP/2𝛑)cos(O)
//
// Where:
//
//	H = Total number of hits triggered during t
type SinePacer struct {
	// The period of the sine wave, e.g. 20*time.Minute
	// MUST BE > 0
	Period time.Duration
	// The mid-point of the sine wave in freq-per-Duration,
	// MUST BE > 0
	Mean Rate
	// The amplitude of the sine wave in freq-per-Duration,
	// MUST NOT BE EQUAL TO OR LARGER THAN MEAN
	Amp Rate
	// The offset, in radians, for the sine wave at t=0.
	StartAt float64
}

// SinePacer satisfies the Pacer interface.
var _ Pacer = SinePacer{}

// String returns a pretty-printed description of the SinePacer's behaviour:
//
//	SinePacer{
//	    Period:  time.Hour,
//	    Mean:    Rate{100, time.Second},
//	    Amp:     Rate{50, time.Second},
//	    StartAt: MeanDown,
//	} =>
//	Sine{Constant{100 hits/1s} ± Constant{50 hits/1s} / 1h, offset 1𝛑}
func (sp SinePacer) String() string {
	return fmt.Sprintf("Sine{%s ± %s / %s, offset %g𝛑}", sp.Mean, sp.Amp, sp.Period, sp.StartAt/math.Pi)
}

// invalid tests the constraints documented in the SinePacer struct definition.
func (sp SinePacer) invalid() bool {
	return sp.Period <= 0 || sp.Mean.hitsPerNs() <= 0 || sp.Amp.hitsPerNs() >= sp.Mean.hitsPerNs()
}

// Pace determines the length of time to sleep until the next hit is sent.
func (sp SinePacer) Pace(elapsedTime time.Duration, elapsedHits uint64) (time.Duration, bool) {
	if sp.invalid() {
		// If the SinePacer configuration is invalid, stop the attack.
		return 0, true
	}
	expectedHits := sp.hits(elapsedTime)
	if elapsedHits < uint64(expectedHits) {
		// Running behind, send next hit immediately.
		return 0, false
	}
	// Re-arranging our hits equation to provide a duration given the number of
	// requests sent is non-trivial, so we must solve for the duration numerically.
	// math.Round() added here because we have to coerce to int64 nanoseconds
	// at some point and it corrects a bunch of off-by-one problems.
	nsPerHit := math.Round(1 / sp.hitsPerNs(elapsedTime))
	hitsToWait := float64(elapsedHits+1) - expectedHits
	nextHitIn := time.Duration(nsPerHit * hitsToWait)

	// If we can't converge to an error of <1e-3 within 5 iterations, bail.
	// This rarely even loops for any large Period if hitsToWait is small.
	for i := 0; i < 5; i++ {
		hitsAtGuess := sp.hits(elapsedTime + nextHitIn)
		err := float64(elapsedHits+1) - hitsAtGuess
		if math.Abs(err) < 1e-3 {
			return nextHitIn, false
		}
		nextHitIn = time.Duration(float64(nextHitIn) / (hitsAtGuess - float64(elapsedHits)))
	}
	return nextHitIn, false
}

// Rate returns a SinePacer's instantaneous hit rate (i.e. requests per second)
// at the given elapsed duration of an attack.
func (sp SinePacer) Rate(elapsed time.Duration) float64 {
	return sp.hitsPerNs(elapsed) * 1e9
}

// ampHits returns AP/2𝛑, which is the number of hits added or subtracted
// from the Mean due to the Amplitude over a quarter of the Period,
// i.e. from 0 → 𝛑/2 radians
func (sp SinePacer) ampHits() float64 {
	return (sp.Amp.hitsPerNs() * float64(sp.Period)) / (2 * math.Pi)
}

// radians converts the elapsed attack time to a radian value.
// The elapsed time t is divided by the wave period, multiplied by 2𝛑 to
// convert to radians, and offset by StartAt radians.
func (sp SinePacer) radians(t time.Duration) float64 {
	return sp.StartAt + float64(t)*2*math.Pi/float64(sp.Period)
}

// hitsPerNs calculates the instantaneous rate of attack at
// t nanoseconds after the attack began.
//
//	R = MA sin(O+(2𝛑/P)t)
func (sp SinePacer) hitsPerNs(t time.Duration) float64 {
	return sp.Mean.hitsPerNs() + sp.Amp.hitsPerNs()*math.Sin(sp.radians(t))
}

// hits returns the number of hits that have been sent during an attack
// lasting t nanoseconds. It returns a float so we can tell exactly how
// much we've missed our target by when solving numerically in Pace.
//
//	H = Mt - (AP/2𝛑)cos(O+(2𝛑/P)t) + (AP/2𝛑)cos(O)
//
// This re-arranges to:
//
//	H = Mt + (AP/2𝛑)(cos(O) - cos(O+(2𝛑/P)t))
func (sp SinePacer) hits(t time.Duration) float64 {
	if t <= 0 || sp.invalid() {
		return 0
	}
	return sp.Mean.hitsPerNs()*float64(t) + sp.ampHits()*(math.Cos(sp.StartAt)-math.Cos(sp.radians(t)))
}

// LinearPacer paces an attack by starting at a given request rate
// and increasing linearly with the given slope.
type LinearPacer struct {
	StartAt Rate
	Slope   float64
}

// Pace determines the length of time to sleep until the next hit is sent.
func (p LinearPacer) Pace(elapsed time.Duration, hits uint64) (time.Duration, bool) {
	switch {
	case p.StartAt.Per == 0 || p.StartAt.Freq == 0:
		return 0, false // Zero value = infinite rate
	case p.StartAt.Per < 0 || p.StartAt.Freq < 0:
		return 0, true
	}

	expectedHits := p.hits(elapsed)
	if hits == 0 || hits < uint64(expectedHits) {
		// Running behind, send next hit immediately.
		return 0, false
	}

	rate := p.Rate(elapsed)
	interval := math.Round(1e9 / rate)

	if n := uint64(interval); n != 0 && math.MaxInt64/n < hits {
		// We would overflow wait if we continued, so stop the attack.
		return 0, true
	}

	delta := float64(hits+1) - expectedHits
	wait := time.Duration(interval * delta)

	return wait, false
}

// Rate returns a LinearPacer's instantaneous hit rate (i.e. requests per second)
// at the given elapsed duration of an attack.
func (p LinearPacer) Rate(elapsed time.Duration) float64 {
	a := p.Slope
	x := elapsed.Seconds()
	b := p.StartAt.hitsPerNs() * 1e9
	return a*x + b
}

// hits returns the number of hits that have been sent during an attack
// lasting t nanoseconds. It returns a float so we can tell exactly how
// much we've missed our target by when solving numerically in Pace.
func (p LinearPacer) hits(t time.Duration) float64 {
	if t < 0 {
		return 0
	}

	a := p.Slope
	b := p.StartAt.hitsPerNs() * 1e9
	x := t.Seconds()

	return (a*math.Pow(x, 2))/2 + b*x
}

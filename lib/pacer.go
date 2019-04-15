package vegeta

import (
	"fmt"
	"math"
	"time"
)

// A Pacer defines the rate of hits during an Attack by
// returning the duration an Attacker should wait until hitting
// the next Target. If the second return value is true, the
// attack will terminate.
type Pacer interface {
	Pace(elapsedTime time.Duration, elapsedHits uint64) (sleep time.Duration, stop bool)
}

// A PacerFunc is a function adapter type that implements the
// Pacer interface.
type PacerFunc func(time.Duration, uint64) (time.Duration, bool)

// Pace implements the Pacer interface.
func (f PacerFunc) Pace(elapsedTime time.Duration, elapsedHits uint64) (time.Duration, bool) {
	return f(elapsedTime, elapsedHits)
}

// Rate sends a constant rate of hits to the target.
type Rate struct {
	Freq int           // Frequency (number of occurrences) per ...
	Per  time.Duration // Time unit, usually 1s
}

// Pace determines the length of time to sleep until the next hit is sent.
func (r Rate) Pace(elapsedTime time.Duration, elapsedHits uint64) (time.Duration, bool) {
	if r.Per <= 0 || r.Freq <= 0 {
		// If Rate configuration is invalid, stop the attack.
		return 0, true
	}
	interval := uint64(r.Per.Nanoseconds() / int64(r.Freq))
	delta := time.Duration((elapsedHits + 1) * interval)
	// Zero or negative durations cause time.Sleep to return immediately.
	return delta - elapsedTime, false
}

// String returns a pretty-printed description of the rate, e.g.:
//   Rate{1 hits/1s} for Rate{Freq:1, Per: time.Second}
func (r Rate) String() string {
	return fmt.Sprintf("Rate{%d hits/%s}", r.Freq, r.Per)
}

func (r Rate) HitsPerNs() float64 {
	return float64(r.Freq) / float64(r.Per)
}

var _ Pacer = Rate{}

const (
	MeanUp   float64 = 0
	Peak             = math.Pi / 2
	MeanDown         = math.Pi
	Trough           = 3 * math.Pi / 2
)

// SinePacer is a Pacer that describes attack request rates with the equation:
//     R = MA sin(O+(2𝛑/P)t)
// Where:
//   R = Instantaneous attack rate at elapsed time t, hits per nanosecond
//   M = Mean attack rate over period P, sp.Mean, hits per nanosecond
//   A = Amplitude of sine wave, sp.Amp, hits per nanosecond
//   O = Offset of sine wave, sp.StartAt, radians
//   P = Period of sine wave, sp.Period, nanoseconds
//   t = Elapsed time since attack, nanoseconds
// The attack rate (sp.HitsPerNs) is described by the equation:
//
// This equation is integrated with respect to time to derive the expected
// number of hits served at time t after the attack began:
//     H = Mt - (AP/2𝛑)cos(O+(2𝛑/P)t) + (AP/2𝛑)cos(O)
// Where:
//   H = Total number of hits triggered during t
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

var _ Pacer = SinePacer{}

func (sp SinePacer) String() string {
	return fmt.Sprintf("Sine{%s ± %s / %s, offset %g𝛑}", sp.Mean, sp.Amp, sp.Period, sp.StartAt/math.Pi)
}

// Pace returns the Duration until the next hit should be sent,
// based on when the attack began and how many hits have been sent thus far.
func (sp SinePacer) Pace(elapsedTime time.Duration, elapsedHits uint64) (time.Duration, bool) {
	if sp.Period <= 0 || sp.Mean.HitsPerNs() <= 0 || sp.Amp.HitsPerNs() >= sp.Mean.HitsPerNs() {
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
	nsPerHit := math.Round(1 / sp.HitsPerNs(elapsedTime))
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

// AmpHits returns AP/2𝛑, which is the number of hits added or subtracted
// from the Mean due to the Amplitude over a quarter of the Period,
// i.e. from 0 → 𝛑/2 radians
func (sp SinePacer) AmpHits() float64 {
	return (sp.Amp.HitsPerNs() * float64(sp.Period)) / (2 * math.Pi)
}

// radians converts the elapsed attack time to a radian value.
// The elapsed time t is divided by the wave period, multiplied by 2𝛑 to
// convert to radians, and offset by StartAt radians.
func (sp SinePacer) Radians(t time.Duration) float64 {
	return sp.StartAt + float64(t)*2*math.Pi/float64(sp.Period)
}

// HitsPerNs calculates the instantaneous rate of attack at
// t nanoseconds after the attack began.
//     R = MA sin(O+(2𝛑/P)t)
func (sp SinePacer) HitsPerNs(t time.Duration) float64 {
	return sp.Mean.HitsPerNs() + sp.Amp.HitsPerNs()*math.Sin(sp.Radians(t))
}

// hits is an internal version of Hits that returns a float64, so we can tell
// exactly how much we've missed our target by when solving numerically.
//     H = Mt - (AP/2𝛑)cos(O+(2𝛑/P)t) + (AP/2𝛑)cos(O)
// This re-arranges to:
//     H = Mt + (AP/2𝛑)(cos(O) - cos(O+(2𝛑/P)t))
func (sp SinePacer) hits(t time.Duration) float64 {
	return sp.Mean.HitsPerNs()*float64(t) + sp.AmpHits()*(math.Cos(sp.StartAt)-math.Cos(sp.Radians(t)))
}

// Hits returns the number of requests that have been sent during an attack
// lasting t nanoseconds.
//     H = Mt - (AP/2𝛑)cos(O+(2𝛑/P)t) + (AP/2𝛑)cos(O)
func (sp SinePacer) Hits(t time.Duration) uint64 {
	if t == 0 || sp.Period <= 0 || sp.Mean.HitsPerNs() <= 0 || sp.Amp.HitsPerNs() >= sp.Mean.HitsPerNs() {
		return 0
	}
	return uint64(math.Round(sp.hits(t)))
}

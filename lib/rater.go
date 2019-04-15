package vegeta

import (
	"fmt"
	"math"
	"time"
)

// A Rater defines the rate of hits during an Attack by
// returning the duration an Attacker should wait until hiting
// the next Target. When a negative value time is returned,
// an Attacker will stop.
type Rater interface {
	Wait(began, now time.Time) time.Duration
}

// A RaterFunc is a function adapter type that implements the
// Rater interface.
type RaterFunc func(began, now time.Time) time.Duration

// Wait implements the Rater interface.
func (f RaterFunc) Wait(began, now time.Time) time.Duration {
	return f(began, now)
}

// A FixedRater is a Rater that produces hits at a fixed rate
// for a given duration. It is not safe for concurrent use.
type FixedRater struct {
	rate  Rate
	hits  uint64
	count uint64
}

// NewFixedRater returns a new FixedRater with the given Rate and duration.
// When duration is zero, the rater will never stop.
func NewFixedRater(rate Rate, du time.Duration) *FixedRater {
	r := FixedRater{rate: rate}
	if du != 0 && !rate.IsZero() {
		r.hits = uint64(du) /
			(uint64(rate.Per.Nanoseconds() / int64(rate.Freq)))
	}
	return &r
}

// Wait is an utility method that calls the rater function itself.
// It's meant to aid readability.
func (r *FixedRater) Wait(began, now time.Time) time.Duration {
	if r.hits != 0 && r.count == r.hits {
		return -1
	}

	r.count++
	interval := uint64(r.rate.Per.Nanoseconds() / int64(r.rate.Freq))
	delta := time.Duration(r.count * interval)

	if wait := began.Add(delta).Sub(now); wait > 0 {
		return wait
	}

	return 0
}

// Rate sends a constant rate of hits to the target.
type Rate struct {
	Freq int           // Frequency (number of occurrences) per ...
	Per  time.Duration // Time unit, usually 1s
}

// IsZero returns true if either Freq or Per are zero valued.
func (r Rate) IsZero() bool {
	return r.Freq == 0 || r.Per == 0
}

// String returns a pretty-printed description of the rate, e.g.:
//   Rate{1 hits/1s} for Rate{Freq:1, Per: time.Second}
func (r Rate) String() string {
	return fmt.Sprintf("Rate{%d hits/%s}", r.Freq, r.Per)
}

const (
	MeanUp   float64 = 0
	Peak             = math.Pi / 2
	MeanDown         = math.Pi
	Trough           = 3 * math.Pi / 2
)

// SineRate is a vegeta.Rater that describes attack request rates
// with the equation:
//     R = MA sin(O+(2𝛑/P)t)
// Where:
//   R = Instantaneous attack rate at elapsed time t, hits per nanosecond
//   M = Mean attack rate over period P, sr.Mean, hits per nanosecond
//   A = Amplitude of sine wave, sr.Amp, hits per nanosecond
//   O = Offset of sine wave, sr.StartAt, radians
//   P = Period of sine wave, sr.Period, nanoseconds
//   t = Elapsed time since attack, nanoseconds
// The attack rate (sr.HitsPerNs) is described by the equation:
//
// This equation is integrated with respect to time to derive the expected
// number of hits served at time t after the attack began:
//     H = Mt - (AP/2𝛑)cos(O+(2𝛑/P)t) + (AP/2𝛑)cos(O)
// Where:
//   H = Total number of hits triggered during t
//
// SineRate is not safe for concurrent use.
type SineRate struct {
	// How long the attack should run for, 0 == infinite.
	For time.Duration
	// The period of the sine wave, e.g. 20*time.Minute
	// MUST BE > 0
	Period time.Duration
	// The mid-point of the sine wave in freq-per-Duration,
	// e.g. 100/float64(time.Second) for 100 QPS
	// MUST BE > 0
	Mean float64
	// The amplitude of the sine wave in freq-per-Duration,
	// e.g. 90/float64(time.Second) for ±90 QPS
	// MUST NOT BE EQUAL TO OR LARGER THAN MEAN
	Amp float64
	// The offset, in radians, for the sine wave at t=0.
	StartAt float64
	// count of hits since attack began.
	count uint64
}

var _ Rater = (*SineRate)(nil)

// Wait returns the Duration until the next hit should be sent,
// based on when the attack began and how many hits have been sent thus far.
func (sr *SineRate) Wait(began time.Time, _ time.Time) time.Duration {
	return sr.wait(time.Since(began))
}

// Wait returns the Duration until the next hit should be sent,
// based on when the attack began and how many hits have been sent thus far.
func (sr *SineRate) wait(elapsedTime time.Duration) time.Duration {
	if sr.For > 0 && elapsedTime > sr.For {
		return -1
	}
	expectedHits := sr.hits(elapsedTime)
	if sr.count < uint64(expectedHits) {
		// Running behind, send next hit immediately.
		return 0
	}
	// Re-arranging our hits equation to provide a duration given the number of
	// requests sent is non-trivial, so we must solve for the duration numerically.
	// math.Round() added here because we have to coerce to int64 nanoseconds
	// at some point and it corrects a bunch of off-by-one problems.
	sr.count++
	nsPerHit := math.Round(1 / sr.HitsPerNs(elapsedTime))
	hitsToWait := float64(sr.count) - expectedHits
	nextHitIn := time.Duration(nsPerHit * hitsToWait)

	// If we can't converge to an error of <1e-3 within 5 iterations, bail.
	// This rarely even loops for any large Period if hitsToWait is small.
	for i := 0; i < 5; i++ {
		hitsAtGuess := sr.hits(elapsedTime + nextHitIn)
		err := float64(sr.count) - hitsAtGuess
		if math.Abs(err) < 1e-3 {
			return nextHitIn
		}
		nextHitIn = time.Duration(float64(nextHitIn) / (hitsAtGuess - float64(sr.count-1)))
	}
	return nextHitIn
}

// AmpHits returns AP/2𝛑, which is the number of hits added or subtracted
// from the Mean due to the Amplitude over a quarter of the Period,
// i.e. from 0 → 𝛑/2 radians
func (sr *SineRate) AmpHits() float64 {
	return (sr.Amp * float64(sr.Period)) / (2 * math.Pi)
}

// radians converts the elapsed attack time to a radian value.
// The elapsed time t is divided by the wave period, multiplied by 2𝛑 to
// convert to radians, and offset by StartAt radians.
func (sr *SineRate) Radians(t time.Duration) float64 {
	return sr.StartAt + float64(t)*2*math.Pi/float64(sr.Period)
}

// HitsPerNs calculates the instantaneous rate of attack at
// t nanoseconds after the attack began.
//     R = MA sin(O+(2𝛑/P)t)
func (sr *SineRate) HitsPerNs(t time.Duration) float64 {
	return sr.Mean + sr.Amp*math.Sin(sr.Radians(t))
}

// hits is an internal version of Hits that returns a float64, so we can tell
// exactly how much we've missed our target by when solving numerically.
//     H = Mt - (AP/2𝛑)cos(O+(2𝛑/P)t) + (AP/2𝛑)cos(O)
// This re-arranges to:
//     H = Mt + (AP/2𝛑)(cos(O) - cos(O+(2𝛑/P)t))
func (sr SineRate) hits(t time.Duration) float64 {
	return sr.Mean*float64(t) + sr.AmpHits()*(math.Cos(sr.StartAt)-math.Cos(sr.Radians(t)))
}

// Hits returns the number of requests that have been sent during an attack
// lasting t nanoseconds.
//     H = Mt - (AP/2𝛑)cos(O+(2𝛑/P)t) + (AP/2𝛑)cos(O)
func (sr *SineRate) Hits(t time.Duration) uint64 {
	if t == 0 || sr.Period <= 0 || sr.Mean <= 0 || sr.Amp >= sr.Mean {
		return 0
	}
	return uint64(math.Round(sr.hits(t)))
}

package vegeta

import (
	"math/rand"
	"strconv"
	"strings"
	"time"
)

// URLInterpolator interface, it must implement InterpolateURL that
// should resolve the interpolation for the URL
type URLInterpolator interface {
	InterpolateURL(string) string
}

// BodyInterpolator interface, it must implement InterpolateBody that
// should resolve the desired Body interpolation
type BodyInterpolator interface {
	InterpolateBody([]byte) []byte
}

// Simple random numeric Interpolation, it will randomize the specified Key
// using the given Limit
type RandomNumericInterpolation struct {
	Key   string
	Limit int
	Rand  *rand.Rand
}

// RandomNumeric Request URL interpolation implementation
func (interpolator *RandomNumericInterpolation) InterpolateURL(url string) string {
	return interpolator.interpolatorReplace(url)
}

// RandomNumeric Request Body interpolation implementation
func (interpolator *RandomNumericInterpolation) InterpolateBody(body []byte) []byte {
	return []byte(interpolator.interpolatorReplace(string(body)))
}

// RandomNumeric generic Interpolator resolver
func (interpolator *RandomNumericInterpolation) interpolatorReplace(content string) string {
	if interpolator.Rand == nil {
		interpolator.Rand = rand.New(rand.NewSource(time.Now().UTC().Unix()))
	}

	return strings.Replace(content, interpolator.Key, strconv.Itoa(interpolator.Rand.Intn(interpolator.Limit)), -1)
}

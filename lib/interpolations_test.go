package vegeta

import (
	"bytes"
	"math/rand"
	"testing"
)

func TestInterpolatorReplace(t *testing.T) {
	interpolation := RandomNumericInterpolation{
		Key:   "{foo}",
		Limit: int(^uint(0) >> 1),
		Rand:  rand.New(rand.NewSource(1435875839)),
	}

	var stringTests = []struct {
		Input  string
		Output string
	}{
		{"https://foo.bar.com/api/{foo}/1", "https://foo.bar.com/api/2290778204292519845/1"},
		{"https://foo.bar.com/api/{foo}/bar/{foo}", "https://foo.bar.com/api/9195823874823970824/bar/9195823874823970824"},
	}

	for _, stringTest := range stringTests {
		if interpolation.interpolatorReplace(stringTest.Input) != stringTest.Output {
			t.Error("The interpolation was not resolved sucessfully")
		}
	}
}

func TestInterpolateURL(t *testing.T) {
	interpolation := RandomNumericInterpolation{
		Key:   "{foo}",
		Limit: int(^uint(0) >> 1),
		Rand:  rand.New(rand.NewSource(1435875839)),
	}

	var urlTests = []struct {
		Input  string
		Output string
	}{
		{"https://foo.bar.com/api/{foo}/1", "https://foo.bar.com/api/2290778204292519845/1"},
		{"https://foo.bar.com/api/{foo}/bar/{foo}", "https://foo.bar.com/api/9195823874823970824/bar/9195823874823970824"},
	}

	for _, urlTest := range urlTests {
		if interpolation.InterpolateURL(urlTest.Input) != urlTest.Output {
			t.Error("The URL interpolation was not resolved sucessfully")
		}
	}
}

func TestInterpolateBody(t *testing.T) {
	interpolation := RandomNumericInterpolation{
		Key:   "{foo}",
		Limit: int(^uint(0) >> 1),
		Rand:  rand.New(rand.NewSource(1435875839)),
	}

	var bodyTests = []struct {
		Input  []byte
		Output []byte
	}{
		{[]byte(`{"id": "{foo}", "value": "bar"}`), []byte(`{"id": "2290778204292519845", "value": "bar"}`)},
		{[]byte(`{"id": "{foo}", "value": "{foo}"}`), []byte(`{"id": "9195823874823970824", "value": "9195823874823970824"}`)},
	}

	for _, bodyTest := range bodyTests {
		if !bytes.Equal(interpolation.InterpolateBody(bodyTest.Input), bodyTest.Output) {
			t.Error("The Body interpolation was not resolved sucessfully")
		}
	}
}

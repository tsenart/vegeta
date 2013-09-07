package main

import (
	"io/ioutil"
	"log"
	"strings"
	"testing"
	"time"
)

func init() {
	// Discard default log output
	log.SetOutput(ioutil.Discard)
}

func TestRateValidation(t *testing.T) {
	rate, duration, targetsf, ordering, reporter, output := defaultArguments()
	rate = 0

	err := run(rate, duration, targetsf, ordering, reporter, output)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errRatePrefix)) {
		t.Errorf("Rate 0 shouldn't be valid: %s", err)
	}
}

func TestDurationValidation(t *testing.T) {
	rate, duration, targetsf, ordering, reporter, output := defaultArguments()
	duration = 0

	err := run(rate, duration, targetsf, ordering, reporter, output)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errDurationPrefix)) {
		t.Errorf("Duration 0 shouldn't be valid: %s", err)
	}
}

func TestOutputValidation(t *testing.T) {
	rate, duration, targetsf, ordering, reporter, _ := defaultArguments()

	// Good cases
	for _, output := range []string{"stdout", "/dev/null"} {
		err := run(rate, duration, targetsf, ordering, reporter, output)
		if err != nil {
			t.Errorf("Output file `%s` should be valid: %s", output, err)
		}
	}

	// Bad case
	badOutput := ""
	err := run(rate, duration, targetsf, ordering, reporter, badOutput)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errOutputFilePrefix)) {
		t.Errorf("Output file `%s` shouldn't be valid: %s", badOutput, err)
	}
}

func TestReporter(t *testing.T) {
	rate, duration, targetsf, ordering, reporter, output := defaultArguments()

	err := run(rate, duration, targetsf, ordering, reporter, output)
	if err != nil {
		t.Errorf("Reporter shouldn't return an error: %s", err)
	}
}

func TestTargetsValidation(t *testing.T) {
	rate, duration, goodFile, ordering, reporter, output := defaultArguments()

	// Good case
	err := run(rate, duration, goodFile, ordering, reporter, output)
	if err != nil {
		t.Errorf("Targets file `%s` should be valid: %s", goodFile, err)
	}

	// Bad case
	badFile := "randomInexistingFile12345.txt"
	err = run(rate, duration, badFile, ordering, reporter, output)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errTargetsFilePrefix)) {
		t.Errorf("Targets file `%s` shouldn't be valid: %s", badFile, err)
	}
}

func TestOrderingValidation(t *testing.T) {
	rate, duration, targetsf, _, reporter, output := defaultArguments()

	// Good cases
	for _, ordering := range []string{"random", "sequential"} {
		err := run(rate, duration, targetsf, ordering, reporter, output)
		if err != nil {
			t.Errorf("Ordering `%s` should be valid: %s", ordering, err)
		}
	}

	// Bad case
	badOrdering := "lolcat"
	err := run(rate, duration, targetsf, badOrdering, reporter, output)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errOrderingPrefix)) {
		t.Errorf("Ordering `%s` shouldn't be valid: %s", badOrdering, err)
	}
}

func defaultArguments() (uint64, time.Duration, string, string, string, string) {
	return uint64(1000), 5 * time.Millisecond, ".targets.txt", "random", "text", "/dev/null"
}

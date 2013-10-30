package main

import (
	"flag"
	"io/ioutil"
	"log"
	"net/http"
	"strings"
	"testing"
	"time"
	"os"
)

func init() {
	// Discard default log output
	log.SetOutput(ioutil.Discard)
}

func TestRateValidation(t *testing.T) {
	rate, duration, targetsf, ordering, output, header := defaultArguments()
	rate = 0

	err := attack(rate, duration, targetsf, ordering, output, header)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errRatePrefix)) {
		t.Errorf("Rate 0 shouldn't be valid: %s", err)
	}
}

func TestDurationValidation(t *testing.T) {
	rate, duration, targetsf, ordering, output, header := defaultArguments()
	duration = 0

	err := attack(rate, duration, targetsf, ordering, output, header)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errDurationPrefix)) {
		t.Errorf("Duration 0 shouldn't be valid: %s", err)
	}
}

func TestTargetsValidation(t *testing.T) {
	rate, duration, goodFile, ordering, output, header := defaultArguments()

	// Good case
	err := attack(rate, duration, goodFile, ordering, output, header)
	if err != nil {
		t.Errorf("Targets file `%s` should be valid: %s", goodFile, err)
	}

	// Bad case
	badFile := "randomInexistingFile12345.txt"
	err = attack(rate, duration, badFile, ordering, output, header)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errTargetsFilePrefix)) {
		t.Errorf("Targets file `%s` shouldn't be valid: %s", badFile, err)
	}
}

func TestOrderingValidation(t *testing.T) {
	rate, duration, targetsf, _, output, header := defaultArguments()

	// Good cases
	for _, ordering := range []string{"random", "sequential"} {
		err := attack(rate, duration, targetsf, ordering, output, header)
		if err != nil {
			t.Errorf("Ordering `%s` should be valid: %s", ordering, err)
		}
	}

	// Bad case
	badOrdering := "lolcat"
	err := attack(rate, duration, targetsf, badOrdering, output, header)
	if err == nil || (err != nil && !strings.HasPrefix(err.Error(), errOrderingPrefix)) {
		t.Errorf("Ordering `%s` shouldn't be valid: %s", badOrdering, err)
	}
}

func TestHeadersParsing(t *testing.T) {
	fs := flag.NewFlagSet("test", flag.ContinueOnError)
	fs.SetOutput(ioutil.Discard)
	hdrs := headers{Header: make(http.Header)}
	fs.Var(hdrs, "H", "Header")
	// Good case
	good := []string{"-H", "Host: lolcathost"}
	if err := fs.Parse(good); err != nil {
		t.Errorf("%v should be a valid header", good[1])
	}
	// Bad cases
	bad := [][]string{[]string{"-H", "Host:"}, []string{"-H", "Host"}}
	for _, args := range bad {
		if err := fs.Parse(args); err == nil {
			t.Errorf("%v should not be a valid header", args[1])
		}
	}
}

func defaultArguments() (uint64, time.Duration, string, string, string, http.Header) {
	return uint64(1000),
		5 * time.Millisecond,
		".targets.txt",
		"random",
		os.DevNull,
		http.Header{}
}

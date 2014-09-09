package main

import (
	"flag"
	"io/ioutil"
	"log"
	"net/http"
	"os"
	"testing"
	"time"

	"github.com/tsenart/vegeta/lib"
)

func init() {
	// Discard default log output
	log.SetOutput(ioutil.Discard)
}

func TestRateValidation(t *testing.T) {
	t.Parallel()

	opts := defaultOpts()
	opts.rate = 0

	if err := attack(opts); err != errZeroRate {
		t.Errorf("Rate 0 shouldn't be valid: %s", err)
	}
}

func TestDurationValidation(t *testing.T) {
	t.Parallel()

	opts := defaultOpts()
	opts.duration = 0

	if err := attack(opts); err != errZeroDuration {
		t.Errorf("Duration 0 shouldn't be valid: %s", err)
	}
}

func TestTargetsValidation(t *testing.T) {
	t.Parallel()

	opts := defaultOpts()

	// Good case
	err := attack(opts)
	if err != nil {
		t.Errorf("Targets file `%s` should be valid: %s", opts.targetsf, err)
	}

	// Bad case
	opts.targetsf = "randomInexistingFile12345.txt"
	err = attack(opts)
	if err == nil {
		t.Errorf("Targets file `%s` shouldn't be valid: %s", opts.targetsf, err)
	}
}

func TestBodyValidation(t *testing.T) {
	t.Parallel()

	opts := defaultOpts()

	// Good case
	err := attack(opts)
	if err != nil {
		t.Errorf("Body file `%s` should be valid: %s", opts.bodyf, err)
	}

	// Bad case
	opts.bodyf = "randomInexistingFile12345.txt"
	err = attack(opts)
	if err == nil {
		t.Errorf("Body file `%s` shouldn't be valid: %s", opts.bodyf, err)
	}
}

func TestOrderingValidation(t *testing.T) {
	t.Parallel()

	opts := defaultOpts()

	// Good cases
	for _, ordering := range []string{"random", "sequential"} {
		opts.ordering = ordering
		err := attack(opts)
		if err != nil {
			t.Errorf("Ordering `%s` should be valid: %s", ordering, err)
		}
	}

	// Bad case
	opts.ordering = "lolcat"
	if err := attack(opts); err != errBadOrdering {
		t.Errorf("Ordering `%s` shouldn't be valid: %s", opts.ordering, err)
	}
}

func TestHeadersParsing(t *testing.T) {
	t.Parallel()

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

func TestClientCert(t *testing.T) {
	t.Parallel()

	opts := defaultOpts()

	// Good cases
	opts.certf = "./test/cert.pem"
	if err := attack(opts); err != nil {
		t.Errorf("Cert `%s` should be valid: %s", opts.certf, err)
	}

	// Bad case
	opts.certf = "./test/badcert.pem"
	if err := attack(opts); err != errBadCert {
		t.Errorf("Cert `%s` shouldn't be valid: %s", opts.certf, err)
	}
}

func defaultOpts() *attackOpts {
	return &attackOpts{
		rate:      uint64(1000),
		duration:  5 * time.Millisecond,
		targetsf:  "./test/targets.txt",
		bodyf:     "./test/body.txt",
		certf:     "",
		ordering:  "random",
		outputf:   os.DevNull,
		redirects: 10,
		timeout:   0,
		headers:   headers{},
		laddr:     localAddr{&vegeta.DefaultLocalAddr},
	}
}

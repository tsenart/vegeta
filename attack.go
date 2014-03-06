package main

import (
	"bytes"
	"flag"
	"fmt"
	"log"
	"net/http"
	"strings"
	"time"

	vegeta "github.com/tsenart/vegeta/lib"
)

func attackCmd(args []string) command {
	return func() error {
		fs := flag.NewFlagSet("vegeta attack", flag.ContinueOnError)
		opts := &attackOpts{headers: headers{http.Header{}}}

		fs.StringVar(&opts.targetsf, "targets", "stdin", "Targets file")
		fs.StringVar(&opts.outputf, "output", "stdout", "Output file")
		fs.StringVar(&opts.ordering, "ordering", "random", "Attack ordering [sequential, random]")
		fs.DurationVar(&opts.duration, "duration", 10*time.Second, "Duration of the test")
		fs.DurationVar(&opts.timeout, "timeout", 0, "Requests timeout")
		fs.Uint64Var(&opts.rate, "rate", 50, "Requests per second")
		fs.IntVar(&opts.redirects, "redirects", 10, "Number of redirects to follow")
		fs.Var(&opts.headers, "header", "Targets request header")

		if err := fs.Parse(args); err != nil {
			return err
		}

		return attack(opts)
	}
}

// attackOpts aggregates the attack function command options
type attackOpts struct {
	targetsf  string
	outputf   string
	ordering  string
	duration  time.Duration
	timeout   time.Duration
	rate      uint64
	redirects int
	headers   headers
}

// attack validates the attack arguments, sets up the
// required resources, launches the attack and writes the results
func attack(opts *attackOpts) error {
	if opts.rate == 0 {
		return fmt.Errorf(errRatePrefix + "can't be zero")
	}

	if opts.duration == 0 {
		return fmt.Errorf(errDurationPrefix + "can't be zero")
	}

	in, err := file(opts.targetsf, false)
	if err != nil {
		return fmt.Errorf(errTargetsFilePrefix+"(%s): %s", opts.targetsf, err)
	}
	defer in.Close()

	targets, err := vegeta.NewTargetsFrom(in)
	if err != nil {
		return fmt.Errorf(errTargetsFilePrefix+"(%s): %s", opts.targetsf, err)
	}
	targets.SetHeader(opts.headers.Header)

	switch opts.ordering {
	case "random":
		targets.Shuffle(time.Now().UnixNano())
	case "sequential":
		break
	default:
		return fmt.Errorf(errOrderingPrefix+"`%s` is invalid", opts.ordering)
	}

	out, err := file(opts.outputf, true)
	if err != nil {
		return fmt.Errorf(errOutputFilePrefix+"(%s): %s", opts.outputf, err)
	}
	defer out.Close()

	vegeta.DefaultAttacker.SetRedirects(opts.redirects)

	if opts.timeout > 0 {
		vegeta.DefaultAttacker.SetTimeout(opts.timeout)
	}

	log.Printf(
		"Vegeta is attacking %d targets in %s order for %s...\n",
		len(targets),
		opts.ordering,
		opts.duration,
	)
	results := vegeta.Attack(targets, opts.rate, opts.duration)

	log.Printf("Done! Writing results to '%s'...", opts.outputf)
	return results.Encode(out)
}

const (
	errRatePrefix        = "Rate: "
	errDurationPrefix    = "Duration: "
	errOutputFilePrefix  = "Output file: "
	errTargetsFilePrefix = "Targets file: "
	errOrderingPrefix    = "Ordering: "
	errReportingPrefix   = "Reporting: "
)

// headers is the http.Header used in each target request
// it is defined here to implement the flag.Value interface
// in order to support multiple identical flags for request header
// specification
type headers struct{ http.Header }

func (h headers) String() string {
	buf := &bytes.Buffer{}
	if err := h.Write(buf); err != nil {
		return ""
	}
	return buf.String()
}

func (h headers) Set(value string) error {
	parts := strings.Split(value, ":")
	if len(parts) != 2 {
		return fmt.Errorf("Header '%s' has a wrong format", value)
	}
	key, val := strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1])
	if key == "" || val == "" {
		return fmt.Errorf("Header '%s' has a wrong format", value)
	}
	h.Add(key, val)
	return nil
}

package main

import (
	"bytes"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"net"
	"net/http"
	"strings"
	"time"

	vegeta "github.com/tsenart/vegeta/lib"
)

func attackCmd() command {
	fs := flag.NewFlagSet("vegeta attack", flag.ExitOnError)
	opts := &attackOpts{
		headers: headers{http.Header{}},
		laddr:   localAddr{&vegeta.DefaultLocalAddr},
	}

	fs.StringVar(&opts.targetsf, "targets", "stdin", "Targets file")
	fs.StringVar(&opts.outputf, "output", "stdout", "Output file")
	fs.StringVar(&opts.bodyf, "body", "", "Requests body file")
	fs.StringVar(&opts.ordering, "ordering", "random", "Attack ordering [sequential, random]")
	fs.DurationVar(&opts.duration, "duration", 10*time.Second, "Duration of the test")
	fs.DurationVar(&opts.timeout, "timeout", vegeta.DefaultTimeout, "Requests timeout")
	fs.Uint64Var(&opts.rate, "rate", 50, "Requests per second")
	fs.IntVar(&opts.redirects, "redirects", vegeta.DefaultRedirects, "Number of redirects to follow")
	fs.Var(&opts.headers, "header", "Request header")
	fs.Var(&opts.laddr, "laddr", "Local IP address")

	return command{fs, func(args []string) error {
		fs.Parse(args)
		return attack(opts)
	}}
}

// attackOpts aggregates the attack function command options
type attackOpts struct {
	targetsf  string
	outputf   string
	bodyf     string
	ordering  string
	duration  time.Duration
	timeout   time.Duration
	rate      uint64
	redirects int
	headers   headers
	laddr     localAddr
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

	var body []byte
	if opts.bodyf != "" {
		bodyr, err := file(opts.bodyf, false)
		if err != nil {
			return fmt.Errorf(errBodyFilePrefix+"(%s): %s", opts.bodyf, err)
		}
		defer bodyr.Close()

		if body, err = ioutil.ReadAll(bodyr); err != nil {
			return fmt.Errorf(errBodyFilePrefix+"(%s): %s", opts.bodyf, err)
		}
	}

	targets, err := vegeta.NewTargetsFrom(in, body, opts.headers.Header)
	if err != nil {
		return fmt.Errorf(errTargetsFilePrefix+"(%s): %s", opts.targetsf, err)
	}

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

	atk := vegeta.NewAttacker(opts.redirects, opts.timeout, *opts.laddr.IPAddr)

	log.Printf(
		"Vegeta is attacking %d targets in %s order for %s...\n",
		len(targets),
		opts.ordering,
		opts.duration,
	)
	results := atk.Attack(targets, opts.rate, opts.duration)

	log.Printf("Done! Writing results to '%s'...", opts.outputf)
	return results.Encode(out)
}

const (
	errRatePrefix        = "Rate: "
	errDurationPrefix    = "Duration: "
	errOutputFilePrefix  = "Output file: "
	errTargetsFilePrefix = "Targets file: "
	errBodyFilePrefix    = "Body file: "
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
	parts := strings.SplitN(value, ":", 2)
	if len(parts) != 2 {
		return fmt.Errorf("header '%s' has a wrong format", value)
	}
	key, val := strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1])
	if key == "" || val == "" {
		return fmt.Errorf("header '%s' has a wrong format", value)
	}
	h.Add(key, val)
	return nil
}

// localAddr implements the Flag interface for parsing net.IPAddr
type localAddr struct{ *net.IPAddr }

func (ip *localAddr) Set(value string) (err error) {
	ip.IPAddr, err = net.ResolveIPAddr("ip", value)
	return
}

package main

import (
	"bytes"
	"crypto/x509"
	"errors"
	"flag"
	"fmt"
	"io/ioutil"
	"log"
	"net"
	"net/http"
	"os"
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
	fs.StringVar(&opts.certf, "cert", "", "x509 Certificate file")
	fs.StringVar(&opts.ordering, "ordering", "random", "Attack ordering [sequential, random]")
	fs.DurationVar(&opts.duration, "duration", 10*time.Second, "Duration of the test")
	fs.DurationVar(&opts.timeout, "timeout", vegeta.DefaultTimeout, "Requests timeout")
	fs.Uint64Var(&opts.rate, "rate", 50, "Requests per second")
	fs.Uint64Var(&opts.maxreqs, "maxreqs", 1000, "Max requests in flight at any given time")
	fs.IntVar(&opts.redirects, "redirects", vegeta.DefaultRedirects, "Number of redirects to follow")
	fs.Var(&opts.headers, "header", "Request header")
	fs.Var(&opts.laddr, "laddr", "Local IP address")

	return command{fs, func(args []string) error {
		fs.Parse(args)
		return attack(opts)
	}}
}

var (
	errZeroDuration   = errors.New("duration must be bigger than zero")
	errZeroRate       = errors.New("rate must be bigger than zero")
	errParsingTargets = errors.New("error parsing targets")
	errBadOrdering    = errors.New("bad ordering")
	errBadCert        = errors.New("bad certificate")
)

// attackOpts aggregates the attack function command options
type attackOpts struct {
	targetsf  string
	outputf   string
	bodyf     string
	certf     string
	ordering  string
	duration  time.Duration
	timeout   time.Duration
	rate      uint64
	maxreqs   uint64
	redirects int
	headers   headers
	laddr     localAddr
}

// attack validates the attack arguments, sets up the
// required resources, launches the attack and writes the results
func attack(opts *attackOpts) (err error) {
	if opts.rate == 0 {
		return errZeroRate
	}

	if opts.duration == 0 {
		return errZeroDuration
	}

	// Open and read input files
	files := map[string][]byte{}
	for _, filename := range []string{opts.bodyf, opts.certf} {
		if filename == "" {
			files[filename] = []byte{}
			continue
		}

		f, err := file(filename, false)
		if err != nil {
			return fmt.Errorf("error opening %s: %s", filename, err)
		}
		defer f.Close()

		if files[filename], err = ioutil.ReadAll(f); err != nil {
			return fmt.Errorf("error reading %s: %s", filename, err)
		}
	}

	r, err := os.Open(opts.targetsf)
	if err != nil {
		return err
	}

	generator := vegeta.NewStreamTargetGenerator(r, files[opts.bodyf], opts.headers.Header)

	targetsCh, errCh := vegeta.NewTargetProducer(
		opts.rate,
		opts.duration,
		generator,
	)

	switch opts.ordering {
	case "random":
		break
	case "sequential":
		break
	default:
		return errBadOrdering
	}

	out, err := file(opts.outputf, true)
	if err != nil {
		return fmt.Errorf("error opening %s: %s", opts.outputf, err)
	}
	defer out.Close()

	tlsc := *vegeta.DefaultTLSConfig
	if opts.certf != "" {
		if tlsc.RootCAs, err = certPool(files[opts.certf]); err != nil {
			return err
		}
	}

	atk := vegeta.NewAttacker(opts.redirects, opts.timeout, *opts.laddr.IPAddr, &tlsc)

	log.Printf(
		"Vegeta is attacking for %s...\n",
		opts.duration,
	)

	results := atk.Attack(targetsCh, opts.maxreqs)

	// check if there where any errors
	for err := range errCh {
		if err != nil {
			log.Println("Error parsing ", err)
			return errParsingTargets
		}
	}

	log.Printf("Done! Writing results to '%s'...", opts.outputf)
	return results.Encode(out)
}

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

// certPool returns a new *x509.CertPool with the passed cert included.
// An error is returned if the cert is invalid.
func certPool(cert []byte) (*x509.CertPool, error) {
	pool := x509.NewCertPool()
	if !pool.AppendCertsFromPEM(cert) {
		return nil, errBadCert
	}
	return pool, nil
}

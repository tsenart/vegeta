package main

import (
	"bytes"
	"crypto/x509"
	"encoding/gob"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/ioutil"
	"net"
	"net/http"
	"os"
	"os/signal"
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
	fs.BoolVar(&opts.lazy, "lazy", false, "Read targets lazily")
	fs.DurationVar(&opts.duration, "duration", 10*time.Second, "Duration of the test")
	fs.DurationVar(&opts.timeout, "timeout", vegeta.DefaultTimeout, "Requests timeout")
	fs.Uint64Var(&opts.rate, "rate", 50, "Requests per second")
	fs.Uint64Var(&opts.workers, "workers", 0, "Number of workers")
	fs.IntVar(&opts.redirects, "redirects", vegeta.DefaultRedirects, "Number of redirects to follow. -1 will not follow but marks as success")
	fs.Var(&opts.headers, "header", "Request header")
	fs.Var(&opts.laddr, "laddr", "Local IP address")
	fs.BoolVar(&opts.keepalive, "keepalive", true, "Use persistent connections")

	return command{fs, func(args []string) error {
		fs.Parse(args)
		return attack(opts)
	}}
}

var (
	errZeroDuration = errors.New("duration must be bigger than zero")
	errZeroRate     = errors.New("rate must be bigger than zero")
	errBadCert      = errors.New("bad certificate")
)

// attackOpts aggregates the attack function command options
type attackOpts struct {
	targetsf  string
	outputf   string
	bodyf     string
	certf     string
	lazy      bool
	duration  time.Duration
	timeout   time.Duration
	rate      uint64
	workers   uint64
	redirects int
	headers   headers
	laddr     localAddr
	keepalive bool
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

	files := map[string]io.Reader{}
	for _, filename := range []string{opts.targetsf, opts.bodyf, opts.certf} {
		if filename == "" {
			continue
		}
		f, err := file(filename, false)
		if err != nil {
			return fmt.Errorf("error opening %s: %s", filename, err)
		}
		defer f.Close()
		files[filename] = f
	}

	var body []byte
	if bodyf, ok := files[opts.bodyf]; ok {
		if body, err = ioutil.ReadAll(bodyf); err != nil {
			return fmt.Errorf("error reading %s: %s", opts.bodyf, err)
		}
	}

	var (
		tr  vegeta.Targeter
		src = files[opts.targetsf]
		hdr = opts.headers.Header
	)
	if opts.lazy {
		tr = vegeta.NewLazyTargeter(src, body, hdr)
	} else if tr, err = vegeta.NewEagerTargeter(src, body, hdr); err != nil {
		return err
	}

	out, err := file(opts.outputf, true)
	if err != nil {
		return fmt.Errorf("error opening %s: %s", opts.outputf, err)
	}
	defer out.Close()

	var cert []byte
	if certf, ok := files[opts.certf]; ok {
		if cert, err = ioutil.ReadAll(certf); err != nil {
			return fmt.Errorf("error reading %s: %s", opts.certf, err)
		}
	}
	tlsc := *vegeta.DefaultTLSConfig
	if opts.certf != "" {
		if tlsc.RootCAs, err = certPool(cert); err != nil {
			return err
		}
	}

	atk := vegeta.NewAttacker(
		vegeta.Redirects(opts.redirects),
		vegeta.Timeout(opts.timeout),
		vegeta.LocalAddr(*opts.laddr.IPAddr),
		vegeta.TLSConfig(&tlsc),
		vegeta.Workers(opts.workers),
		vegeta.KeepAlive(opts.keepalive),
	)

	res := atk.Attack(tr, opts.rate, opts.duration)
	enc := gob.NewEncoder(out)
	sig := make(chan os.Signal, 1)
	signal.Notify(sig, os.Interrupt)

	for {
		select {
		case <-sig:
			atk.Stop()
			return nil
		case r, ok := <-res:
			if !ok {
				return nil
			}
			if err = enc.Encode(r); err != nil {
				return err
			}
		}
	}
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

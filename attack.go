package main

import (
	"crypto/tls"
	"crypto/x509"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/ioutil"
	"net/http"
	"os"
	"os/signal"
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
	fs.StringVar(&opts.certf, "cert", "", "TLS client PEM encoded certificate file")
	fs.StringVar(&opts.keyf, "key", "", "TLS client PEM encoded private key file")
	fs.Var(&opts.rootCerts, "root-certs", "TLS root certificate files (comma separated list)")
	fs.BoolVar(&opts.http2, "http2", true, "Send HTTP/2 requests when supported by the server")
	fs.BoolVar(&opts.insecure, "insecure", false, "Ignore invalid server TLS certificates")
	fs.BoolVar(&opts.lazy, "lazy", false, "Read targets lazily")
	fs.DurationVar(&opts.duration, "duration", 0, "Duration of the test [0 = forever]")
	fs.DurationVar(&opts.timeout, "timeout", vegeta.DefaultTimeout, "Requests timeout")
	fs.Uint64Var(&opts.rate, "rate", 50, "Requests per second")
	fs.Uint64Var(&opts.workers, "workers", vegeta.DefaultWorkers, "Initial number of workers")
	fs.IntVar(&opts.connections, "connections", vegeta.DefaultConnections, "Max open idle connections per target host")
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
	errZeroRate = errors.New("rate must be bigger than zero")
	errBadCert  = errors.New("bad certificate")
)

// attackOpts aggregates the attack function command options
type attackOpts struct {
	targetsf    string
	outputf     string
	bodyf       string
	certf       string
	keyf        string
	rootCerts   csl
	http2       bool
	insecure    bool
	lazy        bool
	duration    time.Duration
	timeout     time.Duration
	rate        uint64
	workers     uint64
	connections int
	redirects   int
	headers     headers
	laddr       localAddr
	keepalive   bool
}

// attack validates the attack arguments, sets up the
// required resources, launches the attack and writes the results
func attack(opts *attackOpts) (err error) {
	if opts.rate == 0 {
		return errZeroRate
	}

	files := map[string]io.Reader{}
	for _, filename := range []string{opts.targetsf, opts.bodyf} {
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

	tlsc, err := tlsConfig(opts.insecure, opts.certf, opts.keyf, opts.rootCerts)
	if err != nil {
		return err
	}

	atk := vegeta.NewAttacker(
		vegeta.Redirects(opts.redirects),
		vegeta.Timeout(opts.timeout),
		vegeta.LocalAddr(*opts.laddr.IPAddr),
		vegeta.TLSConfig(tlsc),
		vegeta.Workers(opts.workers),
		vegeta.KeepAlive(opts.keepalive),
		vegeta.Connections(opts.connections),
		vegeta.HTTP2(opts.http2),
	)

	res := atk.Attack(tr, opts.rate, opts.duration)
	enc := vegeta.NewEncoder(out)
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

// tlsConfig builds a *tls.Config from the given options.
func tlsConfig(insecure bool, certf, keyf string, rootCerts []string) (*tls.Config, error) {
	var err error
	files := map[string][]byte{}
	filenames := append([]string{certf, keyf}, rootCerts...)
	for _, f := range filenames {
		if f != "" {
			if files[f], err = ioutil.ReadFile(f); err != nil {
				return nil, err
			}
		}
	}

	c := tls.Config{InsecureSkipVerify: insecure}
	if cert, ok := files[certf]; ok {
		key, ok := files[keyf]
		if !ok {
			key = cert
		}

		certificate, err := tls.X509KeyPair(cert, key)
		if err != nil {
			return nil, err
		}

		c.Certificates = append(c.Certificates, certificate)
		c.BuildNameToCertificate()
	}

	if len(rootCerts) > 0 {
		c.RootCAs = x509.NewCertPool()
		for _, f := range rootCerts {
			if !c.RootCAs.AppendCertsFromPEM(files[f]) {
				return nil, errBadCert
			}
		}
	}

	return &c, nil
}

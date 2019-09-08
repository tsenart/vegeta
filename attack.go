package main

import (
	"crypto/tls"
	"crypto/x509"
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

	"github.com/tsenart/vegeta/internal/resolver"
	vegeta "github.com/tsenart/vegeta/lib"
)

func attackCmd() command {
	fs := flag.NewFlagSet("vegeta attack", flag.ExitOnError)
	opts := &attackOpts{
		headers:      headers{http.Header{}},
		proxyHeaders: headers{http.Header{}},
		laddr:        localAddr{&vegeta.DefaultLocalAddr},
		rate:         vegeta.Rate{Freq: 50, Per: time.Second},
		maxBody:      vegeta.DefaultMaxBody,
	}
	fs.StringVar(&opts.name, "name", "", "Attack name")
	fs.StringVar(&opts.targetsf, "targets", "stdin", "Targets file")
	fs.StringVar(&opts.format, "format", vegeta.HTTPTargetFormat,
		fmt.Sprintf("Targets format [%s]", strings.Join(vegeta.TargetFormats, ", ")))
	fs.StringVar(&opts.outputf, "output", "stdout", "Output file")
	fs.StringVar(&opts.bodyf, "body", "", "Requests body file")
	fs.StringVar(&opts.certf, "cert", "", "TLS client PEM encoded certificate file")
	fs.StringVar(&opts.keyf, "key", "", "TLS client PEM encoded private key file")
	fs.Var(&opts.rootCerts, "root-certs", "TLS root certificate files (comma separated list)")
	fs.BoolVar(&opts.http2, "http2", true, "Send HTTP/2 requests when supported by the server")
	fs.BoolVar(&opts.h2c, "h2c", false, "Send HTTP/2 requests without TLS encryption")
	fs.BoolVar(&opts.insecure, "insecure", false, "Ignore invalid server TLS certificates")
	fs.BoolVar(&opts.lazy, "lazy", false, "Read targets lazily")
	fs.DurationVar(&opts.duration, "duration", 0, "Duration of the test [0 = forever]")
	fs.DurationVar(&opts.timeout, "timeout", vegeta.DefaultTimeout, "Requests timeout")
	fs.Uint64Var(&opts.workers, "workers", vegeta.DefaultWorkers, "Initial number of workers")
	fs.Uint64Var(&opts.maxWorkers, "max-workers", vegeta.DefaultMaxWorkers, "Maximum number of workers")
	fs.IntVar(&opts.connections, "connections", vegeta.DefaultConnections, "Max open idle connections per target host")
	fs.IntVar(&opts.redirects, "redirects", vegeta.DefaultRedirects, "Number of redirects to follow. -1 will not follow but marks as success")
	fs.Var(&maxBodyFlag{&opts.maxBody}, "max-body", "Maximum number of bytes to capture from response bodies. [-1 = no limit]")
	fs.Var(&rateFlag{&opts.rate}, "rate", "Number of requests per time unit [0 = infinity]")
	fs.Var(&opts.headers, "header", "Request header")
	fs.Var(&opts.proxyHeaders, "proxy-header", "Proxy CONNECT header")
	fs.Var(&opts.laddr, "laddr", "Local IP address")
	fs.BoolVar(&opts.keepalive, "keepalive", true, "Use persistent connections")
	fs.StringVar(&opts.unixSocket, "unix-socket", "", "Connect over a unix socket. This overrides the host address in target URLs")
	systemSpecificFlags(fs, opts)

	return command{fs, func(args []string) error {
		fs.Parse(args)
		return attack(opts)
	}}
}

var (
	errZeroRate = errors.New("rate frequency and time unit must be bigger than zero")
	errBadCert  = errors.New("bad certificate")
)

// attackOpts aggregates the attack function command options
type attackOpts struct {
	name         string
	targetsf     string
	format       string
	outputf      string
	bodyf        string
	certf        string
	keyf         string
	rootCerts    csl
	http2        bool
	h2c          bool
	insecure     bool
	lazy         bool
	duration     time.Duration
	timeout      time.Duration
	rate         vegeta.Rate
	workers      uint64
	maxWorkers   uint64
	connections  int
	redirects    int
	maxBody      int64
	headers      headers
	proxyHeaders headers
	laddr        localAddr
	keepalive    bool
	resolvers    csl
	unixSocket   string
}

// attack validates the attack arguments, sets up the
// required resources, launches the attack and writes the results
func attack(opts *attackOpts) (err error) {
	if opts.maxWorkers == vegeta.DefaultMaxWorkers && opts.rate.Freq == 0 {
		return fmt.Errorf("-rate=0 requires setting -max-workers")
	}

	if len(opts.resolvers) > 0 {
		res, err := resolver.NewResolver(opts.resolvers)
		if err != nil {
			return err
		}
		net.DefaultResolver = res
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
		tr       vegeta.Targeter
		src      = files[opts.targetsf]
		hdr      = opts.headers.Header
		proxyHdr = opts.proxyHeaders.Header
	)

	switch opts.format {
	case vegeta.JSONTargetFormat:
		tr = vegeta.NewJSONTargeter(src, body, hdr)
	case vegeta.HTTPTargetFormat:
		tr = vegeta.NewHTTPTargeter(src, body, hdr)
	default:
		return fmt.Errorf("format %q isn't one of [%s]",
			opts.format, strings.Join(vegeta.TargetFormats, ", "))
	}

	if !opts.lazy {
		targets, err := vegeta.ReadAllTargets(tr)
		if err != nil {
			return err
		}
		tr = vegeta.NewStaticTargeter(targets...)
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
		vegeta.MaxWorkers(opts.maxWorkers),
		vegeta.KeepAlive(opts.keepalive),
		vegeta.Connections(opts.connections),
		vegeta.HTTP2(opts.http2),
		vegeta.H2C(opts.h2c),
		vegeta.MaxBody(opts.maxBody),
		vegeta.UnixSocket(opts.unixSocket),
		vegeta.ProxyHeader(proxyHdr),
	)

	res := atk.Attack(tr, opts.rate, opts.duration, opts.name)
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

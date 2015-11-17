package attack

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
	"syscall"
	"time"

	"github.com/tsenart/vegeta/internal/flagutil"
)

// A Command represents a terminal command for an attack.
type Command struct {
	*flag.FlagSet
	Body        io.Reader
	Cert        io.Reader
	Connections int
	Duration    time.Duration
	Headers     http.Header
	Keepalive   bool
	Key         io.Reader
	LocalAddr   net.IP
	Lazy        bool
	Output      io.Writer
	Rate        uint64
	Redirects   int
	RootCerts   []string
	Targets     io.Reader
	Timeout     time.Duration
	Workers     uint64
}

// NewCommand a new attack Command the registers its flags on the given
// flag.FlagSet.
func NewCommand(fs *flag.FlagSet) *Command {
	c := &Command{
		FlagSet: fs,
		Body:    (*os.File)(nil),
		Cert:    (*os.File)(nil),
		Key:     (*os.File)(nil),
		Headers: http.Header{},
		Output:  os.NewFile(uintptr(syscall.Stdout), "stdout"),
		Targets: os.NewFile(uintptr(syscall.Stdin), "stdin"),
	}
	c.Var(&flagutil.File{File: c.Body.(*os.File), Flags: os.O_RDONLY}, "body", "Requests body file")
	c.Var(&flagutil.File{File: c.Cert.(*os.File), Flags: os.O_RDONLY}, "cert", "TLS client PEM encoded certificate file")
	c.IntVar(&c.Connections, "connections", DefaultConnections, "Max open idle connections per target host")
	c.DurationVar(&c.Duration, "duration", 0, "Duration of the test [0 = forever]")
	c.Var(&flagutil.Header{Header: c.Headers}, "header", "Request header")
	c.BoolVar(&c.Keepalive, "keepalive", true, "Use persistent connections")
	c.Var(&flagutil.File{File: c.Key.(*os.File), Flags: os.O_RDONLY}, "key", "TLS client PEM encoded private key file")
	c.Var(&flagutil.IP{IP: &c.LocalAddr}, "laddr", "Local IP address")
	c.BoolVar(&c.Lazy, "lazy", false, "Read targets lazily")
	c.Var(&flagutil.File{
		File:  c.Output.(*os.File),
		Flags: os.O_WRONLY | os.O_TRUNC | os.O_CREATE,
		Mode:  0666,
	}, "output", "Output file")
	c.Uint64Var(&c.Rate, "rate", 50, "Requests per second")
	c.IntVar(&c.Redirects, "redirects", DefaultRedirects, "Number of redirects to follow. -1 will not follow but marks as success")
	c.Var(&flagutil.StringList{List: &c.RootCerts}, "root-certs", "TLS root certificate files (comma separated list)")
	c.Var(&flagutil.File{File: c.Targets.(*os.File), Flags: os.O_RDONLY}, "targets", "Targets file")
	c.DurationVar(&c.Timeout, "timeout", DefaultTimeout, "Requests timeout")
	c.Uint64Var(&c.Workers, "workers", DefaultWorkers, "Initial number of workers")
	return c
}

var (
	// ErrZeroRate is returned by the Command Run method when the specified rate
	// is zero.
	ErrZeroRate = errors.New("attack: rate must be bigger than zero")
	// ErrBadRootCert is returned by the Command Run method when a given root
	// certificate file can't be parsed.
	ErrBadRootCert = errors.New("attack: bad root certificate")
)

func (c *Command) Run() (err error) {
	if c.Rate == 0 {
		return ErrZeroRate
	}

	var body []byte
	if f, ok := c.Body.(*os.File); ok && f != nil {
		defer f.Close()
		if body, err = ioutil.ReadAll(f); err != nil {
			return fmt.Errorf("error reading body", err)
		}
	}

	var tr Targeter
	if c.Lazy {
		tr = NewLazyTargeter(c.Targets, body, c.Headers)
	} else if tr, err = NewEagerTargeter(c.Targets, body, c.Headers); err != nil {
		return err
	}

	for _, iface := range []interface{}{c.Output, c.Targets} {
		if cl, ok := iface.(io.Closer); ok {
			defer cl.Close()
		}
	}

	tlsc, err := tlsConfig(c.Cert, c.Key, c.RootCerts)
	if err != nil {
		return err
	}

	atk := NewAttacker(
		Redirects(c.Redirects),
		Timeout(c.Timeout),
		LocalAddr(c.LocalAddr),
		TLSConfig(tlsc),
		Workers(c.Workers),
		KeepAlive(c.Keepalive),
		Connections(c.Connections),
	)

	res := atk.Attack(tr, c.Rate, c.Duration)
	enc := NewEncoder(c.Output)
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
func tlsConfig(cert, key io.Reader, rootCerts []string) (*tls.Config, error) {
	var err error

	files := map[string][]byte{}
	for _, f := range rootCerts {
		if f != "" {
			if files[f], err = ioutil.ReadFile(f); err != nil {
				return nil, err
			}
		}
	}

	for _, r := range []io.Reader{cert, key} {
		if files[f], err = ioutil.ReadFile(f); err != nil {
			return nil, err
		}
	}

	var c tls.Config
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

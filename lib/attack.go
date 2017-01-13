package vegeta

import (
	"crypto/tls"
	"fmt"
	"io"
	"io/ioutil"
	"net"
	"net/http"
	"strings"
	"sync"
	"time"

	"github.com/quipo/statsd"
	"golang.org/x/net/http2"
	"os"
)

// Attacker is an attack executor which wraps an http.Client
type Attacker struct {
	dialer    *net.Dialer
	client    http.Client
	stopch    chan struct{}
	workers   uint64
	redirects int
	statsd    *statsdOpts
}

type statsdOpts struct {
	enabled bool
	host    string
	port    uint64
	prefix  string
	client  *statsd.StatsdClient
}

const (
	// DefaultRedirects is the default number of times an Attacker follows
	// redirects.
	DefaultRedirects = 10
	// DefaultTimeout is the default amount of time an Attacker waits for a request
	// before it times out.
	DefaultTimeout = 30 * time.Second
	// DefaultConnections is the default amount of max open idle connections per
	// target host.
	DefaultConnections = 10000
	// DefaultWorkers is the default initial number of workers used to carry an attack.
	DefaultWorkers = 10
	// NoFollow is the value when redirects are not followed but marked successful
	NoFollow = -1
)

var (
	// DefaultLocalAddr is the default local IP address an Attacker uses.
	DefaultLocalAddr = net.IPAddr{IP: net.IPv4zero}
	// DefaultTLSConfig is the default tls.Config an Attacker uses.
	DefaultTLSConfig = &tls.Config{InsecureSkipVerify: true}
)

// NewAttacker returns a new Attacker with default options which are overridden
// by the optionally provided opts.
func NewAttacker(opts ...func(*Attacker)) *Attacker {
	a := &Attacker{stopch: make(chan struct{}), workers: DefaultWorkers, statsd: &statsdOpts{}}
	a.dialer = &net.Dialer{
		LocalAddr: &net.TCPAddr{IP: DefaultLocalAddr.IP, Zone: DefaultLocalAddr.Zone},
		KeepAlive: 30 * time.Second,
		Timeout:   DefaultTimeout,
	}
	a.client = http.Client{
		Transport: &http.Transport{
			Proxy: http.ProxyFromEnvironment,
			Dial:  a.dialer.Dial,
			ResponseHeaderTimeout: DefaultTimeout,
			TLSClientConfig:       DefaultTLSConfig,
			TLSHandshakeTimeout:   10 * time.Second,
			MaxIdleConnsPerHost:   DefaultConnections,
		},
	}

	for _, opt := range opts {
		opt(a)
	}

	a.statsd.client = a.newStatsdClient()

	return a
}

// Workers returns a functional option which sets the initial number of workers
// an Attacker uses to hit its targets. More workers may be spawned dynamically
// to sustain the requested rate in the face of slow responses and errors.
func Workers(n uint64) func(*Attacker) {
	return func(a *Attacker) { a.workers = n }
}

// Connections returns a functional option which sets the number of maximum idle
// open connections per target host.
func Connections(n int) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.MaxIdleConnsPerHost = n
	}
}

// Redirects returns a functional option which sets the maximum
// number of redirects an Attacker will follow.
func Redirects(n int) func(*Attacker) {
	return func(a *Attacker) {
		a.redirects = n
		a.client.CheckRedirect = func(_ *http.Request, via []*http.Request) error {
			if len(via) > n {
				return fmt.Errorf("stopped after %d redirects", n)
			}
			return nil
		}
	}
}

// Timeout returns a functional option which sets the maximum amount of time
// an Attacker will wait for a request to be responded to.
func Timeout(d time.Duration) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.ResponseHeaderTimeout = d
		a.dialer.Timeout = d
		tr.Dial = a.dialer.Dial
	}
}

// LocalAddr returns a functional option which sets the local address
// an Attacker will use with its requests.
func LocalAddr(addr net.IPAddr) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		a.dialer.LocalAddr = &net.TCPAddr{IP: addr.IP, Zone: addr.Zone}
		tr.Dial = a.dialer.Dial
	}
}

// KeepAlive returns a functional option which toggles KeepAlive
// connections on the dialer and transport.
func KeepAlive(keepalive bool) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.DisableKeepAlives = !keepalive
		if !keepalive {
			a.dialer.KeepAlive = 0
			tr.Dial = a.dialer.Dial
		}
	}
}

// TLSConfig returns a functional option which sets the *tls.Config for a
// Attacker to use with its requests.
func TLSConfig(c *tls.Config) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.TLSClientConfig = c
	}
}

// HTTP2 returns a functional option which enables or disables HTTP/2 support
// on requests performed by an Attacker.
func HTTP2(enabled bool) func(*Attacker) {
	return func(a *Attacker) {
		if tr := a.client.Transport.(*http.Transport); enabled {
			http2.ConfigureTransport(tr)
		} else {
			tr.TLSNextProto = map[string]func(string, *tls.Conn) http.RoundTripper{}
		}
	}
}

// Enable Statsd
func StatsdEnabled(enabled bool) func(*Attacker) {
	return func(a *Attacker) { a.statsd.enabled = enabled }
}

// Define statsd host
func StatsdHost(host string) func(*Attacker) {
	return func(a *Attacker) { a.statsd.host = host }
}

// Define statsd port
func StatsdPort(port uint64) func(*Attacker) {
	return func(a *Attacker) { a.statsd.port = port }
}

// Define statsd prefix
func StatsdPrefix(prefix string) func(*Attacker) {
	return func(a *Attacker) { a.statsd.prefix = prefix }
}

// Attack reads its Targets from the passed Targeter and attacks them at
// the rate specified for duration time. When the duration is zero the attack
// runs until Stop is called. Results are put into the returned channel as soon
// as they arrive.
func (a *Attacker) Attack(tr Targeter, rate uint64, du time.Duration) <-chan *Result {
	var workers sync.WaitGroup
	results := make(chan *Result)
	ticks := make(chan time.Time)
	for i := uint64(0); i < a.workers; i++ {
		workers.Add(1)
		go a.attack(tr, &workers, ticks, results)
	}

	go func() {
		defer close(results)
		defer workers.Wait()
		defer close(ticks)
		interval := 1e9 / rate
		hits := rate * uint64(du.Seconds())
		began, done := time.Now(), uint64(0)
		for {
			now, next := time.Now(), began.Add(time.Duration(done*interval))
			time.Sleep(next.Sub(now))
			select {
			case ticks <- max(next, now):
				if done++; done == hits {
					return
				}
			case <-a.stopch:
				return
			default: // all workers are blocked. start one more and try again
				workers.Add(1)
				go a.attack(tr, &workers, ticks, results)
			}
		}
	}()

	return results
}

// Stop stops the current attack.
func (a *Attacker) Stop() {
	select {
	case <-a.stopch:
		return
	default:
		a.statsd.client.Close()
		close(a.stopch)
	}
}

func (a *Attacker) attack(tr Targeter, workers *sync.WaitGroup, ticks <-chan time.Time, results chan<- *Result) {
	defer workers.Done()
	for tm := range ticks {
		results <- a.hit(tr, tm)
	}
}

func (a *Attacker) hit(tr Targeter, tm time.Time) *Result {
	var (
		res = Result{Timestamp: tm}
		tgt Target
		err error
	)

	defer func() {
		res.Latency = time.Since(tm)
		if err != nil {
			res.Error = err.Error()
		}
		if err := a.sendToStatsd(&res); err != nil {
			fmt.Fprintf(os.Stderr, "%s\n", err.Error())
		}
	}()

	if err = tr(&tgt); err != nil {
		a.Stop()
		return &res
	}

	req, err := tgt.Request()
	if err != nil {
		return &res
	}

	r, err := a.client.Do(req)
	if err != nil {
		// ignore redirect errors when the user set --redirects=NoFollow
		if a.redirects == NoFollow && strings.Contains(err.Error(), "stopped after") {
			err = nil
		}
		return &res
	}
	defer r.Body.Close()

	in, err := io.Copy(ioutil.Discard, r.Body)
	if err != nil {
		return &res
	}
	res.BytesIn = uint64(in)

	if req.ContentLength != -1 {
		res.BytesOut = uint64(req.ContentLength)
	}

	if res.Code = uint16(r.StatusCode); res.Code < 200 || res.Code >= 400 {
		res.Error = r.Status
	}

	return &res
}

func (a *Attacker) sendToStatsd(result *Result) error {
	statsdClient := a.statsd.client
	if statsdClient != nil {
		if err := statsdClient.Incr(fmt.Sprintf(".code%d", result.Code), 1); err != nil {
			return err
		}
		if err := statsdClient.Incr(".byteIn", int64(result.BytesIn)); err != nil {
			return err
		}
		if err := statsdClient.Incr(".byteOut", int64(result.BytesOut)); err != nil {
			return err
		}
		if err := statsdClient.FGauge(".latency", float64(result.Latency / time.Millisecond)); err != nil {
			return err
		}
	}
	return nil
}

func (a *Attacker) newStatsdClient() *statsd.StatsdClient {
	if a.statsd.enabled {
		statsdAddr := fmt.Sprintf("%s:%d", a.statsd.host, a.statsd.port)
		statsdclient := statsd.NewStatsdClient(statsdAddr, a.statsd.prefix)
		if err := statsdclient.CreateSocket(); err != nil {
			fmt.Fprintf(os.Stderr, err.Error())
			statsdclient.Close()
			return nil
		}
		return statsdclient
	}
	return nil
}

func max(a, b time.Time) time.Time {
	if a.After(b) {
		return a
	}
	return b
}

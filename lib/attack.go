package vegeta

import (
	"context"
	"crypto/tls"
	"fmt"
	"io"
	"io/ioutil"
	"math"
	"net"
	"net/http"
	"net/url"
	"strconv"
	"sync"
	"time"

	"github.com/gorilla/mux"
	"github.com/prometheus/client_golang/prometheus"
	"github.com/prometheus/client_golang/prometheus/promauto"
	"github.com/prometheus/client_golang/prometheus/promhttp"
	"golang.org/x/net/http2"
)

// Attacker is an attack executor which wraps an http.Client
type Attacker struct {
	dialer      *net.Dialer
	client      http.Client
	stopch      chan struct{}
	workers     uint64
	maxWorkers  uint64
	maxBody     int64
	redirects   int
	seqmu       sync.Mutex
	seq         uint64
	began       time.Time
	chunked     bool
	promEnabled bool
	promBind    string
	promPort    int
	promPath    string
	promSrv     *http.Server
}

// Prometheus metrics
var requestSecondsHistogram = promauto.NewHistogramVec(prometheus.HistogramOpts{
	Name:    "request_seconds",
	Help:    "Request latency",
	Buckets: []float64{0.1, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0, 20, 50},
}, []string{
	"method",
	"url",
	"status",
})

var requestBytesInCounter = promauto.NewCounterVec(prometheus.CounterOpts{
	Name: "request_bytes_in",
	Help: "Bytes received from servers as response to requests",
}, []string{
	"method",
	"url",
	"status",
})

var requestBytesOutCounter = promauto.NewCounterVec(prometheus.CounterOpts{
	Name: "request_bytes_out",
	Help: "Bytes sent to servers during requests",
}, []string{
	"method",
	"url",
	"status",
})

var requestFailCounter = promauto.NewCounterVec(prometheus.CounterOpts{
	Name: "request_fail_count",
	Help: "Internal failures that prevented a hit to the target server",
}, []string{
	"method",
	"url",
	"message",
})

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
	// DefaultMaxConnections is the default amount of connections per target
	// host.
	DefaultMaxConnections = 0
	// DefaultWorkers is the default initial number of workers used to carry an attack.
	DefaultWorkers = 10
	// DefaultMaxWorkers is the default maximum number of workers used to carry an attack.
	DefaultMaxWorkers = math.MaxUint64
	// DefaultMaxBody is the default max number of bytes to be read from response bodies.
	// Defaults to no limit.
	DefaultMaxBody = int64(-1)
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
	a := &Attacker{
		stopch:      make(chan struct{}),
		workers:     DefaultWorkers,
		maxWorkers:  DefaultMaxWorkers,
		maxBody:     DefaultMaxBody,
		began:       time.Now(),
		promEnabled: false,
		promBind:    "0.0.0.0",
		promPort:    8880,
		promPath:    "/metrics",
	}

	a.dialer = &net.Dialer{
		LocalAddr: &net.TCPAddr{IP: DefaultLocalAddr.IP, Zone: DefaultLocalAddr.Zone},
		KeepAlive: 30 * time.Second,
	}

	a.client = http.Client{
		Timeout: DefaultTimeout,
		Transport: &http.Transport{
			Proxy:               http.ProxyFromEnvironment,
			Dial:                a.dialer.Dial,
			TLSClientConfig:     DefaultTLSConfig,
			MaxIdleConnsPerHost: DefaultConnections,
			MaxConnsPerHost:     DefaultMaxConnections,
		},
	}

	for _, opt := range opts {
		opt(a)
	}

	//setup prometheus metrics
	if a.promEnabled {
		go func() {
			router := mux.NewRouter()
			router.Handle(a.promPath, promhttp.Handler())

			listen := fmt.Sprintf("%s:%d", a.promBind, a.promPort)
			a.promSrv = &http.Server{Addr: listen, Handler: router}
			err := a.promSrv.ListenAndServe()
			if err != nil {
				// fmt.Printf("%s\n", err)
			}
		}()
	}

	return a
}

// Workers returns a functional option which sets the initial number of workers
// an Attacker uses to hit its targets. More workers may be spawned dynamically
// to sustain the requested rate in the face of slow responses and errors.
func Workers(n uint64) func(*Attacker) {
	return func(a *Attacker) { a.workers = n }
}

// MaxWorkers returns a functional option which sets the maximum number of workers
// an Attacker can use to hit its targets.
func MaxWorkers(n uint64) func(*Attacker) {
	return func(a *Attacker) { a.maxWorkers = n }
}

// Connections returns a functional option which sets the number of maximum idle
// open connections per target host.
func Connections(n int) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.MaxIdleConnsPerHost = n
	}
}

// MaxConnections returns a functional option which sets the number of maximum
// connections per target host.
func MaxConnections(n int) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.MaxConnsPerHost = n
	}
}

// ChunkedBody returns a functional option which makes the attacker send the
// body of each request with the chunked transfer encoding.
func ChunkedBody(b bool) func(*Attacker) {
	return func(a *Attacker) { a.chunked = b }
}

// PrometheusEnable Enables Prometheus metrics at http://0.0.0.0:8880/metrics during attack
// For custom settings, use PrometheusSettings(..)
func PrometheusEnable() func(*Attacker) {
	return func(a *Attacker) {
		a.promEnabled = true
	}
}

// PrometheusSettings Returns a functional option which configures a Prometheus
// client settings that can be used for monitoring this attack on a remote Prometheus Server
// regarding to requests/s bytes in/out/s and so on.
// Options are:
//   - enabled: whatever to enable Prometheus support
//   - bindHost: host to bind the listening socket to
//   - bindPort: port to bind the listening socket to
//   - metricsPath: http path that will be used to get metrics
// For example, after using PrometheusSettings(true, "0.0.0.0", 8880, "/metrics"),
// during an "attack" you can call "curl http://127.0.0.0:8880/metrics" to see current metrics.
// This endpoint can be configured in scrapper section of your Prometheus server.
func PrometheusSettings(enabled bool, bindHost string, bindPort int, metricsPath string) func(*Attacker) {
	return func(a *Attacker) {
		a.promEnabled = enabled
		a.promBind = bindHost
		a.promPort = bindPort
		a.promPath = metricsPath
	}
}

// Redirects returns a functional option which sets the maximum
// number of redirects an Attacker will follow.
func Redirects(n int) func(*Attacker) {
	return func(a *Attacker) {
		a.redirects = n
		a.client.CheckRedirect = func(_ *http.Request, via []*http.Request) error {
			switch {
			case n == NoFollow:
				return http.ErrUseLastResponse
			case n < len(via):
				return fmt.Errorf("stopped after %d redirects", n)
			default:
				return nil
			}
		}
	}
}

// Proxy returns a functional option which sets the `Proxy` field on
// the http.Client's Transport
func Proxy(proxy func(*http.Request) (*url.URL, error)) func(*Attacker) {
	return func(a *Attacker) {
		tr := a.client.Transport.(*http.Transport)
		tr.Proxy = proxy
	}
}

// Timeout returns a functional option which sets the maximum amount of time
// an Attacker will wait for a request to be responded to and completely read.
func Timeout(d time.Duration) func(*Attacker) {
	return func(a *Attacker) {
		a.client.Timeout = d
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

// H2C returns a functional option which enables H2C support on requests
// performed by an Attacker
func H2C(enabled bool) func(*Attacker) {
	return func(a *Attacker) {
		if tr := a.client.Transport.(*http.Transport); enabled {
			a.client.Transport = &http2.Transport{
				AllowHTTP: true,
				DialTLS: func(network, addr string, cfg *tls.Config) (net.Conn, error) {
					return tr.Dial(network, addr)
				},
			}
		}
	}
}

// MaxBody returns a functional option which limits the max number of bytes
// read from response bodies. Set to -1 to disable any limits.
func MaxBody(n int64) func(*Attacker) {
	return func(a *Attacker) { a.maxBody = n }
}

// UnixSocket changes the dialer for the attacker to use the specified unix socket file
func UnixSocket(socket string) func(*Attacker) {
	return func(a *Attacker) {
		if tr, ok := a.client.Transport.(*http.Transport); socket != "" && ok {
			tr.DialContext = func(_ context.Context, _, _ string) (net.Conn, error) {
				return net.Dial("unix", socket)
			}
		}
	}
}

// Client returns a functional option that allows you to bring your own http.Client
func Client(c *http.Client) func(*Attacker) {
	return func(a *Attacker) { a.client = *c }
}

// ProxyHeader returns a functional option that allows you to add your own
// Proxy CONNECT headers
func ProxyHeader(h http.Header) func(*Attacker) {
	return func(a *Attacker) {
		if tr, ok := a.client.Transport.(*http.Transport); ok {
			tr.ProxyConnectHeader = h
		}
	}
}

// Attack reads its Targets from the passed Targeter and attacks them at
// the rate specified by the Pacer. When the duration is zero the attack
// runs until Stop is called. Results are sent to the returned channel as soon
// as they arrive and will have their Attack field set to the given name.
func (a *Attacker) Attack(tr Targeter, p Pacer, du time.Duration, name string) <-chan *Result {
	var wg sync.WaitGroup

	workers := a.workers
	if workers > a.maxWorkers {
		workers = a.maxWorkers
	}

	results := make(chan *Result)
	ticks := make(chan struct{})
	for i := uint64(0); i < workers; i++ {
		wg.Add(1)
		go a.attack(tr, name, &wg, ticks, results)
	}

	go func() {
		defer close(results)
		defer wg.Wait()
		defer close(ticks)
		defer a.stopPrometheus()

		began, count := time.Now(), uint64(0)
		for {
			elapsed := time.Since(began)
			if du > 0 && elapsed > du {
				return
			}

			wait, stop := p.Pace(elapsed, count)
			if stop {
				return
			}

			time.Sleep(wait)

			if workers < a.maxWorkers {
				select {
				case ticks <- struct{}{}:
					count++
					continue
				case <-a.stopch:
					return
				default:
					// all workers are blocked. start one more and try again
					workers++
					wg.Add(1)
					go a.attack(tr, name, &wg, ticks, results)
				}
			}

			select {
			case ticks <- struct{}{}:
				count++
			case <-a.stopch:
				return
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
		close(a.stopch)
	}
}

func (a *Attacker) attack(tr Targeter, name string, workers *sync.WaitGroup, ticks <-chan struct{}, results chan<- *Result) {
	defer workers.Done()
	for range ticks {
		results <- a.hit(tr, name)
	}
}

func (a *Attacker) hit(tr Targeter, name string) *Result {
	var (
		res = Result{Attack: name}
		tgt Target
		err error
	)

	a.seqmu.Lock()
	res.Timestamp = a.began.Add(time.Since(a.began))
	res.Seq = a.seq
	a.seq++
	a.seqmu.Unlock()

	res.Method = tgt.Method
	res.URL = tgt.URL

	defer func() {
		res.Latency = time.Since(res.Timestamp)
		if a.promEnabled {
			requestSecondsHistogram.WithLabelValues(res.Method, res.URL, fmt.Sprintf("%d", res.Code)).Observe(float64(res.Latency) / float64(time.Second))
		}
		if err != nil {
			res.Error = err.Error()
			if a.promEnabled {
				requestFailCounter.WithLabelValues(res.Method, res.URL, res.Error)
			}
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

	if name != "" {
		req.Header.Set("X-Vegeta-Attack", name)
	}

	req.Header.Set("X-Vegeta-Seq", strconv.FormatUint(res.Seq, 10))

	if a.chunked {
		req.TransferEncoding = append(req.TransferEncoding, "chunked")
	}

	r, err := a.client.Do(req)
	if err != nil {
		return &res
	}
	defer r.Body.Close()

	body := io.Reader(r.Body)
	if a.maxBody >= 0 {
		body = io.LimitReader(r.Body, a.maxBody)
	}

	if res.Body, err = ioutil.ReadAll(body); err != nil {
		return &res
	} else if _, err = io.Copy(ioutil.Discard, r.Body); err != nil {
		return &res
	}

	res.BytesIn = uint64(len(res.Body))

	if req.ContentLength != -1 {
		res.BytesOut = uint64(req.ContentLength)
	}

	if res.Code = uint16(r.StatusCode); res.Code < 200 || res.Code >= 400 {
		res.Error = r.Status
	}

	res.Headers = r.Header

	//Prometheus metrics
	if a.promEnabled {
		requestBytesInCounter.WithLabelValues(res.Method, res.URL, fmt.Sprintf("%d", res.Code)).Add(float64(res.BytesIn))
		requestBytesOutCounter.WithLabelValues(res.Method, res.URL, fmt.Sprintf("%d", res.Code)).Add(float64(res.BytesOut))
	}

	return &res
}

func (a *Attacker) stopPrometheus() {
	if a.promSrv != nil {
		a.promSrv.Close()
	}
}

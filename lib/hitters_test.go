package vegeta

import (
	"net"
	"net/http"
	"sync/atomic"
	"testing"
	"time"

	"github.com/valyala/fasthttp"
)

func BenchmarkFastHTTPHitter_Hit(b *testing.B) {
	benchmarkHitter(b, &FastHTTPHitter{
		Client: &fasthttp.Client{
			Name:                          "vegeta",
			NoDefaultUserAgentHeader:      true,
			ReadTimeout:                   DefaultTimeout,
			DisableHeaderNamesNormalizing: true,
		},
	})
}

func BenchmarkNetHTTPHitter_Hit(b *testing.B) {
	benchmarkHitter(b, &NetHTTPHitter{
		Client: http.DefaultClient,
	})
}

func benchmarkHitter(b *testing.B, h Hitter) {
	reqs := uint64(0)
	pong := []byte("pong")

	s := &fasthttp.Server{
		Handler: func(ctx *fasthttp.RequestCtx) {
			atomic.AddUint64(&reqs, 1)
			ctx.SetStatusCode(200)
			ctx.SetBody(pong)
		},
	}

	ln, err := net.Listen("tcp4", ":0")
	if err != nil {
		b.Fatal(err)
	}

	b.Cleanup(func() {
		_ = ln.Close()
	})

	go func() {
		if err = s.Serve(ln); err != nil {
			b.Log(err)
		}
	}()

	t := Target{
		Method: "GET",
		URL:    "http://" + ln.Addr().String() + "/",
		Header: http.Header{"X-Foo": []string{"bar"}},
	}
	tr := NewStaticTargeter(t)
	a := Attacker{Hitter: h}

	b.ReportAllocs()
	b.ResetTimer()

	start := time.Now()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_ = a.hit(tr, "attack")
		}
	})

	took := time.Since(start)
	rate := float64(atomic.LoadUint64(&reqs)) / took.Seconds()

	b.ReportMetric(rate, "req/s")
}

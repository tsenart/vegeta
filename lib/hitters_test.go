package vegeta_test

import (
	"net"
	"net/http"
	"sync/atomic"
	"testing"
	"time"

	"github.com/valyala/fasthttp"

	vegeta "github.com/tsenart/vegeta/lib"
)

func BenchmarkFastHTTPHitter_Hit(b *testing.B) {
	benchmarkHitter(b, &vegeta.FastHTTPHitter{
		Client: &fasthttp.Client{
			Name:                          "vegeta",
			NoDefaultUserAgentHeader:      true,
			ReadTimeout:                   vegeta.DefaultTimeout,
			DisableHeaderNamesNormalizing: true,
		},
	})
}

func BenchmarkNetHTTPHitter_Hit(b *testing.B) {
	benchmarkHitter(b, &vegeta.NetHTTPHitter{
		Client: http.DefaultClient,
	})
}

func benchmarkHitter(b *testing.B, h vegeta.Hitter) {
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

	t := &vegeta.Target{
		Method: "GET",
		URL:    "http://" + ln.Addr().String() + "/",
	}

	b.ReportAllocs()
	b.ResetTimer()

	start := time.Now()
	b.RunParallel(func(pb *testing.PB) {
		for pb.Next() {
			_ = h.Hit(t)
		}
	})

	took := time.Since(start)
	rate := float64(atomic.LoadUint64(&reqs)) / took.Seconds()

	b.ReportMetric(rate, "req/s")
}

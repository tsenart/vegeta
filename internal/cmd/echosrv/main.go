package main

import (
	"flag"
	"log"
	"net/http"
	"net/http/httputil"
	"sync/atomic"
	"time"
)

func main() {
	sleep := flag.Duration("sleep", 0, "Time to sleep per request")

	flag.Parse()

	count := uint64(0)
	go func(last time.Time) {
		ticks := time.Tick(time.Second)
		for range ticks {
			rate := float64(atomic.SwapUint64(&count, 0)) / time.Since(last).Seconds()
			last = time.Now()
			log.Printf("Rate: %.3f/s", rate)
		}
	}(time.Now())

	http.ListenAndServe(flag.Arg(0), http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		defer atomic.AddUint64(&count, 1)
		time.Sleep(*sleep)

		bs, _ := httputil.DumpRequest(r, true)
		w.Write(bs)
	}))
}

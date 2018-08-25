package main

import (
	"log"
	"net/http"
	"net/http/httputil"
	"os"
	"sync/atomic"
	"time"
)

func main() {
	count := uint64(0)
	go func(last time.Time) {
		ticks := time.Tick(time.Second)
		for range ticks {
			rate := float64(atomic.SwapUint64(&count, 0)) / time.Since(last).Seconds()
			last = time.Now()
			log.Printf("Rate: %.3f/s", rate)
		}
	}(time.Now())

	http.ListenAndServe(os.Args[1], http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		atomic.AddUint64(&count, 1)
		bs, _ := httputil.DumpRequest(r, true)
		w.Write(bs)
	}))
}

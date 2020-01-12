package main

import (
	"bytes"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"flag"
	"io"
	"log"
	"net/http"
	"net/http/httputil"
	"os"
	"sync/atomic"
	"time"
)

func main() {
	dump := flag.Bool("dump", false, "Dump HTTP requests to stdout")
	sleep := flag.Duration("sleep", 0, "Time to sleep per request")
	work := flag.Int("work", 0, "Artificial work load iteration count")

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

		if _, err := hash(*work); err != nil {
			log.Printf("Error: %s", err)
			w.WriteHeader(http.StatusInternalServerError)
			return
		}

		bs, _ := httputil.DumpRequest(r, true)

		out := io.Writer(w)
		if *dump {
			out = io.MultiWriter(w, os.Stdout)
		}

		_, _ = out.Write(bs)
	}))
}

func hash(n int) (string, error) {
	if n == 0 {
		return "", nil
	}

	var buf bytes.Buffer
	_, err := io.CopyN(&buf, rand.Reader, 1024*1024) // 1MB
	if err != nil {
		return "", err
	}

	data := buf.Bytes()
	for i := 0; i < n; i++ {
		hash := sha256.Sum256(data)
		data = hash[:]
	}

	return base64.URLEncoding.EncodeToString(data), nil
}

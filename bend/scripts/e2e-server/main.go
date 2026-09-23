// Test server for bend/scripts/e2e.sh. Listens on 127.0.0.1:$PORT with a
// 50ms idle timeout (so pooled keep-alive connections go stale between
// slow hits) and counts requests per path, served at /stats.
package main

import (
	"fmt"
	"net/http"
	"os"
	"sort"
	"strings"
	"sync"
	"time"
)

func main() {
	var mu sync.Mutex
	counts := map[string]int{}
	count := func(h http.HandlerFunc) http.HandlerFunc {
		return func(w http.ResponseWriter, r *http.Request) {
			mu.Lock()
			counts[r.URL.Path]++
			mu.Unlock()
			h(w, r)
		}
	}
	mux := http.NewServeMux()
	mux.HandleFunc("/ok", count(func(w http.ResponseWriter, r *http.Request) { w.Write([]byte("ok\n")) }))
	mux.HandleFunc("/big", count(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Length", "1048576")
		w.Write([]byte(strings.Repeat("x", 1<<20)))
	}))
	mux.HandleFunc("/chunked", count(func(w http.ResponseWriter, r *http.Request) {
		f := w.(http.Flusher)
		for i := 0; i < 3; i++ {
			w.Write([]byte("0123456789"))
			f.Flush()
		}
	}))
	mux.HandleFunc("/500", count(func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(500)
		w.Write([]byte("boom"))
	}))
	mux.HandleFunc("/slow", count(func(w http.ResponseWriter, r *http.Request) {
		time.Sleep(2 * time.Second)
		w.Write([]byte("late"))
	}))
	mux.HandleFunc("/redirect", count(func(w http.ResponseWriter, r *http.Request) { http.Redirect(w, r, "/ok", http.StatusFound) }))
	mux.HandleFunc("/close", count(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Connection", "close")
		w.Write([]byte("bye"))
	}))
	mux.HandleFunc("/echo", count(func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprintf(w, "X-T=%s seq=%s attack=%s body=%s", r.Header.Get("X-T"), r.Header.Get("X-Vegeta-Seq"), r.Header.Get("X-Vegeta-Attack"), fmt.Sprint(r.ContentLength))
	}))
	mux.HandleFunc("/stats", func(w http.ResponseWriter, r *http.Request) {
		mu.Lock()
		defer mu.Unlock()
		keys := make([]string, 0, len(counts))
		for k := range counts {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, k := range keys {
			fmt.Fprintf(w, "%s %d\n", k, counts[k])
		}
	})
	srv := &http.Server{Addr: "127.0.0.1:" + os.Getenv("PORT"), Handler: mux, IdleTimeout: 50 * time.Millisecond}
	if err := srv.ListenAndServe(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

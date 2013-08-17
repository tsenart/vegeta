package main

import (
	"bytes"
	"net/http"
	"net/http/httptest"
	"os"
	"sync/atomic"
	"testing"
	"time"
)

func TestAttackRate(t *testing.T) {
	hitCount := uint64(0)
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			atomic.AddUint64(&hitCount, 1)
		}),
	)
	targets, err := NewTargets(bytes.NewBufferString("GET " + server.URL + "\n"))
	if err != nil {
		t.Fatal(err)
	}
	rate := uint64(5000)
	rep := NewTextReporter()
	attack(targets, "random", rate, 1*time.Second, rep)
	if hits := atomic.LoadUint64(&hitCount); hits != rate {
		rep.Report(os.Stdout)
		t.Fatalf("Wrong number of hits: want %d, got %d\n", rate, hits)
	}
}

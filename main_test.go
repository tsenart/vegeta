package main

import (
	"bytes"
	"net/http"
	"net/http/httptest"
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
	attack(targets, "random", 50, 1*time.Second, NewTextReporter())
	if hits := atomic.LoadUint64(&hitCount); hits != 50 {
		t.Fatalf("Wrong number of hits: want %d, got %d\n", 50, hits)
	}
}

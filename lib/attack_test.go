package vegeta

import (
	"net/http"
	"net/http/httptest"
	"strings"
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
	request, _ := http.NewRequest("GET", server.URL, nil)
	rate := uint64(5000)
	Attack(Targets{request}, rate, 1*time.Second)
	if hits := atomic.LoadUint64(&hitCount); hits != rate {
		t.Fatalf("Wrong number of hits: want %d, got %d\n", rate, hits)
	}
}

func TestClientCertConfig(t *testing.T) {
	server := httptest.NewTLSServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}),
	)
	request, _ := http.NewRequest("GET", server.URL, nil)
	results := make(chan Result, 1)
	hit(request, results)
	result := <-results
	if strings.Contains(result.Error, "x509: certificate signed by unknown authority") {
		t.Errorf("Invalid certificates should be ignored: Got `%s`", result.Error)
	}
}

package vegeta

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"net"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync/atomic"
	"testing"
	"time"
)

func TestAttackRate(t *testing.T) {
	t.Parallel()

	hitCount := uint64(0)
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			atomic.AddUint64(&hitCount, 1)
		}),
	)

	rate := uint64(1000)
	target := &Target{Method: "GET", URL: server.URL}
	tch, errch := NewTargetProducer(rate, 1*time.Second, func(tch chan<- *Target) error {
		tch <- target
		return nil
	})

	Attack(tch, rate)
	if hits := atomic.LoadUint64(&hitCount); hits != rate {
		t.Fatalf("Wrong number of hits: want %d, got %d\n", rate, hits)
	}
	if err := <-errch; err != nil {
		t.Fatal(err)
	}
}

func NewURLGenerator(n int, target *Target) <-chan *Target {
	tch := make(chan *Target)
	go func() {
		for i := 0; i < n; i++ {
			tch <- target
		}
		close(tch)
	}()
	return tch
}

func TestAttackBody(t *testing.T) {
	t.Parallel()

	want := []byte("VEGETA!")
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			got, err := ioutil.ReadAll(r.Body)
			if err != nil {
				t.Fatal(err)
			}
			if !bytes.Equal(want, got) {
				t.Fatalf("Wrong body. Want: %s, Got: %s", want, got)
			}
		}),
	)

	target := &Target{Method: "GET", URL: server.URL, Body: want}
	Attack(NewURLGenerator(100, target), 1)
}

func TestDefaultAttackerCertConfig(t *testing.T) {
	t.Parallel()

	server := httptest.NewTLSServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}),
	)
	request, _ := http.NewRequest("GET", server.URL, nil)
	_, err := DefaultAttacker.Do(request)
	if err != nil && strings.Contains(err.Error(), "x509: certificate signed by unknown authority") {
		t.Errorf("Invalid certificates should be ignored: Got `%s`", err)
	}
}

func TestRedirects(t *testing.T) {
	t.Parallel()

	var servers [2]*httptest.Server
	var hits uint64

	for i := range servers {
		servers[i] = httptest.NewServer(
			http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				atomic.AddUint64(&hits, 1)
				http.Redirect(w, r, servers[(i+1)%2].URL, 302)
			}),
		)
	}

	atk := NewAttacker(2, DefaultTimeout, DefaultLocalAddr, DefaultTLSConfig)
	tgt := &Target{Method: "GET", URL: servers[0].URL}

	var rate uint64 = 10
	results := atk.Attack(NewURLGenerator(10, tgt), 1)

	want := fmt.Sprintf("stopped after %d redirects", 2)
	for _, result := range results {
		if !strings.Contains(result.Error, want) {
			t.Fatalf("Expected error to be: %s, Got: %s", want, result.Error)
		}
	}

	if want, got := rate*(2+1), hits; want != got {
		t.Fatalf("Expected hits to be: %d, Got: %d", want, got)
	}
}

func TestTimeout(t *testing.T) {
	t.Parallel()

	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			<-time.After(20 * time.Millisecond)
		}),
	)

	atk := NewAttacker(DefaultRedirects, 10*time.Millisecond, DefaultLocalAddr, DefaultTLSConfig)

	tgt := &Target{Method: "GET", URL: server.URL}

	results := atk.Attack(NewURLGenerator(10, tgt), 1)

	want := "net/http: timeout awaiting response headers"
	for _, result := range results {
		if !strings.Contains(result.Error, want) {
			t.Fatalf("Expected error to be: %s, Got: %s", want, result.Error)
		}
	}
}

func TestLocalAddr(t *testing.T) {
	t.Parallel()

	addr, err := net.ResolveIPAddr("ip", "127.0.0.1")
	if err != nil {
		t.Fatal(err)
	}

	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			host, _, err := net.SplitHostPort(r.RemoteAddr)
			if err != nil {
				t.Fatal(err)
			}

			if host != addr.String() {
				t.Fatalf("Wrong source address. Want %s, Got %s", addr, host)
			}
		}),
	)

	atk := NewAttacker(DefaultRedirects, DefaultTimeout, *addr, DefaultTLSConfig)
	tgt := &Target{Method: "GET", URL: server.URL}

	for _, result := range atk.Attack(NewURLGenerator(10, tgt), 1) {
		if result.Error != "" {
			t.Fatal(result.Error)
		}
	}
}

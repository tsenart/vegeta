package vegeta

import (
	"crypto/tls"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"reflect"
	"strings"
	"testing"
	"time"
)

func TestAttackRate(t *testing.T) {
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}),
	)
	tr := NewStaticTargeter(&Target{Method: "GET", URL: server.URL})
	rate := uint64(100)
	atk := NewAttacker()
	var hits uint64
	for _ = range atk.Attack(tr, rate, 1*time.Second) {
		hits++
	}
	if got, want := hits, rate; got != want {
		t.Fatalf("got: %v, want: %v", rate, hits)
	}
}

func TestTLSConfig(t *testing.T) {
	atk := NewAttacker()
	got := atk.client.Transport.(*http.Transport).TLSClientConfig
	if want := (&tls.Config{InsecureSkipVerify: true}); !reflect.DeepEqual(got, want) {
		t.Fatalf("got: %+v, want: %+v", got, want)
	}
}

func TestRedirects(t *testing.T) {
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			http.Redirect(w, r, "/redirect", 302)
		}),
	)
	redirects := 2
	atk := NewAttacker(Redirects(redirects))
	tr := NewStaticTargeter(&Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, time.Now())
	want := fmt.Sprintf("stopped after %d redirects", redirects)
	if got := res.Error; !strings.HasSuffix(got, want) {
		t.Fatalf("want: '%v' in '%v'", want, got)
	}
}

func TestNoFollow(t *testing.T) {
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			http.Redirect(w, r, "/redirect-here", 302)
		}),
	)
	atk := NewAttacker(Redirects(NoFollow))
	tr := NewStaticTargeter(&Target{Method: "GET", URL: server.URL})
	if res := atk.hit(tr, time.Now()); res.Error != "" {
		t.Fatalf("got err: %v", res.Error)
	}
}

func TestTimeout(t *testing.T) {
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			<-time.After(20 * time.Millisecond)
		}),
	)
	atk := NewAttacker(Timeout(10 * time.Millisecond))
	tr := NewStaticTargeter(&Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, time.Now())
	want := "net/http: timeout awaiting response headers"
	if got := res.Error; !strings.HasSuffix(got, want) {
		t.Fatalf("want: '%v' in '%v'", want, got)
	}
}

func TestLocalAddr(t *testing.T) {
	addr, err := net.ResolveIPAddr("ip", "127.0.0.1")
	if err != nil {
		t.Fatal(err)
	}
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			if got, _, err := net.SplitHostPort(r.RemoteAddr); err != nil {
				t.Fatal(err)
			} else if want := addr.String(); got != want {
				t.Fatalf("wrong source address. got %v, want: %v", got, want)
			}
		}),
	)
	atk := NewAttacker(LocalAddr(*addr))
	tr := NewStaticTargeter(&Target{Method: "GET", URL: server.URL})
	atk.hit(tr, time.Now())
}

func TestKeepAlive(t *testing.T) {
	atk := NewAttacker(KeepAlive(false))
	if got, want := atk.dialer.KeepAlive, time.Duration(0); got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
	got := atk.client.Transport.(*http.Transport).DisableKeepAlives
	if want := true; got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestConnections(t *testing.T) {
	atk := NewAttacker(Connections(23))
	got := atk.client.Transport.(*http.Transport).MaxIdleConnsPerHost
	if want := 23; got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestStatusCodeErrors(t *testing.T) {
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			w.WriteHeader(http.StatusBadRequest)
		}),
	)
	atk := NewAttacker()
	tr := NewStaticTargeter(&Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, time.Now())
	if got, want := res.Error, "400 Bad Request"; got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestBadTargeterError(t *testing.T) {
	atk := NewAttacker()
	tr := func() (*Target, error) { return nil, io.EOF }
	res := atk.hit(tr, time.Now())
	if got, want := res.Error, io.EOF.Error(); got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

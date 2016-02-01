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
	t.Parallel()
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}),
	)
	atk := NewAttacker()
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	ps := Phases{{Rate: 100}, {At: time.Second}}

	var got uint64
	for range atk.Attack(tr, ps...) {
		got++
	}

	var want uint64
	for _, hits := range ps.Hits() {
		want += hits
	}

	if got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestAttackDuration_Infinity(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}),
	)
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	atk := NewAttacker()
	time.AfterFunc(2*time.Second, func() { t.Fatal("Timed out") })

	ps, hits := Phases{{Rate: 100}}, uint64(0)
	for range atk.Attack(tr, ps...) {
		if hits++; hits == 150 { // 1.5s
			atk.Stop()
			break
		}
	}

	if got, want := hits, uint64(150); got != want {
		t.Fatalf("got: %+v, want: %+v", got, want)
	}
}

func TestTLSConfig(t *testing.T) {
	t.Parallel()
	atk := NewAttacker()
	got := atk.client.Transport.(*http.Transport).TLSClientConfig
	if want := (&tls.Config{InsecureSkipVerify: true}); !reflect.DeepEqual(got, want) {
		t.Fatalf("got: %+v, want: %+v", got, want)
	}
}

func TestRedirects(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			http.Redirect(w, r, "/redirect", 302)
		}),
	)
	redirects := 2
	atk := NewAttacker(Redirects(redirects))
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, time.Now())
	want := fmt.Sprintf("stopped after %d redirects", redirects)
	if got := res.Error; !strings.HasSuffix(got, want) {
		t.Fatalf("want: '%v' in '%v'", want, got)
	}
}

func TestNoFollow(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			http.Redirect(w, r, "/redirect-here", 302)
		}),
	)
	atk := NewAttacker(Redirects(NoFollow))
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	if res := atk.hit(tr, time.Now()); res.Error != "" {
		t.Fatalf("got err: %v", res.Error)
	}
}

func TestTimeout(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			<-time.After(20 * time.Millisecond)
		}),
	)
	atk := NewAttacker(Timeout(10 * time.Millisecond))
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, time.Now())
	want := "net/http: timeout awaiting response headers"
	if got := res.Error; !strings.HasSuffix(got, want) {
		t.Fatalf("want: '%v' in '%v'", want, got)
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
			if got, _, err := net.SplitHostPort(r.RemoteAddr); err != nil {
				t.Fatal(err)
			} else if want := addr.String(); got != want {
				t.Fatalf("wrong source address. got %v, want: %v", got, want)
			}
		}),
	)
	atk := NewAttacker(LocalAddr(*addr))
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	atk.hit(tr, time.Now())
}

func TestKeepAlive(t *testing.T) {
	t.Parallel()
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
	t.Parallel()
	atk := NewAttacker(Connections(23))
	got := atk.client.Transport.(*http.Transport).MaxIdleConnsPerHost
	if want := 23; got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestStatusCodeErrors(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			w.WriteHeader(http.StatusBadRequest)
		}),
	)
	atk := NewAttacker()
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, time.Now())
	if got, want := res.Error, "400 Bad Request"; got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestBadTargeterError(t *testing.T) {
	t.Parallel()
	atk := NewAttacker()
	tr := func(*Target) error { return io.EOF }
	res := atk.hit(tr, time.Now())
	if got, want := res.Error, io.EOF.Error(); got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestPhases_Hits(t *testing.T) {
	t.Parallel()
	for i, tc := range []struct {
		Phases
		hits []uint64
	}{
		{nil, []uint64{}},
		{Phases{}, []uint64{}},
		{Phases{{50, 0}}, []uint64{0}},
		{Phases{{50, 0}, {50, 0}}, []uint64{0}},
		{Phases{{50, 0}, {50, 1e9}}, []uint64{50}},
		{Phases{{50, 0}, {50, 1e9}, {100, 2e9}}, []uint64{50, 50}},
		{Phases{{50, 0}, {50, 1e9}, {100, 2e9}, {100, 4e9}}, []uint64{50, 50, 200}},
	} {
		if got, want := tc.Hits(), tc.hits; !reflect.DeepEqual(got, want) {
			t.Errorf("test #%d: %+v.Hits(): got %v, want %v", i, tc.Phases, got, want)
		}
	}
}

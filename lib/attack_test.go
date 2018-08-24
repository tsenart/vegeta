package vegeta

import (
	"bytes"
	"crypto/tls"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
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
	defer server.Close()
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	rate := Rate{Freq: 100, Per: time.Second}
	atk := NewAttacker()
	var hits uint64
	for range atk.Attack(tr, rate, 1*time.Second, "") {
		hits++
	}
	if got, want := hits, uint64(rate.Freq); got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestAttackDuration(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}),
	)
	defer server.Close()
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	atk := NewAttacker()
	time.AfterFunc(2*time.Second, func() { t.Fatal("Timed out") })

	rate := Rate{Freq: 100, Per: time.Second}
	hits := uint64(0)
	for range atk.Attack(tr, rate, 0, "") {
		if hits++; hits == 100 {
			atk.Stop()
			break
		}
	}

	if got, want := hits, uint64(rate.Freq); got != want {
		t.Fatalf("got: %v, want: %v", got, want)
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
	defer server.Close()
	redirects := 2
	atk := NewAttacker(Redirects(redirects))
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, "")
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
	defer server.Close()
	atk := NewAttacker(Redirects(NoFollow))
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, "")
	if res.Error != "" {
		t.Fatalf("got err: %v", res.Error)
	}
	if res.Code != 302 {
		t.Fatalf("res.Code => %d, want %d", res.Code, 302)
	}
}

func TestTimeout(t *testing.T) {
	t.Parallel()
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			<-time.After(20 * time.Millisecond)
		}),
	)
	defer server.Close()
	atk := NewAttacker(Timeout(10 * time.Millisecond))
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, "")
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
	defer server.Close()
	atk := NewAttacker(LocalAddr(*addr))
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	atk.hit(tr, "")
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
	defer server.Close()
	atk := NewAttacker()
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, "")
	if got, want := res.Error, "400 Bad Request"; got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestBadTargeterError(t *testing.T) {
	t.Parallel()
	atk := NewAttacker()
	tr := func(*Target) error { return io.EOF }
	res := atk.hit(tr, "")
	if got, want := res.Error, io.EOF.Error(); got != want {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestResponseBodyCapture(t *testing.T) {
	t.Parallel()

	want := []byte("VEGETA")
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			w.Write(want)
		}),
	)
	defer server.Close()
	atk := NewAttacker()
	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	res := atk.hit(tr, "")
	if got := res.Body; !bytes.Equal(got, want) {
		t.Fatalf("got: %v, want: %v", got, want)
	}
}

func TestProxyOption(t *testing.T) {
	t.Parallel()

	body := []byte("PROXIED!")
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			w.Write(body)
		}),
	)
	defer server.Close()

	proxyURL, err := url.Parse(server.URL)
	if err != nil {
		t.Fatal(err)
	}

	atk := NewAttacker(Proxy(func(r *http.Request) (*url.URL, error) {
		return proxyURL, nil
	}))

	tr := NewStaticTargeter(Target{Method: "GET", URL: "http://127.0.0.2"})
	res := atk.hit(tr, "")
	if got, want := res.Error, ""; got != want {
		t.Errorf("got error: %q, want %q", got, want)
	}

	if got, want := res.Body, body; !bytes.Equal(got, want) {
		t.Errorf("got body: %q, want: %q", got, want)
	}
}

func TestMaxBody(t *testing.T) {
	t.Parallel()

	body := []byte("VEGETA")
	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			w.Write(body)
		}),
	)
	defer server.Close()

	for i := DefaultMaxBody; i < int64(len(body)); i++ {
		maxBody := i
		t.Run(fmt.Sprint(maxBody), func(t *testing.T) {
			atk := NewAttacker(MaxBody(maxBody))
			tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
			res := atk.hit(tr, "")

			want := body
			if maxBody >= 0 {
				want = want[:maxBody]
			}

			if got := res.Body; !bytes.Equal(got, want) {
				t.Fatalf("got: %s, want: %s", got, want)
			}
		})
	}
}

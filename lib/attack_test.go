package vegeta

import (
	"bytes"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"io/ioutil"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"path/filepath"
	"reflect"
	"strconv"
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
	rate := Rate{Freq: 100, Per: time.Second}

	var m Metrics
	for res := range atk.Attack(tr, rate, rate.Per, "") {
		m.Add(res)
	}
	m.Close()

	if got, want := m.Requests, uint64(rate.Freq); got != want {
		t.Errorf("got %v hits, want: %v", got, want)
	} else if got, want := m.Duration.Round(time.Second), time.Second; got != want {
		t.Errorf("got duration %s, want %s", got, want)
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

	want := "Client.Timeout exceeded while awaiting headers"
	if got := res.Error; !strings.Contains(got, want) {
		t.Fatalf("want: '%v' in '%v'", want, got)
	}

	if res.Latency == 0 {
		t.Fatal("Latency wasn't captured with a timed-out result")
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

func TestUnixSocket(t *testing.T) {
	t.Parallel()
	body := []byte("IT'S A UNIX SYSTEM, I KNOW THIS")

	socketDir, err := ioutil.TempDir("", "vegata")
	if err != nil {
		t.Fatal("Failed to create socket dir", err)
	}
	defer os.RemoveAll(socketDir)
	socketFile := filepath.Join(socketDir, "test.sock")

	unixListener, err := net.Listen("unix", socketFile)

	if err != nil {
		t.Fatal("Failed to listen on unix socket", err)
	}

	server := http.Server{
		Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			w.Write(body)
		}),
	}
	defer server.Close()

	go server.Serve(unixListener)

	start := time.Now()
	for {
		if time.Since(start) > 1*time.Second {
			t.Fatal("Server didn't listen on unix socket in time")
		}
		_, err := os.Stat(socketFile)
		if err == nil {
			break
		} else if os.IsNotExist(err) {
			time.Sleep(10 * time.Millisecond)
		} else {
			t.Fatal("unexpected error from unix socket", err)
		}
	}

	atk := NewAttacker(UnixSocket(socketFile))

	tr := NewStaticTargeter(Target{Method: "GET", URL: "http://anyserver/"})
	res := atk.hit(tr, "")
	if !bytes.Equal(res.Body, body) {
		t.Fatalf("got: %s, want: %s", string(res.Body), string(body))
	}
}

func TestClient(t *testing.T) {
	t.Parallel()

	dialer := &net.Dialer{
		LocalAddr: &net.TCPAddr{IP: DefaultLocalAddr.IP, Zone: DefaultLocalAddr.Zone},
		KeepAlive: 30 * time.Second,
	}

	client := &http.Client{
		Timeout: time.Duration(1 * time.Nanosecond),
		Transport: &http.Transport{
			Proxy:               http.ProxyFromEnvironment,
			Dial:                dialer.Dial,
			TLSClientConfig:     DefaultTLSConfig,
			MaxIdleConnsPerHost: DefaultConnections,
		},
	}

	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			select {}
		}),
	)
	defer server.Close()

	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})

	atk := NewAttacker(Client(client))
	resp := atk.hit(tr, "TEST")
	if !strings.Contains(resp.Error, "Client.Timeout exceeded while awaiting headers") {
		t.Errorf("Expected timeout error")
	}
}

func TestVegetaHeaders(t *testing.T) {
	t.Parallel()

	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			_ = json.NewEncoder(w).Encode(r.Header)
		}),
	)

	defer server.Close()

	tr := NewStaticTargeter(Target{Method: "GET", URL: server.URL})
	atk := NewAttacker()

	for seq := 0; seq < 5; seq++ {
		attack := "big-bang"
		res := atk.hit(tr, attack)

		var hdr http.Header
		if err := json.Unmarshal(res.Body, &hdr); err != nil {
			t.Fatal(err)
		}

		if have, want := hdr.Get("X-Vegeta-Attack"), attack; have != want {
			t.Errorf("X-Vegeta-Attack: have %q, want %q", have, want)
		}

		if have, want := hdr.Get("X-Vegeta-Seq"), strconv.Itoa(seq); have != want {
			t.Errorf("X-Vegeta-Seq: have %q, want %q", have, want)
		}
	}
}

package resolver

import (
	"fmt"
	"io/ioutil"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/miekg/dns"
)

const (
	dnsmasqPortEnv = "VEGETA_TESTDNSMASQ_PORT"
	fakeDomain     = "acme.notadomain"
)

func TestResolveMiekg(t *testing.T) {

	dns.HandleFunc(".", func(w dns.ResponseWriter, r *dns.Msg) {
		m := &dns.Msg{}
		m.SetReply(r)
		localIP := net.ParseIP("127.0.0.1")
		defer func() {
			err := w.WriteMsg(m)
			if err != nil {
				t.Logf("got error writing dns message: %s", err)
			}
		}()
		if len(r.Question) == 0 {
			m.RecursionAvailable = true
			m.SetRcode(r, dns.RcodeRefused)
			return
		}

		q := r.Question[0]

		if q.Name == fakeDomain+"." {
			m.Answer = []dns.RR{&dns.A{
				Hdr: dns.RR_Header{
					Name:   q.Name,
					Rrtype: dns.TypeA,
					Class:  dns.ClassINET,
					Ttl:    1,
				},
				A: localIP,
			}}
		} else {
			m.SetRcode(r, dns.RcodeNameError)
		}
	})
	const payload = "there is no cloud, just someone else's computer"

	var (
		port = "5300"
	)

	if ePort, ok := os.LookupEnv(dnsmasqPortEnv); ok {
		port = ePort
	}

	ds := dns.Server{
		Addr:         fmt.Sprintf("%s:%s", "127.0.0.1", port),
		Net:          "udp",
		UDPSize:      dns.MinMsgSize,
		ReadTimeout:  2 * time.Second,
		WriteTimeout: 2 * time.Second,
		// Unsafe instructs the server to disregard any sanity checks and directly hand the message to
		// the handler. It will specifically not check if the query has the QR bit not set.
		Unsafe: false,
	}
	go func() {
		err := ds.ListenAndServe()
		if err != nil {
			t.Logf("got error during dns ListenAndServe: %s", err)
		}
	}()

	defer func() {
		_ = ds.Shutdown()
	}()

	res, err := NewResolver([]string{net.JoinHostPort("127.0.0.1", port)})
	if err != nil {
		t.Errorf("error from NewResolver: %s", err)
		return
	}
	net.DefaultResolver = res

	ts := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprintln(w, payload)
	}))
	defer ts.Close()

	tsurl, _ := url.Parse(ts.URL)

	_, hport, err := net.SplitHostPort(tsurl.Host)
	if err != nil {
		t.Errorf("could not parse port from httptest url %s: %s", ts.URL, err)
		return
	}
	tsurl.Host = net.JoinHostPort(fakeDomain, hport)
	resp, err := http.Get(tsurl.String())
	if err != nil {
		t.Errorf("failed resolver round trip: %s", err)
		return
	}
	body, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		t.Errorf("failed to read respose body")
		return
	}
	if strings.TrimSpace(string(body)) != payload {
		t.Errorf("body mismatch, got: '%s', expected: '%s'", body, payload)
	}
}

func TestResolveAddresses(t *testing.T) {
	table := map[string]struct {
		input          []string
		want           []string
		expectError    bool
		expectMismatch bool
	}{
		"Good list": {
			input: []string{
				"8.8.8.8:53",
				"9.9.9.9:1234",
				"2.3.4.5",
			},
			want: []string{
				"8.8.8.8:53",
				"9.9.9.9:1234",
				"2.3.4.5:53",
			},
			expectError:    false,
			expectMismatch: false,
		},
		"Mismatch list": {
			input: []string{
				"9.9.9.9:1234",
			},
			want: []string{
				"9.9.9.9:53",
			},
			expectError:    false,
			expectMismatch: true,
		},
		"Parse error list": {
			input: []string{
				"abcd.com:53",
			},
			expectError: true,
		},
	}
	for subtest, tdata := range table {
		t.Run(subtest, func(t *testing.T) {
			addrs, err := normalizeAddrs(tdata.input)
			if tdata.expectError {
				if err == nil {
					t.Error("expected error, got none")
				}
				return

			}

			if err != nil {
				t.Errorf("expected nil error, got: %s", err)
				return
			}

			match := true
			if len(tdata.want) != len(addrs) {
				match = false
			} else {
				for i, addr := range addrs {
					if addr != tdata.want[i] {
						match = false
						break
					}
				}
			}
			if !tdata.expectMismatch && !match {
				t.Errorf("unexpected mismatch, input: %#v, want: %#v", addrs, tdata.want)
			}

		})
	}

}

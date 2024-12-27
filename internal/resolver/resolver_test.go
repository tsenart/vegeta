package resolver

import (
	"errors"
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

	"github.com/miekg/dns"
)

const (
	fakeDomain = "acme.notadomain"
)

func TestResolver(t *testing.T) {
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

	done := make(chan struct{})

	ds := dns.Server{
		Addr:              "127.0.0.1:0",
		Net:               "udp",
		UDPSize:           dns.MinMsgSize,
		ReadTimeout:       2 * time.Second,
		WriteTimeout:      2 * time.Second,
		NotifyStartedFunc: func() { close(done) },
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

	// wait for notify function to be called, ensuring ds.PacketConn is not nil.
	<-done

	res, err := NewResolver([]string{ds.PacketConn.LocalAddr().String()})
	if err != nil {
		t.Fatalf("error from NewResolver: %s", err)
	}
	net.DefaultResolver = res

	ts := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		fmt.Fprintln(w, payload)
	}))
	defer ts.Close()

	tsurl, _ := url.Parse(ts.URL)

	_, hport, err := net.SplitHostPort(tsurl.Host)
	if err != nil {
		t.Fatalf("could not parse port from httptest url %s: %s", ts.URL, err)
	}
	tsurl.Host = net.JoinHostPort(fakeDomain, hport)
	resp, err := http.Get(tsurl.String())
	if err != nil {
		t.Fatalf("failed resolver round trip: %s", err)
	}
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		t.Fatalf("failed to read response body")
	}
	if strings.TrimSpace(string(body)) != payload {
		t.Errorf("body mismatch, got: '%s', expected: '%s'", body, payload)
	}
}

func TestNormalizeAddrs(t *testing.T) {
	for _, tc := range []struct {
		name string
		in   []string
		out  []string
		err  error
	}{
		{
			name: "default port 53",
			in:   []string{"127.0.0.1"},
			out:  []string{"127.0.0.1:53"},
		},
		{
			name: "invalid host port",
			in:   []string{"127.0.0.1.boom:53"},
			err:  errors.New("host 127.0.0.1.boom is not an IP address"),
		},
		{
			name: "invalid port",
			in:   []string{"127.0.0.1:999999999"},
			err:  errors.New(`strconv.ParseUint: parsing "999999999": value out of range`),
		},
		{
			name: "invalid IP",
			in:   []string{"127.0.0.500:53"},
			err:  errors.New(`host 127.0.0.500 is not an IP address`),
		},
		{
			name: "normalized",
			in:   []string{"127.0.0.1", "8.8.8.8:9000", "1.1.1.1"},
			out:  []string{"127.0.0.1:53", "8.8.8.8:9000", "1.1.1.1:53"},
		},
	} {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()

			addrs, err := normalizeAddrs(tc.in)
			if have, want := addrs, tc.out; !reflect.DeepEqual(have, want) {
				t.Errorf("have addrs: %v, want: %v", have, want)
			}

			if have, want := fmt.Sprint(err), fmt.Sprint(tc.err); have != want {
				t.Errorf("have err: %v, want: %v", have, want)
			}
		})
	}

}

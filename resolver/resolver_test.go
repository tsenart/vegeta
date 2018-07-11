package resolver

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"os"
	"os/exec"
	"strings"
	"testing"
	"time"
)

const (
	dnsmasqRunEnv  = "VEGETA_TESTDNSMASQ_ENABLE"
	dnsmasqPathEnv = "VEGETA_TESTDNSMASQ_PATH"
	dnsmasqPortEnv = "VEGETA_TESTDNSMASQ_PORT"
)

func TestResolveDNSMasq(t *testing.T) {
	const payload = "there is no cloud, just someone else's computer"

	var (
		path = "dnsmasq"
		port = "5300"
	)
	if _, ok := os.LookupEnv(dnsmasqRunEnv); !ok {
		t.Skipf("skipping test becuase %s is not set", dnsmasqRunEnv)
	}
	if ePort, ok := os.LookupEnv(dnsmasqPortEnv); ok {
		port = ePort
	}
	if ePath, ok := os.LookupEnv(dnsmasqPathEnv); ok {
		path = ePath
	}

	stdout := bytes.Buffer{}
	stderr := bytes.Buffer{}
	cmd := exec.Command(path, "-h", "-H", "./hosts", "-p", port, "-d")

	cmd.Stdout = &stdout
	cmd.Stderr = &stderr

	err := cmd.Start()
	if err != nil {
		t.Fatalf("failed starting dnsmasq: %s", err)
	}
	defer func() {
		err := cmd.Wait()
		if err != nil {
			t.Logf("unclean shutdown of dnsmasq: %s", err)
		}
		t.Log(stdout.String())
		t.Log(stderr.String())
	}()
	time.Sleep(time.Second)

	defer func() {
		_ = cmd.Process.Kill()
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
	tsurl.Host = net.JoinHostPort("acme.notadomain", hport)
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

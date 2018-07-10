package vegeta

import (
	"net"
	"net/http"
	"testing"
)

func TestResolve8888(t *testing.T) {
	r, err := NewResolver([]string{"8.8.8.8:53"})
	if err != nil {
		t.FailNow()
	}

	net.DefaultResolver = r

	resp, err := http.Get("https://www.google.com/")

	if err != nil {
		t.Logf("error from http.Get(): %s", err)
		t.FailNow()
	}

	resp.Body.Close()
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
			addrs, err := normalizeResolverAddresses(tdata.input)
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

func TestResolverOverflow(t *testing.T) {
	res := &resolver{
		addresses: []string{"8.8.8.8:53", "9.9.9.9:53"},
		idx:       ^uint64(0),
	}
	_ = res.address()
	if res.idx != 0 {
		t.Error("overflow not handled gracefully")
	}
	// throw away another one to make sure we're back to 0
	_ = res.address()
	for i := 0; i < 5; i++ {
		addr := res.address()
		if expectedAddr := res.addresses[i%len(res.addresses)]; expectedAddr != addr {
			t.Errorf("address mismatch, have: %s, want: %s", addr, expectedAddr)
		}
	}
}

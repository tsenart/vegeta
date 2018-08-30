package resolver

import (
	"context"
	"errors"
	"fmt"
	"net"
	"strconv"
	"strings"
	"sync/atomic"
)

type resolver struct {
	addrs  []string
	dialer *net.Dialer
	idx    uint64
}

// NewResolver - create a new instance of a dns resolver for plugging
// into net.DefaultResolver.  Addresses should be a list of
// ip addrs and optional port numbers, separated by colon.
// For example: 1.2.3.4:53 and 1.2.3.4 are both valid.  In the absence
// of a port number, 53 will be used instead.
func NewResolver(addrs []string) (*net.Resolver, error) {
	if len(addrs) == 0 {
		return nil, errors.New("must specify at least resolver address")
	}
	cleanAddrs, err := normalizeAddrs(addrs)
	if err != nil {
		return nil, err
	}
	return &net.Resolver{
		PreferGo: true,
		Dial:     (&resolver{addrs: cleanAddrs, dialer: &net.Dialer{}}).dial,
	}, nil
}

func normalizeAddrs(addrs []string) ([]string, error) {
	normal := make([]string, len(addrs))
	for i, addr := range addrs {

		// if addr has no port, give it 53
		if !strings.Contains(addr, ":") {
			addr += ":53"
		}

		// validate addr is a valid host:port
		host, portstr, err := net.SplitHostPort(addr)
		if err != nil {
			return nil, err
		}

		// validate valid port.
		_, err = strconv.ParseUint(portstr, 10, 16)
		if err != nil {
			return nil, err
		}

		// make sure host is an ip.
		ip := net.ParseIP(host)
		if ip == nil {
			return nil, fmt.Errorf("host %s is not an IP address", host)
		}

		normal[i] = addr
	}
	return normal, nil
}

// ignore the third parameter, as this represents the dns server address that
// we are overriding.
func (r *resolver) dial(ctx context.Context, network, _ string) (net.Conn, error) {
	return r.dialer.DialContext(ctx, network, r.address())
}

func (r *resolver) address() string {
	return r.addrs[atomic.AddUint64(&r.idx, 1)%uint64(len(r.addrs))]
}

package vegeta

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
	addresses []string
	dialer    *net.Dialer
	idx       uint64
}

// NewResolver - create a new instance of a dns resolver for plugging
// into net.DefaultResolver.  Addresses should be a list of
// ip addresses and optional port numbers, separated by colon.
// For example: 1.2.3.4:53 and 1.2.3.4 are both valid.  In the absence
// of a port number, 53 will be used instead.
func NewResolver(addresses []string) (*net.Resolver, error) {
	normalAddresses, err := normalizeResolverAddresses(addresses)
	if err != nil {
		return nil, err
	}
	return &net.Resolver{
		PreferGo: true,
		Dial:     (&resolver{addresses: normalAddresses, dialer: &net.Dialer{}}).dial,
	}, nil
}

func normalizeResolverAddresses(addresses []string) ([]string, error) {
	if len(addresses) == 0 {
		return nil, errors.New("must specify at least resolver address")
	}
	normalAddresses := make([]string, len(addresses))
	for i, addr := range addresses {
		ipPort := strings.Split(addr, ":")
		port := 53
		var host string

		switch len(ipPort) {
		case 2:
			pu16, err := strconv.ParseUint(ipPort[1], 10, 16)
			if err != nil {
				return nil, err
			}
			port = int(pu16)
			fallthrough
		case 1:
			host = ipPort[0]
		default:
			return nil, fmt.Errorf("invalid ip:port specified: %s", addr)

		}
		ip := net.ParseIP(host)
		if ip == nil {
			return nil, fmt.Errorf("host %s is not an IP address", host)
		}

		normalAddresses[i] = fmt.Sprintf("%s:%d", host, port)
	}
	return normalAddresses, nil
}

func (r *resolver) dial(ctx context.Context, network, _ string) (net.Conn, error) {
	return r.dialer.DialContext(ctx, network, r.address())
}

func (r *resolver) address() string {
	var address string
	if l := uint64(len(r.addresses)); l > 1 {
		idx := atomic.AddUint64(&r.idx, 1)
		address = r.addresses[idx%l]
	} else {
		address = r.addresses[0]
	}
	return address
}

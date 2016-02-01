package main

import (
	"bytes"
	"fmt"
	"net"
	"net/http"
	"strconv"
	"strings"
	"time"

	vegeta "github.com/tsenart/vegeta/lib"
)

// headers is the http.Header used in each target request
// it is defined here to implement the flag.Value interface
// in order to support multiple identical flags for request header
// specification
type headers struct{ http.Header }

func (h headers) String() string {
	buf := &bytes.Buffer{}
	if err := h.Write(buf); err != nil {
		return ""
	}
	return buf.String()
}

// Set implements the flag.Value interface for a map of HTTP Headers.
func (h headers) Set(value string) error {
	parts := strings.SplitN(value, ":", 2)
	if len(parts) != 2 {
		return fmt.Errorf("header '%s' has a wrong format", value)
	}
	key, val := strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1])
	if key == "" || val == "" {
		return fmt.Errorf("header '%s' has a wrong format", value)
	}
	// Add key/value directly to the http.Header (map[string][]string).
	// http.Header.Add() cannonicalizes keys but vegeta is used
	// to test systems that require case-sensitive headers.
	h.Header[key] = append(h.Header[key], val)
	return nil
}

// localAddr implements the Flag interface for parsing net.IPAddr
type localAddr struct{ *net.IPAddr }

func (ip *localAddr) Set(value string) (err error) {
	ip.IPAddr, err = net.ResolveIPAddr("ip", value)
	return
}

// csl implements the flag.Value interface for comma separated lists
type csl []string

func (l *csl) Set(v string) error {
	*l = strings.Split(v, ",")
	return nil
}

func (l csl) String() string { return strings.Join(l, ",") }

// phases implements the flag.Value interface for vegeta.Pla
type phases []vegeta.Phase

func (ps *phases) Set(v string) error {
	for _, phase := range strings.Fields(v) {
		if ts := strings.Split(phase, "@"); len(ts) != 2 {
			return fmt.Errorf("missing @ in %q from plan: %q", phase, v)
		} else if rate, err := strconv.ParseUint(ts[0], 10, 64); err != nil {
			return fmt.Errorf("bad rate %q in %q from plan %q", ts[0], phase, v)
		} else if at, err := time.ParseDuration(ts[1]); err != nil {
			return fmt.Errorf("bad time %q in %q from plan %q", ts[1], phase, v)
		} else if len(*ps) > 0 && at <= (*ps)[len(*ps)-1].At {
			return fmt.Errorf("bad timing order in plan %q", v)
		} else {
			*ps = append(*ps, vegeta.Phase{Rate: rate, At: at})
		}
	}
	return nil
}

func (ps phases) String() string {
	ss := make([]string, len(ps))
	for i := range ps {
		ss[i] = ps[i].String()
	}
	return strings.Join(ss, " ")
}

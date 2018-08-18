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
	// http.Header.Add() canonicalizes keys but vegeta is used
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

type rateFlag struct{ *vegeta.Rate }

func (f *rateFlag) Set(v string) (err error) {
	ps := strings.SplitN(v, "/", 2)
	switch len(ps) {
	case 1:
		ps = append(ps, "1s")
	case 0:
		return fmt.Errorf("-rate format %q doesn't match the \"freq/duration\" format (i.e. 50/1s)", v)
	}

	f.Freq, err = strconv.Atoi(ps[0])
	if err != nil {
		return err
	}

	switch ps[1] {
	case "ns", "us", "µs", "ms", "s", "m", "h":
		ps[1] = "1" + ps[1]
	}

	f.Per, err = time.ParseDuration(ps[1])
	return err
}

func (f *rateFlag) String() string {
	if f.Rate == nil {
		return ""
	}
	return fmt.Sprintf("%d/%s", f.Freq, f.Per)
}

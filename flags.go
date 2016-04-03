package main

import (
	"bytes"
	"fmt"
	"net"
	"net/http"
	"strings"
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

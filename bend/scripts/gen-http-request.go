//go:build ignore

// Prints the request texts Go's transport writes for the targets of
// bend/tests/http.bend (run from the repo root: go run
// ./bend/scripts/gen-http-request.go), \r and \n written as \r and \n.
// Requests are built as Vegeta builds them (Target.Request, then
// X-Vegeta-Attack and X-Vegeta-Seq set) and sent by an http.Transport
// with compression off (the port leaves Accept-Encoding out) and
// keep-alives as asked, dialing a local listener that records the bytes.
// Cases marked "differs" print what Go writes where the port (and the
// LAWS) knowingly differ.
package main

import (
	"context"
	"fmt"
	"io"
	"net"
	"net/http"
	"strconv"
	"strings"
	"time"
)

type tc struct {
	method, url string
	hdr         [][2]string
	body        string
	seq         uint64
	name        string
	ka          bool
	note        string
}

var cases = []tc{
	{"GET", "http://example.com:8080/a?b=c", [][2]string{{"X-A", "1"}, {"X-A", "2"}, {"Accept", "*/*"}}, "", 7, "atk", true, ""},
	{"POST", "http://example.com/p", [][2]string{{"Content-Type", "text/plain"}, {"Host", "h.example"}, {"User-Agent", "ua/1"}}, "hello", 0, "", false, ""},
	{"PUT", "http://example.com/a b/c", nil, "", 1, "", true, ""},
	{"DELETE", "http://example.com/x/%7e;p?q=%zz", [][2]string{{"Content-Length", "99"}, {"Transfer-Encoding", "chunked"}, {"Trailer", "X"}, {"Connection", "keep-alive"}}, "", 2, "n", false, ""},
	{"PATCH", "http://example.com/%41%2f", [][2]string{{"x-lower", "v"}}, "", 3, "", true, ""},
	{"GET", "http://example.com/", [][2]string{{"host", "lower"}, {"user-agent", "lower"}}, "", 4, "", true, ""},
	{"GET", "http://example.com/", [][2]string{{"X-Vegeta-Seq", "9"}, {"X-Vegeta-Attack", "old"}, {"Host", "a"}, {"Host", "b"}}, "", 5, "new", true, ""},
	{"GET", "http://example.com/", [][2]string{{"Bad Name", "v"}}, "", 6, "", true, "differs"},
	{"GET", "http://example.com/", [][2]string{{"X-Nl", "a\nb"}}, "", 6, "", true, "differs"},
}

func main() {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		panic(err)
	}
	got := make(chan string)
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			c.SetReadDeadline(time.Now().Add(300 * time.Millisecond))
			b, _ := io.ReadAll(c)
			c.Write([]byte("HTTP/1.1 204 No Content\r\nConnection: close\r\n\r\n"))
			c.Close()
			got <- string(b)
		}
	}()
	for _, t := range cases {
		tr := &http.Transport{
			DisableCompression: true,
			DisableKeepAlives:  !t.ka,
			DialContext: func(ctx context.Context, _, _ string) (net.Conn, error) {
				return net.Dial("tcp", ln.Addr().String())
			},
		}
		var body io.Reader
		if len(t.body) != 0 {
			body = strings.NewReader(t.body)
		}
		req, err := http.NewRequest(t.method, t.url, body)
		if err != nil {
			panic(err)
		}
		for _, kv := range t.hdr {
			req.Header[kv[0]] = append(req.Header[kv[0]], kv[1])
		}
		if host := req.Header.Get("Host"); host != "" {
			req.Host = host
		}
		if t.name != "" {
			req.Header.Set("X-Vegeta-Attack", t.name)
		}
		req.Header.Set("X-Vegeta-Seq", strconv.FormatUint(t.seq, 10))
		errc := make(chan error, 1)
		go func() {
			r, err := (&http.Client{Transport: tr}).Do(req)
			if err == nil {
				r.Body.Close()
			}
			errc <- err
		}()
		var s string
		select {
		case s = <-got:
		case err := <-errc:
			if err != nil {
				s = "error: " + err.Error()
			} else {
				s = <-got
			}
		}
		prefix := "#|"
		if t.note != "" {
			prefix = "# " + t.note + ": "
		}
		fmt.Println(prefix + strings.NewReplacer("\r", `\r`, "\n", `\n`).Replace(s))
	}
}

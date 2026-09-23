//go:build ignore

// Prints the Go lines of bend/tests/conn.bend (run from the repo root:
// go run ./bend/scripts/gen-conn.go). Each case sends one request the way
// Vegeta's attacker does (lib/attack.go: an http.Client with Vegeta's
// CheckRedirect, Client.Timeout, compression off, X-Vegeta-Seq set, the
// body read through -max-body) to a scripted server, and prints
//
//	name|error|body
//
// where error is the result's error text (Go's, or the status line for
// a code outside 2xx/3xx) and body is what the result keeps (the partial
// body on a failure). Then, for the cases that capture them, the raw
// requests the server read, as name>n|request. \r and \n are written as
// \r and \n. Cases with a note print as comments: what Go does where the
// port knowingly differs. Every connection goes to the scripted server
// whatever the host (the dial is redirected), except in the "refused"
// case, which dials 127.0.0.1:1 for real.
package main

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"net"
	"net/http"
	"strconv"
	"strings"
	"sync"
	"time"
)

// a connection's script: it reads the requests it wants (recording them)
// and writes what it wants; returning closes the connection
type script func(k int, c net.Conn, read func() bool)

type tc struct {
	name      string
	method    string
	url       string
	hdr       [][2]string
	body      string
	redirects int // -1: Vegeta's NoFollow
	maxBody   int64
	timeout   time.Duration
	show      bool   // print the requests the server read
	note      string // a case where the port (and the LAWS) knowingly differ: printed as a comment
	warm      bool   // send a first GET / on the connection first (not shown), so the case reuses it
	srv       script
}

// writes w, then stalls past the client's timeout
func stall(c net.Conn, w string) {
	c.Write([]byte(w))
	time.Sleep(400 * time.Millisecond)
}

const ok5 = "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"

var cases = []tc{
	{name: "refused", method: "GET", url: "http://127.0.0.1:1/", redirects: 10, maxBody: -1},
	{name: "eof-fresh", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) { read() }},
	{name: "eof-reused-post", method: "POST", url: "http://h/", body: "x", redirects: 10, maxBody: -1, warm: true, show: true,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte(ok5))
			read()
		}},
	{name: "eof-reused-get", method: "GET", url: "http://h/r", redirects: 10, maxBody: -1, warm: true, show: true,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			if k == 0 {
				c.Write([]byte(ok5))
				read()
				return
			}
			c.Write([]byte(ok5))
		}},
	{name: "late-head", method: "GET", url: "http://h/", redirects: 10, maxBody: -1, timeout: 150 * time.Millisecond,
		srv: func(k int, c net.Conn, read func() bool) { read(); stall(c, "") }},
	{name: "late-body", method: "GET", url: "http://h/", redirects: 10, maxBody: -1, timeout: 150 * time.Millisecond,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			stall(c, "HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nabc")
		}},
	{name: "late-interim", method: "GET", url: "http://h/", redirects: 10, maxBody: -1, timeout: 150 * time.Millisecond,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			stall(c, "HTTP/1.1 103 Early Hints\r\nLink: x\r\n\r\n")
		}},
	{name: "cut-body", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nabc"))
		}},
	{name: "cut-chunked", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n2\r\nd"))
		}},
	{name: "cut-head", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 200 OK\r\nX: 1\r\n"))
		}},
	{name: "cut-status", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 20"))
		}},
	{name: "cut-name", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 200 OK\r\nContent-Le"))
		}},
	{name: "garbage", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			stall(c, "garbage\r\n\r\n")
		}},
	{name: "bad-chunk", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			stall(c, "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabcXY")
		}},
	{name: "not-found", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 404 Not Found\r\nContent-Length: 4\r\n\r\nnope"))
		}},
	{name: "max-body", method: "GET", url: "http://h/", redirects: 10, maxBody: 2,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 200 OK\r\nContent-Length: 8\r\n\r\n12345678"))
		}},
	{name: "stop-0", method: "GET", url: "http://h/", redirects: 0, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			stall(c, "HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 0\r\n\r\n")
		}},
	{name: "stop-1", method: "POST", url: "http://h/a", body: "b", redirects: 1, maxBody: -1, show: true,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 302 Found\r\nLocation: /b\r\nContent-Length: 0\r\n\r\n"))
			read()
			stall(c, "HTTP/1.1 301 Moved Permanently\r\nLocation: c?q=1\r\nContent-Length: 0\r\n\r\n")
		}},
	{name: "nofollow", method: "GET", url: "http://h/", redirects: -1, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 2\r\n\r\nmv"))
		}},
	{name: "follow-303", method: "POST", url: "http://h/a/b", body: "data",
		hdr:       [][2]string{{"Authorization", "t"}, {"Content-Type", "text/plain"}},
		redirects: 10, maxBody: -1, show: true,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 303 See Other\r\nLocation: ../c\r\nContent-Length: 3\r\n\r\nabc"))
			read()
			c.Write([]byte(ok5))
		}},
	{name: "follow-307-other", method: "PUT", url: "http://h/", body: "data",
		hdr:       [][2]string{{"Authorization", "t"}, {"Content-Type", "text/plain"}},
		redirects: 10, maxBody: -1, show: true,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			if k == 0 {
				c.Write([]byte("HTTP/1.1 307 Temporary Redirect\r\nLocation: http://other:8080/z\r\nConnection: close\r\n\r\nclosed-body"))
				return
			}
			c.Write([]byte(ok5))
		}},
	{name: "host-other", method: "GET", url: "http://h/", hdr: [][2]string{{"Host", "custom"}},
		redirects: 10, maxBody: -1, show: true, note: "differs (LAWS copy the Host header to another host)",
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			if k == 0 {
				c.Write([]byte("HTTP/1.1 302 Found\r\nLocation: http://other/\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"))
				return
			}
			c.Write([]byte(ok5))
		}},
	{name: "late-redirect", method: "GET", url: "http://h/", redirects: 10, maxBody: -1, timeout: 150 * time.Millisecond,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			stall(c, "HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 10\r\n\r\nabc")
		}},
	{name: "lf-redirect", method: "GET", url: "http://h/", redirects: 10, maxBody: -1, show: true,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 302 Found\nLocation: /x\nContent-Length: 0\n\n"))
			read()
			c.Write([]byte(ok5))
		}},
	{name: "lf-close", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 200 OK\n\nabc"))
		}},
	{name: "two-spaces", method: "GET", url: "http://h/", redirects: 10, maxBody: -1, show: true,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1  302 Found\r\nLocation: /x\r\nContent-Length: 0\r\n\r\n"))
			read()
			c.Write([]byte(ok5))
		}},
	{name: "loc-space", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 302 Found\r\nLocation : /x\r\nContent-Length: 2\r\n\r\nmv"))
		}},
	{name: "empty-loc", method: "GET", url: "http://h/", redirects: 10, maxBody: -1,
		srv: func(k int, c net.Conn, read func() bool) {
			read()
			c.Write([]byte("HTTP/1.1 302 Found\r\nLocation: \r\nContent-Length: 2\r\n\r\nmv"))
		}},
}

// reads one request's raw bytes (head, then a Content-Length body)
func readRaw(br *bufio.Reader) (string, bool) {
	var b strings.Builder
	n := 0
	for {
		l, err := br.ReadString('\n')
		b.WriteString(l)
		if err != nil {
			return b.String(), false
		}
		if l == "\r\n" {
			break
		}
		if k, v, ok := strings.Cut(l, ":"); ok && strings.EqualFold(k, "Content-Length") {
			n, _ = strconv.Atoi(strings.TrimSpace(v))
		}
	}
	body := make([]byte, n)
	io.ReadFull(br, body)
	b.Write(body)
	return b.String(), true
}

func esc(s string) string {
	return strings.NewReplacer("\r", `\r`, "\n", `\n`).Replace(s)
}

func run(t tc) {
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		panic(err)
	}
	defer ln.Close()
	var mu sync.Mutex
	var reqs []string
	go func() {
		for k := 0; ; k++ {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			go func(k int, c net.Conn) {
				defer c.Close()
				br := bufio.NewReader(c)
				t.srv(k, c, func() bool {
					s, ok := readRaw(br)
					if s != "" {
						mu.Lock()
						reqs = append(reqs, s)
						mu.Unlock()
					}
					return ok
				})
			}(k, c)
		}
	}()
	tr := &http.Transport{DisableCompression: true}
	if t.srv != nil {
		tr.DialContext = func(ctx context.Context, _, _ string) (net.Conn, error) {
			return net.Dial("tcp", ln.Addr().String())
		}
	}
	n := t.redirects
	cl := &http.Client{Transport: tr, Timeout: t.timeout,
		CheckRedirect: func(_ *http.Request, via []*http.Request) error {
			switch {
			case n == -1:
				return http.ErrUseLastResponse
			case n < len(via):
				return fmt.Errorf("stopped after %d redirects", n)
			default:
				return nil
			}
		}}
	if t.warm {
		r, err := cl.Get("http://h/")
		if err != nil {
			panic(err)
		}
		io.ReadAll(r.Body)
		r.Body.Close()
		mu.Lock()
		reqs = nil
		mu.Unlock()
	}
	var body io.Reader
	if t.body != "" {
		body = strings.NewReader(t.body)
	}
	req, err := http.NewRequest(t.method, t.url, body)
	if err != nil {
		panic(err)
	}
	for _, kv := range t.hdr {
		req.Header.Add(kv[0], kv[1])
	}
	if host := req.Header.Get("Host"); host != "" {
		req.Host = host
	}
	req.Header.Set("X-Vegeta-Seq", "0")
	errText, kept := hit(cl, req, t.maxBody)
	prefix := "#|"
	if t.note != "" {
		prefix = "# " + t.note + ": "
	}
	fmt.Printf("%s%s|%s|%s\n", prefix, t.name, esc(errText), esc(kept))
	if t.show {
		mu.Lock()
		defer mu.Unlock()
		for i, r := range reqs {
			fmt.Printf("%s%s>%d|%s\n", prefix, t.name, i, esc(r))
		}
	}
}

// Vegeta's hit: the error text and the body the result keeps
func hit(cl *http.Client, req *http.Request, maxBody int64) (string, string) {
	r, err := cl.Do(req)
	if err != nil {
		return err.Error(), ""
	}
	defer r.Body.Close()
	var body io.Reader = r.Body
	if maxBody >= 0 {
		body = io.LimitReader(r.Body, maxBody)
	}
	b, err := io.ReadAll(body)
	if err != nil {
		return err.Error(), string(b)
	}
	if _, err := io.Copy(io.Discard, r.Body); err != nil {
		return err.Error(), string(b)
	}
	if r.StatusCode < 200 || r.StatusCode >= 400 {
		return r.Status, string(b)
	}
	return "", string(b)
}

func main() {
	for _, t := range cases {
		run(t)
	}
}

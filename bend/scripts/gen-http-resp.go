//go:build ignore

// Prints the expected lines of bend/tests/http.bend's responses (run from
// the repo root: go run ./bend/scripts/gen-http-resp.go). Each case is
// read as Go's transport reads it: http.ReadResponse, skipping 1xx
// responses but 101, then the body (through io.LimitReader under
// -max-body, then drained), then what is left on the connection. A
// response prints as code|status|headers|body|len(body)|keep|rest,
// headers sorted by name as k=v;k=v, \r and \n written as \r and \n; a
// failure prints as fail|text.
package main

import (
	"bufio"
	"fmt"
	"io"
	"net/http"
	"sort"
	"strings"
)

type tc struct {
	raw     string
	head    bool
	maxBody int64 // -1: none
}

var cases = []tc{
	{"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 5\r\n\r\nhelloEXTRA", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nX-A: 1\r\n\r\n5;ext=1\r\nhello\r\n6\r\n world\r\n0\r\nTrailer-X: y\r\n\r\nNEXT", false, -1},
	{"HTTP/1.1 500 Internal Server Error\r\nX: y\r\n\r\noops", false, -1},
	{"HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 103 Early Hints\r\nLink: </a>\r\n\r\nHTTP/1.1 204 No Content\r\nX: 1\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nContent-Length: 8\r\n\r\n12345678", false, 2},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n3\r\ndef\r\n0\r\n\r\n", false, 4},
	{"HTTP/1.0 200 OK\r\nConnection: keep-alive\r\nContent-Length: 2\r\n\r\nhi", false, -1},
	{"HTTP/1.0 200 OK\r\nContent-Length: 2\r\n\r\nhi", false, -1},
	{"HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhi", false, -1},
	{"HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\n", true, -1},
	{"HTTP/1.1 304 Not Modified\r\nContent-Length: 10\r\n\r\nrest", false, -1},
	{"HTTP/1.1 200 OK\r\ncontent-length: 2\r\nx-multi:  a \t\r\nx-multi: b\r\nX-Fold: a\r\n  b\r\nx-odd name: v\r\n\r\nok", false, -1},
	{"HTTP/1.1 200 OK\nContent-Length: 1\n\nz", false, -1},
	{"HTTP/1.1  201 Created\r\nContent-Length: 0\r\nContent-Length: 0\r\n\r\n", false, -1},
	{"HTTP/1.1 200\r\nContent-Length: 0\r\n\r\n", false, -1},
	{"HTTP/1.1 abc OK\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nBad Header\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\n Folded: x\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nBad@Name: x\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nX: a\x01b\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nContent-Length: x\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nContent-Length: \r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nContent-Length: 1\r\nContent-Length: 2\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nzz\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\nab\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nabX\n", false, -1},
	{"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nabc", false, -1},
	{"HTTP/1.1 200 OK\r\nX: 1\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: CHUNKED\r\nContent-Length: 99\r\n\r\n1 ; x\r\na\r\n0\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nConnection: keep-alive, Close\r\nX: 1\r\nContent-Length: 1\r\n\r\na", false, -1},
	{"HTTP/1.1 200 OK\r\nConnection: Upgrade\r\nContent-Length: 1\r\n\r\na", false, -1},
	{"HTTP/1.0 200 OK\r\nConnection: foo , Keep-Alive\r\nContent-Length: 1\r\n\r\na", false, -1},
	{"HTTP/1.0 200 OK\r\nConnection: keep-alive\r\nConnection: close\r\nContent-Length: 1\r\n\r\na", false, -1},
	{"HTTP/1.1 200 OK\r\nPragma: no-cache\r\nContent-Length: 0\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nPragma: no-cache\r\nCache-Control: max-age=1\r\nContent-Length: 0\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nPragma: No-Cache\r\nContent-Length: 0\r\n\r\n", false, -1},
	{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n1\r\na\r\n0\r\n\r\n", false, -1},
}

func esc(s string) string {
	return strings.NewReplacer("\r", `\r`, "\n", `\n`).Replace(s)
}

func run(c tc) string {
	br := bufio.NewReader(strings.NewReader(c.raw))
	method := "GET"
	if c.head {
		method = "HEAD"
	}
	req, _ := http.NewRequest(method, "http://x/", nil)
	var resp *http.Response
	var err error
	for {
		resp, err = http.ReadResponse(br, req)
		if err != nil {
			return "fail|" + err.Error()
		}
		if resp.StatusCode >= 100 && resp.StatusCode <= 199 && resp.StatusCode != 101 {
			continue
		}
		break
	}
	var body io.Reader = resp.Body
	if c.maxBody >= 0 {
		body = io.LimitReader(resp.Body, c.maxBody)
	}
	b, err := io.ReadAll(body)
	if err != nil {
		return "fail|" + err.Error()
	}
	if _, err := io.Copy(io.Discard, resp.Body); err != nil {
		return "fail|" + err.Error()
	}
	rest, _ := io.ReadAll(br)
	keys := make([]string, 0, len(resp.Header))
	for k := range resp.Header {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	var kvs []string
	for _, k := range keys {
		kvs = append(kvs, k+"="+strings.Join(resp.Header[k], ","))
	}
	return fmt.Sprintf("%d|%s|%s|%s|%d|%t|%s", resp.StatusCode, resp.Status, strings.Join(kvs, ";"), esc(string(b)), len(b), !resp.Close, esc(string(rest)))
}

func main() {
	for _, c := range cases {
		fmt.Println("#|" + run(c))
	}
}

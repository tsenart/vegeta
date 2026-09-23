//go:build ignore

// Prints the expected lines of bend/tests/target.bend (run from the repo
// root: go run ./bend/scripts/gen-http-targets.go). Each case is parsed
// with Vegeta's NewHTTPTargeter until it runs out of targets; a target
// prints as METHOD URL|k=v,...|@body (header names sorted, values in
// order) and an error as its text. Body files (made in a temporary
// directory) hold their own path, so Go's body (the file's bytes) prints
// as the port's (the path).
package main

import (
	"errors"
	"fmt"
	"os"
	"sort"
	"strings"

	vegeta "github.com/tsenart/vegeta/v12/lib"
)

var cases = []string{
	"GET http://127.0.0.1:8080/a?b=c\nX-A: 1\nX-A: 2\n\n# comment\nPOST http://localhost/x\n@tests/golden/body.txt\nPUT http://h:1/\n",
	"get http://x/\n",
	"GET\n",
	"GET foo\n",
	"GET :foo\n",
	"GET http://x/%zz\n",
	"GET http://x/\nX-A\n",
	"GET http://x/\nX-A:  \n",
	"GET http://x/\n: v\n",
	"  GET http://x/  \r\n  X-B :  v : w \r\n\r\n",
	"GET http://x/\n# c\nX-A: 1\n# d\nX-B: 2\nPOST http://y/\n",
	"GET http://x/\nPOST http://y/\n@tests/golden/body.txt\nX-A: 1\n",
	"GET http://x/\n@tests/golden/body.txt\n\n\n\nHEAD http://z/",
	"GET\thttp://x/ y\n",
	"G1T http://x/\n",
	"\n\n# only comments\n   \n",
	"",
	"GET /relative\n",
	"GET mailto:x\n",
	"GET http://x/\nx-a: 1\nX-A: 2\nx-a: 3\n",
}

func main() {
	dir, err := os.MkdirTemp("", "targets")
	if err != nil {
		panic(err)
	}
	defer os.RemoveAll(dir)
	const body = "tests/golden/body.txt"
	if err := os.MkdirAll(dir+"/tests/golden", 0o755); err != nil {
		panic(err)
	}
	if err := os.WriteFile(dir+"/"+body, []byte(body), 0o644); err != nil {
		panic(err)
	}
	if err := os.Chdir(dir); err != nil {
		panic(err)
	}
	for _, c := range cases {
		tr := vegeta.NewHTTPTargeter(strings.NewReader(c), nil, nil)
		var out []string
		for {
			var t vegeta.Target
			err := tr(&t)
			if errors.Is(err, vegeta.ErrNoTargets) {
				break
			} else if err != nil {
				out = []string{err.Error()}
				break
			}
			keys := make([]string, 0, len(t.Header))
			for k := range t.Header {
				keys = append(keys, k)
			}
			sort.Strings(keys)
			var kvs []string
			for _, k := range keys {
				for _, v := range t.Header[k] {
					kvs = append(kvs, k+"="+v)
				}
			}
			body := ""
			if t.Body != nil {
				body = "@" + string(t.Body)
			}
			out = append(out, t.Method+" "+t.URL+"|"+strings.Join(kvs, ",")+"|"+body)
		}
		fmt.Printf("#|%d\n", len(out))
		for _, o := range out {
			fmt.Printf("#|%s\n", o)
		}
	}
}

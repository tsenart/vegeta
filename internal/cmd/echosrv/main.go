package main

import (
	"net/http"
	"net/http/httputil"
	"os"
)

func main() {
	http.ListenAndServe(os.Args[1], http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		bs, _ := httputil.DumpRequest(r, true)
		w.Write(bs)
	}))
}

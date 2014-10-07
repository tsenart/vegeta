package vegeta

import (
	"bytes"
	"crypto/rand"
	"io"
	"io/ioutil"
	"net/http"
	"reflect"
	"testing"
)

func TestTargetRequest(t *testing.T) {
	t.Parallel()

	body, err := ioutil.ReadAll(io.LimitReader(rand.Reader, 1024*512))
	if err != nil {
		t.Fatal(err)
	}

	tgt := Target{
		Method: "GET",
		URL:    "http://:9999/",
		Body:   body,
		Header: http.Header{
			"X-Some-Header":       []string{"1"},
			"X-Some-Other-Header": []string{"2"},
			"X-Some-New-Header":   []string{"3"},
			"Host":                []string{"lolcathost"},
		},
	}
	req, _ := tgt.Request()

	reqBody, err := ioutil.ReadAll(req.Body)
	if err != nil {
		t.Fatal(err)
	}

	if !bytes.Equal(tgt.Body, reqBody) {
		t.Fatalf("Target body wasn't copied correctly")
	}

	tgt.Header.Set("X-Stuff", "0")
	if req.Header.Get("X-Stuff") == "0" {
		t.Error("Each Target must have it's own Header")
	}

	want, got := tgt.Header.Get("Host"), req.Header.Get("Host")
	if want != got {
		t.Fatalf("Target Header wasn't copied correctly. Want: %s, Got: %s", want, got)
	}
	if req.Host != want {
		t.Fatalf("Target Host wasnt copied correctly. Want: %s, Got: %s", want, req.Host)
	}
}

func TestNewEagerTargeter(t *testing.T) {
	t.Parallel()

	src := []byte("GET http://lolcathost:9999/\n\n      // HEAD http://lolcathost.com this is a comment \nHEAD http://lolcathost:9999/\n")
	read, err := NewEagerTargeter(bytes.NewReader(src), nil, nil)
	if err != nil {
		t.Fatalf("Couldn't parse valid source: %s", err)
	}
	for _, method := range []string{"GET", "HEAD"} {
		target, err := read()
		if err != nil {
			t.Fatal(err)
		}
		if target.Method != method || target.URL != "http://lolcathost:9999/" {
			t.Fatalf("Request was parsed incorrectly. Got: %s %s",
				target.Method, target.URL)
		}
	}
}

func TestNewLazyTarget(t *testing.T) {
	body, hdr := []byte("body"), http.Header{}
	src := bytes.NewReader([]byte("GET http://lolcathost:9999/\n// this is a comment \nHEAD http://lolcathost:9999/\n"))
	read := NewLazyTargeter(src, body, hdr)

	for _, want := range []*Target{
		&Target{
			Method: "GET",
			URL:    "http://lolcathost:9999/",
			Body:   body,
			Header: hdr,
		},
		&Target{
			Method: "HEAD",
			URL:    "http://lolcathost:9999/",
			Body:   body,
			Header: hdr,
		},
	} {
		if got, err := read(); err != nil {
			t.Fatal(err)
		} else if !reflect.DeepEqual(got, want) {
			t.Errorf("got: %+v, want: %+v", got, want)
		}
	}

	if got, err := read(); err != ErrNoTargets {
		t.Fatalf("got: %v, want: %v", err, ErrNoTargets)
	} else if got != nil {
		t.Fatalf("got: %v, want: %v", got, nil)
	}
}

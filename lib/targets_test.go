package vegeta

import (
	"bytes"
	"crypto/rand"
	"errors"
	"io"
	"io/ioutil"
	"net/http"
	"strings"
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

	src := []byte("GET http://lolcathost:9999/\n\nHEAD http://lolcathost:9999/")
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
	for want, def := range map[error]string{
		errors.New("bad target"): "GET",
		errors.New("bad method"): "SET http://:6060",
		errors.New("bad URL"):    "GET foobar",
		errors.New("bad body"): `
			GET http://:6060
			@238hhqwjhd8hhw3r.txt`,
		errors.New("bad header"): `
		  GET http://:6060
			Authorization`,
		errors.New("bad header"): `
			GET http://:6060
			Authorization:`,
		errors.New("bad header"): `
			GET http://:6060
			: 1234`,
	} {
		src := bytes.NewBufferString(strings.TrimSpace(def))
		read := NewLazyTargeter(src, []byte{}, http.Header{})
		if _, got := read(); got == nil || !strings.HasPrefix(got.Error(), want.Error()) {
			t.Errorf("got: %s, want: %s\n%s", got, want, def)
		}
	}

	// TODO: Test good path
}

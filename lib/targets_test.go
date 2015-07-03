package vegeta

import (
	"bytes"
	"errors"
	"fmt"
	"io/ioutil"
	"math/rand"
	"net/http"
	"os"
	"reflect"
	"strings"
	"testing"
)

func TestTargetRequest(t *testing.T) {
	t.Parallel()

	body := []byte(`{"id": "{foo}", "value": "bar"}`)

	tgt := Target{
		Method: "GET",
		URL:    "http://{foo}:9999/",
		Body:   body,
		Header: http.Header{
			"X-Some-Header":       []string{"1"},
			"X-Some-Other-Header": []string{"2"},
			"X-Some-New-Header":   []string{"3"},
			"Host":                []string{"lolcathost"},
		},
		URLInterpolators: []URLInterpolator{
			&RandomNumericInterpolation{
				Key:   "{foo}",
				Limit: int(^uint(0) >> 1),
				Rand:  rand.New(rand.NewSource(1435875839)),
			},
		},
		BodyInterpolators: []BodyInterpolator{
			&RandomNumericInterpolation{
				Key:   "{foo}",
				Limit: int(^uint(0) >> 1),
				Rand:  rand.New(rand.NewSource(1435875839)),
			},
		},
	}
	req, _ := tgt.Request()

	reqBody, err := ioutil.ReadAll(req.Body)
	if err != nil {
		t.Fatal(err)
	}

	if !bytes.Equal([]byte(`{"id": "2290778204292519845", "value": "bar"}`), reqBody) {
		t.Fatalf("Target body wasn't copied correctly")
	}

	if req.URL.String() != "http://2290778204292519845:9999/" {
		t.Fatalf("Target URL wasn't resolved correctly")
	}

	tgt.Header.Set("X-Stuff", "0")
	if req.Header.Get("X-Stuff") == "0" {
		t.Error("Each Target must have its own Header")
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

	src := []byte("GET http://:6060/\nHEAD http://:6606/")
	read, err := NewEagerTargeter(bytes.NewReader(src), []byte("body"), nil)
	if err != nil {
		t.Fatalf("Couldn't parse valid source: %s", err)
	}
	for _, want := range []*Target{
		{
			Method: "GET",
			URL:    "http://:6060/",
			Body:   []byte("body"),
			Header: http.Header{},
		},
		{
			Method: "HEAD",
			URL:    "http://:6606/",
			Body:   []byte("body"),
			Header: http.Header{},
		},
	} {
		if got, err := read(); err != nil {
			t.Fatal(err)
		} else if !reflect.DeepEqual(want, got) {
			t.Fatalf("want: %#v, got: %#v", want, got)
		}
	}
}

func TestNewLazyTargeter(t *testing.T) {
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

	bodyf, err := ioutil.TempFile("", "vegeta-")
	if err != nil {
		t.Fatal(err)
	}
	defer bodyf.Close()
	defer os.Remove(bodyf.Name())
	bodyf.WriteString("Hello world!")

	targets := fmt.Sprint(`
		GET http://:6060/
		X-Header: 1
		X-Header: 2

		PUT https://:6060/123

		POST http://foobar.org/fnord
		Authorization: x12345
		@`, bodyf.Name(),
	)

	src := bytes.NewBufferString(strings.TrimSpace(targets))
	read := NewLazyTargeter(src, []byte{}, http.Header{"Content-Type": []string{"text/plain"}})
	for _, want := range []*Target{
		{
			Method: "GET",
			URL:    "http://:6060/",
			Body:   []byte{},
			Header: http.Header{
				"X-Header":     []string{"1", "2"},
				"Content-Type": []string{"text/plain"},
			},
		},
		{
			Method: "PUT",
			URL:    "https://:6060/123",
			Body:   []byte{},
			Header: http.Header{"Content-Type": []string{"text/plain"}},
		},
		{
			Method: "POST",
			URL:    "http://foobar.org/fnord",
			Body:   []byte("Hello world!"),
			Header: http.Header{
				"Authorization": []string{"x12345"},
				"Content-Type":  []string{"text/plain"},
			},
		},
	} {
		if got, err := read(); err != nil {
			t.Fatal(err)
		} else if !reflect.DeepEqual(want, got) {
			t.Fatalf("want: %#v, got: %#v", want, got)
		}
	}
	if got, err := read(); err != ErrNoTargets {
		t.Fatalf("got: %v, want: %v", err, ErrNoTargets)
	} else if got != nil {
		t.Fatalf("got: %v, want: %v", got, nil)
	}
}

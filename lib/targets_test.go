package vegeta

import (
	"bytes"
	"crypto/rand"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"net/http"
	"os"
	"reflect"
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
		t.Error("Each Target must have its own Header")
	}

	want, got := tgt.Header.Get("Host"), req.Header.Get("Host")
	if want != got {
		t.Fatalf("Target Header wasn't copied correctly. Want: %s, Got: %s", want, got)
	}
	if req.Host != want {
		t.Fatalf("Target Host wasn't copied correctly. Want: %s, Got: %s", want, req.Host)
	}
}

func TestJSONTargeter(t *testing.T) {
	for _, tc := range []struct {
		name string
		src  io.Reader
		body []byte
		hdr  http.Header
		in   *Target
		out  *Target
		err  error
	}{
		{
			name: "nil target",
			src:  &bytes.Buffer{},
			in:   nil,
			out:  nil,
			err:  ErrNilTarget,
		},
		{
			name: "empty buffer",
			src:  &bytes.Buffer{},
			in:   &Target{},
			out:  &Target{},
			err:  ErrNoMethod,
		},
		{
			name: "empty object",
			src:  strings.NewReader(`{}`),
			in:   &Target{},
			out:  &Target{},
			err:  ErrNoMethod,
		},
		{
			name: "empty method",
			src:  strings.NewReader(`{"method": ""}`),
			in:   &Target{},
			out:  &Target{},
			err:  ErrNoMethod,
		},
		{
			name: "empty url",
			src:  strings.NewReader(`{"method": "GET"}`),
			in:   &Target{},
			out:  &Target{},
			err:  ErrNoURL,
		},
		{
			name: "bad body encoding",
			src:  strings.NewReader(`{"method": "GET", "url": "http://goku", "body": "NOT BASE64"}`),
			in:   &Target{},
			out:  &Target{},
			err:  errors.New("illegal base64 data at input byte 3"),
		},
		{
			name: "default body",
			src:  strings.NewReader(`{"method": "GET", "url": "http://goku"}`),
			body: []byte(`ATTACK!`),
			in:   &Target{},
			out:  &Target{Method: "GET", URL: "http://goku", Body: []byte("ATTACK!")},
		},
		{
			name: "headers merge",
			src:  strings.NewReader(`{"method": "GET", "url": "http://goku", "header":{"x": ["foo"]}}`),
			hdr:  http.Header{"x": []string{"bar"}},
			in:   &Target{Header: http.Header{"y": []string{"baz"}}},
			out:  &Target{Method: "GET", URL: "http://goku", Header: http.Header{"y": []string{"baz"}, "x": []string{"bar", "foo"}}},
		},
		{
			name: "no defaults",
			src:  strings.NewReader(`{"method": "GET", "url": "http://goku", "header":{"x": ["foo"]}, "body": "QVRUQUNLIQ=="}`),
			in:   &Target{},
			out:  &Target{Method: "GET", URL: "http://goku", Header: http.Header{"x": []string{"foo"}}, Body: []byte("ATTACK!")},
		},
	} {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()

			err := NewJSONTargeter(tc.src, tc.body, tc.hdr)(tc.in)
			if got, want := tc.in, tc.out; !got.Equal(want) {
				t.Errorf("got Target %#v, want %#v", got, want)
			}

			if got, want := fmt.Sprint(err), fmt.Sprint(tc.err); got != want {
				t.Errorf("got error: %+v, want: %+v", got, want)
			}
		})
	}

}

func TestReadAllTargets(t *testing.T) {
	t.Parallel()

	src := []byte("GET http://:6060/\nHEAD http://:6606/")
	want := []Target{
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
	}

	got, err := ReadAllTargets(NewHTTPTargeter(bytes.NewReader(src), []byte("body"), nil))
	if err != nil {
		t.Fatalf("error reading all targets: %v", err)
	}

	if !reflect.DeepEqual(got, want) {
		t.Fatalf("got: %#v, want: %#v", got, want)
	}
}

func TestNewHTTPTargeter(t *testing.T) {
	t.Parallel()

	for want, def := range map[error]string{
		errors.New("bad method"): "DO_WORK http://:6000",
		errors.New("bad method"): "DOwork http://:6000",
		errors.New("bad target"): "GET",
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
		read := NewHTTPTargeter(src, []byte{}, http.Header{})
		if got := read(&Target{}); got == nil || !strings.HasPrefix(got.Error(), want.Error()) {
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

		DELETE http://moo:443/boo

		POST http://foobar.org/fnord
		Authorization: x12345
		@`, bodyf.Name(),
		`


		POST http://foobar.org/fnord/2
		Authorization: x67890
		@`, bodyf.Name(),
		`

		SUBSCRIBE http://foobar.org/sub`,
	)

	src := bytes.NewBufferString(strings.TrimSpace(targets))
	read := NewHTTPTargeter(src, []byte{}, http.Header{"Content-Type": []string{"text/plain"}})
	for _, want := range []Target{
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
			Method: "DELETE",
			URL:    "http://moo:443/boo",
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
		{
			Method: "POST",
			URL:    "http://foobar.org/fnord/2",
			Body:   []byte("Hello world!"),
			Header: http.Header{
				"Authorization": []string{"x67890"},
				"Content-Type":  []string{"text/plain"},
			},
		},
		{
			Method: "SUBSCRIBE",
			URL:    "http://foobar.org/sub",
			Body:   []byte{},
			Header: http.Header{"Content-Type": []string{"text/plain"}},
		},
	} {
		var got Target
		if err := read(&got); err != nil {
			t.Fatal(err)
		} else if !reflect.DeepEqual(want, got) {
			t.Fatalf("want: %#v, got: %#v", want, got)
		}
	}
	var got Target
	if err := read(&got); err != ErrNoTargets {
		t.Fatalf("got: %v, want: %v", err, ErrNoTargets)
	} else if !reflect.DeepEqual(got, Target{}) {
		t.Fatalf("got: %v, want: %v", got, nil)
	}
}

func TestErrNilTarget(t *testing.T) {
	t.Parallel()

	for i, tr := range []Targeter{
		NewStaticTargeter(Target{Method: "GET", URL: "http://foo.bar"}),
		NewJSONTargeter(strings.NewReader(""), nil, nil),
		NewHTTPTargeter(strings.NewReader("GET http://foo.bar"), nil, nil),
	} {
		if got, want := tr(nil), ErrNilTarget; got != want {
			t.Errorf("test #%d: got: %v, want: %v", i, got, want)
		}
	}
}

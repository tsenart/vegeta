package vegeta

import (
	"bytes"
	"crypto/rand"
	"io"
	"io/ioutil"
	"net/http"
	"strconv"
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

func TestNewTargets(t *testing.T) {
	t.Parallel()

	src := []byte("GET http://lolcathost:9999/\n\n      // HEAD http://lolcathost.com this is a comment \nHEAD http://lolcathost:9999/\n")

	stream := NewStreamTargetGenerator(bytes.NewReader(src), nil, nil)

	tch := make(chan *Target, 2)

	if err := stream(tch); err != nil {
		t.Fatal(err)
	}

	if err := stream(tch); err != nil {
		t.Fatal(err)
	}

	for _, method := range []string{"GET", "HEAD"} {
		tt := <-tch
		if tt.Method != method ||
			tt.URL != "http://lolcathost:9999/" {
			t.Fatalf("Request was parsed incorrectly. Got: %s %s", tt.Method, tt.URL)
		}
	}
}

func TestShuffle(t *testing.T) {
	t.Parallel()

	targets := make([]*Target, 50)
	for i := 0; i < 50; i++ {
		targets[i] = &Target{Method: "GET", URL: "http://:" + strconv.Itoa(i)}
	}
	targetsCopy := make([]*Target, 50)
	copy(targetsCopy, targets)

	Shuffle(0, targets)
	for i, target := range targets {
		if targetsCopy[i].URL != target.URL {
			return
		}
	}
	t.Fatal("Targets were not shuffled correctly")
}

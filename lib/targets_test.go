package vegeta

import (
	"bytes"
	"net/http"
	"testing"
)

func TestNewTargetsFrom(t *testing.T) {
	lines := bytes.NewBufferString("GET http://lolcathost:9999/\n\n      // HEAD http://lolcathost.com this is a comment \nHEAD http://lolcathost:9999/\n")
	targets, err := NewTargetsFrom(lines)
	if err != nil {
		t.Fatalf("Couldn't parse valid source: %s", err)
	}
	for i, method := range []string{"GET", "HEAD"} {
		if targets[i].Method != method ||
			targets[i].URL.String() != "http://lolcathost:9999/" {
			t.Fatalf("Request was parsed incorrectly. Got: %s %s",
				targets[i].Method, targets[i].URL.String())
		}
	}
}

func TestNewTargets(t *testing.T) {
	lines := []string{"GET http://lolcathost:9999/", "HEAD http://lolcathost:9999/"}
	targets, err := NewTargets(lines)
	if err != nil {
		t.Fatalf("Couldn't parse valid source: %s", err)
	}
	for i, method := range []string{"GET", "HEAD"} {
		if targets[i].Method != method ||
			targets[i].URL.String() != "http://lolcathost:9999/" {
			t.Fatalf("Request was parsed incorrectly. Got: %s %s",
				targets[i].Method, targets[i].URL.String())
		}
	}
}

func TestShuffle(t *testing.T) {
	targets := make(Targets, 50)
	for i := 0; i < 50; i++ {
		targets[i], _ = http.NewRequest("GET", "http://lolcathost:9999/", nil)
	}
	targetsCopy := make(Targets, 50)
	copy(targetsCopy, targets)

	targets.Shuffle(0)
	for i, target := range targets {
		if targetsCopy[i] != target {
			return
		}
	}
	t.Fatal("Targets were not shuffled correctly")
}

func TestSetHeader(t *testing.T) {
	targets, _ := NewTargets([]string{"GET http://lolcathost:9999/", "HEAD http://lolcathost:9999/"})
	want := "secret"
	targets.SetHeader(http.Header{"Authorization": []string{want}})
	for _, target := range targets {
		if got := target.Header.Get("Authorization"); got != want {
			t.Errorf("Want: %s, Got: %s", want, got)
		}
	}

	// Test Header copy
	targets[0].Header.Set("Authorization", "0")
	if targets[1].Header.Get("Authorization") == "0" {
		t.Error("Each Target must have it's own Header")
	}

	// Test Host header
	want = "lolcathost"
	targets.SetHeader(http.Header{"Host": []string{want}})
	for _, target := range targets {
		if got := target.Host; got != want {
			t.Errorf("Want: %s, Got: %s", want, got)
		}
	}
}

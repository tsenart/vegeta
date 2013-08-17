package main

import (
	"bytes"
	"net/http"
	"testing"
)

func TestNewTargets(t *testing.T) {
	text := "GET http://lolcathost:9999/\n\nHEAD http://lolcathost:9999/\n"
	targets, err := NewTargets(bytes.NewBufferString(text))
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

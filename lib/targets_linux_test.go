package vegeta

import (
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"syscall"
	"testing"
	"time"
)

// TestNewHTTPTargeter_BlockedBody blocks one target's body read with a named
// pipe. Later regular-file and body-free targets must finish decoding before
// the pipe is released; the blocked target must then receive its complete body.
func TestNewHTTPTargeter_BlockedBody(t *testing.T) {
	path := filepath.Join(t.TempDir(), "body")
	if err := syscall.Mkfifo(path, 0600); err != nil {
		t.Fatal(err)
	}
	body := filepath.Join(t.TempDir(), "body")
	if err := os.WriteFile(body, []byte("ready payload"), 0600); err != nil {
		t.Fatal(err)
	}
	tr := NewHTTPTargeter(strings.NewReader(fmt.Sprintf("POST http://example.com/slow\n@%s\nPOST http://example.com/body\n@%s\nGET http://example.com/ready\n", path, body)), nil, nil)
	type result struct {
		target Target
		err    error
	}
	slow := make(chan result, 1)
	go func() {
		var tgt Target
		err := tr(&tgt)
		slow <- result{tgt, err}
	}()

	// Opening the writer confirms that the first decode reached the body read.
	var writer *os.File
	deadline := time.Now().Add(5 * time.Second)
	for writer == nil {
		fd, err := syscall.Open(path, syscall.O_WRONLY|syscall.O_NONBLOCK, 0600)
		if err == nil {
			writer = os.NewFile(uintptr(fd), path)
		} else if !errors.Is(err, syscall.ENXIO) {
			t.Fatal(err)
		} else if time.Now().After(deadline) {
			t.Fatal("body reader did not open pipe")
		} else {
			time.Sleep(time.Millisecond)
		}
	}
	defer writer.Close()

	ready := make(chan result, 2)
	pending := cap(ready)
	defer func() {
		writer.Close()
		for pending > 0 {
			select {
			case <-ready:
				pending--
			case <-time.After(5 * time.Second):
				t.Error("ready target did not finish after release")
				return
			}
		}
	}()
	for i := 0; i < cap(ready); i++ {
		go func() {
			var tgt Target
			err := tr(&tgt)
			ready <- result{tgt, err}
		}()
	}
	want := map[string]string{"http://example.com/ready": "", "http://example.com/body": "ready payload"}
	for i := 0; i < cap(ready); i++ {
		select {
		case got := <-ready:
			pending--
			if body, ok := want[got.target.URL]; got.err != nil || !ok || string(got.target.Body) != body {
				t.Errorf("ready target: %+v, error: %v", got.target, got.err)
			}
			delete(want, got.target.URL)
		case <-time.After(time.Second):
			t.Error("ready target waited for body file")
		}
	}

	if _, err := writer.Write([]byte("payload")); err != nil {
		t.Fatal(err)
	}
	if err := writer.Close(); err != nil {
		t.Fatal(err)
	}
	select {
	case got := <-slow:
		if got.err != nil || got.target.Method != "POST" || got.target.URL != "http://example.com/slow" || string(got.target.Body) != "payload" {
			t.Errorf("body target: %+v, error: %v", got.target, got.err)
		}
	case <-time.After(5 * time.Second):
		t.Fatal("body target did not finish after release")
	}
}

package main

import (
	"bufio"
	"bytes"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"reflect"
	"sync"
	"testing"
	"time"

	vegeta "github.com/tsenart/vegeta/v12/lib"
)

func TestHeadersSet(t *testing.T) {
	h := headers{
		Header: make(http.Header),
	}
	for i, tt := range []struct {
		key, val string
		want     []string
	}{
		{"key", "value", []string{"value"}},
		{"key", "value", []string{"value", "value"}},
		{"Key", "Value", []string{"Value"}},
		{"KEY", "VALUE", []string{"VALUE"}},
	} {
		if err := h.Set(tt.key + ": " + tt.val); err != nil {
			t.Error(err)
		} else if got := h.Header[tt.key]; !reflect.DeepEqual(got, tt.want) {
			t.Errorf("test #%d, '%s: %s': got: %+v, want: %+v", i, tt.key, tt.val, got, tt.want)
		}
	}
}

func decodeMetrics(buf bytes.Buffer) (vegeta.Metrics, error) {
	var metrics vegeta.Metrics
	dec := vegeta.NewDecoder(bufio.NewReader(&buf))

	for {
		var r vegeta.Result
		if err := dec.Decode(&r); err != nil {
			if err == io.EOF {
				break
			}
			return metrics, err
		}
		metrics.Add(&r)
	}
	metrics.Close()

	return metrics, nil
}

func TestAttackSignalOnce(t *testing.T) {
	t.Parallel()

	const (
		signalDelay    = 300 * time.Millisecond // Delay before stopping.
		clientTimeout  = 1 * time.Second        // This, plus delay, is the max time for the attack.
		serverTimeout  = 2 * time.Second        // Must be more than clientTimeout.
		attackDuration = 10 * time.Second       // The attack should never take this long.
	)

	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			time.Sleep(serverTimeout) // Server.Close() will block for this long on shutdown.
		}),
	)
	defer server.Close()

	tr := vegeta.NewStaticTargeter(vegeta.Target{Method: "GET", URL: server.URL})
	atk := vegeta.NewAttacker(vegeta.Timeout(clientTimeout))
	rate := vegeta.Rate{Freq: 10, Per: time.Second} // Every 100ms.

	var buf bytes.Buffer
	writer := bufio.NewWriter(&buf)
	enc := vegeta.NewEncoder(writer)
	sig := make(chan os.Signal, 1)
	res := atk.Attack(tr, rate, attackDuration, "")

	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		processAttack(atk, res, enc, sig, nil)
	}()

	// Allow more than one request to have started before stopping.
	time.Sleep(signalDelay)
	sig <- os.Interrupt
	wg.Wait()
	writer.Flush()

	metrics, err := decodeMetrics(buf)
	if err != nil {
		t.Error(err)
	}
	if got, min := metrics.Requests, uint64(2); got < min {
		t.Errorf("not enough requests recorded. got %+v, min: %+v", got, min)
	}
	if got, want := metrics.Success, 0.0; got != want {
		t.Errorf("all requests should fail. got %+v, want: %+v", got, want)
	}
	if got, max := metrics.Duration, clientTimeout; got > max {
		t.Errorf("attack duration too long. got %+v, max: %+v", got, max)
	}
	if got, want := metrics.Wait.Round(time.Second), clientTimeout; got != want {
		t.Errorf("attack wait doesn't match timeout. got %+v, want: %+v", got, want)
	}
}

func TestAttackSignalTwice(t *testing.T) {
	t.Parallel()

	const (
		attackDuration = 10 * time.Second // The attack should never take this long.
	)

	server := httptest.NewServer(
		http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}),
	)
	defer server.Close()

	tr := vegeta.NewStaticTargeter(vegeta.Target{Method: "GET", URL: server.URL})
	atk := vegeta.NewAttacker()
	rate := vegeta.Rate{Freq: 1, Per: time.Second}

	var buf bytes.Buffer
	writer := bufio.NewWriter(&buf)
	enc := vegeta.NewEncoder(writer)
	sig := make(chan os.Signal, 1)
	res := atk.Attack(tr, rate, attackDuration, "")

	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		processAttack(atk, res, enc, sig, nil)
	}()

	// Exit as soon as possible.
	sig <- os.Interrupt
	sig <- os.Interrupt
	wg.Wait()
	writer.Flush()

	metrics, err := decodeMetrics(buf)
	if err != nil {
		t.Error(err)
	}
	if got, max := metrics.Duration, time.Second; got > max {
		t.Errorf("attack duration too long. got %+v, max: %+v", got, max)
	}
}

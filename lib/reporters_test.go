package vegeta

import (
	"bytes"
	"errors"
	"strings"
	"testing"
	"time"
)

func TestNewHistogramReporter_PropagatesWriteErrors(t *testing.T) {
	t.Parallel()

	h := Histogram{
		Buckets: Buckets{0, 10 * time.Millisecond, 100 * time.Millisecond},
	}
	h.Add(&Result{Latency: 5 * time.Millisecond})

	writeErr := errors.New("disk full")
	reporter := NewHistogramReporter(&h)

	// errWriter always errors, so the tabwriter.Flush will propagate the error.
	if err := reporter(errWriter{writeErr}); err == nil {
		t.Error("expected write error to be propagated, got nil")
	}
}

func TestNewHistogramReporter_Output(t *testing.T) {
	t.Parallel()

	h := Histogram{
		Buckets: Buckets{0, 10 * time.Millisecond, 100 * time.Millisecond},
	}
	h.Add(&Result{Latency: 5 * time.Millisecond})
	h.Add(&Result{Latency: 50 * time.Millisecond})

	var buf bytes.Buffer
	reporter := NewHistogramReporter(&h)
	if err := reporter(&buf); err != nil {
		t.Fatalf("unexpected error: %v", err)
	}

	output := buf.String()
	if !strings.Contains(output, "Bucket") {
		t.Errorf("expected header in output, got:\n%s", output)
	}
	if !strings.Contains(output, "50.00%") {
		t.Errorf("expected 50%% ratio in output, got:\n%s", output)
	}
}

// errWriter is an io.Writer that always returns an error.
type errWriter struct{ err error }

func (w errWriter) Write(p []byte) (int, error) { return 0, w.err }

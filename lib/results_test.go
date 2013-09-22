package vegeta

import (
	"bytes"
	"sort"
	"testing"
	"time"
)

func TestEncoding(t *testing.T) {
	results := Results{
		Result{200, time.Now(), 100 * time.Millisecond, 10, 30, ""},
		Result{200, time.Now(), 20 * time.Millisecond, 20, 20, ""},
		Result{200, time.Now(), 30 * time.Millisecond, 30, 10, ""},
	}
	buffer := &bytes.Buffer{}

	if err := results.Encode(buffer); err != nil {
		t.Fatalf("Failed WriteTo: %s", err)
	}

	decoded := Results{}
	if err := decoded.Decode(buffer); err != nil {
		t.Fatalf("Failed ReadFrom: %s", err)
	}

	if len(decoded) != len(results) {
		t.Fatalf("Length mismatch. Want: %d, Got: %d", len(results), len(decoded))
	}

	for i, result := range results {
		if decoded[i].Timestamp != result.Timestamp {
			t.Fatalf("Expected result with timestamp: %s, got: %s", result.Timestamp, decoded[i].Timestamp)
		}
	}
}

func TestSort(t *testing.T) {
	results := Results{
		Result{Timestamp: time.Date(2013, 9, 10, 20, 4, 0, 3, time.UTC)},
		Result{Timestamp: time.Date(2013, 9, 10, 20, 4, 0, 2, time.UTC)},
		Result{Timestamp: time.Date(2013, 9, 10, 20, 4, 0, 1, time.UTC)},
	}

	results.Sort()

	if !sort.IsSorted(results) {
		t.Fatalf("Sort failed: %v", results)
	}
}

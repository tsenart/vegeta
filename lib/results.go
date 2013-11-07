package vegeta

import (
	"encoding/gob"
	"io"
	"sort"
	"time"
)

// Result represents the metrics defined out of an http.Response
// generated by each target hit
type Result struct {
	Code      uint16
	Timestamp time.Time
	Latency   time.Duration
	BytesOut  uint64
	BytesIn   uint64
	Error     string
	Rate      uint64
}

// Results is a slice of Result structs with encoding,
// decoding and sorting behavior attached
type Results []Result

// Encode encodes the results and writes it to an io.Writer
// returning an error in case of failure
func (r Results) Encode(out io.Writer) error {
	return gob.NewEncoder(out).Encode(r)
}

// Decode reads data from an io.Reader and decodes it into a Results struct
// returning an error in case of failure
func (r *Results) Decode(in io.Reader) error {
	return gob.NewDecoder(in).Decode(r)
}

// Sort sorts Results by Timestamp in ascending order and returns
// the sorted slice
func (r Results) Sort() Results {
	sort.Sort(r)
	return r
}

func (r Results) Len() int           { return len(r) }
func (r Results) Less(i, j int) bool { return r[i].Timestamp.Before(r[j].Timestamp) }
func (r Results) Swap(i, j int)      { r[i], r[j] = r[j], r[i] }

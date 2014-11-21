package vegeta

import (
	"bytes"
	"encoding/json"
	"fmt"
)

// Dumper is an interface defining Results dumping.
type Dumper interface {
	Dump(*Result) ([]byte, error)
}

// DumperFunc is an adapter to allow the use of ordinary functions as
// Dumpers. If f is a function with the appropriate signature, DumperFunc(f)
// is a Dumper object that calls f.
type DumperFunc func(*Result) ([]byte, error)

func (f DumperFunc) Dump(r *Result) ([]byte, error) { return f(r) }

// DumpCSV dumps a Result as a CSV record with six columns.
// The columns are: unix timestamp in ns since epoch, http status code,
// request latency in ns, bytes out, bytes in, and lastly the error.
var DumpCSV DumperFunc = func(r *Result) ([]byte, error) {
	var buf bytes.Buffer
	_, err := fmt.Fprintf(&buf, "%d,%d,%d,%d,%d,\"%s\"\n",
		r.Timestamp.UnixNano(),
		r.Code,
		r.Latency.Nanoseconds(),
		r.BytesOut,
		r.BytesIn,
		r.Error,
	)
	return buf.Bytes(), err
}

// DumpJSON dumps a Result as a JSON object.
var DumpJSON DumperFunc = func(r *Result) ([]byte, error) {
	var buf bytes.Buffer
	err := json.NewEncoder(&buf).Encode(r)
	return buf.Bytes(), err
}

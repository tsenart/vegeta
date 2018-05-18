package vegeta

import (
	"bytes"
	"io"
	"reflect"
	"testing"
	"testing/quick"
	"time"
)

func TestDecoding(t *testing.T) {
	t.Parallel()

	var b1, b2 bytes.Buffer
	enc := []Encoder{NewEncoder(&b1), NewEncoder(&b2)}

	for i := 0; i < 10; i++ {
		if err := enc[i%len(enc)](&Result{Code: uint16(i + 1)}); err != nil {
			t.Fatal(err)
		}
	}

	got := make([]uint16, 10)
	dec := NewRoundRobinDecoder(
		NewDecoder(&b2),
		NewDecoder(&bytes.Reader{}),
		NewDecoder(&b1),
	)

	for i := range got {
		var r Result
		if err := dec(&r); err != nil {
			t.Fatal(err)
		}
		got[i] = r.Code
	}

	want := []uint16{2, 1, 4, 3, 6, 5, 8, 7, 10, 9}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("got: %v, want: %v", got, want)
	}

	var r Result
	if got, want := dec(&r), io.EOF; got != want {
		t.Errorf("got: %v, want: %v", got, want)
	}
}

func TestEncoding(t *testing.T) {
	t.Parallel()

	for _, tc := range []struct {
		encoding string
		enc      func(io.Writer) Encoder
		dec      func(io.Reader) Decoder
	}{
		{"gob", NewEncoder, NewDecoder},
		{"csv", NewCSVEncoder, NewCSVDecoder},
		{"json", NewJSONEncoder, NewJSONDecoder},
	} {
		t.Run(tc.encoding, func(t *testing.T) {
			var buf bytes.Buffer
			enc := tc.enc(&buf)
			dec := tc.dec(&buf)
			err := quick.Check(func(code uint16, ts uint32, latency time.Duration, bsIn, bsOut uint64, e string) bool {
				want := Result{
					Code:      code,
					Timestamp: time.Unix(int64(ts), 0),
					Latency:   latency,
					BytesIn:   bsIn,
					BytesOut:  bsOut,
					Error:     e,
				}

				if err := enc(&want); err != nil {
					t.Fatal(err)
				}

				var got Result
				if err := dec(&got); err != nil {
					t.Fatalf("err: %q buffer: %s", err, buf.String())
				}

				if !got.Equal(want) {
					t.Logf("\ngot:  %#v\nwant: %#v\n", got, want)
					return false
				}

				return true
			}, nil)

			if err != nil {
				t.Fatal(err)
			}
		})
	}

}

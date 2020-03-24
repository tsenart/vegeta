package vegeta

import (
	"bytes"
	"encoding/json"
	"io"
	"io/ioutil"
	"math/rand"
	"net/http"
	"reflect"
	"testing"
	"testing/quick"
	"time"
)

func TestResultDecoding(t *testing.T) {
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

func TestResultEncoding(t *testing.T) {
	newStdJSONEncoder := func(w io.Writer) Encoder {
		enc := json.NewEncoder(w)
		return func(r *Result) error { return enc.Encode(r) }
	}

	newStdJSONDecoder := func(r io.Reader) Decoder {
		dec := json.NewDecoder(r)
		return func(r *Result) error { return dec.Decode(r) }
	}

	for _, tc := range []struct {
		encoding string
		enc      func(io.Writer) Encoder
		dec      func(io.Reader) Decoder
	}{
		{"auto-gob", NewEncoder, DecoderFor},
		{"auto-json", NewJSONEncoder, DecoderFor},
		{"auto-csv", NewCSVEncoder, DecoderFor},
		{"gob", NewEncoder, NewDecoder},
		{"csv", NewCSVEncoder, NewCSVDecoder},
		{"json", NewJSONEncoder, NewJSONDecoder},
		{"json-dec-compat", NewJSONEncoder, newStdJSONDecoder},
		{"json-enc-compat", newStdJSONEncoder, NewJSONDecoder},
	} {
		tc := tc
		t.Run(tc.encoding, func(t *testing.T) {
			t.Parallel()

			err := quick.Check(func(code uint16, ts uint32, latency time.Duration, seq, bsIn, bsOut uint64, body []byte, attack, e string) bool {
				want := Result{
					Attack:    attack,
					Seq:       seq,
					Code:      code,
					Timestamp: time.Unix(int64(ts), 0),
					Latency:   latency,
					BytesIn:   bsIn,
					BytesOut:  bsOut,
					Error:     e,
					Body:      body,
					Method:    "GET",
					URL:       "http://vegeta.test",
					Headers:   http.Header{"Foo": []string{"bar"}},
				}

				var buf bytes.Buffer
				enc := tc.enc(&buf)
				for j := 0; j < 2; j++ {
					if err := enc(&want); err != nil {
						t.Fatal(err)
					}
				}

				dec := tc.dec(&buf)
				if dec == nil {
					t.Fatal("Cannot get decoder")
				}
				for j := 0; j < 2; j++ {
					var got Result
					if err := dec(&got); err != nil {
						t.Fatalf("err: %q buffer: %s", err, buf.String())
					}

					if !got.Equal(want) {
						t.Logf("\ngot:  %#v\nwant: %#v\n", got, want)
						return false
					}
				}

				return true
			}, nil)

			if err != nil {
				t.Fatal(err)
			}
		})
	}
}

func BenchmarkResultEncodings(b *testing.B) {
	b.StopTimer()
	b.ResetTimer()

	rng := rand.New(rand.NewSource(0))
	zf := rand.NewZipf(rng, 3, 2, 1000)
	began := time.Now()
	results := make([]Result, 1e5)

	for i := 0; i < cap(results); i++ {
		results[i] = Result{
			Attack:    "Big Bang!",
			Seq:       uint64(i),
			Timestamp: began.Add(time.Duration(i) * time.Millisecond),
			Latency:   time.Duration(zf.Uint64()) * time.Millisecond,
		}
	}

	for _, tc := range []struct {
		encoding string
		enc      func(io.Writer) Encoder
		dec      func(io.Reader) Decoder
	}{
		{"gob", NewEncoder, NewDecoder},
		{"csv", NewCSVEncoder, NewCSVDecoder},
		{"json", NewJSONEncoder, NewJSONDecoder},
	} {
		enc := tc.enc(ioutil.Discard)

		b.Run(tc.encoding+"-encode", func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				enc.Encode(&results[i%len(results)])
			}
		})

		var buf bytes.Buffer
		enc = tc.enc(&buf)
		for _, r := range results {
			enc.Encode(&r)
		}

		dec := tc.dec(&buf)
		b.Run(tc.encoding+"-decode", func(b *testing.B) {
			var r Result
			for i := 0; i < b.N; i++ {
				dec.Decode(&r)
			}
		})
	}
}

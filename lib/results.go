package vegeta

import (
	"bufio"
	"bytes"
	"encoding/base64"
	"encoding/csv"
	"encoding/gob"
	"io"
	"sort"
	"strconv"
	"time"

	"github.com/mailru/easyjson/jlexer"
	jwriter "github.com/mailru/easyjson/jwriter"
)

func init() {
	gob.Register(&Result{})
}

// Result contains the results of a single Target hit.
type Result struct {
	Attack    string        `json:"attack"`
	Seq       uint64        `json:"seq"`
	Code      uint16        `json:"code"`
	Timestamp time.Time     `json:"timestamp"`
	Latency   time.Duration `json:"latency"`
	BytesOut  uint64        `json:"bytes_out"`
	BytesIn   uint64        `json:"bytes_in"`
	Error     string        `json:"error"`
	Body      []byte        `json:"body"`
	Method    string        `json:"method"`
	URL       string        `json:"url"`
}

// End returns the time at which a Result ended.
func (r *Result) End() time.Time { return r.Timestamp.Add(r.Latency) }

// Equal returns true if the given Result is equal to the receiver.
func (r Result) Equal(other Result) bool {
	return r.Attack == other.Attack &&
		r.Seq == other.Seq &&
		r.Code == other.Code &&
		r.Timestamp.Equal(other.Timestamp) &&
		r.Latency == other.Latency &&
		r.BytesIn == other.BytesIn &&
		r.BytesOut == other.BytesOut &&
		r.Error == other.Error &&
		bytes.Equal(r.Body, other.Body) &&
		r.Method == other.Method &&
		r.URL == other.URL
}

// Results is a slice of Result type elements.
type Results []Result

// Add implements the Add method of the Report interface by appending the given
// Result to the slice.
func (rs *Results) Add(r *Result) { *rs = append(*rs, *r) }

// Close implements the Close method of the Report interface by sorting the
// Results.
func (rs *Results) Close() { sort.Sort(rs) }

// The following methods implement sort.Interface
func (rs Results) Len() int           { return len(rs) }
func (rs Results) Less(i, j int) bool { return rs[i].Timestamp.Before(rs[j].Timestamp) }
func (rs Results) Swap(i, j int)      { rs[i], rs[j] = rs[j], rs[i] }

// A Decoder decodes a Result and returns an error in case of failure.
type Decoder func(*Result) error

// A DecoderFactory constructs a new Decoder from a given io.Reader.
type DecoderFactory func(io.Reader) Decoder

// DecoderFor automatically detects the encoding of the first few bytes in
// the given io.Reader and then returns the corresponding Decoder or nil
// in case of failing to detect a supported encoding.
func DecoderFor(r io.Reader) Decoder {
	var buf bytes.Buffer
	for _, dec := range []DecoderFactory{
		NewDecoder,
		NewJSONDecoder,
		NewCSVDecoder,
	} {
		rd := io.MultiReader(bytes.NewReader(buf.Bytes()), io.TeeReader(r, &buf))
		if err := dec(rd).Decode(&Result{}); err == nil {
			return dec(io.MultiReader(&buf, r))
		}
	}
	return nil
}

// NewRoundRobinDecoder returns a new Decoder that round robins across the
// given Decoders on every invocation or decoding error.
func NewRoundRobinDecoder(dec ...Decoder) Decoder {
	// Optimization for single Decoder case.
	if len(dec) == 1 {
		return dec[0]
	}

	var seq uint64
	return func(r *Result) (err error) {
		for range dec {
			robin := seq % uint64(len(dec))
			seq++
			if err = dec[robin].Decode(r); err != nil {
				continue
			}
			return nil
		}
		return err
	}
}

// NewDecoder returns a new gob Decoder for the given io.Reader.
func NewDecoder(rd io.Reader) Decoder {
	dec := gob.NewDecoder(rd)
	return func(r *Result) error { return dec.Decode(r) }
}

// Decode is an an adapter method calling the Decoder function itself with the
// given parameters.
func (dec Decoder) Decode(r *Result) error { return dec(r) }

// An Encoder encodes a Result and returns an error in case of failure.
type Encoder func(*Result) error

// NewEncoder returns a new Result encoder closure for the given io.Writer
func NewEncoder(r io.Writer) Encoder {
	enc := gob.NewEncoder(r)
	return func(r *Result) error { return enc.Encode(r) }
}

// Encode is an an adapter method calling the Encoder function itself with the
// given parameters.
func (enc Encoder) Encode(r *Result) error { return enc(r) }

// NewCSVEncoder returns an Encoder that dumps the given *Result as a CSV
// record. The columns are: UNIX timestamp in ns since epoch,
// HTTP status code, request latency in ns, bytes out, bytes in,
// response body, and lastly the error.
func NewCSVEncoder(w io.Writer) Encoder {
	enc := csv.NewWriter(w)
	return func(r *Result) error {
		err := enc.Write([]string{
			strconv.FormatInt(r.Timestamp.UnixNano(), 10),
			strconv.FormatUint(uint64(r.Code), 10),
			strconv.FormatInt(r.Latency.Nanoseconds(), 10),
			strconv.FormatUint(r.BytesOut, 10),
			strconv.FormatUint(r.BytesIn, 10),
			r.Error,
			base64.StdEncoding.EncodeToString(r.Body),
			r.Attack,
			strconv.FormatUint(r.Seq, 10),
			r.Method,
			r.URL,
		})
		if err != nil {
			return err
		}

		enc.Flush()

		return enc.Error()
	}
}

// NewCSVDecoder returns a Decoder that decodes CSV encoded Results.
func NewCSVDecoder(r io.Reader) Decoder {
	dec := csv.NewReader(r)
	dec.FieldsPerRecord = 11
	dec.TrimLeadingSpace = true

	return func(r *Result) error {
		rec, err := dec.Read()
		if err != nil {
			return err
		}

		ts, err := strconv.ParseInt(rec[0], 10, 64)
		if err != nil {
			return err
		}
		r.Timestamp = time.Unix(0, ts)

		code, err := strconv.ParseUint(rec[1], 10, 16)
		if err != nil {
			return err
		}
		r.Code = uint16(code)

		latency, err := strconv.ParseInt(rec[2], 10, 64)
		if err != nil {
			return err
		}
		r.Latency = time.Duration(latency)

		if r.BytesOut, err = strconv.ParseUint(rec[3], 10, 64); err != nil {
			return err
		}

		if r.BytesIn, err = strconv.ParseUint(rec[4], 10, 64); err != nil {
			return err
		}

		r.Error = rec[5]
		r.Body, err = base64.StdEncoding.DecodeString(rec[6])

		r.Attack = rec[7]
		if r.Seq, err = strconv.ParseUint(rec[8], 10, 64); err != nil {
			return err
		}

		r.Method = rec[9]
		r.URL = rec[10]

		return err
	}
}

//go:generate easyjson -no_std_marshalers -output_filename results_easyjson.go results.go
//easyjson:json
type jsonResult Result

// NewJSONEncoder returns an Encoder that dumps the given *Results as a JSON
// object.
func NewJSONEncoder(w io.Writer) Encoder {
	var jw jwriter.Writer
	return func(r *Result) error {
		(*jsonResult)(r).MarshalEasyJSON(&jw)
		if jw.Error != nil {
			return jw.Error
		}
		jw.RawByte('\n')
		_, err := jw.DumpTo(w)
		return err
	}
}

// NewJSONDecoder returns a Decoder that decodes JSON encoded Results.
func NewJSONDecoder(r io.Reader) Decoder {
	rd := bufio.NewReader(r)
	return func(r *Result) (err error) {
		var jl jlexer.Lexer
		if jl.Data, err = rd.ReadBytes('\n'); err != nil {
			return err
		}
		(*jsonResult)(r).UnmarshalEasyJSON(&jl)
		return jl.Error()
	}
}

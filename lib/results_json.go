package vegeta

import (
	"bufio"
	"encoding/base64"
	"io"
	"net/http"
	"reflect"
	"strconv"
	"strings"
	"time"
	"unsafe"

	"github.com/valyala/fastjson"
)

// NewJSONEncoder returns an Encoder that dumps the given *Results as a JSON
// object.
func NewJSONEncoder(w io.Writer) Encoder {
	buf := make([]byte, 0, 4096)
	return func(r *Result) error {
		buf = buf[:0]
		buf = append(buf, `{"attack":"`...)
		if len(r.Attack) > 0 {
			buf = appendJSONString(buf, r.Attack)
		}

		buf = append(buf, `","seq":`...)
		buf = strconv.AppendUint(buf, r.Seq, 10)
		buf = append(buf, `,"code":`...)
		buf = strconv.AppendUint(buf, uint64(r.Code), 10)
		buf = append(buf, `,"timestamp":"`...)
		buf = r.Timestamp.AppendFormat(buf, time.RFC3339Nano)
		buf = append(buf, `","latency":`...)
		buf = strconv.AppendInt(buf, int64(r.Latency), 10)
		buf = append(buf, `,"bytes_out":`...)
		buf = strconv.AppendUint(buf, r.BytesOut, 10)
		buf = append(buf, `,"bytes_in":`...)
		buf = strconv.AppendUint(buf, r.BytesIn, 10)

		buf = append(buf, `,"error":"`...)
		if len(r.Error) > 0 {
			buf = appendJSONString(buf, r.Error)
		}

		buf = append(buf, `","body":"`...)
		if len(r.Body) > 0 {
			buf = appendBase64(buf, r.Body)
		}

		buf = append(buf, `","method":"`...)
		buf = append(buf, r.Method...)
		buf = append(buf, `","url":"`...)
		buf = appendJSONString(buf, r.URL)

		buf = append(buf, `","headers":{`...)
		for k, vs := range r.Headers {
			buf = append(buf, '"')
			buf = appendJSONString(buf, k)
			buf = append(buf, `":[`...)
			for _, v := range vs {
				buf = append(buf, '"')
				buf = appendJSONString(buf, v)
				buf = append(buf, `",`...)
			}
			if len(vs) > 0 {
				buf = buf[:len(buf)-1]
			}
			buf = append(buf, `],`...)
		}
		if len(r.Headers) > 0 {
			buf = buf[:len(buf)-1]
		}
		buf = append(buf, "}}\n"...)

		_, err := w.Write(buf)
		return err
	}
}

// NewJSONDecoder returns a Decoder that decodes JSON encoded Results.
func NewJSONDecoder(r io.Reader) Decoder {
	var p fastjson.Parser
	rd := bufio.NewReader(r)
	return func(r *Result) (err error) {
		line, err := rd.ReadBytes('\n')
		if err != nil {
			return err
		}

		v, err := p.ParseBytes(line)
		if err != nil {
			return err
		}

		r.Attack = string(v.GetStringBytes("attack"))
		r.Seq = v.GetUint64("seq")
		r.Code = uint16(v.GetUint("code"))

		r.Timestamp, err = time.Parse(time.RFC3339Nano, string(v.GetStringBytes("timestamp")))
		if err != nil {
			return err
		}

		r.Latency = time.Duration(v.GetInt64("latency"))
		r.BytesIn = v.GetUint64("bytes_in")
		r.BytesOut = v.GetUint64("bytes_out")
		r.Error = string(v.GetStringBytes("error"))

		body := v.GetStringBytes("body")
		r.Body = make([]byte, base64.StdEncoding.DecodedLen(len(body)))
		n, err := base64.StdEncoding.Decode(r.Body, body)
		if err != nil {
			return err
		}
		r.Body = r.Body[:n]

		r.Method = string(v.GetStringBytes("method"))
		r.URL = string(v.GetStringBytes("url"))

		headers, err := v.Get("headers").Object()
		if err != nil {
			return err
		}

		r.Headers = make(http.Header, headers.Len())
		headers.Visit(func(key []byte, v *fastjson.Value) {
			if err != nil { // Previous visit errored
				return
			}

			var vs []*fastjson.Value
			if vs, err = v.Array(); err != nil {
				return
			}

			k := string(key)
			for _, v := range vs {
				r.Headers[k] = append(r.Headers[k], string(v.GetStringBytes()))
			}
		})

		return err
	}
}

func appendBase64(buf []byte, bs []byte) []byte {
	n := base64.StdEncoding.EncodedLen(len(bs))
	buf = expand(buf, n)
	base64.StdEncoding.Encode(buf[len(buf):len(buf)+n], bs)
	return buf[:len(buf)+n]
}

// expand grows the given buf to have enough capacity to hold n
// extra bytes beyond the current len
func expand(buf []byte, n int) []byte {
	l := len(buf)
	free := cap(buf) - l
	grow := n - free
	if grow > 0 {
		buf = append(buf[:cap(buf)], make([]byte, grow)...)[:l]
	}
	return buf
}

// The following code was copied and adapted from https://github.com/valyala/quicktemplate

func s2b(s string) []byte {
	sh := (*reflect.StringHeader)(unsafe.Pointer(&s))
	bh := reflect.SliceHeader{
		Data: sh.Data,
		Len:  sh.Len,
		Cap:  sh.Len,
	}
	return *(*[]byte)(unsafe.Pointer(&bh))
}

func b2s(z []byte) string {
	return *(*string)(unsafe.Pointer(&z))
}

func appendJSONString(buf []byte, s string) []byte {
	if len(s) > 24 &&
		strings.IndexByte(s, '"') < 0 &&
		strings.IndexByte(s, '\\') < 0 &&
		strings.IndexByte(s, '\n') < 0 &&
		strings.IndexByte(s, '\r') < 0 &&
		strings.IndexByte(s, '\t') < 0 &&
		strings.IndexByte(s, '\f') < 0 &&
		strings.IndexByte(s, '\b') < 0 &&
		strings.IndexByte(s, '<') < 0 &&
		strings.IndexByte(s, '\'') < 0 &&
		strings.IndexByte(s, 0) < 0 {

		// fast path - nothing to escape
		return append(buf, s2b(s)...)
	}

	// slow path
	write := func(bs []byte) { buf = append(buf, bs...) }
	b := s2b(s)
	j := 0
	n := len(b)
	if n > 0 {
		// Hint the compiler to remove bounds checks in the loop below.
		_ = b[n-1]
	}
	for i := 0; i < n; i++ {
		switch b[i] {
		case '"':
			write(b[j:i])
			write(strBackslashQuote)
			j = i + 1
		case '\\':
			write(b[j:i])
			write(strBackslashBackslash)
			j = i + 1
		case '\n':
			write(b[j:i])
			write(strBackslashN)
			j = i + 1
		case '\r':
			write(b[j:i])
			write(strBackslashR)
			j = i + 1
		case '\t':
			write(b[j:i])
			write(strBackslashT)
			j = i + 1
		case '\f':
			write(b[j:i])
			write(strBackslashF)
			j = i + 1
		case '\b':
			write(b[j:i])
			write(strBackslashB)
			j = i + 1
		case '<':
			write(b[j:i])
			write(strBackslashLT)
			j = i + 1
		case '\'':
			write(b[j:i])
			write(strBackslashQ)
			j = i + 1
		case 0:
			write(b[j:i])
			write(strBackslashZero)
			j = i + 1
		}
	}
	write(b[j:])

	return buf
}

var (
	strBackslashQuote     = []byte(`\"`)
	strBackslashBackslash = []byte(`\\`)
	strBackslashN         = []byte(`\n`)
	strBackslashR         = []byte(`\r`)
	strBackslashT         = []byte(`\t`)
	strBackslashF         = []byte(`\u000c`)
	strBackslashB         = []byte(`\u0008`)
	strBackslashLT        = []byte(`\u003c`)
	strBackslashQ         = []byte(`\u0027`)
	strBackslashZero      = []byte(`\u0000`)
)

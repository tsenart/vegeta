// This file has been modified from the original generated code to make it work with
// type alias jsonResult so that the methods aren't exposed in Result.

package vegeta

import (
	"time"

	"github.com/mailru/easyjson/jlexer"
	"github.com/mailru/easyjson/jwriter"
)

type jsonResult Result

func (r *jsonResult) decode(in *jlexer.Lexer) {
	isTopLevel := in.IsStart()
	if in.IsNull() {
		if isTopLevel {
			in.Consumed()
		}
		in.Skip()
		return
	}
	in.Delim('{')
	for !in.IsDelim('}') {
		key := in.UnsafeString()
		in.WantColon()
		if in.IsNull() {
			in.Skip()
			in.WantComma()
			continue
		}
		switch key {
		case "attack":
			r.Attack = string(in.String())
		case "seq":
			r.Seq = uint64(in.Uint64())
		case "code":
			r.Code = uint16(in.Uint16())
		case "timestamp":
			if data := in.Raw(); in.Ok() {
				in.AddError((r.Timestamp).UnmarshalJSON(data))
			}
		case "latency":
			r.Latency = time.Duration(in.Int64())
		case "bytes_out":
			r.BytesOut = uint64(in.Uint64())
		case "bytes_in":
			r.BytesIn = uint64(in.Uint64())
		case "error":
			r.Error = string(in.String())
		case "body":
			if in.IsNull() {
				in.Skip()
				r.Body = nil
			} else {
				r.Body = in.Bytes()
			}
		default:
			in.SkipRecursive()
		}
		in.WantComma()
	}
	in.Delim('}')
	if isTopLevel {
		in.Consumed()
	}
}

func (r jsonResult) encode(out *jwriter.Writer) {
	out.RawByte('{')
	first := true
	_ = first
	{
		const prefix string = ",\"attack\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.String(string(r.Attack))
	}
	{
		const prefix string = ",\"seq\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Uint64(uint64(r.Seq))
	}
	{
		const prefix string = ",\"code\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Uint16(uint16(r.Code))
	}
	{
		const prefix string = ",\"timestamp\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Raw((r.Timestamp).MarshalJSON())
	}
	{
		const prefix string = ",\"latency\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Int64(int64(r.Latency))
	}
	{
		const prefix string = ",\"bytes_out\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Uint64(uint64(r.BytesOut))
	}
	{
		const prefix string = ",\"bytes_in\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Uint64(uint64(r.BytesIn))
	}
	{
		const prefix string = ",\"error\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.String(string(r.Error))
	}
	{
		const prefix string = ",\"body\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Base64Bytes(r.Body)
	}
	out.RawByte('}')
}

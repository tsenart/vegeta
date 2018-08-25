// This file has been modified from the original generated code to make it work with
// type alias jsonResult so that the methods aren't exposed in Result.
package vegeta

import (
	"time"

	"github.com/mailru/easyjson/jlexer"
	"github.com/mailru/easyjson/jwriter"
)

type jsonResult Result

func (out *jsonResult) decode(in *jlexer.Lexer) {
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
			out.Attack = string(in.String())
		case "seq":
			out.Seq = uint64(in.Uint64())
		case "code":
			out.Code = uint16(in.Uint16())
		case "timestamp":
			if data := in.Raw(); in.Ok() {
				in.AddError((out.Timestamp).UnmarshalJSON(data))
			}
		case "latency":
			out.Latency = time.Duration(in.Int64())
		case "bytes_out":
			out.BytesOut = uint64(in.Uint64())
		case "bytes_in":
			out.BytesIn = uint64(in.Uint64())
		case "error":
			out.Error = string(in.String())
		case "body":
			if in.IsNull() {
				in.Skip()
				out.Body = nil
			} else {
				out.Body = in.Bytes()
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

func (in jsonResult) encode(out *jwriter.Writer) {
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
		out.String(string(in.Attack))
	}
	{
		const prefix string = ",\"seq\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Uint64(uint64(in.Seq))
	}
	{
		const prefix string = ",\"code\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Uint16(uint16(in.Code))
	}
	{
		const prefix string = ",\"timestamp\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Raw((in.Timestamp).MarshalJSON())
	}
	{
		const prefix string = ",\"latency\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Int64(int64(in.Latency))
	}
	{
		const prefix string = ",\"bytes_out\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Uint64(uint64(in.BytesOut))
	}
	{
		const prefix string = ",\"bytes_in\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Uint64(uint64(in.BytesIn))
	}
	{
		const prefix string = ",\"error\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.String(string(in.Error))
	}
	{
		const prefix string = ",\"body\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Base64Bytes(in.Body)
	}
	out.RawByte('}')
}

// This file has been modified from the original generated code to make it work with
// type alias jsonTarget so that the methods aren't exposed in Target.

package modal

import (
	jlexer "github.com/mailru/easyjson/jlexer"
	jwriter "github.com/mailru/easyjson/jwriter"
)

type jsonTarget Target

func (t *jsonTarget) decode(in *jlexer.Lexer) {
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
		case "app":
			t.AppName = in.String()
		case "function":
			t.FunctionName = in.String()
		case "body":
			if in.IsNull() {
				in.Skip()
				t.Body = nil
			} else {
				t.Body = in.Bytes()
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

func (t jsonTarget) encode(out *jwriter.Writer) {
	out.RawByte('{')
	first := true
	_ = first
	{
		const prefix string = ",\"app\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.String(t.AppName)
	}
	{
		const prefix string = ",\"function\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.String(t.FunctionName)
	}
	if len(t.Body) != 0 {
		const prefix string = ",\"body\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Base64Bytes(t.Body)
	}
	out.RawByte('}')
}

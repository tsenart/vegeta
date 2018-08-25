// This file has been modified from the original generated code to make it work with
// type alias jsonTarget so that the methods aren't exposed in Target.

package vegeta

import (
	http "net/http"

	jlexer "github.com/mailru/easyjson/jlexer"
	jwriter "github.com/mailru/easyjson/jwriter"
)

type jsonTarget Target

func (out *jsonTarget) decode(in *jlexer.Lexer) {
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
		case "method":
			out.Method = string(in.String())
		case "url":
			out.URL = string(in.String())
		case "body":
			if in.IsNull() {
				in.Skip()
				out.Body = nil
			} else {
				out.Body = in.Bytes()
			}
		case "header":
			if in.IsNull() {
				in.Skip()
			} else {
				in.Delim('{')
				if !in.IsDelim('}') {
					out.Header = make(http.Header)
				} else {
					out.Header = nil
				}
				for !in.IsDelim('}') {
					key := string(in.String())
					in.WantColon()
					var v2 []string
					if in.IsNull() {
						in.Skip()
						v2 = nil
					} else {
						in.Delim('[')
						if v2 == nil {
							if !in.IsDelim(']') {
								v2 = make([]string, 0, 4)
							} else {
								v2 = []string{}
							}
						} else {
							v2 = (v2)[:0]
						}
						for !in.IsDelim(']') {
							var v3 string
							v3 = string(in.String())
							v2 = append(v2, v3)
							in.WantComma()
						}
						in.Delim(']')
					}
					(out.Header)[key] = v2
					in.WantComma()
				}
				in.Delim('}')
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

func (in jsonTarget) encode(out *jwriter.Writer) {
	out.RawByte('{')
	first := true
	_ = first
	{
		const prefix string = ",\"method\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.String(string(in.Method))
	}
	{
		const prefix string = ",\"url\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.String(string(in.URL))
	}
	if len(in.Body) != 0 {
		const prefix string = ",\"body\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		out.Base64Bytes(in.Body)
	}
	if len(in.Header) != 0 {
		const prefix string = ",\"header\":"
		if first {
			first = false
			out.RawString(prefix[1:])
		} else {
			out.RawString(prefix)
		}
		{
			out.RawByte('{')
			v6First := true
			for v6Name, v6Value := range in.Header {
				if v6First {
					v6First = false
				} else {
					out.RawByte(',')
				}
				out.String(string(v6Name))
				out.RawByte(':')
				if v6Value == nil && (out.Flags&jwriter.NilSliceAsEmpty) == 0 {
					out.RawString("null")
				} else {
					out.RawByte('[')
					for v7, v8 := range v6Value {
						if v7 > 0 {
							out.RawByte(',')
						}
						out.String(string(v8))
					}
					out.RawByte(']')
				}
			}
			out.RawByte('}')
		}
	}
	out.RawByte('}')
}

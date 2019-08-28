// +build gofuzz

package vegeta

import (
	"bytes"
	"net/http"
)

// FuzzHTTPTargeter tests decoding an HTTP encoded target list.
func FuzzHTTPTargeter(fuzz []byte) int {
	headers, body, fuzz, ok := decodeFuzzTargetDefaults(fuzz)
	if !ok {
		return -1
	}
	targeter := NewHTTPTargeter(
		bytes.NewReader(fuzz),
		body,
		headers,
	)
	_, err := ReadAllTargets(targeter)
	if err != nil {
		return 0
	}
	return 1
}

// FuzzJSONTargeter tests decoding a JSON encoded target list.
func FuzzJSONTargeter(fuzz []byte) int {
	headers, body, fuzz, ok := decodeFuzzTargetDefaults(fuzz)
	if !ok {
		return -1
	}
	targeter := NewJSONTargeter(
		bytes.NewReader(fuzz),
		body,
		headers,
	)
	_, err := ReadAllTargets(targeter)
	if err != nil {
		return 0
	}
	return 1
}

func decodeFuzzTargetDefaults(fuzz []byte) (
	headers http.Header,
	body []byte,
	rest []byte,
	ok bool,
) {
	if len(fuzz) < 2 {
		return
	}
	headers = make(map[string][]string)
	body = []byte{}
	rest = []byte{}
	rest, ok = decodeFuzzHeaders(fuzz, headers)
	if !ok {
		return
	}
	if len(rest) == 0 {
		ok = true
		return
	}
	body, rest, ok = extractFuzzByteString(rest)
	return
}

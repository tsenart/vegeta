package vegeta

import (
	"bytes"
	"fmt"
	"strings"
	"net/http"
)

type header struct {
	key string
	value string
}

type Headers struct {
	headers []header
}

func (h Headers) Headers() *http.Header {
	hdr := new(http.Header)
	for _, header := range h.headers {
		hdr.Add(header.key, header.value)
	}
	return hdr
}

func (h Headers) String() string {
	buf := &bytes.Buffer{}
	for _, header := range h.headers {
		if _, err := buf.WriteString(fmt.Sprintf("%s: %s", header.key, header.value)); err != nil {
			return ""
		}
	}
	return buf.String()
}

func (h Headers) Set(value string) error {
	parts := strings.Split(value, ":")
	if len(parts) != 2 {
		return fmt.Errorf("Header '%s' has a wrong format", value)
	}
	key, val := strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1])
	if key == "" || val == "" {
		return fmt.Errorf("Header '%s' has a wrong format", value)
	}
	
	h.headers = append(h.headers, header{ key: key, value:value })
	return nil
}

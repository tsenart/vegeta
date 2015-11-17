package flagutil

import (
	"bytes"
	"fmt"
	"net"
	"net/http"
	"os"
	"strings"
)

// A File implements the flag.Value interface for an *os.File.
type File struct {
	*os.File
	Mode  os.FileMode
	Flags int
}

// Set parses the given value as filename to open with the defined Mode and
// Flags.
func (f *File) Set(value string) (err error) {
	var file *os.File
	switch value {
	case "stdin":
		file = os.Stdin
	case "stdout":
		file = os.Stdout
	default:
		file, err = os.OpenFile(value, f.Flags, f.Mode)
	}
	*(f.File) = *file
	return
}

// String returns the filename of the file.
func (f File) String() string { return f.Name() }

// A Header implements the flag.Value interface for an http.Header
type Header struct{ http.Header }

// Set parses the given value as an HTTP header and adds it to the Header.
func (h *Header) Set(value string) error {
	parts := strings.SplitN(value, ":", 2)
	if len(parts) != 2 {
		return fmt.Errorf("header '%s' has a wrong format", value)
	}
	key, val := strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1])
	if key == "" || val == "" {
		return fmt.Errorf("header '%s' has a wrong format", value)
	}
	// Add key/value directly to the http.Header (map[string][]string).
	// http.Header.Add() cannonicalizes keys but vegeta is used
	// to test systems that require case-sensitive headers.
	h.Header[key] = append(h.Header[key], val)
	return nil
}

func (h Header) String() string {
	var buf bytes.Buffer
	if err := h.Write(&buf); err != nil {
		return ""
	}
	return buf.String()
}

// An IP implements the Flag interface for a net.IP
type IP struct{ *net.IP }

// Set parses the given value as a net.IP and sets it.
func (f *IP) Set(value string) error {
	if *(f.IP) = net.ParseIP(value); *(f.IP) == nil {
		return fmt.Errorf("invalid IP address: %q", value)
	}
	return nil
}

// StringList implements the flag.Value interface for comma separated list
// of strings
type StringList struct{ List *[]string }

// Set parses the given value as a comma separated list of values and sets it.
func (f *StringList) Set(value string) error {
	*(f.List) = strings.Split(value, ",")
	return nil
}

// String implments the fmt.Stringer interface.
func (f StringList) String() string { return strings.Join((*f.List), ",") }

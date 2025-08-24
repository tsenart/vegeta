package modal

import (
	"bufio"
	"bytes"
	"errors"
	"io"
	"strings"
	"sync"
	"sync/atomic"

	jlexer "github.com/mailru/easyjson/jlexer"
	jwriter "github.com/mailru/easyjson/jwriter"
)

// Target is an HTTP request blueprint.
//
//go:generate go run ../internal/cmd/jsonschema/main.go -type=Target -output=target.schema.json
type Target struct {
	AppName      string `json:"appname"`
	FunctionName string `json:"functionname"`
	Body         []byte `json:"body,omitempty"`
}

// Equal returns true if the target is equal to the other given target.
func (t *Target) Equal(other *Target) bool {
	switch {
	case t == other:
		return true
	case t == nil || other == nil:
		return false
	default:
		return t.AppName == other.AppName &&
			t.FunctionName == other.FunctionName &&
			bytes.Equal(t.Body, other.Body)
	}
}

var (
	// ErrNoTargets is returned when not enough Targets are available.
	ErrNoTargets = errors.New("no targets to attack")
	// ErrNilTarget is returned when the passed Target pointer is nil.
	ErrNilTarget = errors.New("nil target")
	// ErrNoMethod is returned by JSONTargeter when a parsed Target has
	// no method.
	ErrNoMethod = errors.New("target: required method is missing")
	// ErrNoURL is returned by JSONTargeter when a parsed Target has no
	// URL.
	ErrNoURL = errors.New("target: required url is missing")
	// TargetFormats contains the canonical list of the valid target
	// format identifiers.
	TargetFormats    = []string{TextTargetFormat, JSONTargetFormat}
	ErrInvalidTarget = errors.New("target: must be formatted like 'appName/functionName'")
)

const (
	// TextTargetFormat is the human readable identifier for the text target format.
	TextTargetFormat = "text"
	// JSONTargetFormat is the human readable identifier for the JSON target format.
	JSONTargetFormat = "json"
)

// A Targeter decodes a Target or returns an error in case of failure.
// Implementations must be safe for concurrent use.
type Targeter func(*Target) error

// Decode is a convenience method that calls the underlying Targeter function.
func (tr Targeter) Decode(t *Target) error {
	return tr(t)
}

// NewJSONTargeter returns a new targeter that decodes one Target from the
// given io.Reader on every invocation. Each target is one JSON object in its own line.
//
// The method and url fields are required. If present, the body field must be base64 encoded.
// The generated [JSON Schema](lib/target.schema.json) defines the format in detail.
//
//	{"method":"POST", "url":"https://goku/1", "header":{"Content-Type":["text/plain"], "body": "Rk9P"}
//	{"method":"GET",  "url":"https://goku/2"}
//
// body will be set as the Target's body if no body is provided in each target definition.
// hdr will be merged with the each Target's headers.
func NewJSONTargeter(src io.Reader, body []byte) Targeter {
	type reader struct {
		*bufio.Reader
		sync.Mutex
	}
	rd := reader{Reader: bufio.NewReader(src)}

	return func(tgt *Target) (err error) {
		if tgt == nil {
			return ErrNilTarget
		}

		var jl jlexer.Lexer

		rd.Lock()
		for len(jl.Data) == 0 {
			if jl.Data, err = rd.ReadBytes('\n'); err != nil {
				break
			}
			jl.Data = bytes.TrimSpace(jl.Data) // Skip empty lines
		}
		rd.Unlock()

		if err != nil {
			if err == io.EOF {
				err = ErrNoTargets
			}
			return err
		}

		var t jsonTarget
		t.decode(&jl)

		if err = jl.Error(); err != nil {
			return err
		} else if t.AppName == "" {
			return ErrNoMethod
		} else if t.FunctionName == "" {
			return ErrNoURL
		}

		tgt.AppName = t.AppName
		tgt.FunctionName = t.FunctionName
		if tgt.Body = body; len(t.Body) > 0 {
			tgt.Body = t.Body
		}

		return nil
	}
}

func NewTextTargeter(src io.Reader, body []byte) Targeter {
	type reader struct {
		*bufio.Reader
		sync.Mutex
	}
	rd := reader{Reader: bufio.NewReader(src)}

	return func(tgt *Target) (err error) {
		if tgt == nil {
			return ErrNilTarget
		}

		var data []byte

		rd.Lock()
		for len(data) == 0 {
			if data, err = rd.ReadBytes('\n'); err != nil {
				break
			}
			data = bytes.TrimSpace(data) // Skip empty lines
		}
		rd.Unlock()

		if err != nil {
			if err == io.EOF {
				err = ErrNoTargets
			}
			return err
		}

		token := string(data)
		parts := strings.SplitN(token, "/", 2)
		if len(parts) != 2 {
			return ErrInvalidTarget
		}

		tgt.AppName = parts[0]
		tgt.FunctionName = parts[1]

		return nil
	}
}

// A TargetEncoder encodes a Target in a format that can be read by a Targeter.
type TargetEncoder func(*Target) error

// Encode is a convenience method that calls the underlying TargetEncoder function.
func (enc TargetEncoder) Encode(t *Target) error {
	return enc(t)
}

// NewJSONTargetEncoder returns a TargetEncoder that encodes Targets in the JSON format.
func NewJSONTargetEncoder(w io.Writer) TargetEncoder {
	var jw jwriter.Writer
	return func(t *Target) error {
		(*jsonTarget)(t).encode(&jw)
		if jw.Error != nil {
			return jw.Error
		}
		jw.RawByte('\n')
		_, err := jw.DumpTo(w)
		return err
	}
}

// NewStaticTargeter returns a Targeter which round-robins over the passed
// Targets.
func NewStaticTargeter(tgts ...Target) Targeter {
	i := int64(-1)
	return func(tgt *Target) error {
		if tgt == nil {
			return ErrNilTarget
		}
		*tgt = tgts[atomic.AddInt64(&i, 1)%int64(len(tgts))]
		return nil
	}
}

// ReadAllTargets eagerly reads all Targets out of the provided Targeter.
func ReadAllTargets(t Targeter) (tgts []Target, err error) {
	for {
		var tgt Target
		if err = t(&tgt); err == ErrNoTargets {
			break
		} else if err != nil {
			return nil, err
		}
		tgts = append(tgts, tgt)
	}

	if len(tgts) == 0 {
		return nil, ErrNoTargets
	}

	return tgts, nil
}

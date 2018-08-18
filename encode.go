package main

import (
	"bytes"
	"flag"
	"fmt"
	"io"
	"strings"

	vegeta "github.com/tsenart/vegeta/lib"
)

const (
	encodingCSV  = "csv"
	encodingGob  = "gob"
	encodingJSON = "json"
)

func encodeCmd() command {
	encs := "[" + strings.Join([]string{encodingCSV, encodingGob, encodingJSON}, ", ") + "]"
	fs := flag.NewFlagSet("vegeta encode", flag.ExitOnError)
	to := fs.String("to", encodingJSON, "Output encoding "+encs)
	output := fs.String("output", "stdout", "Output file")

	fs.Usage = func() {
		fmt.Println("Usage: vegeta encode [flags] [<file>...]")
		fs.PrintDefaults()
	}

	return command{fs, func(args []string) error {
		fs.Parse(args)
		files := fs.Args()
		if len(files) == 0 {
			files = append(files, "stdin")
		}
		return encode(files, *to, *output)
	}}
}

func encode(files []string, to, output string) error {
	srcs := make([]vegeta.Decoder, len(files))
	decs := []func(io.Reader) vegeta.Decoder{
		vegeta.NewDecoder,
		vegeta.NewJSONDecoder,
		vegeta.NewCSVDecoder,
	}

	for i, f := range files {
		in, err := file(f, false)
		if err != nil {
			return err
		}
		defer in.Close()

		// Auto-detect encoding of each file individually and buffer the read bytes
		// so that they can be read in subsequent decoding attempts as well as
		// in the final decoder.

		var buf bytes.Buffer
		var dec func(io.Reader) vegeta.Decoder
		for j := range decs {
			rd := io.MultiReader(bytes.NewReader(buf.Bytes()), io.TeeReader(in, &buf))
			if err = decs[j](rd).Decode(&vegeta.Result{}); err == nil {
				dec = decs[j]
				break
			}
		}

		if dec == nil {
			return fmt.Errorf("encode: can't detect encoding of %q", f)
		}

		srcs[i] = dec(io.MultiReader(&buf, in))
	}

	dec := vegeta.NewRoundRobinDecoder(srcs...)

	out, err := file(output, true)
	if err != nil {
		return err
	}
	defer out.Close()

	var enc vegeta.Encoder
	switch to {
	case encodingCSV:
		enc = vegeta.NewCSVEncoder(out)
	case encodingGob:
		enc = vegeta.NewEncoder(out)
	case encodingJSON:
		enc = vegeta.NewJSONEncoder(out)
	default:
		return fmt.Errorf("encode: unknown encoding %q", to)
	}

	for {
		var r vegeta.Result
		if err = dec.Decode(&r); err != nil {
			if err == io.EOF {
				break
			}
			return err
		} else if err = enc.Encode(&r); err != nil {
			return err
		}
	}

	return nil
}

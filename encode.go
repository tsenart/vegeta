package main

import (
	"bytes"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"

	vegeta "github.com/tsenart/vegeta/lib"
)

const (
	encodingCSV  = "csv"
	encodingGob  = "gob"
	encodingJSON = "json"
)

const encodeUsage = `Usage: vegeta encode [options] [<file>...]

Encodes vegeta attack results from one encoding to another.
The supported encodings are Gob (binary), CSV and JSON.
Each input file may have a different encoding which is detected
automatically.

Arguments:
  <file>  A file with vegeta attack results encoded with one of
          the supported encodings (gob | json | csv) [default: stdin]

Options:
  --to      Output encoding (gob | json | csv) [default: json]
  --output  Output file [default: stdout]

Examples:
  echo "GET http://:80" | vegeta attack -rate=1/s > results.gob
  cat results.gob | vegeta encode | jq -c 'del(.body)' | vegeta encode -to gob
`

func encodeCmd() command {
	encs := "[" + strings.Join([]string{encodingCSV, encodingGob, encodingJSON}, ", ") + "]"
	fs := flag.NewFlagSet("vegeta encode", flag.ExitOnError)
	to := fs.String("to", encodingJSON, "Output encoding "+encs)
	output := fs.String("output", "stdout", "Output file")

	fs.Usage = func() {
		fmt.Fprintln(os.Stderr, encodeUsage)
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

	sigch := make(chan os.Signal, 1)
	signal.Notify(sigch, os.Interrupt)

	for {
		select {
		case <-sigch:
			return nil
		default:
		}

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

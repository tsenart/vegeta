package main

import (
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"

	vegeta "github.com/tsenart/vegeta/v12/lib"
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

The CSV encoder doesn't write a header. The columns written by it are:

   1. Unix timestamp in nanoseconds since epoch
   2. HTTP status code
   3. Request latency in nanoseconds
   4. Bytes out
   5. Bytes in
   6. Error
   7. Base64 encoded response body
   8. Attack name
   9. Sequence number of request
  10. Method
  11. URL
  12. Base64 encoded response headers

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
		fmt.Fprintf(os.Stderr, "%s\n", encodeUsage)
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
	dec, mc, err := decoder(files)
	defer mc.Close()
	if err != nil {
		return err
	}

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

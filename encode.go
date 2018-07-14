package main

import (
	"flag"
	"fmt"
	"io"
	"os"

	vegeta "github.com/tsenart/vegeta/lib"
)

const (
	encodingCSV  = "csv"
	encodingGob  = "gob"
	encodingJSON = "json"
)

type decoderFunc func(io.Reader) vegeta.Decoder
type encoderFunc func(io.Writer) vegeta.Encoder

func encodeCmd() command {
	var (
		fs     = flag.NewFlagSet("encode", flag.ExitOnError)
		from   = fs.String("from", "gob", "Input decoding [csv, gob, json]")
		to     = fs.String("to", "json", "Output encoding [csv, gob, json]")
		output = fs.String("output", "", "Output file")
	)

	fs.Usage = func() {
		fmt.Println("Usage: vegeta encode [flags] [<file>...]")
		fs.PrintDefaults()
	}

	return command{
		fs,
		func(args []string) error {
			fs.Parse(args)
			return encode(*from, *to, *output, args...)
		},
	}
}

func encode(from, to, output string, inputs ...string) error {
	var decFn decoderFunc

	switch from {
	case encodingCSV:
		decFn = vegeta.NewCSVDecoder
	case encodingJSON:
		decFn = vegeta.NewJSONDecoder
	default:
		// Gob is our default decode format to play nicely in pipes with attack.
		decFn = vegeta.NewDecoder
	}

	decs := []vegeta.Decoder{}

	if len(inputs) > 0 {
		for _, name := range inputs {
			f, err := os.Open(name)
			if err != nil {
				return err
			}
			defer f.Close()

			decs = append(decs, decFn(f))
		}
	} else {
		decs = append(decs, decFn(os.Stdin))
	}

	in := vegeta.NewRoundRobinDecoder(decs...)

	var encFn encoderFunc

	switch to {
	case encodingCSV:
		encFn = vegeta.NewCSVEncoder
	case encodingGob:
		encFn = vegeta.NewEncoder
	default:
		// JSON is our default encoding format to play nicely in pipes with auxiliary
		// tools like jq.
		encFn = vegeta.NewJSONEncoder
	}

	var out vegeta.Encoder

	if output != "" {
		f, err := os.Create(output)
		if err != nil {
			return err
		}
		defer f.Close()

		out = encFn(f)
	} else {
		out = encFn(os.Stdout)
	}

	for {
		var r vegeta.Result
		if err := in.Decode(&r); err != nil {
			if err == io.EOF {
				break
			}
			return err
		} else if err := out.Encode(&r); err != nil {
			return err
		}
	}

	return nil
}

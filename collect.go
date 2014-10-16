package main

import (
	"encoding/gob"
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"

	"github.com/tsenart/vegeta/lib"
)

func collectCmd() command {
	fs := flag.NewFlagSet("vegeta collect", flag.ExitOnError)
	inputs := fs.String("inputs", "stdin", "Input files (comma separated)")
	output := fs.String("output", "stdout", "Output file")
	return command{fs, func(args []string) error {
		fs.Parse(args)
		return collect(*inputs, *output)
	}}
}

// collect reads multiple sources of result streams and serializes them into
// one output stream.
func collect(inputs, output string) error {
	files := strings.Split(inputs, ",")
	srcs := make([]io.Reader, len(files))
	for i, f := range files {
		in, err := file(f, false)
		if err != nil {
			return err
		}
		defer in.Close()
		srcs[i] = in
	}

	out, err := file(output, true)
	if err != nil {
		return fmt.Errorf("error opening %s: %s", output, err)
	}
	defer out.Close()

	res, errs := vegeta.Collect(srcs...)
	enc := gob.NewEncoder(out)
	sig := make(chan os.Signal, 1)
	signal.Notify(sig, os.Interrupt, os.Kill)

	for {
		select {
		case s := <-sig:
			fmt.Printf("Received signal: %s. Exiting gracefully...", s)
			return nil
		case r, ok := <-res:
			if !ok {
				return nil
			}
			if err = enc.Encode(r); err != nil {
				return err
			}
		case err := <-errs:
			return err
		}
	}
}

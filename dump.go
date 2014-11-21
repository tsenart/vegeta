package main

import (
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"

	vegeta "github.com/tsenart/vegeta/lib"
)

func dumpCmd() command {
	fs := flag.NewFlagSet("vegeta dump", flag.ExitOnError)
	dumper := fs.String("dumper", "", "Dumper [json, csv]")
	inputs := fs.String("inputs", "stdin", "Input files (comma separated)")
	output := fs.String("output", "stdout", "Output file")
	return command{fs, func(args []string) error {
		fs.Parse(args)
		return dump(*dumper, *inputs, *output)
	}}
}

func dump(dumper, inputs, output string) error {
	dump, ok := dumpers[dumper]
	if !ok {
		return fmt.Errorf("unsupported dumper: %s", dumper)
	}

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
		return err
	}
	defer out.Close()

	sig := make(chan os.Signal, 1)
	signal.Notify(sig, os.Interrupt)
	res, errs := vegeta.Collect(srcs...)

	for {
		select {
		case _ = <-sig:
			return nil
		case r, ok := <-res:
			if !ok {
				return nil
			}
			dmp, err := dump.Dump(r)
			if err != nil {
				return err
			} else if _, err = out.Write(dmp); err != nil {
				return err
			}
		case err, ok := <-errs:
			if !ok {
				return nil
			}
			return err
		}
	}
}

var dumpers = map[string]vegeta.Dumper{
	"csv":  vegeta.DumpCSV,
	"json": vegeta.DumpJSON,
}

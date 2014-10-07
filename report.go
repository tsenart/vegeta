package main

import (
	"flag"
	"io"
	"log"
	"strings"

	vegeta "github.com/tsenart/vegeta/lib"
)

func reportCmd() command {
	fs := flag.NewFlagSet("vegeta report", flag.ExitOnError)
	opts := &reportOpts{}

	fs.StringVar(&opts.reporter, "reporter", "text", "Reporter [text, json, plot]")
	fs.StringVar(&opts.inputf, "input", "stdin", "Input files (comma separated)")
	fs.StringVar(&opts.outputf, "output", "stdout", "Output file")

	return command{fs, func(args []string) error {
		fs.Parse(args)
		return report(opts)
	}}
}

// reportOpts aggregates the report function command options
type reportOpts struct {
	reporter string
	inputf   string
	outputf  string
}

// report validates the report arguments, sets up the required resources
// and writes the report
func report(opts *reportOpts) error {
	rep, ok := reporters[opts.reporter]
	if !ok {
		log.Println("Reporter provided is not supported. Using text")
		rep = vegeta.ReportText
	}

	files := strings.Split(opts.inputf, ",")
	srcs := make([]io.Reader, len(files))
	for i, f := range files {
		in, err := file(f, false)
		if err != nil {
			return err
		}
		srcs[i] = in
	}

	out, err := file(opts.outputf, true)
	if err != nil {
		return err
	}
	defer out.Close()

	res, err := vegeta.NewResults(srcs...)
	if err != nil {
		return err
	}

	data, err := rep(res)
	if err != nil {
		return err
	}
	_, err = out.Write(data)
	return err
}

var reporters = map[string]vegeta.Reporter{
	"text": vegeta.ReportText,
	"json": vegeta.ReportJSON,
	"plot": vegeta.ReportPlot,
}

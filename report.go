package main

import (
	"flag"
	vegeta "github.com/tsenart/vegeta/lib"
	"io"
	"log"
	"os"
)

func reportCmd(args []string) command {
	fs := flag.NewFlagSet("report", flag.ExitOnError)
	reporter := fs.String("reporter", "text", "Reporter [text, json, plot:timings]")
	input := fs.String("input", "stdin", "Vegeta Results file")
	output := fs.String("output", "stdout", "Output file")
	fs.Parse(args)

	return func() error {
		return report(*reporter, *input, *output)
	}
}

// report validates the report arguments, sets up the required resources
// and writes the report
func report(reporter, input, output string) error {
	var rep vegeta.Reporter
	switch reporter {
	case "text":
		rep = vegeta.ReportText
	case "json":
		rep = vegeta.ReportJSON
	case "plot:timings":
		rep = vegeta.ReportTimingsPlot
	default:
		log.Println("Reporter provided is not supported. Using text")
		rep = vegeta.ReportText
	}

	var in io.Reader
	switch input {
	case "stdin":
		in = os.Stdin
	default:
		file, err := os.Open(input)
		if err != nil {
			return err
		}
		defer file.Close()
		in = file
	}

	var out io.Writer
	switch output {
	case "stdout":
		out = os.Stdout
	default:
		file, err := os.Create(output)
		if err != nil {
			return err
		}
		defer file.Close()
		out = file
	}

	results := vegeta.Results{}
	if err := results.ReadFrom(in); err != nil {
		return err
	}
	if err := rep(results, out); err != nil {
		return err
	}

	return nil
}

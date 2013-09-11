package main

import (
	"flag"
	vegeta "github.com/tsenart/vegeta/lib"
	"log"
)

func reportCmd(args []string) command {
	fs := flag.NewFlagSet("report", flag.ExitOnError)
	reporter := fs.String("reporter", "text", "Reporter [text, json, plot:timings]")
	input := fs.String("input", "stdin", "Input file")
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

	in, err := file(input, false)
	if err != nil {
		return err
	}
	defer in.Close()

	out, err := file(output, true)
	if err != nil {
		return err
	}
	defer out.Close()

	results := vegeta.Results{}
	if err := results.ReadFrom(in); err != nil {
		return err
	}

	if err := rep(results, out); err != nil {
		return err
	}

	return nil
}

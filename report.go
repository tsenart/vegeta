package main

import (
	vegeta "github.com/tsenart/vegeta/lib"
	"io"
	"log"
	"os"
)

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

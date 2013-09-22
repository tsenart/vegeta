package main

import (
	"flag"
	vegeta "github.com/tsenart/vegeta/lib"
	"log"
	"strings"
)

func reportCmd(args []string) command {
	fs := flag.NewFlagSet("report", flag.ExitOnError)
	reporter := fs.String("reporter", "text", "Reporter [text, json, plot]")
	input := fs.String("input", "stdin", "Input files (comma separated)")
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
	case "plot":
		rep = vegeta.ReportPlot
	default:
		log.Println("Reporter provided is not supported. Using text")
		rep = vegeta.ReportText
	}

	all := vegeta.Results{}
	for _, input := range strings.Split(input, ",") {
		in, err := file(input, false)
		if err != nil {
			return err
		}
		defer in.Close()
		results := vegeta.Results{}
		if err := results.Decode(in); err != nil {
			return err
		}
		all = append(all, results...)
	}
	all.Sort()

	out, err := file(output, true)
	if err != nil {
		return err
	}
	defer out.Close()

	if data, err := rep(all); err != nil {
		return err
	} else if _, err := out.Write(data); err != nil {
		return err
	}

	return nil
}

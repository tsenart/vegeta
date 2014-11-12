package main

import (
	"flag"
	"io"
	"log"
	"os"
	"os/signal"
	"sort"
	"strings"

	vegeta "github.com/tsenart/vegeta/lib"
)

func reportCmd() command {
	fs := flag.NewFlagSet("vegeta report", flag.ExitOnError)
	reporter := fs.String("reporter", "text", "Reporter [csv, json, plot, text]")
	inputs := fs.String("inputs", "stdin", "Input files (comma separated)")
	output := fs.String("output", "stdout", "Output file")
	return command{fs, func(args []string) error {
		fs.Parse(args)
		return report(*reporter, *inputs, *output)
	}}
}

// report validates the report arguments, sets up the required resources
// and writes the report
func report(reporter, inputs, output string) error {
	rep, ok := reporters[reporter]
	if !ok {
		log.Println("Reporter provided is not supported. Using text")
		rep = vegeta.ReportText
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

	var results vegeta.Results
	res, errs := vegeta.Collect(srcs...)
	sig := make(chan os.Signal, 1)
	signal.Notify(sig, os.Interrupt)

outer:
	for {
		select {
		case _ = <-sig:
			break outer
		case r, ok := <-res:
			if !ok {
				break outer
			}
			results = append(results, r)
		case err, ok := <-errs:
			if !ok {
				break outer
			}
			return err
		}
	}

	sort.Sort(results)
	data, err := rep.Report(results)
	if err != nil {
		return err
	}
	_, err = out.Write(data)
	return err
}

var reporters = map[string]vegeta.Reporter{
	"csv":  vegeta.ReportCSV,
	"json": vegeta.ReportJSON,
	"plot": vegeta.ReportPlot,
	"text": vegeta.ReportText,
}

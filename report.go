package main

import (
	"flag"
	"log"
	"strconv"
	"strings"
	"time"

	vegeta "github.com/tsenart/vegeta/lib"
)

func reportCmd() command {
	fs := flag.NewFlagSet("vegeta report", flag.ExitOnError)
	opts := &reportOpts{}

	fs.StringVar(&opts.reporter, "reporter", "text", "Reporter [text, json, plot]")
	fs.StringVar(&opts.inputf, "input", "stdin", "Input files (comma separated)")
	fs.StringVar(&opts.outputf, "output", "stdout", "Output file")
	fs.StringVar(&opts.bucketMins, "buckets", "", "Bucket minimum values in ms")

	return command{fs, func(args []string) error {
		fs.Parse(args)
		return report(opts)
	}}
}

// reportOpts aggregates the report function command options
type reportOpts struct {
	reporter   string
	inputf     string
	outputf    string
	bucketMins string
}

// report validates the report arguments, sets up the required resources
// and writes the report
func report(opts *reportOpts) error {
	rep, ok := reporters[opts.reporter]
	if !ok {
		log.Println("Reporter provided is not supported. Using text")
		rep = vegeta.ReportText
	}

	var buckets vegeta.Buckets
	if opts.bucketMins != "" {
		bucketMinStrs := strings.Split(opts.bucketMins, ",")
		bucketMins := make([]time.Duration, len(bucketMinStrs))
		for i, s := range bucketMinStrs {
			ival, err := strconv.ParseInt(s, 10, 64)
			if err != nil {
				log.Printf("Error parsing bucket %q: %v", s, err)
				continue
			}
			bucketMins[i] = time.Millisecond * time.Duration(ival)
		}
		buckets = make(vegeta.Buckets, len(bucketMins)+1)
		buckets[0] = &vegeta.Bucket{Minimum: 0, Maximum: bucketMins[0]}
		for i, min := range bucketMins {
			if i == (len(bucketMins) - 1) {
				buckets[i+1] = &vegeta.Bucket{Minimum: min, Maximum: -1}
				continue
			}
			buckets[i+1] = &vegeta.Bucket{Minimum: min, Maximum: bucketMins[i+1]}
		}
	}

	var all vegeta.Results
	for _, input := range strings.Split(opts.inputf, ",") {
		in, err := file(input, false)
		if err != nil {
			return err
		}

		var results vegeta.Results
		if err = results.Decode(in); err != nil {
			return err
		}
		in.Close()

		all = append(all, results...)
	}
	all.Sort()

	out, err := file(opts.outputf, true)
	if err != nil {
		return err
	}
	defer out.Close()

	data, err := rep(all, buckets)
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

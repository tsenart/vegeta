package main

import (
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"

	vegeta "github.com/tsenart/vegeta/lib"
)

const reportUsage = `Usage: vegeta report [options] [<file>...]

Outputs a report of attack results.

Arguments:
  <file>  A file with vegeta attack results encoded with one of
          the supported encodings (gob | json | csv) [default: stdin]

Options:
  --type    Which report type to generate (text | json | hist[buckets]).
            [default: text]
  --output  Output file [default: stdout]

Examples:
  echo "GET http://:80" | vegeta attack -rate=10/s > results.gob
  echo "GET http://:80" | vegeta attack -rate=100/s | vegeta encode > results.json
  vegeta report results.*
`

func reportCmd() command {
	fs := flag.NewFlagSet("vegeta report", flag.ExitOnError)
	typ := fs.String("type", "text", "Report type to generate [text, json, hist[buckets]]")
	output := fs.String("output", "stdout", "Output file")

	fs.Usage = func() {
		fmt.Fprintln(os.Stderr, reportUsage)
	}

	return command{fs, func(args []string) error {
		fs.Parse(args)
		files := fs.Args()
		if len(files) == 0 {
			files = append(files, "stdin")
		}
		return report(files, *typ, *output)
	}}
}

func report(files []string, typ, output string) error {
	if len(typ) < 4 {
		return fmt.Errorf("invalid report type: %s", typ)
	}

	dec, mc, err := decoder(files)
	defer mc.Close()
	if err != nil {
		return err
	}

	out, err := file(output, true)
	if err != nil {
		return err
	}
	defer out.Close()

	var (
		rep    vegeta.Reporter
		report vegeta.Report
	)

	switch typ[:4] {
	case "plot":
		return fmt.Errorf("The plot reporter has been deprecated and succeeded by the vegeta plot command")
	case "text":
		var m vegeta.Metrics
		rep, report = vegeta.NewTextReporter(&m), &m
	case "json":
		var m vegeta.Metrics
		rep, report = vegeta.NewJSONReporter(&m), &m
	case "hist":
		if len(typ) < 6 {
			return fmt.Errorf("bad buckets: '%s'", typ[4:])
		}
		var hist vegeta.Histogram
		if err := hist.Buckets.UnmarshalText([]byte(typ[4:])); err != nil {
			return err
		}
		rep, report = vegeta.NewHistogramReporter(&hist), &hist
	default:
		return fmt.Errorf("unknown report type: %q", typ)
	}

	sigch := make(chan os.Signal, 1)
	signal.Notify(sigch, os.Interrupt)

decode:
	for {
		select {
		case <-sigch:
			break decode
		default:
			var r vegeta.Result
			if err = dec.Decode(&r); err != nil {
				if err == io.EOF {
					break decode
				}
				return err
			}
			report.Add(&r)
		}
	}

	if c, ok := report.(vegeta.Closer); ok {
		c.Close()
	}

	return rep.Report(out)
}

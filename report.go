package main

import (
	"flag"
	"fmt"
	"io"
	"os"
	"os/signal"
	"strings"
	"time"

	vegeta "github.com/tsenart/vegeta/v12/lib"
)

const reportUsage = `Usage: vegeta report [options] [<file>...]

Outputs a report of attack results.

Arguments:
  <file>  A file with vegeta attack results encoded with one of
          the supported encodings (gob | json | csv) [default: stdin]

Options:
  --type    Which report type to generate (text | json | hist[buckets] | hdrplot).
            [default: text]

  --every   Write the report to --output at every given interval (e.g 100ms)
            The default of 0 means the report will only be written after
            all results have been processed. [default: 0]

  --output  Output file [default: stdout]

Examples:
  echo "GET http://:80" | vegeta attack -rate=10/s > results.gob
  echo "GET http://:80" | vegeta attack -rate=100/s | vegeta encode > results.json
  vegeta report results.*
`

func reportCmd() command {
	fs := flag.NewFlagSet("vegeta report", flag.ExitOnError)
	typ := fs.String("type", "text", "Report type to generate [text, json, hist[buckets], hdrplot]")
	every := fs.Duration("every", 0, "Report interval")
	output := fs.String("output", "stdout", "Output file")
	buckets := fs.String("buckets", "", "Histogram buckets, e.g.: \"[0,1ms,10ms]\"")

	fs.Usage = func() {
		fmt.Fprintln(os.Stderr, reportUsage)
	}

	return command{fs, func(args []string) error {
		fs.Parse(args)
		files := fs.Args()
		if len(files) == 0 {
			files = append(files, "stdin")
		}
		return report(files, *typ, *output, *every, *buckets)
	}}
}

func report(files []string, typ, output string, every time.Duration, bucketsStr string) error {
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

	switch typ {
	case "plot":
		return fmt.Errorf("The plot reporter has been deprecated and succeeded by the vegeta plot command")
	case "text":
		var m vegeta.Metrics
		rep, report = vegeta.NewTextReporter(&m), &m
	case "json":
		var m vegeta.Metrics
		if bucketsStr != "" {
			m.Histogram = &vegeta.Histogram{}
			if err := m.Histogram.Buckets.UnmarshalText([]byte(bucketsStr)); err != nil {
				return err
			}
		}
		rep, report = vegeta.NewJSONReporter(&m), &m
	case "hdrplot":
		var m vegeta.Metrics
		rep, report = vegeta.NewHDRHistogramPlotReporter(&m), &m
	default:
		switch {
		case strings.HasPrefix(typ, "hist"):
			var hist vegeta.Histogram
			if bucketsStr == "" { // Old way
				if len(typ) < 6 {
					return fmt.Errorf("bad buckets: '%s'", typ[4:])
				}
				bucketsStr = typ[4:]
			}
			if err := hist.Buckets.UnmarshalText([]byte(bucketsStr)); err != nil {
				return err
			}
			rep, report = vegeta.NewHistogramReporter(&hist), &hist
		default:
			return fmt.Errorf("unknown report type: %q", typ)
		}
	}

	sigch := make(chan os.Signal, 1)
	signal.Notify(sigch, os.Interrupt)

	var ticks <-chan time.Time
	if every > 0 {
		ticker := time.NewTicker(every)
		defer ticker.Stop()
		ticks = ticker.C
	}

	rc, _ := report.(vegeta.Closer)
decode:
	for {
		select {
		case <-sigch:
			break decode
		case <-ticks:
			if err = clear(out); err != nil {
				return err
			} else if err = writeReport(rep, rc, out); err != nil {
				return err
			}
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

	return writeReport(rep, rc, out)
}

func writeReport(r vegeta.Reporter, rc vegeta.Closer, out io.Writer) error {
	if rc != nil {
		rc.Close()
	}
	return r.Report(out)
}

func clear(out io.Writer) error {
	if f, ok := out.(*os.File); ok && f == os.Stdout {
		return clearScreen()
	}
	return nil
}

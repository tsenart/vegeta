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

var plotUsage = strings.TrimSpace(`
Usage: vegeta plot [options] [<file>...]

Outputs an HTML time series plot of request latencies over time.
The X axis represents elapsed time in seconds from the beginning
of the earliest attack in all input files. The Y axis represents
request latency in milliseconds.

Arguments:
  <file>  A file output by running vegeta attack [default: stdin]

Options:
  --title      Title and header of the resulting HTML page.
               [default: Vegeta Plot]
  --threshold  Threshold of data points to downsample series to.
               Series with less than --threshold number of data
               points are not downsampled. [default: 4000]
`)

func plotCmd() command {
	fs := flag.NewFlagSet("vegeta plot", flag.ExitOnError)
	title := fs.String("title", "Vegeta Plot", "Title and header of the resulting HTML page")
	threshold := fs.Int("threshold", 4000, "Threshold of data points above which series are downsampled.")
	output := fs.String("output", "stdout", "Output file")

	fs.Usage = func() {
		fmt.Fprintln(os.Stderr, plotUsage)
	}

	return command{fs, func(args []string) error {
		fs.Parse(args)
		files := fs.Args()
		if len(files) == 0 {
			files = append(files, "stdin")
		}
		return plot(files, *threshold, *title, *output)
	}}
}

func plot(files []string, threshold int, title, output string) error {
	srcs := make([]vegeta.Decoder, len(files))
	for i, f := range files {
		in, err := file(f, false)
		if err != nil {
			return err
		}
		defer in.Close()
		srcs[i] = vegeta.NewDecoder(in)
	}
	dec := vegeta.NewRoundRobinDecoder(srcs...)

	out, err := file(output, true)
	if err != nil {
		return err
	}
	defer out.Close()

	sigch := make(chan os.Signal, 1)
	signal.Notify(sigch, os.Interrupt)

	var rs vegeta.Results
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
			rs.Add(&r)
		}
	}

	plot := vegeta.NewHTMLPlot(title, threshold, rs)
	return plot.WriteTo(out)
}

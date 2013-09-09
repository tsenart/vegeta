package vegeta

import (
	"code.google.com/p/plotinum/plot"
	"code.google.com/p/plotinum/plotter"
	"code.google.com/p/plotinum/plotutil"
	"code.google.com/p/plotinum/vg"
	"code.google.com/p/plotinum/vg/vgsvg"
	"fmt"
	"io"
	"text/tabwriter"
	"time"
)

// Reporter represents any function which takes a slice of Results and
// generates a report, writing it to an io.Writer and returning an error
// in case of failure
type Reporter func([]Result, io.Writer) error

// ReportText computes and prints some metrics out of results
// as formatted text. Metrics include avg time per request, success ratio,
// total number of request, avg bytes in and avg bytes out.
func ReportText(results []Result, out io.Writer) error {
	totalRequests := float64(len(results))
	totalTime := time.Duration(0)
	totalBytesOut := uint64(0)
	totalBytesIn := uint64(0)
	totalSuccess := uint64(0)
	histogram := map[uint16]uint64{}
	errors := map[string]struct{}{}

	for _, res := range results {
		histogram[res.Code]++
		totalTime += res.Timing
		totalBytesOut += res.BytesOut
		totalBytesIn += res.BytesIn
		if res.Code >= 200 && res.Code < 300 {
			totalSuccess++
		}
		if res.Error != nil {
			errors[res.Error.Error()] = struct{}{}
		}
	}

	avgTime := time.Duration(float64(totalTime) / totalRequests)
	avgBytesOut := float64(totalBytesOut) / totalRequests
	avgBytesIn := float64(totalBytesIn) / totalRequests
	avgSuccess := float64(totalSuccess) / totalRequests

	w := tabwriter.NewWriter(out, 0, 8, 2, '\t', tabwriter.StripEscape)
	fmt.Fprintf(w, "Time(avg)\tRequests\tSuccess\tBytes(rx/tx)\n")
	fmt.Fprintf(w, "%s\t%d\t%.2f%%\t%.2f/%.2f\n", avgTime, int(totalRequests), avgSuccess*100, avgBytesIn, avgBytesOut)

	fmt.Fprintf(w, "\nCount:\t")
	for _, count := range histogram {
		fmt.Fprintf(w, "%d\t", count)
	}
	fmt.Fprintf(w, "\nStatus:\t")
	for code := range histogram {
		fmt.Fprintf(w, "%d\t", code)
	}

	fmt.Fprintln(w, "\n\nError Set:")
	for err := range errors {
		fmt.Fprintln(w, err)
	}

	return w.Flush()
}

// ReportTimingsPlot builds up a plot of the response times of the requests
// in SVG format and writes it to out
func ReportTimingsPlot(results []Result, out io.Writer) error {
	p, err := plot.New()
	if err != nil {
		return err
	}
	pts := make(plotter.XYs, len(results))
	for i := 0; i < len(pts); i++ {
		pts[i].X = results[i].Timestamp.Sub(results[0].Timestamp).Seconds()
		pts[i].Y = results[i].Timing.Seconds() * 1000
	}

	line, err := plotter.NewLine(pts)
	if err != nil {
		return err
	}
	line.Color = plotutil.Color(1)

	p.Add(line)
	p.X.Padding = vg.Length(3.0)
	p.X.Label.Text = "Time elapsed"
	p.Y.Padding = vg.Length(3.0)
	p.Y.Label.Text = "Latency (ms)"

	w, h := vg.Millimeters(float64(len(results))), vg.Centimeters(12.0)
	canvas := vgsvg.New(w, h)
	p.Draw(plot.MakeDrawArea(canvas))

	_, err = canvas.WriteTo(out)
	return err
}

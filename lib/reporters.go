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
)

// Reporter represents any function which takes a slice of Results and
// generates a report, writing it to an io.Writer and returning an error
// in case of failure
type Reporter func([]Result, io.Writer) error

// ReportText writes a computed Metrics struct to out as aligned, formatted text
func ReportText(results []Result, out io.Writer) error {
	m := NewMetrics(results)

	w := tabwriter.NewWriter(out, 0, 8, 2, '\t', tabwriter.StripEscape)
	fmt.Fprintf(w, "Time(avg)\tRequests\tSuccess\tBytes(rx/tx)\n")
	fmt.Fprintf(w, "%s\t%d\t%.2f%%\t%.2f/%.2f\n", m.MeanTiming, m.TotalRequests, m.MeanSuccess*100, m.MeanBytesIn, m.MeanBytesOut)

	fmt.Fprintf(w, "\nCount:\t")
	for _, count := range m.StatusCodes {
		fmt.Fprintf(w, "%d\t", count)
	}
	fmt.Fprintf(w, "\nStatus:\t")
	for code := range m.StatusCodes {
		fmt.Fprintf(w, "%d\t", code)
	}

	fmt.Fprintln(w, "\n\nError Set:")
	for err := range m.Errors {
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

package vegeta

import (
	"code.google.com/p/plotinum/plot"
	"code.google.com/p/plotinum/plotter"
	"code.google.com/p/plotinum/plotutil"
	"code.google.com/p/plotinum/vg"
	"code.google.com/p/plotinum/vg/vgsvg"
	"container/list"
	"io"
	"time"
)

type TimingsPlotReporter struct {
	results *list.List
}

// NewTimingsPlotReporter initializes a TimingsPlotReporter
func NewTimingsPlotReporter() *TimingsPlotReporter {
	return &TimingsPlotReporter{results: list.New()}
}

// Add inserts response to be used in the report, sorted by timestamp.
func (r *TimingsPlotReporter) Add(res *Result) {
	// Empty list
	if r.results.Len() == 0 {
		r.results.PushFront(res)
		return
	}
	// Happened after all others
	if last := r.results.Back().Value.(*Result); last.Timestamp.Before(res.Timestamp) {
		r.results.PushBack(res)
		return
	}
	// Happened before all others
	if first := r.results.Front().Value.(*Result); first.Timestamp.After(res.Timestamp) {
		r.results.PushFront(res)
		return
	}
	// O(n) worst case insertion time
	for e := r.results.Front(); e != nil; e = e.Next() {
		needle := e.Value.(*Result)
		if res.Timestamp.Before(needle.Timestamp) {
			r.results.InsertBefore(res, e)
			return
		}
	}
}

// Report builds up a plot of the response times of the requests
// in SVG format and writes it to out
func (r *TimingsPlotReporter) Report(out io.Writer) error {
	timestamps := make([]time.Time, 0)
	timings := make([]time.Duration, 0)

	for e := r.results.Front(); e != nil; e = e.Next() {
		r := e.Value.(*Result)
		timestamps = append(timestamps, r.Timestamp)
		timings = append(timings, r.Timing)
	}

	p, err := plot.New()
	if err != nil {
		return err
	}
	pts := make(plotter.XYs, len(timestamps))
	for i := 0; i < len(pts); i++ {
		pts[i].X = timestamps[i].Sub(timestamps[0]).Seconds()
		pts[i].Y = timings[i].Seconds() * 1000
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

	w, h := vg.Millimeters(float64(len(timestamps))), vg.Centimeters(12.0)
	canvas := vgsvg.New(w, h)
	p.Draw(plot.MakeDrawArea(canvas))

	_, err = canvas.WriteTo(out)
	return err
}

//go:generate go run -tags=dev assets_gen.go

package plot

import (
	"encoding/json"
	"fmt"
	"html/template"
	"io"
	"math"
	"sort"
	"strconv"
	"strings"
	"time"

	vegeta "github.com/tsenart/vegeta/v12/lib"
	"github.com/tsenart/vegeta/v12/lib/lttb"
)

// An Plot represents an interactive HTML time series
// plot of Result latencies over time.
type Plot struct {
	title     string
	threshold int
	series    map[string]*labeledSeries
	label     Labeler
}

// An Labeler is a function that returns a label
// to partition and represent Results in separate (but overlaid) line charts
// in the rendered plot.
type Labeler func(*vegeta.Result) (label string)

// ErrorLabeler is an HTMLPlotLabeler which
// labels a result with an OK or ERROR label
// based on whether it has an error set.
func ErrorLabeler(r *vegeta.Result) (label string) {
	switch r.Error {
	case "":
		return "OK"
	default:
		return "ERROR"
	}
}

// labeledSeries groups timeSeries by a label function applied to
// each incoming result. It re-orders and buffers out-of-order results
// by their sequence number before adding them to the labeled timeSeries.
type labeledSeries struct {
	began  time.Time
	seq    uint64
	buf    map[uint64]point
	series map[string]*timeSeries
	label  Labeler
}

// a point to be added to a timeSeries.
type point struct {
	ts  *timeSeries
	seq uint64
	t   time.Time
	v   float64
}

func newLabeledSeries(label Labeler) *labeledSeries {
	return &labeledSeries{
		buf:    map[uint64]point{},
		series: map[string]*timeSeries{},
		label:  label,
	}
}

func (ls *labeledSeries) add(r *vegeta.Result) (err error) {
	label := ls.label(r)

	ts, ok := ls.series[label]
	if !ok {
		ts = newTimeSeries(r.Attack, label)
		ls.series[label] = ts
	}

	p := point{
		ts:  ts,
		seq: r.Seq,
		t:   r.Timestamp,
		v:   r.Latency.Seconds() * 1000,
	}

	if ls.buf[p.seq] = p; p.seq != ls.seq {
		return nil // buffer
	} else if ls.seq == 0 {
		ls.began = r.Timestamp // first point in attack
	}

	for len(ls.buf) > 0 {
		p, ok := ls.buf[ls.seq]
		if !ok {
			break
		}
		delete(ls.buf, ls.seq)

		// timestamp in ms precision
		err = p.ts.add(uint64(p.t.Sub(ls.began))/1e6, p.v)
		if err != nil {
			return fmt.Errorf("point with sequence number %d in %v", p.seq, err)
		}

		ls.seq++
	}

	return nil
}

// Opt is a functional option type for Plot.
type Opt func(*Plot)

// Title returns an Opt that sets the title of a Plot.
func Title(title string) Opt {
	return func(p *Plot) { p.title = title }
}

// Downsample returns an Opt that enables downsampling
// to the given threshold number of data points per labeled series.
func Downsample(threshold int) Opt {
	return func(p *Plot) { p.threshold = threshold }
}

// Label returns an Opt that sets the given Labeler
// to be used to partition results into multiple overlaid line charts.
func Label(l Labeler) Opt {
	return func(p *Plot) { p.label = l }
}

// New returns a Plot with the given Opts applied.
// If no Label opt is given, ErrorLabeler will be used as default.
func New(opts ...Opt) *Plot {
	p := &Plot{series: map[string]*labeledSeries{}}
	for _, opt := range opts {
		opt(p)
	}

	if p.label == nil {
		p.label = ErrorLabeler
	}

	return p
}

// Add adds the given Result to the Plot time series.
func (p *Plot) Add(r *vegeta.Result) error {
	s, ok := p.series[r.Attack]
	if !ok {
		s = newLabeledSeries(p.label)
		p.series[r.Attack] = s
	}
	return s.add(r)
}

// Close closes the HTML plot for writing.
func (p *Plot) Close() {
	for _, as := range p.series {
		for _, ts := range as.series {
			ts.data.Finish()
		}
	}
}

// WriteTo writes the HTML plot to the give io.Writer.
func (p *Plot) WriteTo(w io.Writer) (n int64, err error) {
	type dygraphsOpts struct {
		Title       string   `json:"title"`
		Labels      []string `json:"labels,omitempty"`
		YLabel      string   `json:"ylabel"`
		XLabel      string   `json:"xlabel"`
		Colors      []string `json:"colors,omitempty"`
		Legend      string   `json:"legend"`
		ShowRoller  bool     `json:"showRoller"`
		LogScale    bool     `json:"logScale"`
		StrokeWidth float64  `json:"strokeWidth"`
	}

	type plotData struct {
		Title         string
		DygraphsCSS   template.CSS
		HTML2CanvasJS template.JS
		DygraphsJS    template.JS
		Data          template.JS
		Opts          template.JS
	}

	dp, labels, err := p.data()
	if err != nil {
		return 0, err
	}

	var sz int
	if len(dp) > 0 {
		sz = len(dp) * len(dp[0]) * 12 // heuristic
	}

	data := dp.Append(make([]byte, 0, sz))

	opts := dygraphsOpts{
		Title:       p.title,
		Labels:      labels,
		YLabel:      "Latency (ms)",
		XLabel:      "Seconds elapsed",
		Legend:      "always",
		ShowRoller:  true,
		LogScale:    true,
		StrokeWidth: 1.3,
		Colors:      labelColors(labels[1:]),
	}

	optsJSON, err := json.MarshalIndent(&opts, "    ", " ")
	if err != nil {
		return 0, err
	}

	assets := map[string][]byte{}
	for _, path := range []string{"dygraph.min.js", "dygraph.css", "html2canvas.min.js"} {
		bs, err := asset(path)
		if err != nil {
			return 0, err
		}
		assets[path] = bs
	}

	cw := countingWriter{w: w}
	err = plotTemplate.Execute(&cw, &plotData{
		Title:         p.title,
		DygraphsCSS:   template.CSS(assets["dygraph.css"]),
		HTML2CanvasJS: template.JS(assets["html2canvas.min.js"]),
		DygraphsJS:    template.JS(assets["dygraph.min.js"]),
		Data:          template.JS(data),
		Opts:          template.JS(optsJSON),
	})

	return cw.n, err
}

var (
	failures = []string{
		"#EE7860",
		"#DD624E",
		"#CA4E3E",
		"#B63A30",
		"#9F2823",
		"#881618",
		"#6F050E",
	}
	successes = []string{
		"#E9D758",
		"#297373",
		"#39393A",
		"#A1CDF4",
		"#593C8F",
		"#171738",
		"#A1674A",
	}
)

func labelColors(labels []string) []string {
	colors := make([]string, 0, len(labels))

	var failure, success int
	for _, label := range labels {
		var color string
		if strings.Contains(label, "ERROR") {
			color = failures[failure%len(failures)]
			failure++
		} else {
			color = successes[success%len(successes)]
			success++
		}
		colors = append(colors, color)
	}

	return colors
}

// See http://dygraphs.com/data.html
func (p *Plot) data() (dataPoints, []string, error) {
	var (
		series []*timeSeries
		count  int
	)

	for _, as := range p.series {
		for _, s := range as.series {
			if s != nil {
				series = append(series, s)
				count += s.len
			}
		}
	}

	var (
		size   = 1 + len(series)
		nan    = math.NaN()
		labels = make([]string, size)
		data   = make(dataPoints, 0, count)
	)

	labels[0] = "Seconds"

	sort.Slice(series, func(i, j int) bool {
		return series[i].attack+series[i].label <
			series[j].attack+series[j].label
	})

	for i, s := range series {
		points, err := lttb.Downsample(s.len, p.threshold, s.iter())
		if err != nil {
			return nil, nil, err
		}

		for _, p := range points {
			pt := make([]float64, size)
			for j := range pt {
				pt[j] = nan
			}
			pt[0], pt[i+1] = p.X, p.Y
			data = append(data, pt)
		}

		labels[i+1] = s.attack + ": " + s.label
	}

	sort.Sort(data)

	return data, labels, nil
}

func asset(path string) ([]byte, error) {
	file, err := Assets.Open(path)
	if err != nil {
		return nil, err
	}
	return io.ReadAll(file)
}

type countingWriter struct {
	n int64
	w io.Writer
}

func (cw *countingWriter) Write(p []byte) (int, error) {
	n, err := cw.w.Write(p)
	cw.n += int64(n)
	return n, err
}

type dataPoints [][]float64

func (ps dataPoints) Len() int { return len(ps) }

func (ps dataPoints) Less(i, j int) bool {
	// Sort by X axis (seconds elapsed)
	return ps[i][0] < ps[j][0]
}

func (ps dataPoints) Swap(i, j int) {
	ps[i], ps[j] = ps[j], ps[i]
}

func (ps dataPoints) Append(buf []byte) []byte {
	buf = append(buf, "[\n  "...)

	for i, p := range ps {
		buf = append(buf, "  ["...)

		for j, f := range p {
			if math.IsNaN(f) {
				buf = append(buf, "NaN"...)
			} else {
				buf = strconv.AppendFloat(buf, f, 'f', -1, 64)
			}

			if j < len(p)-1 {
				buf = append(buf, ',')
			}
		}

		if buf = append(buf, "]"...); i < len(ps)-1 {
			buf = append(buf, ",\n  "...)
		}
	}

	return append(buf, "  ]"...)
}

var plotTemplate = func() *template.Template {
	bs, err := asset("plot.html.tpl")
	if err != nil {
		panic(err)
	}
	return template.Must(template.New("plot").Parse(string(bs)))
}()

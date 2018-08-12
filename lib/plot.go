package vegeta

import (
	"encoding/json"
	"html/template"
	"io"
	"math"
	"strconv"
	"time"

	"github.com/tsenart/vegeta/lib/lttb"
)

// An HTMLPlot represents an interactive HTML time series
// plot of Result latencies over time.
type HTMLPlot struct {
	title     string
	threshold int
	series    map[string]*labeledSeries
	label     func(*Result) string
}

// labeledSeries groups timeSeries by a label function applied to
// each incoming result. It re-orders and buffers out-of-order results
// by their sequence number before adding them to the labeled timeSeries.
type labeledSeries struct {
	began  time.Time
	seq    uint64
	buf    map[uint64]point
	series map[string]*timeSeries
	label  func(*Result) string
}

// a point to be added to a timeSeries.
type point struct {
	ts  *timeSeries
	seq uint64
	t   time.Time
	v   float64
}

func newLabeledSeries(label func(*Result) string) *labeledSeries {
	return &labeledSeries{
		buf:    map[uint64]point{},
		series: map[string]*timeSeries{},
		label:  label,
	}
}

func (ls *labeledSeries) add(r *Result) {
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
		return // buffer
	} else if ls.seq == 0 {
		ls.began = r.Timestamp // first point in attack
	}

	// found successor
	for {
		p, ok := ls.buf[ls.seq]
		if !ok {
			return
		}

		delete(ls.buf, ls.seq)
		p.ts.add(p.seq, uint64(p.t.Sub(ls.began))/1e6, p.v) // timestamp in ms precision
		ls.seq++
	}
}

// NewHTMLPlot returns an HTMLPlot with the given title,
// downsampling threshold, and result labeling function.
func NewHTMLPlot(title string, threshold int, label func(*Result) string) *HTMLPlot {
	return &HTMLPlot{
		title:     title,
		threshold: threshold,
		series:    map[string]*labeledSeries{},
		label:     label,
	}
}

// Add adds the given Result to the HTMLPlot time series.
func (p *HTMLPlot) Add(r *Result) {
	s, ok := p.series[r.Attack]
	if !ok {
		s = newLabeledSeries(p.label)
		p.series[r.Attack] = s
	}
	s.add(r)
}

// Close closes the HTML plot for writing.
func (p *HTMLPlot) Close() {
	for _, as := range p.series {
		for _, ts := range as.series {
			if ts != nil {
				ts.data.Finish()
			}
		}
	}
}

// WriteTo writes the HTML plot to the give io.Writer.
func (p HTMLPlot) WriteTo(w io.Writer) (n int64, err error) {
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

	// TODO: Improve colors to be more intutive
	// Green pallette for OK series
	// Red pallette for Error series

	opts := dygraphsOpts{
		Title:       p.title,
		Labels:      labels,
		YLabel:      "Latency (ms)",
		XLabel:      "Seconds elapsed",
		Legend:      "always",
		ShowRoller:  true,
		LogScale:    true,
		StrokeWidth: 1.3,
	}

	optsJSON, err := json.MarshalIndent(&opts, "    ", " ")
	if err != nil {
		return 0, err
	}

	cw := countingWriter{w: w}
	err = plotTemplate.Execute(&cw, &plotData{
		Title:         p.title,
		HTML2CanvasJS: template.JS(asset(html2canvas)),
		DygraphsJS:    template.JS(asset(dygraphs)),
		Data:          template.JS(data),
		Opts:          template.JS(optsJSON),
	})

	return cw.n, err
}

// See http://dygraphs.com/data.html
func (p *HTMLPlot) data() (dataPoints, []string, error) {
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

	return data, labels, nil
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

var plotTemplate = template.Must(template.New("plot").Parse(`
<!doctype html>
<html>
<head>
  <title>{{.Title}}</title>
  <meta charset="utf-8">
</head>
<body>
  <div id="latencies" style="font-family: Courier; width: 100%%; height: 600px"></div>
  <button id="download">Download as PNG</button>
	<script>{{.HTML2CanvasJS}}</script>
	<script>{{.DygraphsJS}}</script>
  <script>
  document.getElementById("download").addEventListener("click", function(e) {
    html2canvas(document.body, {background: "#fff"}).then(function(canvas) {
      var url = canvas.toDataURL('image/png').replace(/^data:image\/[^;]/, 'data:application/octet-stream');
      var a = document.createElement("a");
      a.setAttribute("download", "vegeta-plot.png");
      a.setAttribute("href", url);
      a.click();
    });
  });

  var container = document.getElementById("latencies");
  var opts = {{.Opts}};
  var data = {{.Data}};
  var plot = new Dygraph(container, data, opts);
  </script>
</body>
</html>`))

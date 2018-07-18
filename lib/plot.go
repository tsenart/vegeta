package vegeta

import (
	"encoding/json"
	"html/template"
	"io"

	tsz "github.com/dgryski/go-tsz"
)

// An HTMLPlot represents an interactive HTML time series
// plot of Result latencies over time.
type HTMLPlot struct {
	title     string
	threshold int
	series    map[string]map[string]*timeSeries
}

// NewHTMLPlot returns an HTMLPlot with the given title,
// downsampling threshold.
func NewHTMLPlot(title string, threshold int) *HTMLPlot {
	return &HTMLPlot{
		title:     title,
		threshold: threshold,
		series:    map[string]map[string]*timeSeries{},
	}
}

// Add adds the given Result to the HTMLPlot time series.
func (p *HTMLPlot) Add(r *Result) {
	attack, ok := p.series[r.Attack]
	if !ok {
		attack = make(map[string]*timeSeries, 2)
		p.series[r.Attack] = attack
	}

	var label string
	if r.Error == "" {
		label = "OK"
	} else {
		label = "Error"
	}

	s, ok := attack[label]
	if !ok {
		s = &timeSeries{
			attack: r.Attack,
			label:  label,
			began:  r.Timestamp,
			data:   tsz.New(0),
		}
		attack[label] = s
	}

	s.add(r)
}

func (p *HTMLPlot) Close() {
	for _, labels := range p.series {
		for _, s := range labels {
			s.data.Finish()
		}
	}
}

// WriteTo writes the HTML plot to the give io.Writer.
func (p HTMLPlot) WriteTo(w io.Writer) (n int64, err error) {
	type chart struct {
		Type     string `json:"type"`
		RenderTo string `json:"renderTo"`
	}

	type title struct {
		Text string `json:"text"`
	}

	type axis struct {
		Type  string `json:"type"`
		Title title  `json:"title"`
	}

	type data struct {
		Name string  `json:"name"`
		Data []point `json:"data"`
	}

	type highChartOpts struct {
		Chart  chart  `json:"chart"`
		Title  title  `json:"title"`
		XAxis  axis   `json:"xAxis"`
		YAxis  axis   `json:"yAxis"`
		Series []data `json:"series"`
	}

	type templateData struct {
		Title             string
		HTML2CanvasJS     string
		HighChartOptsJSON string
	}

	opts := highChartOpts{
		Chart: chart{Type: "line", RenderTo: "latencies"},
		Title: title{Text: p.title},
		XAxis: axis{Title: title{Text: "Time elapsed (s)"}},
		YAxis: axis{
			Title: title{Text: "Latency (ms)"},
			Type:  "logarithmic",
		},
	}

	for attack, labels := range p.series {
		for label, s := range labels {
			d := data{Name: attack + ": " + label}
			if d.Data, err = s.lttb(p.threshold); err != nil {
				return 0, err
			}
			opts.Series = append(opts.Series, d)
		}
	}

	bs, err := json.Marshal(&opts)
	if err != nil {
		return 0, err
	}

	cw := countingWriter{w: w}
	err = plotTemplate.Execute(&cw, &templateData{
		Title:             p.title,
		HTML2CanvasJS:     string(asset(html2canvas)),
		HighChartOptsJSON: string(bs),
	})

	return cw.n, err
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
  <script src="https://code.highcharts.com/highcharts.src.js"></script>
  <script>{{.HTML2CanvasJS}}</script>
  <script>
	Highcharts.chart(JSON.parse("{{.HighChartOptsJSON}}"));
  document.getElementById("download").addEventListener("click", function(e) {
    html2canvas(document.body, {background: "#fff"}).then(function(canvas) {
      var url = canvas.toDataURL('image/png').replace(/^data:image\/[^;]/, 'data:application/octet-stream');
      var a = document.createElement("a");
      a.setAttribute("download", "vegeta-plot.png");
      a.setAttribute("href", url);
      a.click();
    });
  });
  </script>
</body>
</html>`))

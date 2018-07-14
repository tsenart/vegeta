package vegeta

import (
	"fmt"
	"io"
	"strconv"
	"strings"
	"time"

	lttb "github.com/dgryski/go-lttb"
	colorful "github.com/lucasb-eyer/go-colorful"
)

// An HTMLPlot represents an interactive HTML time series
// plot of Result latencies over time.
type HTMLPlot struct {
	title     string
	threshold int
	series    map[string]*points
}

type points struct {
	attack string
	began  time.Time
	ok     []lttb.Point
	err    []lttb.Point
}

// NewHTMLPlot returns an HTMLPlot with the given title,
// downsampling threshold and latency data points based on the
// given Results.
func NewHTMLPlot(title string, threshold int, rs Results) *HTMLPlot {
	// group by Attack, each split in Error and OK series
	series := map[string]*points{}
	for _, r := range rs {
		s, ok := series[r.Attack]
		if !ok {
			s = &points{attack: r.Attack, began: r.Timestamp}
			series[r.Attack] = s
		}

		point := lttb.Point{
			X: r.Timestamp.Sub(s.began).Seconds(),
			Y: r.Latency.Seconds() * 1000,
		}

		if r.Error == "" {
			s.ok = append(s.ok, point)
		} else {
			s.err = append(s.err, point)
		}
	}

	return &HTMLPlot{
		title:     title,
		threshold: threshold,
		series:    series,
	}
}

// WriteTo writes the HTML plot to the give io.Writer.
func (p HTMLPlot) WriteTo(w io.Writer) (err error) {
	_, err = fmt.Fprintf(w, plotsTemplateHead, p.title, asset(dygraphs), asset(html2canvas))
	if err != nil {
		return err
	}

	const count = 2 // OK and Errors
	i, offsets := 0, make(map[string]int, len(p.series))
	for name := range p.series {
		offsets[name] = 1 + i*count
		i++
	}

	const nan = "NaN"

	data := make([]string, 1+len(p.series)*count)
	for attack, points := range p.series {
		for idx, ps := range [2][]lttb.Point{points.err, points.ok} {
			for i, p := range lttb.LTTB(ps, p.threshold) {
				for j := range data {
					data[j] = nan
				}

				offset := offsets[attack] + idx
				data[0] = strconv.FormatFloat(p.X, 'f', -1, 32)
				data[offset] = strconv.FormatFloat(p.Y, 'f', -1, 32)

				s := "[" + strings.Join(data, ",") + "]"

				if i < len(ps)-1 {
					s += ","
				}

				if _, err = io.WriteString(w, s); err != nil {
					return err
				}
			}
		}
	}

	labels := make([]string, len(data))
	labels[0] = strconv.Quote("Seconds")

	for attack, offset := range offsets {
		labels[offset] = strconv.Quote(attack + " - ERR")
		labels[offset+1] = strconv.Quote(attack + " - OK")
	}

	colors := make([]string, 0, len(labels)-1)
	palette, err := colorful.HappyPalette(cap(colors))
	if err != nil {
		return err
	}

	for _, color := range palette {
		colors = append(colors, strconv.Quote(color.Hex()))
	}

	_, err = fmt.Fprintf(w, plotsTemplateTail, p.title, strings.Join(labels, ","), strings.Join(colors, ","))
	return err
}

const (
	plotsTemplateHead = `<!doctype html>
<html>
<head>
  <title>%s</title>
  <meta charset="utf-8">
</head>
<body>
  <div id="latencies" style="font-family: Courier; width: 100%%; height: 600px"></div>
  <button id="download">Download as PNG</button>
  <script>%s</script>
  <script>%s</script>
  <script>
  new Dygraph(
    document.getElementById("latencies"),
    [`
	plotsTemplateTail = `],
    {
      title: '%s',
      labels: [%s],
      ylabel: 'Latency (ms)',
      xlabel: 'Seconds elapsed',
      colors: [%s],
      showRoller: true,
      legend: 'always',
      logscale: true,
      strokeWidth: 1.3
    }
  );
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
</html>`
)

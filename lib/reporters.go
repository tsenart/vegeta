package vegeta

import (
	"encoding/json"
	"fmt"
	"io"
	"strconv"
	"strings"
	"text/tabwriter"

	"github.com/lucasb-eyer/go-colorful"
)

// A Report represents the state a Reporter uses to write out its reports.
type Report interface {
	// Add adds a given *Result to a Report.
	Add(*Result)
}

// Closer wraps the optional Report Close method.
type Closer interface {
	// Close permantently closes a Report, running any necessary book keeping.
	Close()
}

// A Reporter function writes out reports to the given io.Writer or returns an
// error in case of failure.
type Reporter func(io.Writer) error

// Report is a convenience method wrapping the Reporter function type.
func (rep Reporter) Report(w io.Writer) error { return rep(w) }

// NewHistogramReporter returns a Reporter that writes out a Histogram as
// aligned, formatted text.
func NewHistogramReporter(h *Histogram) Reporter {
	return func(w io.Writer) (err error) {
		tw := tabwriter.NewWriter(w, 0, 8, 2, ' ', tabwriter.StripEscape)
		if _, err = fmt.Fprintf(tw, "Bucket\t\t#\t%%\tHistogram\n"); err != nil {
			return err
		}

		for i, count := range h.Counts {
			ratio := float64(count) / float64(h.Total)
			lo, hi := h.Buckets.Nth(i)
			pad := strings.Repeat("#", int(ratio*75))
			_, err = fmt.Fprintf(tw, "[%s,\t%s]\t%d\t%.2f%%\t%s\n", lo, hi, count, ratio*100, pad)
			if err != nil {
				return nil
			}
		}

		return tw.Flush()
	}
}

// NewTextReporter returns a Reporter that writes out Metrics as aligned,
// formatted text.
func NewTextReporter(m *Metrics) Reporter {
	const fmtstr = "Requests\t[total, rate]\t%d, %.2f\n" +
		"Duration\t[total, attack, wait]\t%s, %s, %s\n" +
		"Latencies\t[mean, 50, 95, 99, max]\t%s, %s, %s, %s, %s\n" +
		"Bytes In\t[total, mean]\t%d, %.2f\n" +
		"Bytes Out\t[total, mean]\t%d, %.2f\n" +
		"Success\t[ratio]\t%.2f%%\n" +
		"Status Codes\t[code:count]\t"

	return func(w io.Writer) (err error) {
		tw := tabwriter.NewWriter(w, 0, 8, 2, ' ', tabwriter.StripEscape)
		if _, err = fmt.Fprintf(tw, fmtstr,
			m.Requests, m.Rate,
			m.Duration+m.Wait, m.Duration, m.Wait,
			m.Latencies.Mean, m.Latencies.P50, m.Latencies.P95, m.Latencies.P99, m.Latencies.Max,
			m.BytesIn.Total, m.BytesIn.Mean,
			m.BytesOut.Total, m.BytesOut.Mean,
			m.Success*100,
		); err != nil {
			return err
		}

		for code, count := range m.StatusCodes {
			if _, err = fmt.Fprintf(tw, "%s:%d  ", code, count); err != nil {
				return err
			}
		}

		if _, err = fmt.Fprintln(tw, "\nError Set:"); err != nil {
			return err
		}

		for _, e := range m.Errors {
			if _, err = fmt.Fprintln(tw, e); err != nil {
				return err
			}
		}

		return tw.Flush()
	}
}

// NewJSONReporter returns a Reporter that writes out Metrics as JSON.
func NewJSONReporter(m *Metrics) Reporter {
	return func(w io.Writer) error {
		return json.NewEncoder(w).Encode(m)
	}
}

// NewPlotReporter returns a Reporter that writes a self-contained
// HTML page with an interactive plot of the latencies of Requests, built with
// http://dygraphs.com/
func NewPlotReporter(title string, rs *Results) Reporter {
	return func(w io.Writer) (err error) {
		_, err = fmt.Fprintf(w, plotsTemplateHead, title, asset(dygraphs), asset(html2canvas))
		if err != nil {
			return err
		}

		attacks := make(map[string]Results, len(*rs))
		for _, r := range *rs {
			attacks[r.Attack] = append(attacks[r.Attack], r)
		}

		const series = 2 // OK and Errors
		i, offsets := 0, make(map[string]int, len(attacks))
		for attack := range attacks {
			offsets[attack] = 1 + i*series
			i++
		}

		const nan = "NaN"

		data := make([]string, 1+len(attacks)*series)
		for attack, results := range attacks {
			for i, r := range results {
				for j := range data {
					data[j] = nan
				}

				offset := offsets[attack]
				if r.Error == "" {
					offset++
				}

				ts := r.Timestamp.Sub(results[0].Timestamp).Seconds()
				data[0] = strconv.FormatFloat(ts, 'f', -1, 32)

				latency := r.Latency.Seconds() * 1000
				data[offset] = strconv.FormatFloat(latency, 'f', -1, 32)

				s := "[" + strings.Join(data, ",") + "]"

				if i < len(*rs)-1 {
					s += ","
				}

				if _, err = io.WriteString(w, s); err != nil {
					return err
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

		_, err = fmt.Fprintf(w, plotsTemplateTail, title, strings.Join(labels, ","), strings.Join(colors, ","))
		return err
	}
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

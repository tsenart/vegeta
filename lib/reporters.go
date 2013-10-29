package vegeta

import (
	"bytes"
	"encoding/json"
	"fmt"
	"text/tabwriter"
)

// Reporter represents any function which takes a slice of Results and
// generates a report returned as a slice of bytes and an error in case
// of failure
type Reporter func([]Result) ([]byte, error)

// ReportText returns a computed Metrics struct as aligned, formatted text
func ReportText(results []Result) ([]byte, error) {
	m := NewMetrics(results)
	out := &bytes.Buffer{}

	w := tabwriter.NewWriter(out, 0, 8, 2, '\t', tabwriter.StripEscape)
	fmt.Fprintf(w, "Requests\t[total]\t%d\n", m.Requests)
	fmt.Fprintf(w, "Duration\t[total]\t%s\n", m.Duration)
	fmt.Fprintf(w, "Latencies\t[mean, 95, 99, max]\t%s, %s, %s, %s\n",
		m.Latencies.Mean, m.Latencies.P95, m.Latencies.P99, m.Latencies.Max)
	fmt.Fprintf(w, "Bytes In\t[total, mean]\t%d, %.2f\n", m.BytesIn.Total, m.BytesIn.Mean)
	fmt.Fprintf(w, "Bytes Out\t[total, mean]\t%d, %.2f\n", m.BytesOut.Total, m.BytesOut.Mean)
	fmt.Fprintf(w, "Success\t[ratio]\t%.2f%%\n", m.Success*100)
	fmt.Fprintf(w, "Status Codes\t[code:count]\t")
	for code, count := range m.StatusCodes {
		fmt.Fprintf(w, "%s:%d  ", code, count)
	}
	fmt.Fprintln(w, "\nError Set:")
	for _, err := range m.Errors {
		fmt.Fprintln(w, err)
	}

	if err := w.Flush(); err != nil {
		return []byte{}, err
	}
	return out.Bytes(), nil
}

// ReportJSON writes a computed Metrics struct to as JSON
func ReportJSON(results []Result) ([]byte, error) {
	return json.Marshal(NewMetrics(results))
}

// ReportPlot builds up a self contained HTML page with an interactive plot
// of the latencies of the requests. Built with http://dygraphs.com/
func ReportPlot(results []Result) ([]byte, error) {
	out := &bytes.Buffer{}
	for _, result := range results {
		fmt.Fprintf(out, "[%f,%f],",
			result.Timestamp.Sub(results[0].Timestamp).Seconds(),
			result.Latency.Seconds()*1000,
		)
	}
	out.Truncate(out.Len() - 1) // Remove trailing comma
	return []byte(fmt.Sprintf(plotsTemplate, dygraphJSLibSrc(), out)), nil
}

var plotsTemplate = `<!doctype>
<html>
<head>
  <title>Vegeta Plots</title>
</head>
<body>
  <div id="latencies" style="font-family: Courier; width: 100%%; height: 600px"></div>
  <script>
	%s
  </script>
  <script>
  new Dygraph(
    document.getElementById("latencies"),
    [%s],
    {
      title: 'Vegeta Plot',
      labels: ['Seconds', 'Latency (ms)'],
      ylabel: 'Latency (ms)',
      xlabel: 'Seconds elapsed',
      showRoller: true,
      colors: ['#8AE234'],
      fillGraph: true,
      legend: 'always',
      logscale: true
    }
  );
  </script>
</body>
</html>`

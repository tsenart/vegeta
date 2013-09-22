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
	fmt.Fprintf(w, "Time(avg)\tRequests\tSuccess\tBytes(rx/tx)\n")
	fmt.Fprintf(w, "%s\t%d\t%.2f%%\t%.2f/%.2f\n", m.MeanTiming, m.TotalRequests, m.MeanSuccess*100, m.MeanBytesIn, m.MeanBytesOut)

	fmt.Fprintf(w, "\nCount:\t")
	for _, count := range m.StatusCodes {
		fmt.Fprintf(w, "%d\t", count)
	}
	fmt.Fprintf(w, "\nStatus:\t")
	for code := range m.StatusCodes {
		fmt.Fprintf(w, "%s\t", code)
	}

	fmt.Fprintln(w, "\n\nError Set:")
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
			result.Timing.Seconds()*1000,
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

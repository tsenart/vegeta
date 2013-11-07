package vegeta

import (
	"bytes"
	"encoding/json"
	"fmt"
	"text/tabwriter"
	"encoding/csv"
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



type ResultGroup struct {
	from uint64
	to uint64
	rate uint64
}

func ReportCSV(results []Result) ([]byte, error) {
	out := &bytes.Buffer{}
	m := NewMetrics(results)
	// result := fnmt.Sprintf("%d req/s,%s,%s,%s,%s,%f,%f,%f",rate,
	//		  m.Latencies.Mean.CsvString(), m.Latencies.P95.CsvString(), m.Latencies.P99.CsvString(), m.Latencies.Max.CsvString(),
	//		  m.BytesIn.Mean, m.BytesOut.Mean, m.Success)
	header := []string{ "rate" , "mean" , "p95", "p99" , "max", "bytesIn", "bytesOut", "success"  }

	w := csv.NewWriter(out)
	w.Write(header)

	resultGroups := slicesPerAttackRate(results)

	for _,resultGroup := range resultGroups {
		m := NewMetrics(results[resultGroup.from:resultGroup.to])
		w.Write(m.Csv(resultGroup.rate))
	}

	w.Flush()

	return out.Bytes(), nil
}





func slicesPerAttackRate(results []Result) ([]ResultGroup) {
	
	resultGroups := []ResultGroup{}


    if len(results) > 0 { 

		resultGroup := new(ResultGroup)
		resultGroup.from = 0
		resultGroup.to = 0
		resultGroup.rate = results[0].rate


		for i, result := range results {
			if result.rate != resultGroup.rate {
				resultGroup.to = i 
				append(resultGroups, resultGroup)
				resultGroup = new(ResultGroup)
				resultGroup.from = i
				resultGroup.rate = result.rate

			}
		}
		resultGroup.to = len(results)
		append(resultGroups, resultGroup)

	}

	return resultGroups
}
package vegeta

import (
	"fmt"
	"io"
	"text/tabwriter"
	"time"
)

// TextReporter prints the test results as text
// Metrics incude avg time per request, success ratio,
// total number of request, avg bytes in and avg bytes out
type TextReporter struct {
	responses []*Result
}

// NewTextReporter initializes a TextReporter with n responses
func NewTextReporter() *TextReporter {
	return &TextReporter{responses: make([]*Result, 0)}
}

// Report computes and writes the report to out.
// It returns an error in case of failure.
func (r *TextReporter) Report(out io.Writer) error {
	totalRequests := len(r.responses)
	totalTime := time.Duration(0)
	totalBytesOut := uint64(0)
	totalBytesIn := uint64(0)
	totalSuccess := uint64(0)
	histogram := map[uint64]uint64{}
	errors := map[string]struct{}{}

	for _, res := range r.responses {
		histogram[res.code]++
		totalTime += res.Timing
		totalBytesOut += res.bytesOut
		totalBytesIn += res.bytesIn
		if res.code >= 200 && res.code < 300 {
			totalSuccess++
		}
		if res.err != nil {
			errors[res.err.Error()] = struct{}{}
		}
	}

	avgTime := time.Duration(float64(totalTime) / float64(totalRequests))
	avgBytesOut := float64(totalBytesOut) / float64(totalRequests)
	avgBytesIn := float64(totalBytesIn) / float64(totalRequests)
	avgSuccess := float64(totalSuccess) / float64(totalRequests)

	w := tabwriter.NewWriter(out, 0, 8, 2, '\t', tabwriter.StripEscape)
	fmt.Fprintf(w, "Time(avg)\tRequests\tSuccess\tBytes(rx/tx)\n")
	fmt.Fprintf(w, "%s\t%d\t%.2f%%\t%.2f/%.2f\n", avgTime, totalRequests, avgSuccess*100, avgBytesOut, avgBytesIn)

	fmt.Fprintf(w, "\nCount:\t")
	for _, count := range histogram {
		fmt.Fprintf(w, "%d\t", count)
	}
	fmt.Fprintf(w, "\nStatus:\t")
	for code, _ := range histogram {
		fmt.Fprintf(w, "%d\t", code)
	}

	fmt.Fprintln(w, "\n\nError Set:")
	for err, _ := range errors {
		fmt.Fprintln(w, err)
	}

	return w.Flush()
}

// add adds a response to be used in the report
// Order of arrival is not relevant for this reporter
func (r *TextReporter) add(res *Result) {
	r.responses = append(r.responses, res)
}

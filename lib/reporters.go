package vegeta

import (
	"encoding/json"
	"fmt"
	"io"
	"sort"
	"strings"
	"text/tabwriter"
	"time"
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
	const fmtstr = "Requests\t[total, rate, throughput]\t%d, %.2f, %.2f\n" +
		"Duration\t[total, attack, wait]\t%s, %s, %s\n" +
		"Latencies\t[mean, 50, 95, 99, max]\t%s, %s, %s, %s, %s\n" +
		"Bytes In\t[total, mean]\t%d, %.2f\n" +
		"Bytes Out\t[total, mean]\t%d, %.2f\n" +
		"Success\t[ratio]\t%.2f%%\n" +
		"Status Codes\t[code:count]\t"

	return func(w io.Writer) (err error) {
		tw := tabwriter.NewWriter(w, 0, 8, 2, ' ', tabwriter.StripEscape)
		if _, err = fmt.Fprintf(tw, fmtstr,
			m.Requests, m.Rate, m.Throughput,
			m.Duration+m.Wait, m.Duration, m.Wait,
			m.Latencies.Mean, m.Latencies.P50, m.Latencies.P95, m.Latencies.P99, m.Latencies.Max,
			m.BytesIn.Total, m.BytesIn.Mean,
			m.BytesOut.Total, m.BytesOut.Mean,
			m.Success*100,
		); err != nil {
			return err
		}

		codes := make([]string, 0, len(m.StatusCodes))
		for code := range m.StatusCodes {
			codes = append(codes, code)
		}

		sort.Strings(codes)

		for _, code := range codes {
			count := m.StatusCodes[code]
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

var logarithmic = []float64{
	0.00,
	0.100,
	0.200,
	0.300,
	0.400,
	0.500,
	0.550,
	0.600,
	0.650,
	0.700,
	0.750,
	0.775,
	0.800,
	0.825,
	0.850,
	0.875,
	0.8875,
	0.900,
	0.9125,
	0.925,
	0.9375,
	0.94375,
	0.950,
	0.95625,
	0.9625,
	0.96875,
	0.971875,
	0.975,
	0.978125,
	0.98125,
	0.984375,
	0.985938,
	0.9875,
	0.989062,
	0.990625,
	0.992188,
	0.992969,
	0.99375,
	0.994531,
	0.995313,
	0.996094,
	0.996484,
	0.996875,
	0.997266,
	0.997656,
	0.998047,
	0.998242,
	0.998437,
	0.998633,
	0.998828,
	0.999023,
	0.999121,
	0.999219,
	0.999316,
	0.999414,
	0.999512,
	0.999561,
	0.999609,
	0.999658,
	0.999707,
	0.999756,
	0.99978,
	0.999805,
	0.999829,
	0.999854,
	0.999878,
	0.99989,
	0.999902,
	0.999915,
	0.999927,
	0.999939,
	0.999945,
	0.999951,
	0.999957,
	0.999963,
	0.999969,
	0.999973,
	0.999976,
	0.999979,
	0.999982,
	0.999985,
	0.999986,
	0.999988,
	0.999989,
	0.999991,
	0.999992,
	0.999993,
	0.999994,
	0.999995,
	0.999996,
	0.999997,
	0.999998,
	0.999999,
	1.0,
}

// NewHDRHistogramPlotReporter returns a Reporter that writes out latency metrics
// in a format plottable by http://hdrhistogram.github.io/HdrHistogram/plotFiles.html.
func NewHDRHistogramPlotReporter(m *Metrics) Reporter {
	return func(w io.Writer) error {
		tw := tabwriter.NewWriter(w, 0, 8, 2, ' ', tabwriter.StripEscape)
		_, err := fmt.Fprintf(tw, "Value(ms)\tPercentile\tTotalCount\t1/(1-Percentile)\n")
		if err != nil {
			return err
		}

		total := float64(m.Requests)
		for _, q := range logarithmic {
			value := milliseconds(m.Latencies.Quantile(q))
			oneBy := oneByQuantile(q)
			count := int64((q * total) + 0.5) // Count at quantile
			_, err = fmt.Fprintf(tw, "%f\t%f\t%d\t%f\n", value, q, count, oneBy)
			if err != nil {
				return err
			}
		}

		return tw.Flush()
	}
}

// milliseconds converts the given duration to a number of
// fractional milliseconds. Splitting the integer and fraction
// ourselves guarantees that converting the returned float64 to an
// integer rounds the same way that a pure integer conversion would have,
// even in cases where, say, float64(d.Nanoseconds())/1e9 would have rounded
// differently.
func milliseconds(d time.Duration) float64 {
	msec, nsec := d/time.Millisecond, d%time.Millisecond
	return float64(msec) + float64(nsec)/1e6
}

func oneByQuantile(q float64) float64 {
	if q < 1.0 {
		return 1 / (1 - q)
	}
	return float64(10000000)
}

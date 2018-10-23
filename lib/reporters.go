package vegeta

import (
	"encoding/json"
	"fmt"
	"io"
	"sort"
	"strings"
	"text/tabwriter"
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

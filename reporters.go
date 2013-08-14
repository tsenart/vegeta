package main

import (
	"fmt"
	"io"
	"time"
)

// Reporter represents any reporter of the results of the test
type Reporter interface {
	Add(res *Response)
	Report(io.Writer) error
}

type TextReporter struct {
	responses []*Response
}

// NewTextReporter initializes a TextReporter with n responses
func NewTextReporter() *TextReporter {
	return &TextReporter{responses: make([]*Response, 0)}
}

// Add adds a response to be used in the report
// Order of arrival is not relevant for this reporter
func (r *TextReporter) Add(res *Response) {
	r.responses = append(r.responses, res)
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
		totalTime += res.timing
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

	buf := ""
	buf += fmt.Sprintln("Results: ")
	buf += fmt.Sprintf("Time      (avg): %s\n", avgTime)
	buf += fmt.Sprintf("Bytes out (avg): %f\n", avgBytesOut)
	buf += fmt.Sprintf("Bytes in  (avg): %f\n", avgBytesIn)
	buf += fmt.Sprintf("Success ratio:   %f\n", avgSuccess)
	buf += fmt.Sprintf("Requests:        %d\n", totalRequests)
	buf += fmt.Sprintln("\nStatus codes histogram:")
	for code, count := range histogram {
		buf += fmt.Sprintf("%3d\t%d\n", code, count)
	}
	buf += fmt.Sprintln("\nError set:")
	for err, _ := range errors {
		buf += fmt.Sprintln(err)
	}
	_, err := out.Write([]byte(buf))
	return err
}

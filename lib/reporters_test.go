package vegeta

import (
	"testing"
	"time"
)

func BenchmarkReportPlot(b *testing.B) {
	b.StopTimer()
	// Build result set
	results := make([]Result, 50000)
	for began, i := time.Now(), 0; i < len(results); i++ {
		results[i].Code = uint16(i % 600)
		results[i].Latency = 50 * time.Millisecond
		results[i].Timestamp = began.Add(time.Duration(i) * 50 * time.Millisecond)
		if i%5 == 0 {
			results[i].Error = "Error"
		}
	}
	// Start benchmark
	b.StartTimer()
	for i := 0; i < b.N; i++ {
		ReportPlot(results)
	}
}

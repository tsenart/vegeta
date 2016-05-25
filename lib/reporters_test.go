package vegeta

import (
	"io/ioutil"
	"testing"
	"time"
)

func BenchmarkPlotReporter(b *testing.B) {
	b.StopTimer()
	// Build result set
	rs := make(Results, 50000)
	for began, i := time.Now(), 0; i < 50000; i++ {
		rs[i] = Result{
			Code:      uint16(i % 600),
			Latency:   50 * time.Millisecond,
			Timestamp: began.Add(time.Duration(i) * 50 * time.Millisecond),
		}
		if i%5 == 0 {
			rs[i].Error = "Error"
		}
	}
	rep := NewPlotReporter("Vegeta Plot", &rs)
	// Start benchmark
	b.ReportAllocs()
	b.StartTimer()
	for i := 0; i < b.N; i++ {
		rep.Report(ioutil.Discard)
	}
}

package vegeta

import (
	"io/ioutil"
	"testing"
	"time"
)

func BenchmarkHTMLPlot(b *testing.B) {
	b.StopTimer()
	// Build result set
	rs := make(Results, 50000000)
	for began, i := time.Now(), 0; i < cap(rs); i++ {
		rs[i] = Result{
			Attack:    "foo",
			Code:      uint16(i % 600),
			Latency:   50 * time.Millisecond,
			Timestamp: began.Add(time.Duration(i) * 50 * time.Millisecond),
		}
		if i%5 == 0 {
			rs[i].Error = "Error"
		}
	}

	plot := NewHTMLPlot("Vegeta Plot",
		Downsample(5000),
		Labeler(func(r *Result) string {
			if r.Code >= 200 && r.Code < 300 {
				return "OK"
			}
			return "Error"
		}),
	)

	b.Run("Add", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			plot.Add(&rs[i%len(rs)])
		}
	})

	b.Run("WriteTo", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_, _ = plot.WriteTo(ioutil.Discard)
		}
	})
}

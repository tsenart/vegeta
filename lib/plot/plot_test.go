package plot

import (
	"io/ioutil"
	"testing"
	"time"

	vegeta "github.com/tsenart/vegeta/lib"
)

func BenchmarkPlot(b *testing.B) {
	b.StopTimer()
	// Build result set
	rs := make(vegeta.Results, 50000000)
	for began, i := time.Now(), 0; i < cap(rs); i++ {
		rs[i] = vegeta.Result{
			Attack:    "foo",
			Code:      uint16(i % 600),
			Latency:   50 * time.Millisecond,
			Timestamp: began.Add(time.Duration(i) * 50 * time.Millisecond),
		}
		if i%5 == 0 {
			rs[i].Error = "Error"
		}
	}

	plot := New(
		Title("Vegeta Plot"),
		Downsample(5000),
		Label(ErrorLabeler),
	)

	b.Run("Add", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_ = plot.Add(&rs[i%len(rs)])
		}
	})

	b.Run("WriteTo", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			_, _ = plot.WriteTo(ioutil.Discard)
		}
	})
}

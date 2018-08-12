package plot

import (
	"io/ioutil"
	"math/rand"
	"testing"
	"time"

	vegeta "github.com/tsenart/vegeta/lib"
)

func TestLabeledSeries(t *testing.T) {
	s := newLabeledSeries(func(r *vegeta.Result) string {
		return r.Attack
	})

	count := int(1e5)
	attacks := []string{"foo", "bar", "baz"}

	// test out of order adds
	for i := count - 1; i >= 0; i-- {
		r := vegeta.Result{
			Attack:    attacks[i%len(attacks)],
			Seq:       uint64(i),
			Timestamp: time.Unix(int64(i), 0),
			Latency:   time.Duration(rand.Intn(1000)) * time.Millisecond,
		}

		if err := s.add(&r); err != nil {
			t.Fatal(err)
		}

		_, ok := s.series[r.Attack]
		if !ok {
			t.Fatalf("series %q not found after adding %v", r.Attack, r)
		}
	}

	total := 0
	for label, ts := range s.series {
		total += ts.len

		t.Logf("series %q has %d points", label, ts.len)

		ps, err := ts.iter()(ts.len)
		if err != nil {
			t.Errorf("series %q: %v", label, err)
		}

		if have, want := len(ps), ts.len; have != want {
			t.Errorf("missing points: have %d, want %d", have, want)
		}

		prev := 0.0
		for _, p := range ps {
			if p.X < prev {
				t.Fatalf("series %q: point %v not in order", label, p)
			}
			prev = p.X
		}
	}

	if have, want := total, count; have != want {
		t.Errorf("lost data points: have %d, want %d", have, want)
	}
}

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

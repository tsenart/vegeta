package plot

import (
	"bytes"
	"flag"
	"io/ioutil"
	"math/rand"
	"path/filepath"
	"sort"
	"testing"
	"time"

	"github.com/google/go-cmp/cmp"
	vegeta "github.com/tsenart/vegeta/v12/lib"
	"github.com/tsenart/vegeta/v12/lib/lttb"
)

var update = flag.Bool("update", false, "Update .golden files")

func TestPlot(t *testing.T) {
	p := New(Title("TestPlot"), Downsample(400))

	rng := rand.New(rand.NewSource(0))
	zf := rand.NewZipf(rng, 3, 2, 1000)
	attacks := []string{"500QPS", "1000QPS", "2000QPS"}
	began := time.Now()
	for i := 0; i < 1e5; i++ {
		for _, attack := range attacks {
			r := vegeta.Result{
				Attack:    attack,
				Seq:       uint64(i),
				Timestamp: began.Add(time.Duration(i) * time.Millisecond),
				Latency:   time.Duration(zf.Uint64()) * time.Millisecond,
			}

			if err := p.Add(&r); err != nil {
				t.Fatal(err)
			}
		}
	}

	p.Close()

	var b bytes.Buffer
	if _, err := p.WriteTo(&b); err != nil {
		t.Fatal(err)
	}

	gp := filepath.Join("testdata", filepath.FromSlash(t.Name())+".golden.html")
	if *update {
		t.Logf("updating %q", gp)
		if err := ioutil.WriteFile(gp, b.Bytes(), 0644); err != nil {
			t.Fatalf("failed to update %q: %s", gp, err)
		}
	}

	g, err := ioutil.ReadFile(gp)
	if err != nil {
		t.Fatalf("failed reading %q: %s", gp, err)
	}

	if !bytes.Equal(b.Bytes(), g) {
		t.Log(b.String())
		t.Errorf("bytes do not match %q", gp)
	}
}

func TestLabeledSeries(t *testing.T) {
	t.Parallel()

	s := newLabeledSeries(ErrorLabeler)
	count := 500000
	want := map[string][]lttb.Point{}

	// test out of order adds
	began := time.Unix(0, 0)
	for i := count - 1; i >= 0; i-- {
		r := vegeta.Result{
			Attack:    "attack",
			Seq:       uint64(i),
			Timestamp: began.Add(time.Duration(i) * time.Millisecond),
			Latency:   time.Duration(rand.Intn(1000)) * time.Millisecond,
		}

		if i%2 == 0 {
			r.Error = "Boom!"
		}

		label := ErrorLabeler(&r)
		point := lttb.Point{
			X: r.Timestamp.Sub(began).Seconds(),
			Y: r.Latency.Seconds() * 1000,
		}

		want[label] = append(want[label], point)

		if err := s.add(&r); err != nil {
			t.Fatal(err)
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

		if have, want := len(ps), count/2; have != want {
			t.Errorf("missing points: have %d, want %d", have, want)
		}

		sort.Slice(want[label], func(i, j int) bool {
			return want[label][i].X < want[label][j].X
		})

		if diff := cmp.Diff(ps, want[label]); diff != "" {
			t.Error(diff)
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

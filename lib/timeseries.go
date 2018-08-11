package vegeta

import (
	"time"

	tsz "github.com/dgryski/go-tsz"
	"github.com/tsenart/vegeta/lib/lttb"
)

type timeSeries struct {
	attack string
	label  string
	data   *tsz.Series
	len    int
}

func newTimeSeries(attack, label string) *timeSeries {
	return &timeSeries{
		attack: attack,
		label:  label,
		data:   tsz.New(0),
	}
}

func (ts *timeSeries) add(seq, t uint64, v float64) {
	ts.data.Push(t, v)
	ts.len++
}

func (ts *timeSeries) iter() lttb.Iter {
	it := ts.data.Iter()
	return func(count int) ([]lttb.Point, error) {
		ps := make([]lttb.Point, 0, count)
		for i := 0; i < count && it.Next(); i++ {
			t, v := it.Values()
			ps = append(ps, lttb.Point{
				X: time.Duration(t * 1e6).Seconds(),
				Y: v,
			})
		}
		return ps, it.Err()
	}
}

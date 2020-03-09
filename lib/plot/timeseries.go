package plot

import (
	"errors"
	"time"

	tsz "github.com/tsenart/go-tsz"
	"github.com/tsenart/vegeta/v12/lib/lttb"
)

// An in-memory timeSeries of points with high compression of
// both timestamps and values.  It's not safe for concurrent use.
type timeSeries struct {
	attack string
	label  string
	prev   uint64
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

var errMonotonicTimestamp = errors.New("timeseries: non monotonically increasing timestamp")

func (ts *timeSeries) add(t uint64, v float64) error {
	if ts.prev > t {
		return errMonotonicTimestamp
	}

	ts.data.Push(t, v)
	ts.prev = t
	ts.len++

	return nil
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

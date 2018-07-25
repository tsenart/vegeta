package vegeta

import (
	"time"

	tsz "github.com/dgryski/go-tsz"
)

type timeSeries struct {
	attack string
	label  string // OK or ERROR
	began  time.Time
	data   *tsz.Series
	len    int
}

func newTimeSeries(attack, label string, began time.Time) *timeSeries {
	return &timeSeries{
		attack: attack,
		label:  label,
		began:  began,
		data:   tsz.New(0),
	}
}

func (ts *timeSeries) add(t uint32, v float64) {
	ts.data.Push(t, v)
	ts.len++
}

func (ts *timeSeries) iter() func(int) ([]point, error) {
	it := ts.data.Iter()
	return func(count int) ([]point, error) {
		ps := make([]point, 0, count)
		for i := 0; i < count && it.Next(); i++ {
			x, y := it.Values()
			d := time.Duration(x) * 100 * time.Microsecond
			ps = append(ps, point{x: d.Seconds(), y: y})
		}
		return ps, it.Err()
	}
}

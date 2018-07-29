package vegeta

import (
	"errors"
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
			d := time.Duration(x)
			ps = append(ps, point{x: d.Seconds(), y: y})
		}
		return ps, it.Err()
	}
}

// a point in a line chart
type point struct{ x, y float64 }

// a bucket of points
type bucket []point

// LTTB down-samples the data to contain only threshold number of points that
// have the same visual shape as the original data. The algorithm is called
// Largest-Triangle-Three-Buckets and is described in:
// https://skemman.is/bitstream/1946/15343/3/SS_MSthesis.pdf
func lttb(count, threshold int, iter func(count int) ([]point, error)) ([]point, error) {
	if threshold >= count || threshold == 0 {
		points, err := iter(count)
		return points, err
	}

	if threshold < 3 {
		return nil, errors.New("lttb: min threshold is 3")
	}

	// Bucket size. Leave room for start and end data points
	size := float64(count-2) / float64(threshold-2)

	// Get the first point and the current bucket.
	points, err := iter(int(1 + size))
	if err != nil {
		return nil, err
	}

	samples := make([]point, 0, threshold)
	samples = append(samples, points[0]) // Always add the first point
	current := points[1:]

	for i := 0; i < threshold-2; i++ {
		// Calculate bucket boundaries (non inclusive hi)
		lo := int(float64(i+1)*size) + 1
		hi := int(float64(i+2)*size) + 1

		next, err := iter(hi - lo)
		if err != nil {
			return nil, err
		}

		samples = append(samples, lttbSample(samples[len(samples)-1], current, next))
		current = next
	}

	// Always add the last point unmodified
	if points, err = iter(count - len(samples)); err != nil {
		return nil, err
	} else if len(points) == 0 {
		points = current
	}

	if len(points) > 0 {
		samples = append(samples, points[len(points)-1])
	}

	return samples, nil
}

func lttbSample(a point, current, next bucket) (b point) {
	// Calculate point c as the average point of all points in the next bucket.
	var c point
	for i := range next {
		c.x, c.y = c.x+next[i].x, c.y+next[i].y
	}

	length := float64(len(next))
	c.x, c.y = c.x/length, c.y/length

	// Find index of point b that together with points a and c forms the largest triangle
	// amongst all points in the current bucket.
	var largest float64
	var index int
	for i, p := range current {
		// Calculate triangle area over three buckets
		area := (a.x-c.x)*(p.y-a.y) - (a.x-p.x)*(c.y-a.y)

		// We only care about the relative area here. Calling math.Abs() is slower than squaring.
		if area *= area; area > largest {
			largest, index = area, i
		}
	}

	return current[index]
}

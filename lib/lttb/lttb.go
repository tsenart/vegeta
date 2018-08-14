package lttb

import "errors"

// A Point in a line chart.
type Point struct{ X, Y float64 }

// An Iter is an iterator function that returns
// count number of Points or an error.
type Iter func(count int) ([]Point, error)

// Downsample `count` number of data points retrieved from the given iterator
// function to contain only `threshold` number of points while maintaining close
// visual similarity to the original data. The algorithm is called
// Largest-Triangle-Three-Buckets and is described in:
// https://skemman.is/bitstream/1946/15343/3/SS_MSthesis.pdf
//
// This implementation grew out of https://github.com/dgryski/go-lttb
// to limit memory usage by leveraging iterators.
func Downsample(count, threshold int, it Iter) ([]Point, error) {
	if threshold >= count || threshold == 0 {
		points, err := it(count)
		return points, err
	}

	if threshold < 3 {
		return nil, errors.New("lttb: min threshold is 3")
	}

	// Bucket size. Leave room for start and end data points
	size := float64(count-2) / float64(threshold-2)

	// Get the first point and the current bucket.
	points, err := it(int(1 + size))
	if err != nil {
		return nil, err
	}

	samples := make([]Point, 0, threshold)
	samples = append(samples, points[0]) // Always add the first point
	current := points[1:]

	for i := 0; i < threshold-2; i++ {
		// Calculate bucket boundaries (non inclusive hi)
		lo := int(float64(i+1)*size) + 1
		hi := int(float64(i+2)*size) + 1

		next, err := it(hi - lo)
		if err != nil {
			return nil, err
		}

		samples = append(samples, sample(samples[len(samples)-1], current, next))
		current = next
	}

	// Always add the last point unmodified
	if points, err = it(count - len(samples)); err != nil {
		return nil, err
	} else if len(points) == 0 {
		points = current
	}

	if len(points) > 0 {
		samples = append(samples, points[len(points)-1])
	}

	return samples, nil
}

func sample(a Point, current, next []Point) (b Point) {
	// Calculate point c as the average point of all points in the next bucket.
	var c Point
	for i := range next {
		c.X, c.Y = c.X+next[i].X, c.Y+next[i].Y
	}

	length := float64(len(next))
	c.X, c.Y = c.X/length, c.Y/length

	// Find index of point b that together with points a and c forms the largest triangle
	// amongst all points in the current bucket.
	var largest float64
	var index int
	for i, p := range current {
		// Calculate triangle area over three buckets
		area := (a.X-c.X)*(p.Y-a.Y) - (a.X-p.X)*(c.Y-a.Y)

		// We only care about the relative area here. Calling math.Abs() is slower than squaring.
		if area *= area; area > largest {
			largest, index = area, i
		}
	}

	return current[index]
}

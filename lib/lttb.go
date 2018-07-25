package vegeta

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
		return iter(count)
	}

	// Bucket size. Leave room for start and end data points
	var size int
	if threshold < 3 {
		size = count - 2
	} else {
		size = (count - 2) / (threshold - 2)
	}

	// Get the first point and the current bucket.
	points, err := iter(1 + size)
	if err != nil {
		return nil, err
	}

	samples := make([]point, 0, threshold)
	samples = append(samples, points[0]) // Always add the first point
	current := points[1:]

	for len(samples) < (threshold - 1) {
		next, err := iter(size)
		if err != nil {
			return nil, err
		}

		if len(next) == 0 {
			break
		}

		samples = append(samples, lttbSample(samples[len(samples)-1], current, next))
		current = next
	}

	// Always add the last point unmodified
	return append(samples, current[len(current)-1]), nil
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

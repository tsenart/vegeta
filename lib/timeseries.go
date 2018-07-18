package vegeta

import (
	"math"
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

type point [2]float64

func (ts timeSeries) add(r *Result) {
	ts.data.Push(
		uint32(r.Timestamp.Sub(ts.began).Seconds()),
		r.Latency.Seconds()*1000,
	)
	ts.len++

}

func (ts timeSeries) points(count int) ([]point, error) {
	it := ts.data.Iter()
	ps := make([]point, 0, count)
	for i := 0; i < ts.len && it.Next(); i++ {
		x, y := it.Values()
		ps = append(ps, point{float64(x), y})
	}
	return ps, it.Err()
}

// LTTB down-samples the data to contain only threshold number of points that
// have the same visual shape as the original data
func (ts timeSeries) lttb(threshold int) ([]point, error) {

	if threshold >= ts.len || threshold == 0 {
		return ts.points(ts.len)
	}

	sampled := make([]point, 0, threshold)

	// Bucket size. Leave room for start and end data points
	every := float64(ts.len-2) / float64(threshold-2)

	bucketStart := 0
	bucketCenter := int(math.Floor(every)) + 1
	windowSize := int(math.Floor(2*every)) + 1

	data, err := ts.points(windowSize)
	if err != nil {
		return sampled, err
	}

	sampled = append(sampled, data[0]) // Always add the first point

	var a int

	for i := 0; i < threshold-2; i++ {

		bucketEnd := int(math.Floor(float64(i+2)*every)) + 1

		// Calculate point average for next bucket (containing c)
		avgRangeStart := bucketCenter
		avgRangeEnd := bucketEnd

		if avgRangeEnd >= ts.len {
			avgRangeEnd = ts.len
		}

		avgRangeLength := float64(avgRangeEnd - avgRangeStart)

		var avgX, avgY float64
		for ; avgRangeStart < avgRangeEnd; avgRangeStart++ {
			avgX += data[avgRangeStart][0]
			avgY += data[avgRangeStart][1]
		}
		avgX /= avgRangeLength
		avgY /= avgRangeLength

		// Get the range for this bucket
		rangeOffs := bucketStart
		rangeTo := bucketCenter

		// Point a
		pointAX := data[a][0]
		pointAY := data[a][1]

		var maxArea float64

		var nextA int
		for ; rangeOffs < rangeTo; rangeOffs++ {
			// Calculate triangle area over three buckets
			area := (pointAX-avgX)*(data[rangeOffs][1]-pointAY) - (pointAX-data[rangeOffs][0])*(avgY-pointAY)
			// We only care about the relative area here.
			// Calling math.Abs() is slower than squaring
			area *= area
			if area > maxArea {
				maxArea = area
				nextA = rangeOffs // Next a is this b
			}
		}

		sampled = append(sampled, data[nextA]) // Pick this point from the bucket
		a = nextA                              // This a is the next a (chosen b)

		data, err = ts.points(windowSize)
		if err != nil {
			return sampled, err
		}
	}

	// sampled = append(sampled, data[len(data)-1]) // Always add last

	return sampled, nil
}

package vegeta

import "time"

// Histogram computes a histogram for the given Results with the defined
// buckets and returns it. The provided Results must be sorted.
func Histogram(buckets []time.Duration, r Results) []uint64 {
	var i int
	counts := make([]uint64, len(buckets))
	for _, res := range r {
		for i = 0; i < len(buckets)-1; i++ {
			if res.Latency >= buckets[i] && res.Latency < buckets[i+1] {
				break
			}
		}
		counts[i]++
	}
	return counts
}

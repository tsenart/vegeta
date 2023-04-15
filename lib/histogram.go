package vegeta

import (
	"bytes"
	"fmt"
	"math"
	"strconv"
	"strings"
	"time"
)

// Buckets represents an Histogram's latency buckets.
type Buckets []time.Duration

// Histogram is a bucketed latency Histogram.
type Histogram struct {
	Buckets Buckets
	Counts  []uint64
	Total   uint64
}

// Add implements the Add method of the Report interface by finding the right
// Bucket for the given Result latency and increasing its count by one as well
// as the total count.
func (h *Histogram) Add(r *Result) {
	if len(h.Counts) != len(h.Buckets) {
		h.Counts = make([]uint64, len(h.Buckets))
	}

	var i int
	for ; i < len(h.Buckets)-1; i++ {
		if r.Latency >= h.Buckets[i] && r.Latency < h.Buckets[i+1] {
			break
		}
	}

	h.Total++
	h.Counts[i]++
}

// MarshalJSON returns a JSON encoding of the buckets and their counts.
func (h *Histogram) MarshalJSON() ([]byte, error) {
	var buf bytes.Buffer

	// Custom marshalling to guarantee order.
	buf.WriteString("{")
	for i := range h.Buckets {
		if i > 0 {
			buf.WriteString(", ")
		}
		if _, err := fmt.Fprintf(&buf, "\"%d\": %d", h.Buckets[i], h.Counts[i]); err != nil {
			return nil, err
		}
	}
	buf.WriteString("}")

	return buf.Bytes(), nil
}

// Nth returns the nth bucket represented as a string.
func (bs Buckets) Nth(i int) (left, right string) {
	if i >= len(bs)-1 {
		return bs[i].String(), "+Inf"
	}
	return bs[i].String(), bs[i+1].String()
}

// UnmarshalText implements the encoding.TextUnmarshaler interface.
func (bs *Buckets) UnmarshalText(value []byte) error {
	if len(value) < 2 || value[0] != '[' || value[len(value)-1] != ']' {
		return fmt.Errorf("bad buckets: %s", value)
	}
	for i, v := range strings.Split(string(value[1:len(value)-1]), ",") {
		d, err := time.ParseDuration(strings.TrimSpace(v))
		if err != nil {
			return err
		}
		// add a default range of [0-Buckets[0]) if needed
		if i == 0 && d > 0 {
			*bs = append(*bs, 0)
		}
		*bs = append(*bs, d)
	}
	if len(*bs) == 0 {
		return fmt.Errorf("bad buckets: %s", value)
	}
	return nil
}

// UnmarshalExpoSeqText generate buckets in the way implementing exponential sequence
// , whose args would be [hi, bucketAmount], in which hi represents upper bound and bucketAmount represents required number of buckets
// Find n in the formula: A1+r^n= An, or n=e^(ln(hi)/bucketAmount), where variable n is the interval base in this case.
func (bs *Buckets) UnmarshalExpoSeqText(value []byte) error {
	if len(value) < 2 || value[0] != '[' || value[len(value)-1] != ']' {
		return fmt.Errorf("bad buckets: %s", value)
	}

	args := strings.Split(string(value[1:len(value)-1]), ",")
	if len(args) != 2 {
		return fmt.Errorf("bad buckets: %s", value)
	}

	hi, power, err := parseDuration(strings.TrimSpace(args[0]))
	if err != nil {
		return err
	}
	if hi == 0 {
		return fmt.Errorf("bad buckets, upper boundary should not be 0: %s", value)
	}

	bucketAmt, err := strconv.ParseFloat(strings.TrimSpace(args[1]), 64)
	if err != nil {
		return err
	}

	interval := math.Exp(math.Log(float64(hi)) / float64(bucketAmt))

	for i := float64(0); float64(i) < float64(hi); i *= interval {
		// add a default range of [0-Buckets[0]) if needed
		if i == 0 {
			*bs = append(*bs, 0)
			i += interval
		}
		*bs = append(*bs, time.Duration(i*math.Pow10(power)))
	}
	*bs = append(*bs, time.Duration(hi*math.Pow10(power)))

	return nil
}

func parseDuration(arg string) (float64, int, error) {
	floatArg, err := time.ParseDuration(strings.TrimSpace(arg))
	if err != nil {
		return 0, 0, err
	}

	c := float64(floatArg)
	power := 0
	for c > 1000 {
		c = c / 1000
		power += 3
	}
	return c, power, nil
}

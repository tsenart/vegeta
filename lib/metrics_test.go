package vegeta

import (
	"reflect"
	"testing"
	"time"
)

func TestMetrics_Add(t *testing.T) {
	t.Parallel()

	codes := []uint16{500, 200, 302}
	errors := []string{"Internal server error", ""}

	var got Metrics
	for i := 1; i <= 10000; i++ {
		got.Add(&Result{
			Code:      codes[i%len(codes)],
			Timestamp: time.Unix(int64(i-1), 0),
			Latency:   time.Duration(i) * time.Microsecond,
			BytesIn:   1024,
			BytesOut:  512,
			Error:     errors[i%len(errors)],
		})
	}
	got.Close()

	duration := func(s string) time.Duration {
		d, err := time.ParseDuration(s)
		if err != nil {
			panic(err)
		}
		return d
	}

	want := Metrics{
		Latencies: LatencyMetrics{
			Total: duration("50.005s"),
			Mean:  duration("5.0005ms"),
			P50:   duration("4.991ms"),
			P95:   duration("9.509ms"),
			P99:   duration("9.898ms"),
			Max:   duration("10ms"),
		},
		BytesIn:     ByteMetrics{Total: 10240000, Mean: 1024},
		BytesOut:    ByteMetrics{Total: 5120000, Mean: 512},
		Earliest:    time.Unix(0, 0),
		Latest:      time.Unix(9999, 0),
		End:         time.Unix(9999, 0).Add(10000 * time.Microsecond),
		Duration:    duration("2h46m39s"),
		Wait:        duration("10ms"),
		Requests:    10000,
		Rate:        1.000100010001,
		Success:     0.6667,
		StatusCodes: map[string]int{"500": 3333, "200": 3334, "302": 3333},
		Errors:      []string{"Internal server error"},

		errors:    got.errors,
		success:   got.success,
		latencies: got.latencies,
	}

	if !reflect.DeepEqual(got, want) {
		t.Errorf("\ngot:  %+v\nwant: %+v", got, want)
	}
}

// https://github.com/tsenart/vegeta/issues/208
func TestMetrics_NoInfiniteRate(t *testing.T) {
	t.Parallel()

	m := Metrics{Requests: 1, Duration: time.Microsecond}
	m.Close()

	if got, want := m.Rate, 1.0; got != want {
		t.Errorf("got rate %f, want %f", got, want)
	}
}

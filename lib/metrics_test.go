package vegeta

import (
	"io/ioutil"
	"math/rand"
	"reflect"
	"testing"
	"time"

	bmizerany "github.com/bmizerany/perks/quantile"
	gk "github.com/dgryski/go-gk"
	streadway "github.com/streadway/quantile"
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
			Total:     duration("50.005s"),
			Mean:      duration("5.0005ms"),
			P50:       duration("5.0005ms"),
			P90:       duration("9.0005ms"),
			P95:       duration("9.5005ms"),
			P99:       duration("9.9005ms"),
			Max:       duration("10ms"),
			Min:       duration("1us"),
			estimator: got.Latencies.estimator,
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
		Throughput:  0.6667660098349737,
		Success:     0.6667,
		StatusCodes: map[string]int{"500": 3333, "200": 3334, "302": 3333},
		Errors:      []string{"Internal server error"},

		errors:  got.errors,
		success: got.success,
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

// https://github.com/tsenart/vegeta/pull/277
func TestMetrics_NonNilErrorsOnClose(t *testing.T) {
	t.Parallel()

	m := Metrics{Errors: nil}
	m.Close()

	got, want := m.Errors, []string{}

	if !reflect.DeepEqual(got, want) {
		t.Errorf("\ngot:  %+v\nwant: %+v", got, want)
	}
}

// https://github.com/tsenart/vegeta/issues/461
func TestMetrics_EmptyMetricsCanBeReported(t *testing.T) {
	t.Parallel()

	var m Metrics
	m.Close()

	reporter := NewJSONReporter(&m)
	if err := reporter(ioutil.Discard); err != nil {
		t.Error(err)
	}
}
func BenchmarkMetrics(b *testing.B) {
	b.StopTimer()
	b.ResetTimer()

	rng := rand.New(rand.NewSource(time.Now().UnixNano()))

	latencies := make([]time.Duration, 1000000)
	for i := range latencies {
		latencies[i] = time.Duration(1e6 + rng.Int63n(1e10-1e6)) // 1ms to 10s
	}

	for _, tc := range []struct {
		name string
		estimator
	}{
		{"streadway/quantile", streadway.New(
			streadway.Known(0.50, 0.01),
			streadway.Known(0.90, 0.005),
			streadway.Known(0.95, 0.001),
			streadway.Known(0.99, 0.0005),
		)},
		{"bmizerany/perks/quantile", newBmizeranyEstimator(
			0.50,
			0.90,
			0.95,
			0.99,
		)},
		{"dgrisky/go-gk", newDgriskyEstimator(0.5)},
		{"influxdata/tdigest", newTdigestEstimator(100)},
	} {
		m := Metrics{Latencies: LatencyMetrics{estimator: tc.estimator}}
		b.Run("Add/"+tc.name, func(b *testing.B) {
			for i := 0; i <= b.N; i++ {
				m.Add(&Result{
					Code:      200,
					Timestamp: time.Unix(int64(i), 0),
					Latency:   latencies[i%len(latencies)],
					BytesIn:   1024,
					BytesOut:  512,
				})
			}

		})

		b.Run("Close/"+tc.name, func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				m.Close()
			}
		})
	}

}

type bmizeranyEstimator struct {
	*bmizerany.Stream
}

func newBmizeranyEstimator(qs ...float64) *bmizeranyEstimator {
	return &bmizeranyEstimator{Stream: bmizerany.NewTargeted(qs...)}
}

func (e *bmizeranyEstimator) Add(s float64) { e.Insert(s) }
func (e *bmizeranyEstimator) Get(q float64) float64 {
	return e.Query(q)
}

type dgryskiEstimator struct {
	*gk.Stream
}

func newDgriskyEstimator(epsilon float64) *dgryskiEstimator {
	return &dgryskiEstimator{Stream: gk.New(epsilon)}
}

func (e *dgryskiEstimator) Add(s float64) { e.Insert(s) }
func (e *dgryskiEstimator) Get(q float64) float64 {
	return e.Query(q)
}

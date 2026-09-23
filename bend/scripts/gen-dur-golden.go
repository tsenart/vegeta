//go:build ignore

// Writes bend/tests/golden/dur.txt (run from the repo root:
// go run ./bend/scripts/gen-dur-golden.go).
//
//	show n String round parse(String)    Duration.String, Vegeta's report
//	                                     rounding, ParseDuration of the text
//	parse [s] result                     ParseDuration(s), "None" on error
//
// Only inputs where Go and the port agree are listed: the port reads no
// negative duration but -0, and nothing from 281474 s up (LAWS dur_ok).
package main

import (
	"fmt"
	"os"
	"strings"
	"time"
)

var durations = [...]time.Duration{time.Hour, time.Minute, time.Second, time.Millisecond, time.Microsecond, time.Nanosecond}

// Vegeta's report rounding (lib/reporters.go)
func round(d time.Duration) time.Duration {
	for i, unit := range durations {
		if d >= unit && i < len(durations)-1 {
			return d.Round(durations[i+1])
		}
	}
	return d
}

func main() {
	var b strings.Builder
	for _, n := range []int64{0, 1, 999, 1000, 1001, 1500, 25833, 326000, 364103, 423778, 999999, 1000000, 1000500,
		1519000, 16501000, 999999999, 1000000000, 1000000001, 1500000000, 1999999999, 59999999999, 60000000000,
		61500000000, 3599999999999, 3600000000000, 3629999999999, 3630000000000, 3661500000000, 90061000000000,
		281473999999999} {
		d := time.Duration(n)
		p, err := time.ParseDuration(d.String())
		if err != nil {
			panic(err)
		}
		fmt.Fprintf(&b, "show %d %s %d %d\n", n, d, round(d), p)
	}
	for _, s := range []string{"0", "-0", "+0", "+5s", "1.5s", ".5s", "5.s", "1h30m", "1h30m45.5s", "", "1", "5x",
		"5sec", "1us", "1µs", "1μs", "1.5µs", "0.1ns", "1.0000000001s", "100ms", "2.5h", "0.333333333333333h",
		"1.123456789012345678901h", "-0s", "-0.000h", "+-5s", "-+5s", "1.s5m", "3m0.5s", "78h11m13.999999999s",
		"0.000000001h", "4.444444444444444444m", "1h1h", ".s", "1.2.3s", "s", "1m0", "00001s", "0.9999999999999999h",
		"281473.999999999s", "12345.6789ms", "7.77777us", "+0.5m"} {
		d, err := time.ParseDuration(s)
		r := fmt.Sprint(int64(d))
		if err != nil {
			r = "None"
		}
		fmt.Fprintf(&b, "parse [%s] %s\n", s, r)
	}
	if err := os.WriteFile("bend/tests/golden/dur.txt", []byte(b.String()), 0o644); err != nil {
		panic(err)
	}
}

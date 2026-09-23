//go:build ignore

// Writes bend/tests/golden/civil.txt (run from the repo root:
// go run ./bend/scripts/gen-civil-golden.go).
//
//	time sec nsec off rfc3339 unix_nanos   off is the zone offset + 86400; the
//	                                       text is MarshalJSON's, unquoted
//	parse [s] sec nsec off                 time.Parse(RFC3339, s), "None" on error
//	days y m d n                           days from 1970-01-01 to y-m-d
//	ymd n y m d                            the date n days after 1970-01-01
//
// Only inputs where Go and the port agree are listed: the port reads
// times from 1970 on (local and UTC).
package main

import (
	"fmt"
	"math/big"
	"os"
	"strings"
	"time"
)

func zone(off int) *time.Location {
	if off == 0 {
		return time.UTC
	}
	return time.FixedZone("", off)
}

func main() {
	var b strings.Builder
	times := [][3]int64{{0, 0, 0}, {951868799, 500000000, 0}, {1790381387, 935870875, 7200},
		{4107542400, 0, 0}, {2147483648, 1, -25200}, {0, 0, 19800}, {43200, 0, -43200},
		{1735606799, 999999999, 50400}, {946686599, 100000000, -1800}, {1234567890, 123456789, 3600},
		{253402300799, 999999999, 0}, {5, 5, 0}, {1000000000, 10, 20700}}
	for _, t := range times {
		tm := time.Unix(t[0], t[1]).In(zone(int(t[2])))
		j, err := tm.MarshalJSON()
		if err != nil {
			panic(err)
		}
		// the nanosecond count, exactly (UnixNano overflows past 2262)
		ns := new(big.Int).Add(new(big.Int).Mul(big.NewInt(t[0]), big.NewInt(1e9)), big.NewInt(t[1]))
		fmt.Fprintf(&b, "time %d %d %d %s %s\n", t[0], t[1], t[2]+86400, strings.Trim(string(j), `"`), ns)
	}
	for _, s := range []string{"2026-09-23T02:09:47.500+02:00", "2026-09-23T02:09:47Z", "2026-09-23T02:09:47+00:00",
		"2026-09-23T02:09:47-00:00", "2026-02-30T00:00:00Z", "2024-02-29T12:00:00Z", "2023-02-29T12:00:00Z",
		"2026-09-23T24:00:00Z", "2026-09-23T23:60:00Z", "2026-09-23T23:59:60Z", "2026-09-23 02:09:47Z",
		"2026-09-23T02:09:47", "2026-09-23T02:09:47.Z", "2026-09-23T02:09:47+24:00", "2026-09-23T02:09:47+02:60",
		"2026-9-23T02:09:47Z", "2026-09-23T02:09:47.000000001+13:45", "1970-01-01T00:00:00Z",
		"1970-01-01T01:00:00+01:00", "2026-13-01T00:00:00Z", "2026-00-10T00:00:00Z", "2026-09-00T00:00:00Z",
		"2026-09-23T02:09:47z", "2026-09-23t02:09:47Z", "2026-09-23T02:09:47+0200", "", "garbage",
		"2026-09-23T02:09:47+25:00", "2026-09-23T02:09:47-24:00", "2026-09-23T02:09:47+23:99", "2026-09-23T02:09:47+24:01",
		"2026-09-23T02:09:47.1234567891Z", "2026-09-23T02:09:47,5Z", "2026-09-23T02:09:47.5+02:00x",
		"+2026-09-23T02:09:47Z", "20260-09-23T02:09:47Z", "2026-09-23T02:09:47.5-01:30"} {
		t, err := time.Parse(time.RFC3339, s)
		if err != nil {
			fmt.Fprintf(&b, "parse [%s] None\n", s)
			continue
		}
		_, off := t.Zone()
		fmt.Fprintf(&b, "parse [%s] %d %d %d\n", s, t.Unix(), t.Nanosecond(), off+86400)
	}
	for _, d := range [][3]int{{1970, 1, 1}, {1970, 12, 31}, {1972, 2, 29}, {2000, 2, 29}, {2000, 3, 1}, {2026, 9, 23},
		{2100, 2, 28}, {2100, 3, 1}, {2400, 12, 31}, {9999, 12, 31}} {
		n := time.Date(d[0], time.Month(d[1]), d[2], 0, 0, 0, 0, time.UTC).Unix() / 86400
		fmt.Fprintf(&b, "days %d %d %d %d\n", d[0], d[1], d[2], n)
	}
	for _, n := range []int64{0, 1, 58, 59, 365, 789, 10956, 11016, 11017, 20719, 47540, 47541, 2932896} {
		t := time.Unix(n*86400, 0).UTC()
		fmt.Fprintf(&b, "ymd %d %d %d %d\n", n, t.Year(), int(t.Month()), t.Day())
	}
	if err := os.WriteFile("bend/tests/golden/civil.txt", []byte(b.String()), 0o644); err != nil {
		panic(err)
	}
}

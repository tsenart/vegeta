//go:build ignore

// Writes bend/tests/golden/f64.txt (run from the repo root:
// go run ./bend/scripts/gen-f64-golden.go). Each number is written as a
// decimal integer and converted exactly, then rounded once to float64,
// as F64.of_big does.
//
//	div p q f0 f2 f6 json   x = float64(p) / float64(q)
//	add a b c d json        x = a/b + c/d (each rounded first)
//	mul a b c d json        x = (a/b) * (c/d)
//	ddv a b c d json        x = (a/b) / (c/d)
//	trunc p q t             int64(float64(p) / float64(q) * 1e9)
package main

import (
	"encoding/json"
	"fmt"
	"math/big"
	"os"
	"strconv"
	"strings"
)

func f(s string) float64 {
	n, ok := new(big.Int).SetString(s, 10)
	if !ok {
		panic(s)
	}
	x, _ := new(big.Float).SetInt(n).Float64()
	return x
}

func js(x float64) string {
	b, err := json.Marshal(x)
	if err != nil {
		panic(err)
	}
	return string(b)
}

func main() {
	e300 := "1" + strings.Repeat("0", 300)
	divs := [][2]string{{"0", "1"}, {"1", "3"}, {"2", "3"}, {"10", "4"}, {"1", "8"}, {"5", "1000"}, {"194329", "2"},
		{"3", "7"}, {"1000000", "3"}, {"1", "1000000000"}, {"123456789", "1000"}, {"7", "3"}, {"125", "1000"},
		{"135", "1000"}, {"4503599627370496", "3"}, {"999999999999", "1000000000"}, {"1", "7000000"},
		{"1000000000000000000000", "1"}, {"30000000000000000000000", "7"}, {"5", "2"}, {"7", "2"}, {"1", "2"},
		{"3", "8"}, {"1", "1000000"}, {"999999", "1000000000000"}, {"1", "10"}, {"123", "1"},
		{"999999999999999999999", "1"}, {"12345678901234567890123", "1"}, {"1", e300},
		{"9007199254740993", "1"}, {"25833", "1"}, {"364103", "1000"}, {"17", "1024"}}
	var b strings.Builder
	for _, p := range divs {
		x := f(p[0]) / f(p[1])
		fmt.Fprintf(&b, "div %s %s %s %s %s %s\n", p[0], p[1], strconv.FormatFloat(x, 'f', 0, 64),
			strconv.FormatFloat(x, 'f', 2, 64), strconv.FormatFloat(x, 'f', 6, 64), js(x))
	}
	quads := [][4]string{{"1", "10", "2", "10"}, {"1", "3", "2", "3"}, {"1", "1000000", "1", "10000000"},
		{"4503599627370496", "1", "1", "2"}, {"9007199254740992", "1", "1", "1"}, {"9007199254740992", "1", "3", "1"}}
	for _, q := range quads {
		fmt.Fprintf(&b, "add %s %s %s %s %s\n", q[0], q[1], q[2], q[3], js(f(q[0])/f(q[1])+f(q[2])/f(q[3])))
	}
	for _, q := range quads {
		fmt.Fprintf(&b, "mul %s %s %s %s %s\n", q[0], q[1], q[2], q[3], js((f(q[0])/f(q[1]))*(f(q[2])/f(q[3]))))
	}
	// quotients of quotients: into the subnormals
	dds := [][4]string{{"1", e300, "100000000000000000000000", "1"}, {"3", e300, "10000000000", "1"},
		{"1", e300, "1" + strings.Repeat("0", 24), "1"}, {"7", e300, "1" + strings.Repeat("0", 8), "3"}}
	for _, q := range dds {
		fmt.Fprintf(&b, "ddv %s %s %s %s %s\n", q[0], q[1], q[2], q[3], js((f(q[0])/f(q[1]))/(f(q[2])/f(q[3]))))
	}
	truncs := [][2]string{{"3", "2"}, {"1", "3"}, {"2", "3"}, {"7", "10"}, {"281473", "1"}, {"1", "1000000000"}}
	for _, p := range truncs {
		fmt.Fprintf(&b, "trunc %s %s %d\n", p[0], p[1], int64(f(p[0])/f(p[1])*1e9))
	}
	if err := os.WriteFile("bend/tests/golden/f64.txt", []byte(b.String()), 0o644); err != nil {
		panic(err)
	}
}

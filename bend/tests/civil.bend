# Civil against Go (golden/civil.txt, from scripts/gen-civil-golden.go),
# then round trips, the port's deviations (no time before 1970) and
# instant arithmetic.
import Base
import ../lib/civil.bend as Civil

def tstr(+t: Civil.Time) -> String:
  Civil.Time{s, ns, off} = t
  Nat.show(s) ++ " " ++ Nat.show(ns) ++ " " ++ Nat.show(off)

def m(+x: Maybe<&2, Civil.Time>) -> String:
  match x:
    case None{}:
      "None"
    case Some{t}:
      tstr(t)

def c(+x: Cmp) -> String:
  match x:
    case LT{}:
      "LT"
    case EQ{}:
      "EQ"
    case GT{}:
      "GT"

def tm(+t: Civil.Time) -> String:
  "time " ++ tstr(t) ++ " " ++ Civil.rfc3339(t) ++ " " ++ Civil.unix_nanos(t)

def parse(+s: String) -> String:
  "parse [" ++ s ++ "] " ++ m(Civil.parse_rfc3339(s))

def days(+y: Nat, +mo: Nat, +d: Nat) -> String:
  "days " ++ Nat.show(y) ++ " " ++ Nat.show(mo) ++ " " ++ Nat.show(d) ++ " " ++ Nat.show(Civil.ymd_to_days(y, mo, d))

def ymd_str(+t: Civil.Ymd) -> String:
  Civil.Ymd{y, mo, d} = t
  Nat.show(y) ++ " " ++ Nat.show(mo) ++ " " ++ Nat.show(d)

def ymd(+n: Nat) -> String:
  "ymd " ++ Nat.show(n) ++ " " ++ ymd_str(Civil.days_to_ymd(n))

def same(+a: Maybe<&2, Civil.Time>, +t: Civil.Time) -> String:
  match a:
    case None{}:
      "F"
    case Some{u}:
      Civil.pick(String, String.eq(tstr(u), tstr(t)), "T", "F")

def rt(+t: Civil.Time) -> String:
  "rt " ++ tstr(t) ++ " " ++ same(Civil.parse_rfc3339(Civil.rfc3339(t)), t)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(tm(Civil.Time{0n, 0n, 86400n}))
    IO.print(tm(Civil.Time{951868799n, 500000000n, 86400n}))
    IO.print(tm(Civil.Time{1790381387n, 935870875n, 93600n}))
    IO.print(tm(Civil.Time{4107542400n, 0n, 86400n}))
    IO.print(tm(Civil.Time{2147483648n, 1n, 61200n}))
    IO.print(tm(Civil.Time{0n, 0n, 106200n}))
    IO.print(tm(Civil.Time{43200n, 0n, 43200n}))
    IO.print(tm(Civil.Time{1735606799n, 999999999n, 136800n}))
    IO.print(tm(Civil.Time{946686599n, 100000000n, 84600n}))
    IO.print(tm(Civil.Time{1234567890n, 123456789n, 90000n}))
    IO.print(tm(Civil.Time{Nat.add(Nat.mul(253402n, 1000000n), 300799n), 999999999n, 86400n}))
    IO.print(tm(Civil.Time{5n, 5n, 86400n}))
    IO.print(tm(Civil.Time{1000000000n, 10n, 107100n}))
    IO.print(parse("2026-09-23T02:09:47.500+02:00"))
    IO.print(parse("2026-09-23T02:09:47Z"))
    IO.print(parse("2026-09-23T02:09:47+00:00"))
    IO.print(parse("2026-09-23T02:09:47-00:00"))
    IO.print(parse("2026-02-30T00:00:00Z"))
    IO.print(parse("2024-02-29T12:00:00Z"))
    IO.print(parse("2023-02-29T12:00:00Z"))
    IO.print(parse("2026-09-23T24:00:00Z"))
    IO.print(parse("2026-09-23T23:60:00Z"))
    IO.print(parse("2026-09-23T23:59:60Z"))
    IO.print(parse("2026-09-23 02:09:47Z"))
    IO.print(parse("2026-09-23T02:09:47"))
    IO.print(parse("2026-09-23T02:09:47.Z"))
    IO.print(parse("2026-09-23T02:09:47+24:00"))
    IO.print(parse("2026-09-23T02:09:47+02:60"))
    IO.print(parse("2026-9-23T02:09:47Z"))
    IO.print(parse("2026-09-23T02:09:47.000000001+13:45"))
    IO.print(parse("1970-01-01T00:00:00Z"))
    IO.print(parse("1970-01-01T01:00:00+01:00"))
    IO.print(parse("2026-13-01T00:00:00Z"))
    IO.print(parse("2026-00-10T00:00:00Z"))
    IO.print(parse("2026-09-00T00:00:00Z"))
    IO.print(parse("2026-09-23T02:09:47z"))
    IO.print(parse("2026-09-23t02:09:47Z"))
    IO.print(parse("2026-09-23T02:09:47+0200"))
    IO.print(parse(""))
    IO.print(parse("garbage"))
    IO.print(parse("2026-09-23T02:09:47+25:00"))
    IO.print(parse("2026-09-23T02:09:47-24:00"))
    IO.print(parse("2026-09-23T02:09:47+23:99"))
    IO.print(parse("2026-09-23T02:09:47+24:01"))
    IO.print(parse("2026-09-23T02:09:47.1234567891Z"))
    IO.print(parse("2026-09-23T02:09:47,5Z"))
    IO.print(parse("2026-09-23T02:09:47.5+02:00x"))
    IO.print(parse("+2026-09-23T02:09:47Z"))
    IO.print(parse("20260-09-23T02:09:47Z"))
    IO.print(parse("2026-09-23T02:09:47.5-01:30"))
    IO.print(days(1970n, 1n, 1n))
    IO.print(days(1970n, 12n, 31n))
    IO.print(days(1972n, 2n, 29n))
    IO.print(days(2000n, 2n, 29n))
    IO.print(days(2000n, 3n, 1n))
    IO.print(days(2026n, 9n, 23n))
    IO.print(days(2100n, 2n, 28n))
    IO.print(days(2100n, 3n, 1n))
    IO.print(days(2400n, 12n, 31n))
    IO.print(days(9999n, 12n, 31n))
    IO.print(ymd(0n))
    IO.print(ymd(1n))
    IO.print(ymd(58n))
    IO.print(ymd(59n))
    IO.print(ymd(365n))
    IO.print(ymd(789n))
    IO.print(ymd(10956n))
    IO.print(ymd(11016n))
    IO.print(ymd(11017n))
    IO.print(ymd(20719n))
    IO.print(ymd(47540n))
    IO.print(ymd(47541n))
    IO.print(ymd(2932896n))
    IO.print(rt(Civil.Time{0n, 0n, 86400n}))
    IO.print(rt(Civil.Time{951868799n, 500000000n, 86400n}))
    IO.print(rt(Civil.Time{1790381387n, 935870875n, 93600n}))
    IO.print(rt(Civil.Time{4107542400n, 0n, 86400n}))
    IO.print(rt(Civil.Time{2147483648n, 1n, 61200n}))
    IO.print(rt(Civil.Time{0n, 0n, 106200n}))
    IO.print(rt(Civil.Time{43200n, 0n, 43200n}))
    IO.print(rt(Civil.Time{1735606799n, 999999999n, 136800n}))
    IO.print(rt(Civil.Time{946686599n, 100000000n, 84600n}))
    IO.print(rt(Civil.Time{1234567890n, 123456789n, 90000n}))
    IO.print(rt(Civil.Time{Nat.add(Nat.mul(253402n, 1000000n), 300799n), 999999999n, 86400n}))
    IO.print(rt(Civil.Time{5n, 5n, 86400n}))
    IO.print(rt(Civil.Time{1000000000n, 10n, 107100n}))
    IO.print(parse("1969-12-31T23:59:59Z"))
    IO.print(parse("1970-01-01T00:00:00+01:00"))
    IO.print(parse("1970-01-01T00:59:59.999+01:00"))
    IO.print(parse("1970-01-01T01:00:00.5+01:00"))
    IO.print(c(Civil.cmp(Civil.Time{5n, 1500000000n, 0n}, Civil.Time{6n, 400000000n, 172800n})) ++ c(Civil.cmp(Civil.Time{6n, 400000000n, 1n}, Civil.Time{5n, 1400000000n, 2n})) ++ c(Civil.cmp(Civil.Time{1n, 2n, 3n}, Civil.Time{1n, 3n, 3n})) ++ c(Civil.cmp(Civil.Time{2n, 0n, 3n}, Civil.Time{1n, 999999999n, 3n})))
    IO.print(tstr(Civil.add_ns(Civil.Time{1n, 999999999n, 86400n}, 2n)) ++ " " ++ tstr(Civil.add_ns(Civil.Time{1n, 5n, 7n}, Nat.mul(3600n, 1000000000n))) ++ " " ++ tstr(Civil.add_ns(Civil.Time{0n, 1500000000n, 7n}, 0n)))
    IO.print(Nat.show(Civil.sub_ns(Civil.Time{10n, 0n, 1n}, Civil.Time{9n, 999999999n, 2n})) ++ " " ++ Nat.show(Civil.sub_ns(Civil.Time{9n, 0n, 1n}, Civil.Time{10n, 0n, 1n})) ++ " " ++ Nat.show(Civil.sub_ns(Civil.Time{9n, 2000000000n, 1n}, Civil.Time{10n, 0n, 1n})) ++ " " ++ Nat.show(Civil.sub_ns(Civil.Time{1790129387n, 5n, 1n}, Civil.Time{1790129386n, 7n, 1n})))
    IO.print(Civil.unix_nanos(Civil.Time{0n, 1500000000n, 0n}) ++ " " ++ Civil.unix_nanos(Civil.Time{0n, 0n, 0n}) ++ " " ++ Civil.unix_nanos(Civil.Time{1n, 7n, 0n}))

#|time 0 0 86400 1970-01-01T00:00:00Z 0
#|time 951868799 500000000 86400 2000-02-29T23:59:59.5Z 951868799500000000
#|time 1790381387 935870875 93600 2026-09-26T02:09:47.935870875+02:00 1790381387935870875
#|time 4107542400 0 86400 2100-03-01T00:00:00Z 4107542400000000000
#|time 2147483648 1 61200 2038-01-18T20:14:08.000000001-07:00 2147483648000000001
#|time 0 0 106200 1970-01-01T05:30:00+05:30 0
#|time 43200 0 43200 1970-01-01T00:00:00-12:00 43200000000000
#|time 1735606799 999999999 136800 2024-12-31T14:59:59.999999999+14:00 1735606799999999999
#|time 946686599 100000000 84600 1999-12-31T23:59:59.1-00:30 946686599100000000
#|time 1234567890 123456789 90000 2009-02-14T00:31:30.123456789+01:00 1234567890123456789
#|time 253402300799 999999999 86400 9999-12-31T23:59:59.999999999Z 253402300799999999999
#|time 5 5 86400 1970-01-01T00:00:05.000000005Z 5000000005
#|time 1000000000 10 107100 2001-09-09T07:31:40.00000001+05:45 1000000000000000010
#|parse [2026-09-23T02:09:47.500+02:00] 1790122187 500000000 93600
#|parse [2026-09-23T02:09:47Z] 1790129387 0 86400
#|parse [2026-09-23T02:09:47+00:00] 1790129387 0 86400
#|parse [2026-09-23T02:09:47-00:00] 1790129387 0 86400
#|parse [2026-02-30T00:00:00Z] None
#|parse [2024-02-29T12:00:00Z] 1709208000 0 86400
#|parse [2023-02-29T12:00:00Z] None
#|parse [2026-09-23T24:00:00Z] None
#|parse [2026-09-23T23:60:00Z] None
#|parse [2026-09-23T23:59:60Z] None
#|parse [2026-09-23 02:09:47Z] None
#|parse [2026-09-23T02:09:47] None
#|parse [2026-09-23T02:09:47.Z] None
#|parse [2026-09-23T02:09:47+24:00] 1790042987 0 172800
#|parse [2026-09-23T02:09:47+02:60] 1790118587 0 97200
#|parse [2026-9-23T02:09:47Z] None
#|parse [2026-09-23T02:09:47.000000001+13:45] 1790079887 1 135900
#|parse [1970-01-01T00:00:00Z] 0 0 86400
#|parse [1970-01-01T01:00:00+01:00] 0 0 90000
#|parse [2026-13-01T00:00:00Z] None
#|parse [2026-00-10T00:00:00Z] None
#|parse [2026-09-00T00:00:00Z] None
#|parse [2026-09-23T02:09:47z] None
#|parse [2026-09-23t02:09:47Z] None
#|parse [2026-09-23T02:09:47+0200] None
#|parse [] None
#|parse [garbage] None
#|parse [2026-09-23T02:09:47+25:00] None
#|parse [2026-09-23T02:09:47-24:00] 1790215787 0 0
#|parse [2026-09-23T02:09:47+23:99] None
#|parse [2026-09-23T02:09:47+24:01] 1790042927 0 172860
#|parse [2026-09-23T02:09:47.1234567891Z] 1790129387 123456789 86400
#|parse [2026-09-23T02:09:47,5Z] 1790129387 500000000 86400
#|parse [2026-09-23T02:09:47.5+02:00x] None
#|parse [+2026-09-23T02:09:47Z] None
#|parse [20260-09-23T02:09:47Z] None
#|parse [2026-09-23T02:09:47.5-01:30] 1790134787 500000000 81000
#|days 1970 1 1 0
#|days 1970 12 31 364
#|days 1972 2 29 789
#|days 2000 2 29 11016
#|days 2000 3 1 11017
#|days 2026 9 23 20719
#|days 2100 2 28 47540
#|days 2100 3 1 47541
#|days 2400 12 31 157419
#|days 9999 12 31 2932896
#|ymd 0 1970 1 1
#|ymd 1 1970 1 2
#|ymd 58 1970 2 28
#|ymd 59 1970 3 1
#|ymd 365 1971 1 1
#|ymd 789 1972 2 29
#|ymd 10956 1999 12 31
#|ymd 11016 2000 2 29
#|ymd 11017 2000 3 1
#|ymd 20719 2026 9 23
#|ymd 47540 2100 2 28
#|ymd 47541 2100 3 1
#|ymd 2932896 9999 12 31
#|rt 0 0 86400 T
#|rt 951868799 500000000 86400 T
#|rt 1790381387 935870875 93600 T
#|rt 4107542400 0 86400 T
#|rt 2147483648 1 61200 T
#|rt 0 0 106200 T
#|rt 43200 0 43200 T
#|rt 1735606799 999999999 136800 T
#|rt 946686599 100000000 84600 T
#|rt 1234567890 123456789 90000 T
#|rt 253402300799 999999999 86400 T
#|rt 5 5 86400 T
#|rt 1000000000 10 107100 T
#|parse [1969-12-31T23:59:59Z] None
#|parse [1970-01-01T00:00:00+01:00] None
#|parse [1970-01-01T00:59:59.999+01:00] None
#|parse [1970-01-01T01:00:00.5+01:00] 0 500000000 90000
#|GTEQLTGT
#|2 1 86400 3601 5 7 1 500000000 7
#|1 0 1000000000 999999998
#|1500000000 0 1000000007

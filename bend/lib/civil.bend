# Wall-clock time: UTC seconds, nanoseconds, and the local offset in
# seconds plus 86400 (so it is never negative).
#
# Days are counted from 1970-01-01 with Howard Hinnant's algorithms
# (days_from_civil, civil_from_days), shifted so no Nat goes negative:
# years count from 0000-03-01, and 1970-01-01 is day 719468 of that count.
import Base
import ./dec.bend as Dec

type Time is Data:
  Time{sec: Nat, nsec: Nat, off: Nat}

type Ymd is Data:
  Ymd{y: Nat, m: Nat, d: Nat}

# c ? a : b
def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def sec() -> Nat:
  1000000000n

def time_sec(+t: Time) -> Nat:
  Time{s, ns, off} = t
  s

def time_nsec(+t: Time) -> Nat:
  Time{s, ns, off} = t
  ns

def time_off(+t: Time) -> Nat:
  Time{s, ns, off} = t
  off

def ymd_y(+t: Ymd) -> Nat:
  Ymd{y, m, d} = t
  y

def ymd_m(+t: Ymd) -> Nat:
  Ymd{y, m, d} = t
  m

def ymd_d(+t: Ymd) -> Nat:
  Ymd{y, m, d} = t
  d

# ---------------------------------------------------------------------
# Days: the calendar counted out, as LAWS' days_of states it (years from
# 1970 one by one: at most a few thousand steps, a few dozen in practice)
# ---------------------------------------------------------------------

def leap(+y: Nat) -> Bool:
  Bool.and(Nat.is_eq(Nat.mod(y, 4n), 0n), Bool.or(Bool.not(Nat.is_eq(Nat.mod(y, 100n), 0n)), Nat.is_eq(Nat.mod(y, 400n), 0n)))

def year_len(+y: Nat) -> Nat:
  pick(Nat, leap(y), 366n, 365n)

def month_len(+y: Nat, +m: Nat) -> Nat:
  pick(Nat, Nat.is_eq(m, 2n), pick(Nat, leap(y), 29n, 28n),
  pick(Nat, Bool.or(Bool.or(Nat.is_eq(m, 4n), Nat.is_eq(m, 6n)), Bool.or(Nat.is_eq(m, 9n), Nat.is_eq(m, 11n))), 30n, 31n))

# days in the c years from 1970
def days_in_years(+c: Nat) -> Nat:
  match c:
    case 0n:
      0n
    case 1n+p:
      Nat.add(days_in_years(p), year_len(Nat.add(1970n, p)))

# days in the first k months of year y
def days_in_months(+k: Nat, +y: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(days_in_months(p, y), month_len(y, 1n+p))

def ymd_to_days.go(+y: Nat, +m: Nat, +d: Nat) -> Nat:
  Nat.add(days_in_years(Nat.sub(y, 1970n)), Nat.add(days_in_months(Nat.sub(m, 1n), y), Nat.sub(d, 1n)))

def ymd_to_days(y: Nat, m: Nat, d: Nat) -> Nat:
  ymd_to_days.go(y, m, d)

# a count and what is left over
type CR is Data:
  CR{c: Nat, r: Nat}

def CR.c(+x: CR) -> Nat:
  CR{c, r} = x
  c

def CR.r(+x: CR) -> Nat:
  CR{c, r} = x
  r

# whole years from 1970 + c while r covers them (stop: r is within year c)
def years.go(fuel: Nat, stop: Bool, +c: Nat, +r: Nat) -> CR:
  match fuel:
    case 0n:
      CR{c, r}
    case 1n+f:
      match stop:
        case True{}:
          CR{c, r}
        case False{}:
          +r2 = Nat.sub(r, year_len(Nat.add(1970n, c)))
          years.go(f, Nat.is_lt(r2, year_len(Nat.add(1970n, 1n+c))), 1n+c, r2)

# whole months of year y from month 1 + k while r covers them
def months.go(fuel: Nat, stop: Bool, +y: Nat, +k: Nat, +r: Nat) -> CR:
  match fuel:
    case 0n:
      CR{k, r}
    case 1n+f:
      match stop:
        case True{}:
          CR{k, r}
        case False{}:
          +r2 = Nat.sub(r, month_len(y, 1n+k))
          months.go(f, Nat.is_lt(r2, month_len(y, 2n+k)), y, 1n+k, r2)

def days_to_ymd.of(+y: Nat, +mr: CR) -> Ymd:
  Ymd{y, 1n+CR.c(mr), 1n+CR.r(mr)}

def days_to_ymd.year(+yr: CR) -> Ymd:
  +y = Nat.add(1970n, CR.c(yr))
  days_to_ymd.of(y, months.go(12n, Nat.is_lt(CR.r(yr), month_len(y, 1n)), y, 0n, CR.r(yr)))

def days_to_ymd.go(+n: Nat) -> Ymd:
  days_to_ymd.year(years.go(1n+n, Nat.is_lt(n, year_len(1970n)), 0n, n))

def days_to_ymd(d: Nat) -> Ymd:
  days_to_ymd.go(d)

# ---------------------------------------------------------------------
# RFC3339 text (Go's time.Time.MarshalJSON, unquoted)
# ---------------------------------------------------------------------

def absdiff(+a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.sub(a, b), Nat.sub(b, a))

def pad2(+n: Nat) -> String:
  Dec.pad(2n, n)

def strip_zeros_l(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 48), strip_zeros_l(rest), SCon{c, rest})

def trim_zeros_r(+s: String) -> String:
  String.reverse(strip_zeros_l(String.reverse(s)))

# "." and the digits of r (r < 10^prec) without trailing zeros, or nothing
def frac_text(+r: Nat, +prec: Nat) -> String:
  pick(String, Nat.is_eq(r, 0n), "", "." ++ trim_zeros_r(Dec.pad(prec, r)))

def rfc_date(+t: Ymd) -> String:
  Ymd{y, m, d} = t
  Dec.pad(4n, y) ++ "-" ++ pad2(m) ++ "-" ++ pad2(d)

# the text of a time taken apart (rfc3339 matches its time first, so the
# checker never unfolds the arithmetic on an opaque time)
def rfc3339.of(+t: Time) -> String:
  +off = time_off(t)
  +local = Nat.sub(Nat.add(time_sec(t), off), 86400n)
  +sod = Nat.mod(local, 86400n)
  +zo = absdiff(off, 86400n)
  +zone = pick(String, Nat.is_eq(off, 86400n), "Z",
    pick(String, Nat.is_gt(off, 86400n), "+", "-") ++ pad2(Nat.div(zo, 3600n)) ++ ":" ++ pad2(Nat.mod(Nat.div(zo, 60n), 60n)))
  rfc_date(days_to_ymd(Nat.div(local, 86400n))) ++ "T" ++ pad2(Nat.div(sod, 3600n)) ++ ":" ++ pad2(Nat.mod(Nat.div(sod, 60n), 60n)) ++ ":" ++ pad2(Nat.mod(sod, 60n))
    ++ frac_text(time_nsec(t), 9n) ++ zone

def rfc3339(+t: Time) -> String:
  match t:
    case Time{+sec, +nsec, +off}:
      rfc3339.of(Time{sec, nsec, off})

# ---------------------------------------------------------------------
# Parsing RFC3339 as Go's time.Parse(time.RFC3339, s) does:
# YYYY-MM-DDTHH:MM:SS[(.|,)F+](Z|[+-]HH:MM), zone hours up to 24 and
# minutes up to 60 (Go's ranges), fraction digits past 9 dropped; dates
# from 1970 only
# ---------------------------------------------------------------------

def is_digit(+c: Char) -> Bool:
  Bool.and(U32.is_ge(code(c), 48), U32.is_le(code(c), 57))

def all_digits.go(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(is_digit(c), all_digits.go(rest))

# exactly n digits
def digits_n(+s: String, +n: Nat) -> Bool:
  Bool.and(Nat.is_eq(String.length(s), n), all_digits.go(s))

# the byte at i is k
def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

def at(+s: String, +i: Nat, k: U32) -> Bool:
  first_is(String.drop(s, i), k)

def field(+s: String, +i: Nat, +n: Nat) -> String:
  String.take(String.drop(s, i), n)

# the digits' value, a non-digit counting as 0 (so garbage stays small)
def sval.go(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      sval.go(rest, Nat.add(Nat.mul(acc, 10n), pick(Nat, is_digit(c), Dec.digit(c), 0n)))

def num(+s: String, +i: Nat, +n: Nat) -> Nat:
  sval.go(field(s, i, n), 0n)

def num_ok(+s: String, +i: Nat, +n: Nat) -> Bool:
  digits_n(field(s, i, n), n)

# the fraction digits and the zone after the seconds
type FZ is Data:
  FZ{frac: String, zone: String}

def FZ.frac(+p: FZ) -> String:
  FZ{frac, zone} = p
  frac

def FZ.zone(+p: FZ) -> String:
  FZ{frac, zone} = p
  zone

def span_digits.a(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, is_digit(c), SCon{c, span_digits.a(rest)}, SNil{})

# a fraction starts with "." or "," (as Go reads it)
def has_frac(+r: String) -> Bool:
  Bool.or(first_is(r, 46), first_is(r, 44))

def split_frac(+r: String) -> FZ:
  +ds = span_digits.a(String.drop(r, 1n))
  pick(FZ, has_frac(r), FZ{ds, String.drop(r, Nat.add(1n, String.length(ds)))}, FZ{"", r})

def frac_ok(+r: String, +f: String) -> Bool:
  Bool.or(Bool.not(has_frac(r)), Nat.is_ge(String.length(f), 1n))

# the first 9 digits, as nanoseconds (Go drops the rest)
def frac_ns(+f: String) -> Nat:
  +g = String.take(f, 9n)
  Nat.mul(Dec.value(g), Nat.pow(10n, Nat.sub(9n, String.length(g))))

def zone_num_ok(+z: String) -> Bool:
  Bool.and(Nat.is_eq(String.length(z), 6n),
    Bool.and(Bool.or(first_is(z, 43), first_is(z, 45)),
      Bool.and(num_ok(z, 1n, 2n), Bool.and(at(z, 3n, 58), Bool.and(num_ok(z, 4n, 2n),
        Bool.and(Nat.is_le(num(z, 1n, 2n), 24n), Nat.is_le(num(z, 4n, 2n), 60n)))))))

def zone_ok(+z: String) -> Bool:
  Bool.or(String.eq(z, "Z"), zone_num_ok(z))

# the zone as an offset plus 86400 (the literal second, so the checker
# never unfolds it)
def zone_off(+z: String) -> Nat:
  +secs = Nat.add(Nat.mul(num(z, 1n, 2n), 3600n), Nat.mul(num(z, 4n, 2n), 60n))
  pick(Nat, String.eq(z, "Z"), 86400n, pick(Nat, first_is(z, 43), Nat.add(secs, 86400n), Nat.sub(86400n, secs)))

def date_ok(+s: String) -> Bool:
  +y = num(s, 0n, 4n)
  +m = num(s, 5n, 2n)
  +d = num(s, 8n, 2n)
  Bool.and(Bool.and(num_ok(s, 0n, 4n), Bool.and(at(s, 4n, 45), Bool.and(num_ok(s, 5n, 2n), Bool.and(at(s, 7n, 45), num_ok(s, 8n, 2n))))),
    Bool.and(Nat.is_ge(y, 1970n), Bool.and(Bool.and(Nat.is_ge(m, 1n), Nat.is_le(m, 12n)), Bool.and(Nat.is_ge(d, 1n), Nat.is_le(d, month_len(y, m))))))

def clock_ok(+s: String) -> Bool:
  Bool.and(Bool.and(at(s, 10n, 84), Bool.and(num_ok(s, 11n, 2n), Bool.and(at(s, 13n, 58), Bool.and(num_ok(s, 14n, 2n), Bool.and(at(s, 16n, 58), num_ok(s, 17n, 2n)))))),
    Bool.and(Nat.is_lt(num(s, 11n, 2n), 24n), Bool.and(Nat.is_lt(num(s, 14n, 2n), 60n), Nat.is_lt(num(s, 17n, 2n), 60n))))

# local seconds since the epoch, plus 86400
def local86(+s: String) -> Nat:
  +days = ymd_to_days(num(s, 0n, 4n), num(s, 5n, 2n), num(s, 8n, 2n))
  Nat.add(Nat.add(Nat.mul(days, 86400n), 86400n),
    Nat.add(Nat.add(Nat.mul(num(s, 11n, 2n), 3600n), Nat.mul(num(s, 14n, 2n), 60n)), num(s, 17n, 2n)))

def parse.of(ok: Bool, +t: Time) -> Maybe<&2, Time>:
  match ok:
    case True{}:
      Some{t}
    case False{}:
      None{}

def parse_rfc3339.go(+s: String) -> Maybe<&2, Time>:
  +r = String.drop(s, 19n)
  +fz = split_frac(r)
  +off = zone_off(FZ.zone(fz))
  +l = local86(s)
  +ok = Bool.and(Bool.and(date_ok(s), clock_ok(s)),
    Bool.and(Bool.and(frac_ok(r, FZ.frac(fz)), zone_ok(FZ.zone(fz))), Nat.is_ge(l, off)))
  parse.of(ok, Time{Nat.sub(l, off), frac_ns(FZ.frac(fz)), off})

# "" reads as nothing, as .go reads it; the match first keeps the checker
# from unfolding the parser on a text it cannot see
def parse_rfc3339(s: String) -> Maybe<&2, Time>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +rest}:
      parse_rfc3339.go(SCon{c, rest})

# ---------------------------------------------------------------------
# Instants
# ---------------------------------------------------------------------

# ns has at most nine digits: it is below a second, told by its digit
# count (LAWS' nsec_ok), so a proof never compares it with 10^9
def nsec_fits(+ns: Nat) -> Bool:
  Nat.is_lt(String.length(Dec.show(ns)), 10n)

# the whole seconds in ns: 0 when it fits (no division to reason about)
def ns_carry.of(fits: Bool, +ns: Nat) -> Nat:
  match fits:
    case True{}:
      0n
    case False{}:
      Nat.div(ns, sec())

def ns_carry(+ns: Nat) -> Nat:
  ns_carry.of(nsec_fits(ns), ns)

# ns below a second: ns itself when it fits
def ns_low.of(fits: Bool, +ns: Nat) -> Nat:
  match fits:
    case True{}:
      ns
    case False{}:
      Nat.mod(ns, sec())

def ns_low(+ns: Nat) -> Nat:
  ns_low.of(nsec_fits(ns), ns)

# the CSV timestamp: the decimal nanosecond count
def unix_nanos(+t: Time) -> String:
  +s = Nat.add(time_sec(t), ns_carry(time_nsec(t)))
  +n = ns_low(time_nsec(t))
  pick(String, Nat.is_eq(s, 0n), Dec.show(n), Dec.show(s) ++ Dec.pad(9n, n))

# by seconds then nanoseconds (carried, so any nsec compares right)
def cmp(+a: Time, +b: Time) -> Cmp:
  +sa = Nat.add(time_sec(a), Nat.div(time_nsec(a), sec()))
  +sb = Nat.add(time_sec(b), Nat.div(time_nsec(b), sec()))
  +c = Nat.cmp(sa, sb)
  pick(Cmp, Cmp.is_eq(c), Nat.cmp(Nat.mod(time_nsec(a), sec()), Nat.mod(time_nsec(b), sec())), c)

def add_ns(+t: Time, n: Nat) -> Time:
  +ns = Nat.add(time_nsec(t), n)
  Time{Nat.add(time_sec(t), Nat.div(ns, sec())), Nat.mod(ns, sec()), time_off(t)}

# a - b in ns, 0 when b is later
def sub_ns(+a: Time, +b: Time) -> Nat:
  +sa = Nat.add(time_sec(a), Nat.div(time_nsec(a), sec()))
  +sb = Nat.add(time_sec(b), Nat.div(time_nsec(b), sec()))
  +na = Nat.mod(time_nsec(a), sec())
  +nb = Nat.mod(time_nsec(b), sec())
  pick(Nat, Nat.is_lt(sa, sb), 0n, Nat.sub(Nat.add(Nat.mul(Nat.sub(sa, sb), sec()), na), nb))

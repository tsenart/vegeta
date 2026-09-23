# Report metrics: an accumulator of hits, mergeable, closed into a Summary.
#
# The accumulator holds, for the results added so far: their count and
# successes, the status codes as an ascending code -> count list, the
# error set as an ascending list, the exact totals as Bigs, the extremes
# (least and greatest latency, first and last start, last end: NoExt when
# there are none) and the latencies as a rope. All but the rope are
# canonical functions of the multiset of results, and merge is a
# commutative monoid on them (unions of ascending lists, sums, mins and
# maxes); the rope concatenates in O(1) and is sorted once, in close, for
# the exact nearest-rank percentiles and the histogram.
#
# Times are kept as (seconds, nanoseconds below a second): a nanosecond
# count since the epoch does not fit a runtime Nat.
import Base
import ./big.bend as Big
import ./f64.bend as F64
import ./civil.bend as Civil
import ./hit.bend as Hit

type Lats is Data:
  LNone{}
  LOne{x: Nat}
  LCat{l: Lats, r: Lats}

type Ext is Data:
  NoExt{}
  Ext{lmin: Nat, lmax: Nat, es: Nat, en: Nat, ls: Nat, ln: Nat, xs: Nat, xn: Nat}

type Acc is Data:
  Acc{buckets: List<&2, Nat>, n: Nat, ok: Nat, codes: List<&2, Sigma<&2, &2, Nat, _ => Nat>>,
      errors: List<&2, String>, lat: Big.Big, bin: Big.Big, bout: Big.Big, ext: Ext, lats: Lats}

type Summary is Data:
  Summary{requests: Nat, success: Nat,
          codes: List<&2, Sigma<&2, &2, Nat, _ => Nat>>, errors: List<&2, String>,
          lat_total: Big.Big, lat_mean: Nat, lat_min: Nat, lat_max: Nat,
          p50: Nat, p90: Nat, p95: Nat, p99: Nat,
          bytes_in: Big.Big, bytes_out: Big.Big, in_mean: F64.F64, out_mean: F64.F64,
          rate: F64.F64, throughput: F64.F64, ratio: F64.F64,
          earliest: Maybe<&2, Civil.Time>, latest: Maybe<&2, Civil.Time>, end: Maybe<&2, Civil.Time>,
          duration: Nat, wait: Nat, buckets: List<&2, Nat>, hist: List<&2, Nat>}

# c ? a : b
def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def sec() -> Nat:
  1000000000n

# Base's Nat.min and Nat.max count down in unary: slow and deep at runtime
def nmin(+a: Nat, +b: Nat) -> Nat:
  pick(Nat, Nat.is_le(a, b), a, b)

def nmax(+a: Nat, +b: Nat) -> Nat:
  pick(Nat, Nat.is_le(a, b), b, a)

def is_ok(+c: Nat) -> Bool:
  Bool.and(Nat.is_ge(c, 200n), Nat.is_lt(c, 400n))

# ---------------------------------------------------------------------
# Status codes: ascending code -> count
# ---------------------------------------------------------------------

def code_k(+p: Sigma<&2, &2, Nat, _ => Nat>) -> Nat:
  (k, v) = p
  k

def code_v(+p: Sigma<&2, &2, Nat, _ => Nat>) -> Nat:
  (k, v) = p
  v

def code_sum(+p: Sigma<&2, &2, Nat, _ => Nat>, +q: Sigma<&2, &2, Nat, _ => Nat>) -> Sigma<&2, &2, Nat, _ => Nat>:
  (code_k(p), Nat.add(code_v(p), code_v(q)))

# the union of two ascending lists, adding the counts of a code in both
def codes_merge.go(fuel: Nat, xs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>, ys: List<&2, Sigma<&2, &2, Nat, _ => Nat>>)
  -> List<&2, Sigma<&2, &2, Nat, _ => Nat>>:
  match fuel:
    case 0n:
      List.append(&2, Sigma<&2, &2, Nat, _ => Nat>, xs, ys)
    case 1n+f:
      match xs:
        case Nil{}:
          ys
        case Con{+p, +xr}:
          match ys:
            case Nil{}:
              Con{p, xr}
            case Con{+q, +yr}:
              +lt = Nat.is_lt(code_k(p), code_k(q))
              +gt = Nat.is_gt(code_k(p), code_k(q))
              Con{pick(Sigma<&2, &2, Nat, _ => Nat>, lt, p, pick(Sigma<&2, &2, Nat, _ => Nat>, gt, q, code_sum(p, q))),
                codes_merge.go(f, pick(List<&2, Sigma<&2, &2, Nat, _ => Nat>>, gt, Con{p, xr}, xr),
                  pick(List<&2, Sigma<&2, &2, Nat, _ => Nat>>, lt, Con{q, yr}, yr))}

def codes_merge(+xs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>, +ys: List<&2, Sigma<&2, &2, Nat, _ => Nat>>)
  -> List<&2, Sigma<&2, &2, Nat, _ => Nat>>:
  codes_merge.go(Nat.add(List.length(&2, Sigma<&2, &2, Nat, _ => Nat>, xs), List.length(&2, Sigma<&2, &2, Nat, _ => Nat>, ys)), xs, ys)

# ---------------------------------------------------------------------
# The error set: ascending, distinct
# ---------------------------------------------------------------------

def strs_merge.go(fuel: Nat, xs: List<&2, String>, ys: List<&2, String>) -> List<&2, String>:
  match fuel:
    case 0n:
      List.append(&2, String, xs, ys)
    case 1n+f:
      match xs:
        case Nil{}:
          ys
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              Con{x, xr}
            case Con{+y, +yr}:
              +lt = String.is_lt(x, y)
              +gt = String.is_lt(y, x)
              Con{pick(String, gt, y, x),
                strs_merge.go(f, pick(List<&2, String>, gt, Con{x, xr}, xr), pick(List<&2, String>, lt, Con{y, yr}, yr))}

def strs_merge(+xs: List<&2, String>, +ys: List<&2, String>) -> List<&2, String>:
  strs_merge.go(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), xs, ys)

# ---------------------------------------------------------------------
# Extremes
# ---------------------------------------------------------------------

# (s1, n1) is no later than (s2, n2)
def no_later(+s1: Nat, +n1: Nat, +s2: Nat, +n2: Nat) -> Bool:
  Bool.or(Nat.is_lt(s1, s2), Bool.and(Nat.is_eq(s1, s2), Nat.is_le(n1, n2)))

def ext_both(+a1: Nat, +b1: Nat, +es1: Nat, +en1: Nat, +ls1: Nat, +ln1: Nat, +xs1: Nat, +xn1: Nat,
             +a2: Nat, +b2: Nat, +es2: Nat, +en2: Nat, +ls2: Nat, +ln2: Nat, +xs2: Nat, +xn2: Nat) -> Ext:
  +e1 = no_later(es1, en1, es2, en2)
  +l1 = no_later(ls1, ln1, ls2, ln2)
  +x1 = no_later(xs1, xn1, xs2, xn2)
  Ext{nmin(a1, a2), nmax(b1, b2),
      pick(Nat, e1, es1, es2), pick(Nat, e1, en1, en2),
      pick(Nat, l1, ls2, ls1), pick(Nat, l1, ln2, ln1),
      pick(Nat, x1, xs2, xs1), pick(Nat, x1, xn2, xn1)}

def ext_merge.r(b: Ext, +a1: Nat, +b1: Nat, +es1: Nat, +en1: Nat, +ls1: Nat, +ln1: Nat, +xs1: Nat, +xn1: Nat) -> Ext:
  match b:
    case NoExt{}:
      Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}
    case Ext{+a2, +b2, +es2, +en2, +ls2, +ln2, +xs2, +xn2}:
      ext_both(a1, b1, es1, en1, ls1, ln1, xs1, xn1, a2, b2, es2, en2, ls2, ln2, xs2, xn2)

def ext_merge(a: Ext, b: Ext) -> Ext:
  match a:
    case NoExt{}:
      b
    case Ext{+a1, +b1, +es1, +en1, +ls1, +ln1, +xs1, +xn1}:
      ext_merge.r(b, a1, b1, es1, en1, ls1, ln1, xs1, xn1)

# ---------------------------------------------------------------------
# Latencies: a rope, flattened and sorted in close
# ---------------------------------------------------------------------

def lcat.r(b: Lats, a: Lats) -> Lats:
  match b:
    case LNone{}:
      a
    case LOne{x}:
      LCat{a, LOne{x}}
    case LCat{l, r}:
      LCat{a, LCat{l, r}}

def lcat(a: Lats, b: Lats) -> Lats:
  match a:
    case LNone{}:
      b
    case LOne{x}:
      lcat.r(b, LOne{x})
    case LCat{l, r}:
      lcat.r(b, LCat{l, r})

def flatten(t: Lats, acc: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case LNone{}:
      acc
    case LOne{x}:
      Con{x, acc}
    case LCat{l, r}:
      flatten(l, flatten(r, acc))

# two ascending lists merged (fuel: their total length)
def nmerge(fuel: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match fuel:
    case 0n:
      List.append(&2, Nat, xs, ys)
    case 1n+f:
      match xs:
        case Nil{}:
          ys
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              Con{x, xr}
            case Con{+y, +yr}:
              +le = Nat.is_le(x, y)
              Con{pick(Nat, le, x, y), nmerge(f, pick(List<&2, Nat>, le, xr, Con{x, xr}), pick(List<&2, Nat>, le, Con{y, yr}, yr))}

# merge sort of the n numbers xs, both halves in parallel (fuel: n bounds
# the depth)
def msort(fuel: Nat, small: Bool, +xs: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      xs
    case 1n+(+f):
      match small:
        case True{}:
          xs
        case False{}:
          +h = Nat.div(n, 2n)
          +m = Nat.sub(n, h)
          a b = msort(f, Nat.is_le(h, 1n), List.take(&2, Nat, xs, h), h) msort(f, Nat.is_le(m, 1n), List.drop(&2, Nat, xs, h), m)
          nmerge(n, a, b)

def sort(+xs: List<&2, Nat>) -> List<&2, Nat>:
  +n = List.length(&2, Nat, xs)
  msort(n, Nat.is_le(n, 1n), xs, n)

# ---------------------------------------------------------------------
# Histogram: Go's Histogram.Add
# ---------------------------------------------------------------------

# whether lat falls in the first bucket of bs: [b0, b1), or anything for
# the last bucket
def in_first(+bs: List<&2, Nat>, +lat: Nat) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{+b, +rest}:
      match rest:
        case Nil{}:
          True{}
        case Con{+c, +more}:
          Bool.and(Nat.is_le(b, lat), Nat.is_lt(lat, c))

def bucket_of.go(bs: List<&2, Nat>, stop: Bool, +lat: Nat, +i: Nat) -> Nat:
  match bs:
    case Nil{}:
      i
    case Con{+b, +rest}:
      match stop:
        case True{}:
          i
        case False{}:
          bucket_of.go(rest, in_first(rest, lat), lat, 1n+i)

def bucket_of(+bs: List<&2, Nat>, +lat: Nat) -> Nat:
  bucket_of.go(bs, in_first(bs, lat), lat, 0n)

def inc_at(cs: List<&2, Nat>, i: Nat) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      []
    case Con{+c, +rest}:
      match i:
        case 0n:
          Con{1n+c, rest}
        case 1n+j:
          Con{c, inc_at(rest, j)}

def hist_of(xs: List<&2, Nat>, +bs: List<&2, Nat>, cs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      cs
    case Con{+x, +rest}:
      hist_of(rest, bs, inc_at(cs, bucket_of(bs, x)))

# ---------------------------------------------------------------------
# The accumulator
# ---------------------------------------------------------------------

def empty(bs: List<&2, Nat>) -> Acc:
  Acc{bs, 0n, 0n, [], [], Big.of(0n), Big.of(0n), Big.of(0n), NoExt{}, LNone{}}

def merge(+a: Acc, +b: Acc) -> Acc:
  Acc{bs, n1, ok1, cs1, es1, l1, i1, o1, x1, t1} = a
  Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2} = b
  Acc{bs, Nat.add(n1, n2), Nat.add(ok1, ok2), codes_merge(cs1, cs2), strs_merge(es1, es2),
      Big.add(l1, l2), Big.add(i1, i2), Big.add(o1, o2), ext_merge(x1, x2), lcat(t1, t2)}

# one result on its own: its start and end carried into (s, ns < 1s)
def of_hit(+h: Hit.Hit) -> Acc:
  Hit.Hit{attack, seq, code, ts, lat, bo, bi, err, body, method, url, hdrs} = h
  Civil.Time{s0, ns0, off} = ts
  +s = Nat.add(s0, Nat.div(ns0, sec()))
  +ns = Nat.mod(ns0, sec())
  +en = Nat.add(ns, Nat.mod(lat, sec()))
  +es = Nat.add(Nat.add(s, Nat.div(lat, sec())), Nat.div(en, sec()))
  Acc{[], 1n, pick(Nat, is_ok(code), 1n, 0n), [(code, 1n)], pick(List<&2, String>, String.is_empty(err), [], [err]),
      Big.of(lat), Big.of(bi), Big.of(bo), Ext{lat, lat, s, ns, s, ns, es, Nat.mod(en, sec())}, LOne{lat}}

def add(+a: Acc, +h: Hit.Hit) -> Acc:
  merge(a, of_hit(h))

# ---------------------------------------------------------------------
# Closing
# ---------------------------------------------------------------------

# F64.of_nat(sec()) = 1953125 * 2^9, as a literal (the checker would
# unfold a closed Big.of(10^9) one unit at a time)
def sec_f64() -> F64.F64:
  F64.F64{Big.Big{[3125n, 195n]}, 9n, False{}}

# Go's Duration.Seconds(): float64(d / 1s) + float64(d % 1s) / 1e9
def seconds(+d: Nat) -> F64.F64:
  F64.add(F64.of_nat(Nat.div(d, sec())), F64.div(F64.of_nat(Nat.mod(d, sec())), sec_f64()))

# (s2, n2) - (s1, n1) in ns, for (s1, n1) no later
def span_ns(+s1: Nat, +n1: Nat, +s2: Nat, +n2: Nat) -> Nat:
  Nat.sub(Nat.add(Nat.mul(Nat.sub(s2, s1), sec()), n2), n1)

# nearest rank: the ceil(q% of n)-th smallest, counted from 0
def rank(+q: Nat, +n: Nat) -> Nat:
  Nat.sub(Nat.div(Nat.add(Nat.mul(q, n), 99n), 100n), 1n)

def nth_or0(+i: Nat, +xs: List<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, xs, i), 0n)

def per_sec(pos: Bool, +x: F64.F64, +d: Nat) -> F64.F64:
  match pos:
    case True{}:
      F64.div(x, seconds(d))
    case False{}:
      x

def utc(+s: Nat, +ns: Nat) -> Maybe<&2, Civil.Time>:
  Some{Civil.Time{s, ns, 86400n}}

def close.full(+bs: List<&2, Nat>, +n: Nat, +ok: Nat, +codes: List<&2, Sigma<&2, &2, Nat, _ => Nat>>, +errs: List<&2, String>,
               +lat: Big.Big, +bin: Big.Big, +bout: Big.Big, +lmin: Nat, +lmax: Nat, +es: Nat, +en: Nat, +ls: Nat, +ln: Nat,
               +xs: Nat, +xn: Nat, +sorted: List<&2, Nat>) -> Summary:
  +dur = span_ns(es, en, ls, ln)
  +wait = span_ns(ls, ln, xs, xn)
  +fn = F64.of_nat(n)
  +fok = F64.of_nat(ok)
  +pos = Nat.is_gt(dur, 0n)
  Summary{n, ok, codes, errs, lat, F64.trunc(F64.div(F64.of_big(lat), fn)), lmin, lmax,
    nth_or0(rank(50n, n), sorted), nth_or0(rank(90n, n), sorted), nth_or0(rank(95n, n), sorted), nth_or0(rank(99n, n), sorted),
    bin, bout, F64.div(F64.of_big(bin), fn), F64.div(F64.of_big(bout), fn),
    per_sec(pos, fn, dur), per_sec(pos, fok, Nat.add(dur, wait)), F64.div(fok, fn),
    utc(es, en), utc(ls, ln), utc(xs, xn), dur, wait, bs,
    hist_of(sorted, bs, List.replicate(Nat, List.length(&2, Nat, bs), 0n))}

def close.of(x: Ext, +bs: List<&2, Nat>, +n: Nat, +ok: Nat, +codes: List<&2, Sigma<&2, &2, Nat, _ => Nat>>, +errs: List<&2, String>,
             +lat: Big.Big, +bin: Big.Big, +bout: Big.Big, t: Lats) -> Summary:
  match x:
    case NoExt{}:
      Summary{0n, 0n, [], [], Big.of(0n), 0n, 0n, 0n, 0n, 0n, 0n, 0n,
              Big.of(0n), Big.of(0n), F64.zero(), F64.zero(), F64.zero(), F64.zero(), F64.zero(),
              None{}, None{}, None{}, 0n, 0n, bs, List.replicate(Nat, List.length(&2, Nat, bs), 0n)}
    case Ext{+lmin, +lmax, +es, +en, +ls, +ln, +xs, +xn}:
      close.full(bs, n, ok, codes, errs, lat, bin, bout, lmin, lmax, es, en, ls, ln, xs, xn, sort(flatten(t, [])))

# the span, first start to last end, is below 281474 s, so the summary's
# durations fit a runtime Nat (below 2^48 ns); the report refuses the rest
def span_ok.of(x: Ext) -> Bool:
  match x:
    case NoExt{}:
      True{}
    case Ext{lmin, lmax, +es, en, ls, ln, +xs, xn}:
      Nat.is_lt(Nat.sub(xs, es), 281474n)

def span_ok(+a: Acc) -> Bool:
  Acc{bs, n, ok, codes, errs, lat, bin, bout, x, t} = a
  span_ok.of(x)

def close(+a: Acc) -> Summary:
  Acc{bs, n, ok, codes, errs, lat, bin, bout, x, t} = a
  close.of(x, bs, n, ok, codes, errs, lat, bin, bout, t)

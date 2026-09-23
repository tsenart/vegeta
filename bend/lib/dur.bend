# Go time.Duration text, and Vegeta's report rounding.
#
# show is Go's Duration.String for n >= 0; round is Vegeta's report
# rounding; parse is time.ParseDuration less negative durations ("-" only
# before a zero duration, read as 0) and less durations from 281474 s up
# (LAWS dur_ok). Fractions are computed in float64, as Go does.
import Base
import ./dec.bend as Dec
import ./big.bend as Big
import ./f64.bend as F64

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

def micro() -> String:
  SCon{Chr{194}, SCon{Chr{181}, SNil{}}}

def greek_mu() -> String:
  SCon{Chr{206}, SCon{Chr{188}, SNil{}}}

def us() -> Nat:
  1000n

def ms() -> Nat:
  1000000n

def sec() -> Nat:
  1000000000n

# ---------------------------------------------------------------------
# Text
# ---------------------------------------------------------------------

def strip_zeros_l(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 48), strip_zeros_l(rest), SCon{c, rest})

def trim_zeros_r(+s: String) -> String:
  String.reverse(strip_zeros_l(String.reverse(s)))

# Go's fmtFrac: "." and the digits of r (r < 10^prec) without trailing
# zeros, or nothing when r is 0
def frac_text(+r: Nat, +prec: Nat) -> String:
  pick(String, Nat.is_eq(r, 0n), "", "." ++ trim_zeros_r(Dec.pad(prec, r)))

def show.go(+n: Nat) -> String:
  +u = Nat.div(n, sec())
  +secs = Dec.show(Nat.mod(u, 60n)) ++ frac_text(Nat.mod(n, sec()), 9n) ++ "s"
  +mins = pick(String, Nat.is_ge(u, 60n), Dec.show(Nat.mod(Nat.div(u, 60n), 60n)) ++ "m", "")
  +hrs = pick(String, Nat.is_ge(u, 3600n), Dec.show(Nat.div(u, 3600n)) ++ "h", "")
  pick(String, Nat.is_eq(n, 0n), "0s",
  pick(String, Nat.is_lt(n, us()), Dec.show(n) ++ "ns",
  pick(String, Nat.is_lt(n, ms()), Dec.show(Nat.div(n, us())) ++ frac_text(Nat.mod(n, us()), 3n) ++ micro() ++ "s",
  pick(String, Nat.is_lt(n, sec()), Dec.show(Nat.div(n, ms())) ++ frac_text(Nat.mod(n, ms()), 6n) ++ "ms",
    hrs ++ mins ++ secs))))

def show(n: Nat) -> String:
  show.go(n)

# ---------------------------------------------------------------------
# Rounding
# ---------------------------------------------------------------------

# Go's Duration.Round(f * b) for n >= 0 (halves round up)
def round_to(+n: Nat, +f: Nat, +b: Nat) -> Nat:
  +q = Nat.div(n, b)
  +a = Nat.mod(q, f)
  +c = Nat.mod(n, b)
  +up = Bool.or(Nat.is_ge(Nat.mul(2n, a), f), Bool.and(Nat.is_eq(Nat.add(Nat.mul(2n, a), 1n), f), Nat.is_ge(Nat.mul(2n, c), b)))
  Nat.mul(pick(Nat, up, Nat.add(Nat.sub(q, a), f), Nat.sub(q, a)), b)

def round.go(+n: Nat) -> Nat:
  +secs = Nat.div(n, sec())
  pick(Nat, Nat.is_ge(secs, 3600n), round_to(n, 60n, sec()),
  pick(Nat, Nat.is_ge(secs, 60n), round_to(n, 1n, sec()),
  pick(Nat, Nat.is_ge(secs, 1n), round_to(n, 1n, ms()),
  pick(Nat, Nat.is_ge(n, ms()), round_to(n, 1n, us()), n))))

def round(n: Nat) -> Nat:
  round.go(n)

# ---------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------

type SS is Data:
  SS{a: String, b: String}

def SS.a(+p: SS) -> String:
  SS{a, b} = p
  a

def SS.b(+p: SS) -> String:
  SS{a, b} = p
  b

def is_digit(+c: Char) -> Bool:
  Bool.and(U32.is_ge(code(c), 48), U32.is_le(code(c), 57))

def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

# the leading digits of s, and what follows them
def span_digits(s: String) -> SS:
  match s:
    case SNil{}:
      SS{"", ""}
    case SCon{+c, +rest}:
      +r = span_digits(rest)
      pick(SS, is_digit(c), SS{SCon{c, SS.a(r)}, SS.b(r)}, SS{"", SCon{c, rest}})

def in_range32(+k: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(k, lo), U32.is_le(k, hi))

def is_num_or_dot(+k: U32) -> Bool:
  Bool.or(in_range32(k, 48, 57), U32.is_eq(k, 46))

# the leading run of a unit name: up to the next digit or dot
def span_unit(s: String) -> SS:
  match s:
    case SNil{}:
      SS{"", ""}
    case SCon{+c, +rest}:
      +r = span_unit(rest)
      pick(SS, is_num_or_dot(code(c)), SS{"", SCon{c, rest}}, SS{SCon{c, SS.a(r)}, SS.b(r)})

def is_micro(+u: String) -> Bool:
  Bool.or(Bool.or(String.eq(u, "us"), String.eq(u, micro() ++ "s")), String.eq(u, greek_mu() ++ "s"))

def is_unit_name(+u: String) -> Bool:
  Bool.or(Bool.or(Bool.or(String.eq(u, "ns"), String.eq(u, "us")), Bool.or(String.eq(u, micro() ++ "s"), String.eq(u, greek_mu() ++ "s"))),
    Bool.or(Bool.or(String.eq(u, "ms"), String.eq(u, "s")), Bool.or(String.eq(u, "m"), String.eq(u, "h"))))

# a unit's size in ns
def unit_big(+u: String) -> Big.Big:
  pick(Big.Big, String.eq(u, "ns"), Big.Big{[1n]},
  pick(Big.Big, Bool.or(Bool.or(String.eq(u, "us"), String.eq(u, micro() ++ "s")), String.eq(u, greek_mu() ++ "s")), Big.Big{[1000n]},
  pick(Big.Big, String.eq(u, "ms"), Big.Big{[0n, 100n]},
  pick(Big.Big, String.eq(u, "s"), Big.Big{[0n, 0n, 10n]},
  pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]})))))

def has_nonzero_digit(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.or(in_range32(code(c), 49, 57), has_nonzero_digit(rest))

def bdigits.go(s: String, +acc: Big.Big) -> Big.Big:
  match s:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      bdigits.go(rest, Big.add(Big.mul_small(acc, 10n), Big.of(Dec.digit(c))))

# the number a run of digits denotes
def bdigits(+s: String) -> Big.Big:
  bdigits.go(s, Big.of(0n))

# (1<<63 - 1) / 10 and 1<<63
def go_cut() -> Big.Big:
  Big.Big{[7580n, 8547n, 2036n, 2337n, 92n]}

def go_top() -> Big.Big:
  Big.Big{[5808n, 5477n, 368n, 3372n, 922n]}

type GF is Data:
  GF{x: Big.Big, scale: Big.Big, over: Bool}

def GF.x(+g: GF) -> Big.Big:
  GF{x, scale, over} = g
  x

def GF.scale(+g: GF) -> Big.Big:
  GF{x, scale, over} = g
  scale

def GF.over(+g: GF) -> Bool:
  GF{x, scale, over} = g
  over

def gf.digit(over: Bool, +c: Char, +g: GF) -> GF:
  match over:
    case True{}:
      g
    case False{}:
      +y = Big.add(Big.mul_small(GF.x(g), 10n), Big.of(Dec.digit(c)))
      +stop = Bool.or(Cmp.is_gt(Big.cmp(GF.x(g), go_cut())), Cmp.is_gt(Big.cmp(y, go_top())))
      pick(GF, stop, GF{GF.x(g), GF.scale(g), True{}}, GF{y, Big.mul_small(GF.scale(g), 10n), False{}})

# Go's leadingFraction: the digits' value and 10^(digits read), where
# digits past int64's range are dropped
def gf.go(s: String, +g: GF) -> GF:
  match s:
    case SNil{}:
      g
    case SCon{+c, +rest}:
      gf.go(rest, gf.digit(GF.over(g), c, g))

# what a fraction adds, in ns: int64(float64(f) * (float64(unit) / scale))
def frac_ns.go(+fp: String, +unit: Big.Big) -> Nat:
  +g = gf.go(fp, GF{Big.of(0n), Big.of(1n), False{}})
  F64.trunc(F64.mul(F64.of_big(GF.x(g)), F64.div(F64.of_big(unit), F64.of_big(GF.scale(g)))))

def frac_ns(has: Bool, +fp: String, +unit: Big.Big) -> Nat:
  match has:
    case True{}:
      frac_ns.go(fp, unit)
    case False{}:
      0n

# the state of a parse: whether all is well so far, the exact value
# num/den (to check the bound), and Go's value in ns
type Acc is Data:
  Acc{ok: Bool, num: Big.Big, den: Big.Big, v: Big.Big}

def Acc.ok(+a: Acc) -> Bool:
  Acc{ok, num, den, v} = a
  ok

def Acc.num(+a: Acc) -> Big.Big:
  Acc{ok, num, den, v} = a
  num

def Acc.den(+a: Acc) -> Big.Big:
  Acc{ok, num, den, v} = a
  den

def Acc.v(+a: Acc) -> Big.Big:
  Acc{ok, num, den, v} = a
  v

# one term read off the front of s, added to acc; with what follows it
type Step is Data:
  Step{acc: Acc, rest: String}

def Step.acc(+s: Step) -> Acc:
  Step{acc, rest} = s
  acc

def Step.rest(+s: Step) -> String:
  Step{acc, rest} = s
  rest

def term(+s: String, +acc: Acc) -> Step:
  +p = span_digits(s)
  +dot = first_is(SS.b(p), 46)
  +q = span_digits(pick(String, dot, String.drop(SS.b(p), 1n), SS.b(p)))
  +num = Bool.or(Bool.not(String.is_empty(SS.a(p))), Bool.and(dot, Bool.not(String.is_empty(SS.a(q)))))
  +u = span_unit(SS.b(q))
  +unit = unit_big(SS.a(u))
  +scale = F64.pow10(String.length(SS.a(q)))
  +ip = bdigits(SS.a(p))
  +tn = Big.mul(Big.add(Big.mul(ip, scale), bdigits(SS.a(q))), unit)
  +v = Big.add(Big.mul(ip, unit), Big.of(frac_ns(Bool.not(String.is_empty(SS.a(q))), SS.a(q), unit)))
  +ok = Bool.and(Acc.ok(acc), Bool.and(num, is_unit_name(SS.a(u))))
  Step{Acc{ok, Big.add(Big.mul(Acc.num(acc), scale), Big.mul(tn, Acc.den(acc))), Big.mul(Acc.den(acc), scale), Big.add(Acc.v(acc), v)}, SS.b(u)}

# out of fuel: done if stopped, else input is left over
def terms.end(stop: Bool, +acc: Acc) -> Acc:
  match stop:
    case True{}:
      acc
    case False{}:
      Acc{False{}, Acc.num(acc), Acc.den(acc), Acc.v(acc)}

# terms until the input or the syntax ends
def terms.go(fuel: Nat, stop: Bool, +s: String, +acc: Acc) -> Acc:
  match fuel:
    case 0n:
      terms.end(stop, acc)
    case 1n+f:
      match stop:
        case True{}:
          acc
        case False{}:
          +st = term(s, acc)
          terms.go(f, Bool.or(Bool.not(Acc.ok(Step.acc(st))), String.is_empty(Step.rest(st))), Step.rest(st), Step.acc(st))

def terms(+t: String) -> Acc:
  terms.go(String.length(t), False{}, t, Acc{True{}, Big.of(0n), Big.of(1n), Big.of(0n)})

# ---------------------------------------------------------------------
# The language, exactly as LAWS' dur_ok states it
# ---------------------------------------------------------------------

# one or more terms: digits, an optional fraction, and a known unit
def terms_ok(+fuel: Nat, +s: String) -> Bool:
  match fuel:
    case 0n:
      False{}
    case 1n+f:
      +p = span_digits(s)
      +dot = first_is(SS.b(p), 46)
      +q = span_digits(pick(String, dot, String.drop(SS.b(p), 1n), SS.b(p)))
      +num = Bool.or(Bool.not(String.is_empty(SS.a(p))), Bool.and(dot, Bool.not(String.is_empty(SS.a(q)))))
      +u = span_unit(SS.b(q))
      Bool.and(Bool.and(num, is_unit_name(SS.a(u))), Bool.or(String.is_empty(SS.b(u)), terms_ok(f, SS.b(u))))

def bpow10(n: Nat) -> Big.Big:
  match n:
    case 0n:
      Big.of(1n)
    case 1n+p:
      Big.mul(bpow10(p), Big.of(10n))

def ldigits.go(s: String, +acc: Big.Big) -> Big.Big:
  match s:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      ldigits.go(rest, Big.add(Big.mul(acc, Big.of(10n)), Big.of(Dec.digit(c))))

def ldigits(+s: String) -> Big.Big:
  ldigits.go(s, Big.of(0n))

type Frac is Data:
  Frac{num: Big.Big, den: Big.Big}

def mk_frac(+n: Big.Big, +d: Big.Big) -> Frac:
  Frac{n, d}

def frac_add(+a: Frac, +b: Frac) -> Frac:
  Frac{an, ad} = a
  Frac{bn, bd} = b
  Frac{Big.add(Big.mul(an, bd), Big.mul(bn, ad)), Big.mul(ad, bd)}

# the exact value in ns of a run of terms
def terms_val(+fuel: Nat, +s: String) -> Frac:
  match fuel:
    case 0n:
      mk_frac(Big.of(0n), Big.of(1n))
    case 1n+f:
      +p = span_digits(s)
      +dot = first_is(SS.b(p), 46)
      +q = pick(SS, dot, span_digits(String.drop(SS.b(p), 1n)), SS{"", SS.b(p)})
      +u = span_unit(SS.b(q))
      +scale = bpow10(String.length(SS.a(q)))
      +this = mk_frac(Big.mul(Big.add(Big.mul(ldigits(SS.a(p)), scale), ldigits(SS.a(q))), unit_big(SS.a(u))), scale)
      pick(Frac, String.is_empty(SS.b(u)), this, frac_add(this, terms_val(f, SS.b(u))))

# 281474 s
def dur_bound() -> Big.Big:
  Big.Big{[0n, 0n, 4740n, 281n]}

def frac_below(+x: Frac, +bound: Big.Big) -> Bool:
  Frac{n, d} = x
  Cmp.is_lt(Big.cmp(n, Big.mul(bound, d)))

def dur_fits(+t: String) -> Bool:
  frac_below(terms_val(String.length(t), t), dur_bound())

# ---------------------------------------------------------------------
# Parsing: the sign, then the terms (the value as Go computes it)
# ---------------------------------------------------------------------

def parse.of(ok: Bool, +n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

# a valid unsigned run of terms: Go's value (the Nat is built only once
# it is known to fit)
def parse.body(ok: Bool, +t: String) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{Big.to_nat(Acc.v(terms(t)))}
    case False{}:
      None{}

def parse.zero(z: Bool, +t: String) -> Maybe<&2, Nat>:
  match z:
    case True{}:
      Some{0n}
    case False{}:
      parse.body(Bool.and(terms_ok(String.length(t), t), dur_fits(t)), t)

def parse.again(a: Bool, +t: String) -> Maybe<&2, Nat>:
  match a:
    case True{}:
      None{}
    case False{}:
      parse.zero(String.eq(t, "0"), t)

# after "+" or no sign
def parse.t(+t: String) -> Maybe<&2, Nat>:
  parse.again(Bool.or(first_is(t, 43), first_is(t, 45)), t)

# after "-": only a zero duration, read as 0
def parse.neg(+t: String) -> Maybe<&2, Nat>:
  parse.of(Bool.and(Bool.not(Bool.or(first_is(t, 43), first_is(t, 45))),
    Bool.or(String.eq(t, "0"), Bool.and(terms_ok(String.length(t), t), Bool.not(has_nonzero_digit(t))))), 0n)

def parse.sgn(neg: Bool, pos: Bool, +s: String) -> Maybe<&2, Nat>:
  match neg:
    case True{}:
      parse.neg(String.drop(s, 1n))
    case False{}:
      match pos:
        case True{}:
          parse.t(String.drop(s, 1n))
        case False{}:
          parse.t(s)

def parse.go(+s: String) -> Maybe<&2, Nat>:
  parse.sgn(first_is(s, 45), first_is(s, 43), s)

def parse(s: String) -> Maybe<&2, Nat>:
  parse.go(s)

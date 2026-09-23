# Exact float64 emulation: value = m * 2^e (neg = False) or m / 2^e (neg = True).
#
# Canonical form (LAWS is_double): zero is F64{0, 0, False}; otherwise m
# is odd and below 2^53. Every operation computes its exact rational
# result p/q (Bigs) and rounds it to nearest even, down to the subnormals
# (2^-1074). Signed exponents are Nats offset by off() = 4096.
import Base
import ./big.bend as Big
import ./dec.bend as Dec

type F64 is Data:
  F64{m: Big.Big, e: Nat, neg: Bool}

def zero() -> F64:
  F64{Big.of(0n), 0n, False{}}

# c ? a : b
def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def off() -> Nat:
  4096n

def f_m(+x: F64) -> Big.Big:
  F64{m, e, neg} = x
  m

def f_e(+x: F64) -> Nat:
  F64{m, e, neg} = x
  e

def f_neg(+x: F64) -> Bool:
  F64{m, e, neg} = x
  neg

# ---------------------------------------------------------------------
# Big helpers
# ---------------------------------------------------------------------

def quo(+qr: Big.QR) -> Big.Big:
  Big.Big{Big.QR.q(qr)}

def big1() -> Big.Big:
  Big.of(1n)

def pow2.go(n: Nat, +acc: Big.Big) -> Big.Big:
  match n:
    case 0n:
      acc
    case 1n+p:
      pow2.go(p, Big.mul_small(acc, 1073741824n))

# 2^k
def pow2(+k: Nat) -> Big.Big:
  Big.mul_small(pow2.go(Nat.div(k, 30n), big1()), Nat.pow(2n, Nat.mod(k, 30n)))

# b * 2^n, by doubling (LAWS' bshl doubles with Big.mul; mul_small is
# linear, and the values agree)
def bshl(n: Nat, +b: Big.Big) -> Big.Big:
  match n:
    case 0n:
      b
    case 1n+p:
      bshl(p, Big.mul_small(b, 2n))

def p2.go(n: Nat, +acc: Big.Big) -> Big.Big:
  match n:
    case 0n:
      acc
    case 1n+p:
      p2.go(p, Big.mul_small(acc, 1024n))

# 2^k, ten bits a step (a proof can tell 2^10 is 1024; 2^30 is too big
# for it to evaluate)
def p2(+k: Nat) -> Big.Big:
  bshl(Nat.mod(k, 10n), p2.go(Nat.div(k, 10n), big1()))

def pow10.go(n: Nat, +acc: Big.Big) -> Big.Big:
  match n:
    case 0n:
      acc
    case 1n+p:
      pow10.go(p, Big.mul_small(acc, 1000000000n))

# 10^k
def pow10(+k: Nat) -> Big.Big:
  Big.mul_small(pow10.go(Nat.div(k, 9n), big1()), Nat.pow(10n, Nat.mod(k, 9n)))

def is_odd(+b: Big.Big) -> Bool:
  Bool.not(Big.is_zero(Big.QR.r(Big.div_small(b, 2n))))

def half(+b: Big.Big) -> Big.Big:
  quo(Big.div_small(b, 2n))

def b_ge(+a: Big.Big, +b: Big.Big) -> Bool:
  Bool.not(Cmp.is_lt(Big.cmp(a, b)))

# binary digits of a Nat below 2^48
def nbits.go(fuel: Nat, stop: Bool, +n: Nat, +acc: Nat) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match stop:
        case True{}:
          acc
        case False{}:
          nbits.go(f, Nat.is_eq(Nat.div(n, 2n), 0n), Nat.div(n, 2n), 1n+acc)

def nbits(+n: Nat) -> Nat:
  nbits.go(50n, Nat.is_eq(n, 0n), n, 0n)

def small(+b: Big.Big) -> Bool:
  Nat.is_le(List.length(&2, Nat, Big.limbs(b)), 3n)

# binary digits of a Big: 30 at a time until it fits a Nat
def bitlen.go(fuel: Nat, stop: Bool, +b: Big.Big, +acc: Nat) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match stop:
        case True{}:
          Nat.add(acc, nbits(Big.to_nat(b)))
        case False{}:
          +c = quo(Big.div_small(b, 1073741824n))
          bitlen.go(f, small(c), c, Nat.add(acc, 30n))

def bitlen(+b: Big.Big) -> Nat:
  bitlen.go(400n, small(b), b, 0n)

# bit length: the least l with b < 2^l (acc is 2^l); ten bits a step,
# then one
def blen.one(fuel: Nat, stop: Bool, +b: Big.Big, +acc: Big.Big, +l: Nat) -> Nat:
  match fuel:
    case 0n:
      l
    case 1n+f:
      match stop:
        case True{}:
          l
        case False{}:
          +a2 = Big.mul_small(acc, 2n)
          blen.one(f, Cmp.is_lt(Big.cmp(b, a2)), b, a2, 1n+l)

def blen.ten(fuel: Nat, stop: Bool, +b: Big.Big, +acc: Big.Big, +l: Nat) -> Nat:
  match fuel:
    case 0n:
      l
    case 1n+f:
      match stop:
        case True{}:
          blen.one(11n, Cmp.is_lt(Big.cmp(b, acc)), b, acc, l)
        case False{}:
          +a2 = Big.mul_small(acc, 1024n)
          blen.ten(f, Cmp.is_lt(Big.cmp(b, Big.mul_small(a2, 1024n))), b, a2, Nat.add(10n, l))

def blen(+b: Big.Big) -> Nat:
  blen.ten(Nat.add(2n, Nat.mul(List.length(&2, Nat, Big.limbs(b)), 2n)), Cmp.is_lt(Big.cmp(b, Big.mul_small(big1(), 1024n))), b, big1(), 0n)

# trailing zero bits of a Big above zero
def tz.go(fuel: Nat, stop: Bool, +b: Big.Big, +acc: Nat) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match stop:
        case True{}:
          acc
        case False{}:
          tz.go(f, is_odd(half(b)), half(b), 1n+acc)

def tz(+b: Big.Big) -> Nat:
  tz.go(200n, is_odd(b), b, 0n)

# ---------------------------------------------------------------------
# Rounding an exact rational to a double
# ---------------------------------------------------------------------

# x = num(x) / den(x)
def num(+x: F64) -> Big.Big:
  pick(Big.Big, f_neg(x), f_m(x), bshl(f_e(x), f_m(x)))

def den(+x: F64) -> Big.Big:
  pick(Big.Big, f_neg(x), bshl(f_e(x), Big.of(1n)), Big.of(1n))

# b / 2, as LAWS divides
def half2(+b: Big.Big) -> Big.Big:
  Big.div(b, Big.of(2n))

# b is odd, as LAWS tells it (through Big.mod)
def odd(+b: Big.Big) -> Bool:
  Bool.not(Cmp.is_eq(Big.cmp(Big.mod(b, Big.of(2n)), Big.of(0n))))

# 10^n, by multiplying (LAWS' bpow10, for the small d of fixed notation)
def bpow10(n: Nat) -> Big.Big:
  match n:
    case 0n:
      Big.of(1n)
    case 1n+p:
      Big.mul(bpow10(p), Big.of(10n))

# p/q to the nearest integer, ties to even
def round_int(+p: Big.Big, +q: Big.Big) -> Big.Big:
  +k = Big.div(p, q)
  +r = Big.mod(p, q)
  +c = Big.cmp(Big.add(r, r), q)
  pick(Big.Big, Bool.or(Cmp.is_gt(c), Bool.and(Cmp.is_eq(c), odd(k))), Big.add(k, big1()), k)

# m * 2^(t + b) / 2^a
def strip.mk(+m: Big.Big, +t: Nat, +a: Nat, +b: Nat) -> F64:
  +u = Nat.add(t, b)
  pick(F64, Nat.is_ge(u, a), F64{m, Nat.sub(u, a), False{}}, F64{m, Nat.sub(a, u), True{}})

# halve m while it is even (t halvings so far)
def strip.go(fuel: Nat, stop: Bool, +m: Big.Big, +t: Nat, +a: Nat, +b: Nat) -> F64:
  match fuel:
    case 0n:
      strip.mk(m, t, a, b)
    case 1n+f:
      match stop:
        case True{}:
          strip.mk(m, t, a, b)
        case False{}:
          strip.go(f, odd(half2(m)), half2(m), 1n+t, a, b)

# the double m * 2^b / 2^a (m below 2^54), m's trailing zeros moved to
# the exponent
def finish(z: Bool, +m: Big.Big, +a: Nat, +b: Nat) -> F64:
  match z:
    case True{}:
      zero()
    case False{}:
      strip.go(60n, odd(m), m, 0n, a, b)

# p/q above zero, scaled by 2^a / 2^b to [2^52, 2^53) (or below, when a
# is 1074: the subnormals), rounded to an integer, ties to even. The first
# scale comes from the bit lengths and lands in [2^52, 2^54)
def round.nz(+p: Big.Big, +q: Big.Big) -> F64:
  +x = Nat.add(53n, blen(q))
  +bp = blen(p)
  +a0 = Nat.sub(x, bp)
  +b0 = Nat.sub(bp, x)
  +over = b_ge(Big.mul(p, p2(a0)), Big.mul(p2(53n), Big.mul(q, p2(b0))))
  +a1 = pick(Nat, over, Nat.sub(a0, 1n), a0)
  +b = pick(Nat, Bool.and(over, Nat.is_eq(a0, 0n)), 1n+b0, b0)
  +a = pick(Nat, Nat.is_lt(a1, 1075n), a1, 1074n)
  +m = round_int(Big.mul(p, p2(a)), Big.mul(q, p2(b)))
  finish(Big.is_zero(m), m, a, b)

def round.of(z: Bool, +p: Big.Big, +q: Big.Big) -> F64:
  match z:
    case True{}:
      zero()
    case False{}:
      round.nz(p, q)

# the double nearest p/q, ties to even (zero for q = 0)
def round(+p: Big.Big, +q: Big.Big) -> F64:
  round.of(Bool.or(Big.is_zero(p), Big.is_zero(q)), p, q)

# b / 2^n, by halving
def shr(n: Nat, +b: Big.Big) -> Big.Big:
  match n:
    case 0n:
      b
    case 1n+p:
      shr(p, half(b))

# a Big above zero below 10^12 < 2^53 is a double as it is: its odd part
# times 2^tz, what round(b, 1) gives. This path keeps a closed constant
# like of_nat(100n) cheap in the checker (round's 2^30 steps are not)
def of_big.exact(z: Bool, +b: Big.Big) -> F64:
  match z:
    case True{}:
      zero()
    case False{}:
      F64{shr(tz(b), b), tz(b), False{}}

def of_big.of(few: Bool, +b: Big.Big) -> F64:
  match few:
    case True{}:
      of_big.exact(Big.is_zero(b), b)
    case False{}:
      round(b, big1())

def of_big(+b: Big.Big) -> F64:
  of_big.of(small(b), b)

def of_nat(n: Nat) -> F64:
  of_big(Big.of(n))

def add(+a: F64, +b: F64) -> F64:
  round(Big.add(Big.mul(num(a), den(b)), Big.mul(num(b), den(a))), Big.mul(den(a), den(b)))

def mul(+a: F64, +b: F64) -> F64:
  round(Big.mul(num(a), num(b)), Big.mul(den(a), den(b)))

def div(+a: F64, +b: F64) -> F64:
  round(Big.mul(num(a), den(b)), Big.mul(den(a), num(b)))

# toward zero, as Go's time.Duration(f) conversion
def trunc(+x: F64) -> Nat:
  Big.to_nat(Big.div(num(x), den(x)))

def same(+a: F64, +b: F64) -> Bool:
  Bool.and(Cmp.is_eq(Big.cmp(f_m(a), f_m(b))),
    Bool.and(Nat.is_eq(f_e(a), f_e(b)), Cmp.is_eq(Bool.cmp(f_neg(a), f_neg(b)))))

# ---------------------------------------------------------------------
# Fixed notation: Go's strconv.FormatFloat(x, 'f', d, 64)
# ---------------------------------------------------------------------

def zeros(n: Nat) -> String:
  String.repeat("0", n)

def zpad(+w: Nat, +s: String) -> String:
  zeros(Nat.sub(w, String.length(s))) ++ s

def fixed_text.frac(+d: Nat, +k: Big.Big) -> String:
  Big.show(Big.div(k, bpow10(d))) ++ "." ++ zpad(d, Big.show(Big.mod(k, bpow10(d))))

# K with d decimals: "12.50" for (2, 1250)
def fixed_text(d: Nat, +k: Big.Big) -> String:
  match d:
    case 0n:
      Big.show(k)
    case 1n+p:
      fixed_text.frac(1n+p, k)

def fixed.go(+d: Nat, +x: F64) -> String:
  fixed_text(d, round_int(Big.mul(num(x), bpow10(d)), den(x)))

def fixed(d: Nat, +x: F64) -> String:
  fixed.go(d, x)

# ---------------------------------------------------------------------
# Shortest notation: Go's encoding/json float64 text
# ---------------------------------------------------------------------

# decimal exponents are Nats offset by 400

def ndigits(+b: Big.Big) -> Nat:
  String.length(Big.show(b))

# k + 400 for 10^k <= n/d < 10^(k+1), n/d above zero
def kexp.lt1(+n: Big.Big, +d: Big.Big) -> Nat:
  +z0 = Nat.max(1n, Nat.sub(ndigits(d), ndigits(n)))
  Nat.sub(400n, pick(Nat, b_ge(Big.mul(n, pow10(z0)), d), z0, 1n+z0))

def kexp(+n: Big.Big, +d: Big.Big) -> Nat:
  +i = Big.div(n, d)
  pick(Nat, Big.is_zero(i), kexp.lt1(n, d), Nat.add(399n, ndigits(i)))

# the double D * 10^(j - 400) rounds to
def dval(+dd: Big.Big, +j: Nat) -> F64:
  round(Big.mul(dd, pow10(Nat.sub(j, 400n))), pow10(Nat.sub(400n, j)))

type Cand is Data:
  Cand{ok: Bool, d: Big.Big, j: Nat}

def Cand.ok(+c: Cand) -> Bool:
  Cand{ok, d, j} = c
  ok

def Cand.d(+c: Cand) -> Big.Big:
  Cand{ok, d, j} = c
  d

def Cand.j(+c: Cand) -> Nat:
  Cand{ok, d, j} = c
  j

# the nd-digit decimals around x (k offset by 400), and whether one
# reads back as x (the closer one when both do)
def cand(+x: F64, +k: Nat, +nd: Nat) -> Cand:
  +j = Nat.sub(Nat.add(k, 1n), nd)
  +p = Big.mul(num(x), pow10(Nat.sub(400n, j)))
  +q = Big.mul(den(x), pow10(Nat.sub(j, 400n)))
  +qr = Big.divmod(p, q)
  +lo = quo(qr)
  +hi = Big.add(lo, big1())
  +lo_ok = same(dval(lo, j), x)
  +hi_ok = same(dval(hi, j), x)
  +c = Big.cmp(Big.add(Big.QR.r(qr), Big.QR.r(qr)), q)
  +prefer_lo = Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), Bool.not(is_odd(lo))))
  +use_lo = Bool.and(lo_ok, Bool.or(Bool.not(hi_ok), prefer_lo))
  Cand{Bool.or(lo_ok, hi_ok), pick(Big.Big, use_lo, lo, hi), j}

def short.go(fuel: Nat, stop: Bool, +nd: Nat, +x: F64, +k: Nat, +c: Cand) -> Cand:
  match fuel:
    case 0n:
      c
    case 1n+f:
      match stop:
        case True{}:
          c
        case False{}:
          +c2 = cand(x, k, nd)
          short.go(f, Cand.ok(c2), 1n+nd, x, k, c2)

def count_zeros_r.go(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      pick(Nat, Nat.is_eq(Dec.digit(c), 0n), count_zeros_r.go(rest, 1n+acc), acc)

# trailing '0's of s
def count_zeros_r(+s: String) -> Nat:
  count_zeros_r.go(String.reverse(s), 0n)

# float64(1e-6) = 4722366482869645 * 2^-72
def below_1e_6(+x: F64) -> Bool:
  Cmp.is_lt(Big.cmp(Big.mul(num(x), pow2(72n)), Big.mul(Big.Big{[9645n, 8286n, 3664n, 4722n]}, den(x))))

def from_1e21(+x: F64) -> Bool:
  Bool.not(Cmp.is_gt(Big.cmp(Big.mul(Big.Big{[0n, 0n, 0n, 0n, 0n, 10n]}, den(x)), num(x))))

# digits ds (no trailing zero) times 10^(j - 400), in exponent form
def exp_text(+ds: String, +j: Nat) -> String:
  +l = String.length(ds)
  +ex = Nat.sub(Nat.add(j, l), 1n)
  +frac = pick(String, Nat.is_gt(l, 1n), "." ++ String.drop(ds, 1n), "")
  String.take(ds, 1n) ++ frac ++ "e" ++ pick(String, Nat.is_ge(ex, 400n), "+" ++ Dec.pad(2n, Nat.sub(ex, 400n)), "-" ++ Dec.show(Nat.sub(400n, ex)))

# the same, in plain form
def plain_text(+ds: String, +j: Nat) -> String:
  +l = String.length(ds)
  +f = Nat.sub(400n, j)
  pick(String, Nat.is_ge(j, 400n), ds ++ zeros(Nat.sub(j, 400n)),
    pick(String, Nat.is_gt(l, f), String.take(ds, Nat.sub(l, f)) ++ "." ++ String.drop(ds, Nat.sub(l, f)),
      "0." ++ zeros(Nat.sub(f, l)) ++ ds))

def json.text(+x: F64, +s: String, +j: Nat) -> String:
  +z = count_zeros_r(s)
  +ds = String.take(s, Nat.sub(String.length(s), z))
  pick(String, Bool.or(below_1e_6(x), from_1e21(x)), exp_text(ds, Nat.add(j, z)), plain_text(ds, Nat.add(j, z)))

def json.nz(+x: F64) -> String:
  +c = short.go(17n, False{}, 1n, x, kexp(num(x), den(x)), Cand{False{}, Big.of(0n), 0n})
  json.text(x, Big.show(Cand.d(c)), Cand.j(c))

def json.of(z: Bool, +x: F64) -> String:
  match z:
    case True{}:
      "0"
    case False{}:
      json.nz(x)

def json(+x: F64) -> String:
  json.of(Big.is_zero(f_m(x)), x)

# Vegeta in Bend -- the laws.
#
# Strings are bytes: one character per byte (0..255), as on the wire.
# The shell converts at the edges (arguments arrive as text, output
# leaves as bytes).
#
# The human states them; PROOF.bend proves them; lib/ is whatever makes
# the proofs go through. Every def in this file is part of the statement:
# a helper here only reads or describes values, it never ships. Output
# that must match Go byte for byte is stated as a definition of the text
# (there, the format is the spec); everything else is stated as a
# property that characterizes the code without re-implementing it.
#
# A law is never weakened to make a proof go through. A hypothesis says
# in a comment why the claim is false without it.

import Base
import ./lib/dec.bend as Dec
import ./lib/big.bend as Big
import ./lib/f64.bend as F64
import ./lib/dur.bend as Dur
import ./lib/civil.bend as Civil
import ./lib/b64.bend as B64
import ./lib/csv.bend as Csv
import ./lib/json.bend as Json
import ./lib/hdr.bend as Hdr
import ./lib/hit.bend as Hit
import ./lib/target.bend as Tgt
import ./lib/http.bend as Http
import ./lib/metrics.bend as Met
import ./lib/pacer.bend as Pace
import ./lib/engine.bend as Eng
import ./lib/conn.bend as Conn
import ./lib/text.bend as Text
import ./lib/tab.bend as Tab
import ./lib/report.bend as Rep
import ./lib/flags.bend as Flags

# =====================================================================
# Reading characters and digits
# =====================================================================

# c ? a : b
def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# =====================================================================
# Characters and digits
# =====================================================================

def code(c: Char) -> U32:
  Chr{k} = c
  k

def is_digit(c: Char) -> Bool:
  +k = code(c)
  Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57))

def digit(c: Char) -> Nat:
  U32.to_nat((code(c) - 48 : U32))

def in_range32(+k: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(k, lo), U32.is_le(k, hi))

def is_alnum(+k: U32) -> Bool:
  Bool.or(in_range32(k, 48, 57), Bool.or(in_range32(k, 65, 90), in_range32(k, 97, 122)))

def has_char(s: String, +k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.or(U32.is_eq(code(c), k), has_char(rest, k))

def str1(k: U32) -> String:
  SCon{Chr{k}, SNil{}}

# the byte at index i, or 0 past the end
def byte_at(s: String, i: Nat) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{+c, +rest}:
      match i:
        case 0n:
          code(c)
        case 1n+j:
          byte_at(rest, j)

def is_space(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), Bool.and(U32.is_ge(k, 9), U32.is_le(k, 13)))

def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

def split_cons(+c: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{c, SNil{}}]
    case Con{+p, +rest}:
      Con{SCon{c, p}, rest}

def split_on(+k: U32, s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [""]
    case SCon{+c, +rest}:
      +r = split_on(k, rest)
      pick(List<&2, String>, U32.is_eq(code(c), k), Con{"", r}, split_cons(c, r))

def all_digits.go(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(is_digit(c), all_digits.go(rest))

# a non-empty run of ASCII digits
def all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.and(is_digit(c), all_digits.go(rest))

def digits_value.go(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      digits_value.go(rest, Nat.add(Nat.mul(acc, 10n), digit(c)))

# the number a run of digits denotes, most significant first
def digits_value(s: String) -> Nat:
  digits_value.go(s, 0n)

# digits without a leading zero, or "0" itself
def canonical_nat(+s: String) -> Bool:
  Bool.and(all_digits(s), Bool.or(String.eq(s, "0"), Bool.not(String.starts_with(s, "0"))))

# =====================================================================
# Decimal numbers (lib/dec.bend)
# =====================================================================

# LAW: show writes a canonical decimal...
law dec_show_canonical:
  for +n: Nat
  {canonical_nat(Dec.show(n)) == True{} : Bool}

# LAW: ...that denotes n.
law dec_show_value:
  for +n: Nat
  {digits_value(Dec.show(n)) == n : Nat}

# LAW: read accepts every run of digits (leading zeros too) and gives
# its value...
law dec_read_accepts:
  for +s: String
  for -h: {all_digits(s) == True{} : Bool}
  {Dec.read(s) == Some{digits_value(s)} : Maybe<&2, Nat>}

# LAW: ...and rejects everything else.
law dec_read_rejects:
  for +s: String
  for -h: {all_digits(s) == False{} : Bool}
  {Dec.read(s) == None{} : Maybe<&2, Nat>}

# LAW: pad left-fills with zeros up to width w, never truncating.
law dec_pad:
  for +w: Nat
  for +n: Nat
  {Dec.pad(w, n) == String.repeat("0", Nat.sub(w, String.length(Dec.show(n)))) ++ Dec.show(n) : String}

# =====================================================================
# Big naturals (lib/big.bend): little-endian limbs in base 10000
# =====================================================================

def limbs_val(ls: List<&2, Nat>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{+h, +t}:
      Nat.add(h, Nat.mul(10000n, limbs_val(t)))

def limbs_ok(ls: List<&2, Nat>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Nat.is_lt(h, 10000n), limbs_ok(t))

# the number a Big denotes
def big_val(b: Big.Big) -> Nat:
  Big.Big{ls} = b
  limbs_val(ls)

def last_nonzero(ls: List<&2, Nat>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      match rest:
        case Nil{}:
          Nat.is_gt(h, 0n)
        case Con{+g, +more}:
          last_nonzero(Con{g, more})

# every limb is a base-10000 digit (so no runtime Nat nears 2^48) and the
# top limb is not zero (so equal values are equal Bigs; zero is [])
def big_ok(+b: Big.Big) -> Bool:
  Big.Big{ls} = b
  Bool.and(limbs_ok(ls), last_nonzero(ls))

law big_of:
  for +n: Nat
  {big_val(Big.of(n)) == n : Nat} & {big_ok(Big.of(n)) == True{} : Bool}

law big_add:
  for +a: Big.Big
  for +b: Big.Big
  for -ha: {big_ok(a) == True{} : Bool}
  for -hb: {big_ok(b) == True{} : Bool}
  {big_val(Big.add(a, b)) == Nat.add(big_val(a), big_val(b)) : Nat} & {big_ok(Big.add(a, b)) == True{} : Bool}

law big_mul:
  for +a: Big.Big
  for +b: Big.Big
  for -ha: {big_ok(a) == True{} : Bool}
  for -hb: {big_ok(b) == True{} : Bool}
  {big_val(Big.mul(a, b)) == Nat.mul(big_val(a), big_val(b)) : Nat} & {big_ok(Big.mul(a, b)) == True{} : Bool}

# LAW: division is Euclid's, for a divisor above zero (there is no
# quotient by zero to speak of).
law big_divmod:
  for +a: Big.Big
  for +b: Big.Big
  for -ha: {big_ok(a) == True{} : Bool}
  for -hb: {big_ok(b) == True{} : Bool}
  for -hz: {Nat.is_gt(big_val(b), 0n) == True{} : Bool}
  {Nat.add(Nat.mul(big_val(Big.div(a, b)), big_val(b)), big_val(Big.mod(a, b))) == big_val(a) : Nat}
  & {Nat.is_lt(big_val(Big.mod(a, b)), big_val(b)) == True{} : Bool}
  & {big_ok(Big.div(a, b)) == True{} : Bool}
  & {big_ok(Big.mod(a, b)) == True{} : Bool}

law big_cmp:
  for +a: Big.Big
  for +b: Big.Big
  {Big.cmp(a, b) == Nat.cmp(big_val(a), big_val(b)) : Cmp}

law big_show:
  for +b: Big.Big
  for -h: {big_ok(b) == True{} : Bool}
  {Big.show(b) == Dec.show(big_val(b)) : String}

# =====================================================================
# Doubles (lib/f64.bend): the float64 values Go computes, exactly
# =====================================================================
#
# An F64{m, e, neg} is m * 2^e, or m / 2^e when neg. Everything here is
# stated in Big (base-10000 limbs, fixed to Nat by the big_* laws), so a
# check never has to unfold a huge Nat and tests run at runtime.

def pow2(e: Nat) -> Nat:
  Nat.pow(2n, e)

def pow10(e: Nat) -> Nat:
  Nat.pow(10n, e)

def absdiff(+a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.sub(a, b), Nat.sub(b, a))

def B(+n: Nat) -> Big.Big:
  Big.of(n)

# b * 2^n, by doubling
def bshl(n: Nat, +b: Big.Big) -> Big.Big:
  match n:
    case 0n:
      b
    case 1n+p:
      bshl(p, Big.mul(b, B(2n)))

def b_lt(+a: Big.Big, +b: Big.Big) -> Bool:
  Cmp.is_lt(Big.cmp(a, b))

def b_le(+a: Big.Big, +b: Big.Big) -> Bool:
  Bool.not(Cmp.is_gt(Big.cmp(a, b)))

def b_zero(+a: Big.Big) -> Bool:
  Cmp.is_eq(Big.cmp(a, B(0n)))

def f_m(+x: F64.F64) -> Big.Big:
  F64.F64{m, e, neg} = x
  m

def f_e(+x: F64.F64) -> Nat:
  F64.F64{m, e, neg} = x
  e

def f_neg(+x: F64.F64) -> Bool:
  F64.F64{m, e, neg} = x
  neg

# x = f_num(x) / f_den(x)
def f_num(+x: F64.F64) -> Big.Big:
  pick(Big.Big, f_neg(x), f_m(x), bshl(f_e(x), f_m(x)))

def f_den(+x: F64.F64) -> Big.Big:
  pick(Big.Big, f_neg(x), bshl(f_e(x), B(1n)), B(1n))

def bitlen.go(fuel: Nat, +b: Big.Big, +acc: Nat) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      pick(Nat, b_zero(b), acc, bitlen.go(f, Big.div(b, B(2n)), 1n+acc))

# binary digits of a mantissa (below 2^60 for every double)
def bitlen(+b: Big.Big) -> Nat:
  bitlen.go(60n, b, 0n)

# a canonical double: zero is F64{0, 0, False}; otherwise the mantissa is
# odd (one form per value), under 2^53, and the value within float64's
# range: down to 2^-1074, below 2^1024
def is_double(+x: F64.F64) -> Bool:
  +m = f_m(x)
  +e = f_e(x)
  +l = bitlen(m)
  Bool.and(big_ok(m), pick(Bool, b_zero(m),
    Bool.and(Nat.is_eq(e, 0n), Bool.not(f_neg(x))),
    Bool.and(Bool.not(b_zero(Big.mod(m, B(2n)))), Bool.and(Nat.is_le(l, 53n),
      pick(Bool, f_neg(x), Bool.and(Nat.is_gt(e, 0n), Nat.is_le(e, 1074n)), Nat.is_le(Nat.add(e, l), 1024n))))))

# the exponent of x's 53-bit significand window, plus 1074 (so never
# negative): the gap to the next double up is 2^(w - 1074); for zero it
# is the least subnormal, 2^-1074
def window(+x: F64.F64) -> Nat:
  +l = bitlen(f_m(x))
  pick(Nat, b_zero(f_m(x)), 0n, pick(Nat, f_neg(x), Nat.sub(Nat.add(1074n, l), Nat.add(f_e(x), 53n)), Nat.sub(Nat.add(Nat.add(1074n, l), f_e(x)), 53n)))

# whether x's 53-bit significand is even (ties round to it): its mantissa
# sits strictly inside the window (a spare low zero bit), or x is 0
def sig_even(+x: F64.F64) -> Bool:
  +l = bitlen(f_m(x))
  Bool.or(b_zero(f_m(x)), Bool.and(Nat.is_lt(l, 53n), Bool.or(Bool.not(f_neg(x)), Nat.is_lt(f_e(x), 1074n))))

# p/q rounds to x under IEEE round-to-nearest-even: its distance to x is
# under half the gap to the neighbor on its side, or exactly half and x's
# significand is even. The gap below a power of two (mantissa 1) above
# the subnormals is half the gap above. With t = p/q and x = n/d, and gaps
# 2^(g - 1074): t - x < 2^(g-1075) is p*d*2^1075 < n*q*2^1075 + q*d*2^g.
def rounds_to(+p: Big.Big, +q: Big.Big, +x: F64.F64) -> Bool:
  +n = f_num(x)
  +d = f_den(x)
  +g = window(x)
  +gd = pick(Nat, Bool.and(Cmp.is_eq(Big.cmp(f_m(x), B(1n))), Nat.is_gt(g, 0n)), Nat.sub(g, 1n), g)
  +pd = bshl(1075n, Big.mul(p, d))
  +nq = bshl(1075n, Big.mul(n, q))
  +up = Big.add(nq, bshl(g, Big.mul(q, d)))
  +dn = Big.add(pd, bshl(gd, Big.mul(q, d)))
  +tie_ok = sig_even(x)
  Bool.and(pick(Bool, tie_ok, b_le(pd, up), b_lt(pd, up)),
    Bool.or(b_zero(n), pick(Bool, tie_ok, b_le(nq, dn), b_lt(nq, dn))))

# the values we round stay far below float64's overflow
def in_range(+p: Big.Big, +q: Big.Big) -> Bool:
  Bool.and(Bool.not(b_zero(q)), b_lt(p, bshl(1000n, q)))

# LAW: a Big becomes the double it rounds to
law f64_of_big:
  for +b: Big.Big
  for -h0: {big_ok(b) == True{} : Bool}
  for -h1: {in_range(b, B(1n)) == True{} : Bool}
  {is_double(F64.of_big(b)) == True{} : Bool} & {rounds_to(b, B(1n), F64.of_big(b)) == True{} : Bool}

# LAW: of_nat is of_big
law f64_of_nat:
  for +n: Nat
  {F64.of_nat(n) == F64.of_big(Big.of(n)) : F64.F64}

# LAW: add, mul and div are IEEE's: the exact result, rounded to nearest even
law f64_add:
  for +a: F64.F64
  for +b: F64.F64
  for -ha: {is_double(a) == True{} : Bool}
  for -hb: {is_double(b) == True{} : Bool}
  for -hr: {in_range(Big.add(Big.mul(f_num(a), f_den(b)), Big.mul(f_num(b), f_den(a))), Big.mul(f_den(a), f_den(b))) == True{} : Bool}
  {is_double(F64.add(a, b)) == True{} : Bool}
  & {rounds_to(Big.add(Big.mul(f_num(a), f_den(b)), Big.mul(f_num(b), f_den(a))), Big.mul(f_den(a), f_den(b)), F64.add(a, b)) == True{} : Bool}

law f64_mul:
  for +a: F64.F64
  for +b: F64.F64
  for -ha: {is_double(a) == True{} : Bool}
  for -hb: {is_double(b) == True{} : Bool}
  for -hr: {in_range(Big.mul(f_num(a), f_num(b)), Big.mul(f_den(a), f_den(b))) == True{} : Bool}
  {is_double(F64.mul(a, b)) == True{} : Bool}
  & {rounds_to(Big.mul(f_num(a), f_num(b)), Big.mul(f_den(a), f_den(b)), F64.mul(a, b)) == True{} : Bool}

# LAW: (Go divides by zero only to get Inf or NaN, which Vegeta never prints)
law f64_div:
  for +a: F64.F64
  for +b: F64.F64
  for -ha: {is_double(a) == True{} : Bool}
  for -hb: {is_double(b) == True{} : Bool}
  for -hr: {in_range(Big.mul(f_num(a), f_den(b)), Big.mul(f_den(a), f_num(b))) == True{} : Bool}
  {is_double(F64.div(a, b)) == True{} : Bool}
  & {rounds_to(Big.mul(f_num(a), f_den(b)), Big.mul(f_den(a), f_num(b)), F64.div(a, b)) == True{} : Bool}

# LAW: trunc drops the fraction, as Go's time.Duration(f) does (for the
# values that fit a duration)
law f64_trunc:
  for +x: F64.F64
  for -h0: {is_double(x) == True{} : Bool}
  for -h1: {b_lt(Big.div(f_num(x), f_den(x)), bshl(48n, B(1n))) == True{} : Bool}
  {F64.trunc(x) == big_val(Big.div(f_num(x), f_den(x))) : Nat}

# ---------------------------------------------------------------------
# Comparing distances exactly
# ---------------------------------------------------------------------

# |a - t| compared with |c - t|, without subtracting
def dist_cmp(+a: Big.Big, +c: Big.Big, +t: Big.Big) -> Cmp:
  pick(Cmp, b_le(a, t),
    pick(Cmp, b_le(c, t), Big.cmp(c, a), Big.cmp(Big.add(t, t), Big.add(a, c))),
    pick(Cmp, b_le(c, t), Big.cmp(Big.add(a, c), Big.add(t, t)), Big.cmp(a, c)))

def bpow10(n: Nat) -> Big.Big:
  match n:
    case 0n:
      B(1n)
    case 1n+p:
      Big.mul(bpow10(p), B(10n))

def bdigits.go(s: String, +acc: Big.Big) -> Big.Big:
  match s:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      bdigits.go(rest, Big.add(Big.mul(acc, B(10n)), B(digit(c))))

# the number a run of digits denotes, as a Big
def bdigits(+s: String) -> Big.Big:
  bdigits.go(s, B(0n))

# ---------------------------------------------------------------------
# Fixed notation: Go's %.Nf
# ---------------------------------------------------------------------

def drop_dot(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 46), rest, SCon{c, drop_dot(rest)})

def zpad(+w: Nat, +s: String) -> String:
  String.repeat("0", Nat.sub(w, String.length(s))) ++ s

# K with d decimals: "12.50" for (2, 1250)
def fixed_text(+d: Nat, +k: Big.Big) -> String:
  match d:
    case 0n:
      Big.show(k)
    case 1n+p:
      Big.show(Big.div(k, bpow10(1n+p))) ++ "." ++ zpad(1n+p, Big.show(Big.mod(k, bpow10(1n+p))))

# the K a fixed-notation text denotes (its digits, dot removed)
def fixed_k(+s: String) -> Big.Big:
  bdigits(drop_dot(s))

# LAW: %.Nf writes some K/10^d in canonical fixed notation...
law f64_fixed_text:
  for +d: Nat
  for +x: F64.F64
  for -h: {is_double(x) == True{} : Bool}
  {F64.fixed(d, x) == fixed_text(d, fixed_k(F64.fixed(d, x))) : String}

# no d-decimal is closer to x than kk/10^d; on a tie, kk is even (the
# exact binary value decides ties, as in Go: 0.125 prints as "0.12")
def fixed_nearest(+d: Nat, +x: F64.F64, +kk: Big.Big, +k: Big.Big) -> Bool:
  +t = Big.mul(f_num(x), bpow10(d))
  +c = dist_cmp(Big.mul(kk, f_den(x)), Big.mul(k, f_den(x)), t)
  Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), Bool.or(Cmp.is_eq(Big.cmp(kk, k)), b_zero(Big.mod(kk, B(2n))))))

# LAW: ...and that K is the nearest to x times 10^d, ties to even.
law f64_fixed_nearest:
  for +d: Nat
  for +x: F64.F64
  for +k: Big.Big
  for -h0: {is_double(x) == True{} : Bool}
  for -h1: {big_ok(k) == True{} : Bool}
  {fixed_nearest(d, x, fixed_k(F64.fixed(d, x)), k) == True{} : Bool}

# ---------------------------------------------------------------------
# Shortest notation: Go's encoding/json float64 output
# ---------------------------------------------------------------------

type SS is Data:
  SS{a: String, b: String}

def SS.a(+p: SS) -> String:
  SS{a, b} = p
  a

def SS.b(+p: SS) -> String:
  SS{a, b} = p
  b

# the leading digits of s, and what follows them
def span_digits(s: String) -> SS:
  match s:
    case SNil{}:
      SS{"", ""}
    case SCon{+c, +rest}:
      +r = span_digits(rest)
      pick(SS, is_digit(c), SS{SCon{c, SS.a(r)}, SS.b(r)}, SS{"", SCon{c, rest}})

# a decimal literal: digits, an optional fraction, an optional exponent
type Lit is Data:
  Lit{ip: String, fp: String, eneg: Bool, ex: String, ok: Bool}

def Lit.ip(+l: Lit) -> String:
  Lit{ip, fp, eneg, ex, ok} = l
  ip

def Lit.fp(+l: Lit) -> String:
  Lit{ip, fp, eneg, ex, ok} = l
  fp

def Lit.eneg(+l: Lit) -> Bool:
  Lit{ip, fp, eneg, ex, ok} = l
  eneg

def Lit.ex(+l: Lit) -> String:
  Lit{ip, fp, eneg, ex, ok} = l
  ex

def Lit.ok(+l: Lit) -> Bool:
  Lit{ip, fp, eneg, ex, ok} = l
  ok


# after the digits and fraction: nothing, or e/E, a sign, and digits
def lit_exp(+ip: String, +fp: String, +r: String) -> Lit:
  +e = Bool.or(first_is(r, 101), first_is(r, 69))
  +t = String.drop(r, 1n)
  +neg = first_is(t, 45)
  +sgn = Bool.or(neg, first_is(t, 43))
  +ds = span_digits(pick(String, sgn, String.drop(t, 1n), t))
  pick(Lit, String.is_empty(r), Lit{ip, fp, False{}, "0", True{}},
    Lit{ip, fp, neg, SS.a(ds), Bool.and(e, Bool.and(all_digits(SS.a(ds)), String.is_empty(SS.b(ds))))})

def lit(+s: String) -> Lit:
  +p = span_digits(s)
  +r = SS.b(p)
  +q = span_digits(String.drop(r, 1n))
  +dot = first_is(r, 46)
  +l = pick(Lit, dot, lit_exp(SS.a(p), SS.a(q), SS.b(q)), lit_exp(SS.a(p), "", r))
  Lit{Lit.ip(l), Lit.fp(l), Lit.eneg(l), Lit.ex(l),
    Bool.and(Lit.ok(l), Bool.and(all_digits(SS.a(p)), Bool.or(Bool.not(dot), all_digits(SS.a(q)))))}

# the exact value of a literal, as num / den
def lit_num(+s: String) -> Big.Big:
  +l = lit(s)
  Big.mul(bdigits(Lit.ip(l) ++ Lit.fp(l)), pick(Big.Big, Lit.eneg(l), B(1n), bpow10(digits_value(Lit.ex(l)))))

def lit_den(+s: String) -> Big.Big:
  +l = lit(s)
  Big.mul(bpow10(String.length(Lit.fp(l))), pick(Big.Big, Lit.eneg(l), bpow10(digits_value(Lit.ex(l))), B(1n)))

def strip_zeros_l(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 48), strip_zeros_l(rest), SCon{c, rest})

# significant digits: the mantissa's digits between its first and last nonzero
def sig(+s: String) -> Nat:
  +l = lit(s)
  String.length(strip_zeros_l(String.reverse(strip_zeros_l(Lit.ip(l) ++ Lit.fp(l)))))

# float64(1e-6), exactly: 4722366482869645 * 2^-72, a hair below 10^-6
# (big constants are written as limbs: a closed product would make the
# checker expand a huge Nat)
def below_1e_6(+x: F64.F64) -> Bool:
  b_lt(bshl(72n, f_num(x)), Big.mul(Big.Big{[9645n, 8286n, 3664n, 4722n]}, f_den(x)))

def from_1e21(+x: F64.F64) -> Bool:
  b_le(Big.mul(Big.Big{[0n, 0n, 0n, 0n, 0n, 10n]}, f_den(x)), f_num(x))

# 1e9 as a double: 1953125 * 2^9
def f64_1e9() -> F64.F64:
  F64.F64{Big.Big{[3125n, 195n]}, 9n, False{}}

# Go's layout for a shortest-digits literal of x: plain ("0.25", "120")
# for 0 and 1e-6 <= x < 1e21; otherwise exponent form ("1e-7", "1.5e+21")
# with one leading digit, a sign, and a two-digit exponent that loses its
# leading zero when negative (encoding/json's "e-07" -> "e-7")
def json_layout(+x: F64.F64, +s: String) -> Bool:
  +l = lit(s)
  +fp = Lit.fp(l)
  +frac = pick(String, String.is_empty(fp), "", "." ++ fp)
  +nz = Bool.or(String.is_empty(fp), Bool.not(String.ends_with(fp, "0")))
  +e = digits_value(Lit.ex(l))
  +ed = pick(String, Bool.or(Lit.eneg(l), Nat.is_ge(e, 10n)), Dec.show(e), "0" ++ Dec.show(e))
  +expo = Bool.and(Bool.or(below_1e_6(x), from_1e21(x)), Bool.not(b_zero(f_m(x))))
  Bool.and(Lit.ok(l), Bool.and(nz, pick(Bool, expo,
    Bool.and(Nat.is_eq(String.length(Lit.ip(l)), 1n), Bool.and(Bool.not(String.eq(Lit.ip(l), "0")),
      String.eq(s, Lit.ip(l) ++ frac ++ "e" ++ pick(String, Lit.eneg(l), "-", "+") ++ ed))),
    Bool.and(canonical_nat(Lit.ip(l)), String.eq(s, Lit.ip(l) ++ frac)))))

# LAW: the JSON text of x is a literal in Go's layout...
law f64_json_layout:
  for +x: F64.F64
  for -h: {is_double(x) == True{} : Bool}
  {json_layout(x, F64.json(x)) == True{} : Bool}

# LAW: ...that reads back as x...
law f64_json_rounds:
  for +x: F64.F64
  for -h: {is_double(x) == True{} : Bool}
  {rounds_to(lit_num(F64.json(x)), lit_den(F64.json(x)), x) == True{} : Bool}

# LAW: ...with the fewest significant digits of any literal that does...
law f64_json_shortest:
  for +x: F64.F64
  for +t: String
  for -h0: {is_double(x) == True{} : Bool}
  for -h1: {Lit.ok(lit(t)) == True{} : Bool}
  for -h2: {rounds_to(lit_num(t), lit_den(t), x) == True{} : Bool}
  {Nat.is_le(sig(F64.json(x)), sig(t)) == True{} : Bool}

# LAW: ...and, among those, the closest to x.
law f64_json_closest:
  for +x: F64.F64
  for +t: String
  for -h0: {is_double(x) == True{} : Bool}
  for -h1: {Lit.ok(lit(t)) == True{} : Bool}
  for -h2: {rounds_to(lit_num(t), lit_den(t), x) == True{} : Bool}
  for -h3: {sig(t) == sig(F64.json(x)) : Nat}
  {Cmp.is_gt(dist_cmp(Big.mul(lit_num(F64.json(x)), Big.mul(lit_den(t), f_den(x))),
                      Big.mul(lit_num(t), Big.mul(lit_den(F64.json(x)), f_den(x))),
                      Big.mul(f_num(x), Big.mul(lit_den(F64.json(x)), lit_den(t))))) == False{} : Bool}

# =====================================================================
# Durations (lib/dur.bend): Go's time.Duration text, Vegeta's rounding
# =====================================================================

# "µ" (U+00B5) and "μ" (U+03BC), as the UTF-8 bytes Go writes and reads
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

def trim_zeros_r(+s: String) -> String:
  String.reverse(strip_zeros_l(String.reverse(s)))

# Go's fmtFrac: "." and the digits of r (r < 10^prec) without trailing
# zeros, or nothing when r is 0
def frac_text(+r: Nat, +prec: Nat) -> String:
  pick(String, Nat.is_eq(r, 0n), "", "." ++ trim_zeros_r(Dec.pad(prec, r)))

# Go's time.Duration.String for n >= 0
def go_dur(+n: Nat) -> String:
  +u = Nat.div(n, sec())
  +secs = Dec.show(Nat.mod(u, 60n)) ++ frac_text(Nat.mod(n, sec()), 9n) ++ "s"
  +mins = pick(String, Nat.is_ge(u, 60n), Dec.show(Nat.mod(Nat.div(u, 60n), 60n)) ++ "m", "")
  +hrs = pick(String, Nat.is_ge(u, 3600n), Dec.show(Nat.div(u, 3600n)) ++ "h", "")
  pick(String, Nat.is_eq(n, 0n), "0s",
  pick(String, Nat.is_lt(n, us()), Dec.show(n) ++ "ns",
  pick(String, Nat.is_lt(n, ms()), Dec.show(Nat.div(n, us())) ++ frac_text(Nat.mod(n, us()), 3n) ++ micro() ++ "s",
  pick(String, Nat.is_lt(n, sec()), Dec.show(Nat.div(n, ms())) ++ frac_text(Nat.mod(n, ms()), 6n) ++ "ms",
    hrs ++ mins ++ secs))))

# LAW: show is Go's Duration.String.
law dur_show:
  for +n: Nat
  {Dur.show(n) == go_dur(n) : String}

# LAW: parse reads back what show writes.
law dur_parse_show:
  for +n: Nat
  {Dur.parse(Dur.show(n)) == Some{n} : Maybe<&2, Nat>}

# the units time.ParseDuration knows: a name and a size in ns written as
# factor * base, plus the size as a double (no closed products: the
# checker would expand them into huge unary Nats)
type DUnit is Data:
  DUnit{name: String, factor: Nat, base: Nat, fl: F64.F64}

def dur_units() -> List<&2, DUnit>:
  [DUnit{"ns", 1n, 1n, F64.F64{Big.Big{[1n]}, 0n, False{}}},
   DUnit{"us", 1n, 1000n, F64.F64{Big.Big{[125n]}, 3n, False{}}},
   DUnit{micro() ++ "s", 1n, 1000n, F64.F64{Big.Big{[125n]}, 3n, False{}}},
   DUnit{greek_mu() ++ "s", 1n, 1000n, F64.F64{Big.Big{[125n]}, 3n, False{}}},
   DUnit{"ms", 1n, 1000000n, F64.F64{Big.Big{[5625n, 1n]}, 6n, False{}}},
   DUnit{"s", 1n, 1000000000n, F64.F64{Big.Big{[3125n, 195n]}, 9n, False{}}},
   DUnit{"m", 60n, 1000000000n, F64.F64{Big.Big{[6875n, 2929n]}, 11n, False{}}},
   DUnit{"h", 3600n, 1000000000n, F64.F64{Big.Big{[3125n, 3945n, 4n]}, 13n, False{}}}]

def unit_at(+i: Nat) -> DUnit:
  Maybe.default(&2, DUnit, List.get(&2, DUnit, dur_units(), i), DUnit{"", 0n, 1n, F64.F64{Big.Big{[]}, 0n, False{}}})

def du_name(+u: DUnit) -> String:
  DUnit{n, f, b, x} = u
  n

def unit_name(+i: Nat) -> String:
  du_name(unit_at(i))

def du_factor(+u: DUnit) -> Nat:
  DUnit{n, f, b, x} = u
  f

def unit_factor(+i: Nat) -> Nat:
  du_factor(unit_at(i))

def du_base(+u: DUnit) -> Nat:
  DUnit{n, f, b, x} = u
  b

def unit_base(+i: Nat) -> Nat:
  du_base(unit_at(i))

def du_f64(+u: DUnit) -> F64.F64:
  DUnit{n, f, b, x} = u
  x

def unit_f64(+i: Nat) -> F64.F64:
  du_f64(unit_at(i))

# k of unit i, in ns (k first: a symbolic factor keeps the product folded)
def of_unit(+k: Nat, +i: Nat) -> Nat:
  Nat.mul(Nat.mul(k, unit_factor(i)), unit_base(i))

# LAW: a whole number of a unit parses to its size in ns.
law dur_parse_term:
  for +k: Nat
  for +i: Nat
  for -h: {Nat.is_lt(i, 8n) == True{} : Bool}
  {Dur.parse(Dec.show(k) ++ unit_name(i)) == Some{of_unit(k, i)} : Maybe<&2, Nat>}

# LAW: a fraction of a unit parses as Go computes it, in float64:
# int64(float64(f) * (float64(unit) / float64(10^len(f)))), up to 15 digits.
law dur_parse_frac:
  for +k: Nat
  for +f: String
  for +i: Nat
  for -h0: {Nat.is_lt(i, 8n) == True{} : Bool}
  for -h1: {all_digits(f) == True{} : Bool}
  for -h2: {Nat.is_le(String.length(f), 15n) == True{} : Bool}
  {Dur.parse(Dec.show(k) ++ "." ++ f ++ unit_name(i))
   == Some{Nat.add(of_unit(k, i),
       F64.trunc(F64.mul(F64.of_nat(digits_value(f)), F64.div(unit_f64(i), F64.of_nat(pow10(String.length(f)))))))} : Maybe<&2, Nat>}

# LAW: terms add up: "1h" then "30m" parses as their sum. ("0" alone is a
# duration but not a term: "1m0" is missing its unit.)
law dur_parse_concat:
  for +a: String
  for +b: String
  for +x: Nat
  for +y: Nat
  for -ha: {Dur.parse(a) == Some{x} : Maybe<&2, Nat>}
  for -hb: {Dur.parse(b) == Some{y} : Maybe<&2, Nat>}
  for -h0: {Bool.or(String.eq(a, "0"), String.eq(b, "0")) == False{} : Bool}
  {Dur.parse(a ++ b) == Some{Nat.add(x, y)} : Maybe<&2, Nat>}

def is_unit_name(+u: String) -> Bool:
  Bool.or(Bool.or(Bool.or(String.eq(u, "ns"), String.eq(u, "us")), Bool.or(String.eq(u, micro() ++ "s"), String.eq(u, greek_mu() ++ "s"))),
    Bool.or(Bool.or(String.eq(u, "ms"), String.eq(u, "s")), Bool.or(String.eq(u, "m"), String.eq(u, "h"))))

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

# one or more terms: digits, an optional fraction (a digit on some side
# of the dot), and a known unit
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

# what time.ParseDuration accepts, less negative durations: "0" or terms,
# after an optional "+"; and "-0"
def dur_ok(+s: String) -> Bool:
  +t = pick(String, first_is(s, 43), String.drop(s, 1n), s)
  Bool.or(String.eq(s, "-0"), Bool.or(String.eq(t, "0"), terms_ok(String.length(t), t)))

# LAW: parse accepts exactly that language (Go also reads "-5s" as a
# negative duration; Vegeta's durations are never negative, so the port
# refuses it -- pending the owner's approval)
law dur_parse_domain:
  for +s: String
  {Maybe.is_some(&2, Nat, Dur.parse(s)) == dur_ok(s) : Bool}

# LAW: a "+" changes nothing, and "0" and "-0" are zero
law dur_parse_sign:
  for +s: String
  {Dur.parse("+" ++ s) == pick(Maybe<&2, Nat>, Bool.or(first_is(s, 43), first_is(s, 45)), None{}, Dur.parse(s)) : Maybe<&2, Nat>}
  & {Dur.parse("-0") == Some{0n} : Maybe<&2, Nat>}
  & {Dur.parse("0") == Some{0n} : Maybe<&2, Nat>}

# Go's Duration.Round(f * b) for n >= 0 (halves round up), without the
# closed product f * b: with q = n / b, a = q mod f and c = n mod b, the
# remainder is a*b + c, and it is at least half of f*b exactly when
# 2a >= f, or 2a + 1 = f and 2c >= b
def round_to(+n: Nat, +f: Nat, +b: Nat) -> Nat:
  +q = Nat.div(n, b)
  +a = Nat.mod(q, f)
  +c = Nat.mod(n, b)
  +up = Bool.or(Nat.is_ge(Nat.mul(2n, a), f), Bool.and(Nat.is_eq(Nat.add(Nat.mul(2n, a), 1n), f), Nat.is_ge(Nat.mul(2n, c), b)))
  Nat.mul(pick(Nat, up, Nat.add(Nat.sub(q, a), f), Nat.sub(q, a)), b)

# Vegeta's report rounding: to the minute from an hour up, to the second
# from a minute, to the ms from a second, to the µs from a ms, else as is
def round_go(+n: Nat) -> Nat:
  +secs = Nat.div(n, sec())
  pick(Nat, Nat.is_ge(secs, 3600n), round_to(n, 60n, sec()),
  pick(Nat, Nat.is_ge(secs, 60n), round_to(n, 1n, sec()),
  pick(Nat, Nat.is_ge(secs, 1n), round_to(n, 1n, ms()),
  pick(Nat, Nat.is_ge(n, ms()), round_to(n, 1n, us()), n))))

law dur_round:
  for +n: Nat
  {Dur.round(n) == round_go(n) : Nat}

# =====================================================================
# Calendar time (lib/civil.bend)
# =====================================================================

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

# the Gregorian calendar, counted out: the days from 1970-01-01 to y-m-d
def days_of(+y: Nat, +m: Nat, +d: Nat) -> Nat:
  Nat.add(days_in_years(Nat.sub(y, 1970n)), Nat.add(days_in_months(Nat.sub(m, 1n), y), Nat.sub(d, 1n)))

def valid_date(+y: Nat, +m: Nat, +d: Nat) -> Bool:
  Bool.and(Nat.is_ge(y, 1970n), Bool.and(Bool.and(Nat.is_ge(m, 1n), Nat.is_le(m, 12n)),
    Bool.and(Nat.is_ge(d, 1n), Nat.is_le(d, month_len(y, m)))))

# LAW: the fast day count is the calendar's
law civil_days:
  for +y: Nat
  for +m: Nat
  for +d: Nat
  for -h: {valid_date(y, m, d) == True{} : Bool}
  {Civil.ymd_to_days(y, m, d) == days_of(y, m, d) : Nat}

# LAW: dates and day numbers convert both ways
law civil_ymd_days:
  for +y: Nat
  for +m: Nat
  for +d: Nat
  for -h: {valid_date(y, m, d) == True{} : Bool}
  {Civil.days_to_ymd(Civil.ymd_to_days(y, m, d)) == Civil.Ymd{y, m, d} : Civil.Ymd}

def civil_ymd_ok(+n: Nat, +t: Civil.Ymd) -> Bool:
  Civil.Ymd{y, m, d} = t
  Bool.and(valid_date(y, m, d), Nat.is_eq(Civil.ymd_to_days(y, m, d), n))

def civil_back(+n: Nat) -> Bool:
  civil_ymd_ok(n, Civil.days_to_ymd(n))

# LAW: every day number is some valid date's
law civil_days_ymd:
  for +n: Nat
  {civil_back(n) == True{} : Bool}

def time_sec(+t: Civil.Time) -> Nat:
  Civil.Time{s, ns, off} = t
  s

def time_nsec(+t: Civil.Time) -> Nat:
  Civil.Time{s, ns, off} = t
  ns

def time_off(+t: Civil.Time) -> Nat:
  Civil.Time{s, ns, off} = t
  off

# nanoseconds since the epoch (a theory Nat: past 2^48, never computed at runtime)
def total_ns(+t: Civil.Time) -> Nat:
  Nat.add(Nat.mul(time_sec(t), sec()), time_nsec(t))

# an instant Go prints in RFC3339: nsec below a second, a whole-minute
# offset within a day (RFC3339 has no offset seconds), local time from 1970
def valid_time(+t: Civil.Time) -> Bool:
  +off = time_off(t)
  Bool.and(Nat.is_lt(time_nsec(t), sec()), Bool.and(Nat.is_le(off, 172800n),
    Bool.and(Nat.is_eq(Nat.mod(off, 60n), 0n), Nat.is_ge(Nat.add(time_sec(t), off), 86400n))))

def pad2(+n: Nat) -> String:
  Dec.pad(2n, n)

# Go's time.Time.MarshalJSON text, unquoted: local date and time, the
# fraction without trailing zeros, and Z or the signed offset
def rfc_date(+t: Civil.Ymd) -> String:
  Civil.Ymd{y, m, d} = t
  Dec.pad(4n, y) ++ "-" ++ pad2(m) ++ "-" ++ pad2(d)

def rfc_text(+t: Civil.Time) -> String:
  +off = time_off(t)
  +local = Nat.sub(Nat.add(time_sec(t), off), 86400n)
  +sod = Nat.mod(local, 86400n)
  +zo = absdiff(off, 86400n)
  +zone = pick(String, Nat.is_eq(off, 86400n), "Z",
    pick(String, Nat.is_gt(off, 86400n), "+", "-") ++ pad2(Nat.div(zo, 3600n)) ++ ":" ++ pad2(Nat.mod(Nat.div(zo, 60n), 60n)))
  rfc_date(Civil.days_to_ymd(Nat.div(local, 86400n))) ++ "T" ++ pad2(Nat.div(sod, 3600n)) ++ ":" ++ pad2(Nat.mod(Nat.div(sod, 60n), 60n)) ++ ":" ++ pad2(Nat.mod(sod, 60n))
    ++ frac_text(time_nsec(t), 9n) ++ zone

law civil_rfc3339:
  for +t: Civil.Time
  for -h: {valid_time(t) == True{} : Bool}
  {Civil.rfc3339(t) == rfc_text(t) : String}

law civil_rfc3339_parse:
  for +t: Civil.Time
  for -h: {valid_time(t) == True{} : Bool}
  {Civil.parse_rfc3339(Civil.rfc3339(t)) == Some{t} : Maybe<&2, Civil.Time>}

# LAW: instants compare by their nanosecond count, whatever their zones
law civil_cmp:
  for +a: Civil.Time
  for +b: Civil.Time
  {Civil.cmp(a, b) == Nat.cmp(total_ns(a), total_ns(b)) : Cmp}

# LAW: the CSV timestamp column is the decimal nanosecond count
law civil_unix_nanos:
  for +t: Civil.Time
  for -h: {Nat.is_lt(time_nsec(t), sec()) == True{} : Bool}
  {Civil.unix_nanos(t) == Dec.show(total_ns(t)) : String}

# LAW: adding moves the instant and keeps the zone; subtracting measures
# the distance (zero when b is later)
law civil_add_sub:
  for +t: Civil.Time
  for +u: Civil.Time
  for +n: Nat
  for -h: {Nat.is_lt(time_nsec(t), sec()) == True{} : Bool}
  {total_ns(Civil.add_ns(t, n)) == Nat.add(total_ns(t), n) : Nat}
  & {time_off(Civil.add_ns(t, n)) == time_off(t) : Nat}
  & {Nat.is_lt(time_nsec(Civil.add_ns(t, n)), sec()) == True{} : Bool}
  & {Civil.sub_ns(u, t) == Nat.sub(total_ns(u), total_ns(t)) : Nat}

# =====================================================================
# Bytes
# =====================================================================
#
# Strings on the wire hold one byte per character (0..255).

def ch(k: U32) -> Char:
  Chr{k}


def bytes(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(U32.is_lt(code(c), 256), bytes(rest))

def byte_ok(+k: U32) -> Bool:
  U32.is_lt(k, 256)

# =====================================================================
# Base64 (lib/b64.bend): the standard alphabet, with padding
# =====================================================================

def b64_char(+i: U32) -> String:
  str1(pick(U32, U32.is_lt(i, 26), (65 + i : U32),
       pick(U32, U32.is_lt(i, 52), (71 + i : U32),
       pick(U32, U32.is_lt(i, 62), (i - 4 : U32),
       pick(U32, U32.is_eq(i, 62), 43, 47)))))

# LAW: three bytes become four characters, six bits each, high bits first
law b64_three:
  for +a: U32
  for +b: U32
  for +c: U32
  for -h: {Bool.and(byte_ok(a), Bool.and(byte_ok(b), byte_ok(c))) == True{} : Bool}
  {B64.encode(str1(a) ++ str1(b) ++ str1(c))
   == b64_char((a >> 2n : U32)) ++ b64_char((((a .&. 3) << 4n) .|. (b >> 4n) : U32))
      ++ b64_char((((b .&. 15) << 2n) .|. (c >> 6n) : U32)) ++ b64_char((c .&. 63 : U32)) : String}

# LAW: a final two bytes pad with one "=", a final byte with two
law b64_tail:
  for +a: U32
  for +b: U32
  for -h: {Bool.and(byte_ok(a), byte_ok(b)) == True{} : Bool}
  {B64.encode(str1(a) ++ str1(b))
   == b64_char((a >> 2n : U32)) ++ b64_char((((a .&. 3) << 4n) .|. (b >> 4n) : U32)) ++ b64_char(((b .&. 15) << 2n : U32)) ++ "=" : String}
  & {B64.encode(str1(a)) == b64_char((a >> 2n : U32)) ++ b64_char(((a .&. 3) << 4n : U32)) ++ "==" : String}
  & {B64.encode("") == "" : String}

# LAW: encoding works block by block
law b64_concat:
  for +x: String
  for +y: String
  for -h0: {Nat.mod(String.length(x), 3n) == 0n : Nat}
  for -h1: {Bool.and(bytes(x), bytes(y)) == True{} : Bool}
  {B64.encode(x ++ y) == B64.encode(x) ++ B64.encode(y) : String}

# LAW: decoding inverts encoding...
law b64_decode:
  for +s: String
  for -h: {bytes(s) == True{} : Bool}
  {B64.decode(B64.encode(s)) == Some{s} : Maybe<&2, String>}

# =====================================================================
# CSV (lib/csv.bend): Go's encoding/csv writer, and its reader with
# TrimLeadingSpace
# =====================================================================


# the field starts with a rune Go's unicode.IsSpace accepts: ASCII space,
# \t..\r, U+0085, U+00A0, U+1680, U+2000..U+200A, U+2028, U+2029, U+202F,
# U+205F, U+3000 (as UTF-8 bytes)
def first_space(+s: String) -> Bool:
  +b0 = byte_at(s, 0n)
  +b1 = byte_at(s, 1n)
  +b2 = byte_at(s, 2n)
  Bool.and(Bool.not(String.is_empty(s)),
  Bool.or(Bool.or(is_space(b0), Bool.and(U32.is_eq(b0, 194), Bool.or(U32.is_eq(b1, 133), U32.is_eq(b1, 160)))),
  Bool.or(Bool.and(U32.is_eq(b0, 225), Bool.and(U32.is_eq(b1, 154), U32.is_eq(b2, 128))),
  Bool.or(Bool.and(U32.is_eq(b0, 226), Bool.or(Bool.and(U32.is_eq(b1, 128), Bool.or(in_range32(b2, 128, 138), Bool.or(in_range32(b2, 168, 169), U32.is_eq(b2, 175)))),
                                               Bool.and(U32.is_eq(b1, 129), U32.is_eq(b2, 159)))),
    Bool.and(U32.is_eq(b0, 227), Bool.and(U32.is_eq(b1, 128), U32.is_eq(b2, 128)))))))

# Go's fieldNeedsQuotes (the delimiter is a comma)
def needs_quotes(+s: String) -> Bool:
  pick(Bool, String.is_empty(s), False{},
    Bool.or(String.eq(s, "\\."), Bool.or(first_space(s),
      Bool.or(Bool.or(has_char(s, 44), has_char(s, 34)), Bool.or(has_char(s, 13), has_char(s, 10))))))

def double_quotes(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 34), "\"\"", SCon{c, SNil{}}) ++ double_quotes(rest)

# LAW: a field is written bare, or quoted with its quotes doubled
law csv_field:
  for +s: String
  {Csv.field(s) == pick(String, needs_quotes(s), "\"" ++ double_quotes(s) ++ "\"", s) : String}

def join_fields(fs: List<&2, String>) -> String:
  match fs:
    case Nil{}:
      ""
    case Con{+f, +rest}:
      match rest:
        case Nil{}:
          Csv.field(f)
        case Con{+g, +more}:
          Csv.field(f) ++ "," ++ join_fields(Con{g, more})

# LAW: a row is its fields, comma-separated, ending in a newline
law csv_row:
  for +fs: List<&2, String>
  {Csv.row(fs) == join_fields(fs) ++ "\n" : String}

def all_bytes(fs: List<&2, String>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, +rest}:
      Bool.and(bytes(f), all_bytes(rest))

def no_crlf_pair(fs: List<&2, String>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case Con{+f, +rest}:
      Bool.and(Bool.not(String.contains(f, "\r\n")), no_crlf_pair(rest))

# a row the reader can give back: some field; not the lone empty field
# (its line is blank, and Go's reader skips blank lines); and no "\r\n"
# inside a field (Go's reader turns it into "\n")
def representable(+fs: List<&2, String>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{+f, +rest}:
      Bool.and(Bool.and(all_bytes(Con{f, rest}), no_crlf_pair(Con{f, rest})),
        Bool.or(Bool.not(String.is_empty(f)), Bool.not(List.is_empty(&2, String, rest))))

# LAW: every representable row reads back, whatever follows it
law csv_parse_row:
  for +fs: List<&2, String>
  for +rest: String
  for -h: {representable(fs) == True{} : Bool}
  {Csv.parse_row(Csv.row(fs) ++ rest) == Some{(fs, rest)} : Maybe<&1, List<&2, String> & String>}

# =====================================================================
# JSON strings (lib/json.bend): easyjson's escaping (HTML-safe: <, > and &
# are escaped); the JSON report uses encoding/json's, which since Go 1.22
# also writes \b and \f short
# =====================================================================

def hexd(+n: U32) -> String:
  str1(pick(U32, U32.is_lt(n, 10), (48 + n : U32), (87 + n : U32)))



def cont(+s: String, +i: Nat) -> Bool:
  Bool.and(Nat.is_lt(i, String.length(s)), in_range32(byte_at(s, i), 128, 191))

# the length of the valid UTF-8 sequence s starts with, or 0 (Go's
# utf8.DecodeRuneInString: no overlongs, no surrogates, nothing past U+10FFFF)
def utf8_len(+s: String) -> Nat:
  +b0 = byte_at(s, 0n)
  +b1 = byte_at(s, 1n)
  +c1 = cont(s, 1n)
  +c2 = cont(s, 2n)
  +c3 = cont(s, 3n)
  pick(Nat, U32.is_lt(b0, 128), 1n,
  pick(Nat, Bool.and(in_range32(b0, 194, 223), c1), 2n,
  pick(Nat, Bool.and(U32.is_eq(b0, 224), Bool.and(in_range32(b1, 160, 191), c2)), 3n,
  pick(Nat, Bool.and(Bool.or(in_range32(b0, 225, 236), in_range32(b0, 238, 239)), Bool.and(c1, c2)), 3n,
  pick(Nat, Bool.and(U32.is_eq(b0, 237), Bool.and(in_range32(b1, 128, 159), c2)), 3n,
  pick(Nat, Bool.and(U32.is_eq(b0, 240), Bool.and(in_range32(b1, 144, 191), Bool.and(c2, c3))), 4n,
  pick(Nat, Bool.and(in_range32(b0, 241, 243), Bool.and(c1, Bool.and(c2, c3))), 4n,
  pick(Nat, Bool.and(U32.is_eq(b0, 244), Bool.and(in_range32(b1, 128, 143), Bool.and(c2, c3))), 4n, 0n))))))))

# one ASCII byte, escaped
def jesc_ascii(+k: U32) -> String:
  pick(String, U32.is_eq(k, 34), "\\\"",
  pick(String, U32.is_eq(k, 92), "\\\\",
  pick(String, U32.is_eq(k, 10), "\\n",
  pick(String, U32.is_eq(k, 13), "\\r",
  pick(String, U32.is_eq(k, 9), "\\t",
  pick(String, Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))),
    "\\u00" ++ hexd((k >> 4n : U32)) ++ hexd((k .&. 15 : U32)),
    str1(k)))))))

# one step of escaping: the text for what s starts with...
def jesc_head(+s: String) -> String:
  +n = utf8_len(s)
  +b0 = byte_at(s, 0n)
  pick(String, String.is_empty(s), "",
  pick(String, Nat.is_eq(n, 0n), "\\ufffd",
  pick(String, Nat.is_eq(n, 1n), jesc_ascii(b0),
  pick(String, Bool.and(Nat.is_eq(n, 3n), Bool.and(U32.is_eq(b0, 226), Bool.and(U32.is_eq(byte_at(s, 1n), 128),
      Bool.or(U32.is_eq(byte_at(s, 2n), 168), U32.is_eq(byte_at(s, 2n), 169))))),
    "\\u202" ++ pick(String, U32.is_eq(byte_at(s, 2n), 168), "8", "9"),
    String.take(s, n)))))

# ...and how many bytes that step takes (a stray byte is one)
def jesc_len(+s: String) -> Nat:
  Nat.max(1n, utf8_len(s))

def jesc.go(+fuel: Nat, +s: String) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      jesc_head(s) ++ jesc.go(f, String.drop(s, jesc_len(s)))

def jesc(+s: String) -> String:
  jesc.go(String.length(s), s)

# LAW: a JSON string is its bytes escaped, in quotes: ASCII by the table,
# valid UTF-8 as is (but U+2028 and U+2029 escaped), a stray byte as �
law json_str:
  for +s: String
  {Json.str(s) == "\"" ++ jesc(s) ++ "\"" : String}

def utf8_ok.go(+fuel: Nat, +s: String) -> Bool:
  match fuel:
    case 0n:
      True{}
    case 1n+f:
      +n = utf8_len(s)
      Bool.or(String.is_empty(s), Bool.and(Bool.not(Nat.is_eq(n, 0n)), utf8_ok.go(f, String.drop(s, n))))

# valid UTF-8 (a stray byte comes back as U+FFFD, so it cannot round-trip)
def utf8_ok(+s: String) -> Bool:
  Bool.and(bytes(s), utf8_ok.go(String.length(s), s))

# LAW: the reader gives back every valid UTF-8 string, whatever follows it
law json_read_str:
  for +s: String
  for +rest: String
  for -h: {utf8_ok(s) == True{} : Bool}
  {Json.read_str(Json.str(s) ++ rest) == Some{(s, rest)} : Maybe<&1, String & String>}

# =====================================================================
# Headers
# =====================================================================


# a byte allowed in a header name (an RFC 7230 token character)
def token_byte(+k: U32) -> Bool:
  Bool.or(is_alnum(k), has_char("!#$%&'*+-.^_`|~", k))

def all_token(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(token_byte(code(c)), all_token(rest))

def token(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), all_token(s))

def canon.go(s: String, +up: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      +k = code(c)
      +k2 = pick(U32, Bool.and(up, in_range32(k, 97, 122)), (k - 32 : U32),
             pick(U32, Bool.and(Bool.not(up), in_range32(k, 65, 90)), (k + 32 : U32), k))
      SCon{Chr{k2}, canon.go(rest, U32.is_eq(k, 45))}

# Go's CanonicalMIMEHeaderKey: "content-type" is "Content-Type"; a name
# with a byte outside the token set stays as it is
def canon(+s: String) -> String:
  pick(String, token(s), canon.go(s, True{}), s)

def hdr_key(+h: Hdr.Header) -> String:
  Hdr.Header{k, vs} = h
  k

def hdr_vals(+h: Hdr.Header) -> List<&2, String>:
  Hdr.Header{k, vs} = h
  vs

def trim_ows_l(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, Bool.or(U32.is_eq(code(c), 32), U32.is_eq(code(c), 9)), trim_ows_l(rest), SCon{c, rest})

# trims spaces and tabs at both ends (textproto.TrimString)
def trim_ows(+s: String) -> String:
  String.reverse(trim_ows_l(String.reverse(trim_ows_l(s))))

def nl_to_space(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, Bool.or(U32.is_eq(code(c), 10), U32.is_eq(code(c), 13)), " ", SCon{c, SNil{}}) ++ nl_to_space(rest)

def insert_hdr(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [h]
    case Con{+x, +rest}:
      pick(List<&2, Hdr.Header>, String.is_lt(hdr_key(h), hdr_key(x)), Con{h, Con{x, rest}}, Con{x, insert_hdr(h, rest)})

# headers ordered by name (Go writes http.Header in sorted key order)
def sort_hdrs(hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      insert_hdr(h, sort_hdrs(rest))

def hdr_lines(+k: String, vs: List<&2, String>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{+v, +rest}:
      k ++ ": " ++ trim_ows(nl_to_space(v)) ++ "\r\n" ++ hdr_lines(k, rest)

def hdrs_text(hs: List<&2, Hdr.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      pick(String, token(hdr_key(h)), hdr_lines(hdr_key(h), hdr_vals(h)), "") ++ hdrs_text(rest)

# Go's headerBytes: http.Header.Write, then a blank line; nothing for nil
def hdr_block(+m: Maybe<&2, List<&2, Hdr.Header>>) -> String:
  match m:
    case None{}:
      ""
    case Some{hs}:
      hdrs_text(sort_hdrs(hs)) ++ "\r\n"

# =====================================================================
# Results (lib/hit.bend): Go's vegeta.Result, in CSV and in JSON
# =====================================================================

def body_or_empty(+m: Maybe<&2, String>) -> String:
  Maybe.default(&2, String, m, "")

# the CSV record Go's NewCSVEncoder writes
def csv_text(+h: Hit.Hit) -> String:
  Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Csv.row([Civil.unix_nanos(ts), Dec.show(code), Dec.show(lat), Dec.show(bout), Dec.show(bin), err,
    B64.encode(body_or_empty(body)), attack, Dec.show(seq), method, url, B64.encode(hdr_block(hdrs))])

# the strings joined with sep between them
def join_str(+sep: String, xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      match rest:
        case Nil{}:
          x
        case Con{+y, +more}:
          x ++ sep ++ join_str(sep, Con{y, more})

def json_strs(vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{+v, +rest}:
      Con{Json.str(v), json_strs(rest)}

def json_list(vs: List<&2, String>) -> String:
  join_str(",", json_strs(vs))

def json_hdr_items(hs: List<&2, Hdr.Header>) -> List<&2, String>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      Con{Json.str(hdr_key(h)) ++ ":[" ++ json_list(hdr_vals(h)) ++ "]", json_hdr_items(rest)}

def json_hdrs(hs: List<&2, Hdr.Header>) -> String:
  join_str(",", json_hdr_items(hs))

def json_body(+m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "null"
    case Some{x}:
      "\"" ++ B64.encode(x) ++ "\""

def json_hdrs_of(+m: Maybe<&2, List<&2, Hdr.Header>>) -> String:
  match m:
    case None{}:
      "null"
    case Some{hs}:
      "{" ++ json_hdrs(sort_hdrs(hs)) ++ "}"

# the JSON line Go's NewJSONEncoder writes; header names sorted (Go's map
# order is random, so any order matches Go; sorted makes it a function)
def json_text(+h: Hit.Hit) -> String:
  Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  "{\"attack\":" ++ Json.str(attack) ++ ",\"seq\":" ++ Dec.show(seq) ++ ",\"code\":" ++ Dec.show(code)
    ++ ",\"timestamp\":\"" ++ Civil.rfc3339(ts) ++ "\",\"latency\":" ++ Dec.show(lat)
    ++ ",\"bytes_out\":" ++ Dec.show(bout) ++ ",\"bytes_in\":" ++ Dec.show(bin)
    ++ ",\"error\":" ++ Json.str(err) ++ ",\"body\":" ++ json_body(body)
    ++ ",\"method\":" ++ Json.str(method) ++ ",\"url\":" ++ Json.str(url)
    ++ ",\"headers\":" ++ json_hdrs_of(hdrs) ++ "}\n"

law hit_to_csv:
  for +h: Hit.Hit
  {Hit.to_csv(h) == csv_text(h) : String}

law hit_to_json:
  for +h: Hit.Hit
  {Hit.to_json(h) == json_text(h) : String}

def all_utf8(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(utf8_ok(x), all_utf8(rest))

def no_crlf(+s: String) -> Bool:
  Bool.not(Bool.or(has_char(s, 10), has_char(s, 13)))

def no_ctl(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.or(U32.is_eq(code(c), 9), Bool.and(U32.is_ge(code(c), 32), Bool.not(U32.is_eq(code(c), 127)))), no_ctl(rest))

# a header value that survives http.Header.Write and textproto's reader:
# bytes, trimmed, and no control byte but tab (textproto rejects them)
def clean_val(+v: String) -> Bool:
  Bool.and(bytes(v), Bool.and(no_ctl(v), String.eq(trim_ows(v), v)))

def all_clean(vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case Con{+v, +rest}:
      Bool.and(clean_val(v), all_clean(rest))

# names strictly ascending (so sorted and distinct)
def hdrs_ascending(hs: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      match rest:
        case Nil{}:
          True{}
        case Con{+g, +more}:
          Bool.and(String.is_lt(hdr_key(h), hdr_key(g)), hdrs_ascending(Con{g, more}))

def hdrs_csv_ok(hs: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      Bool.and(Bool.and(token(hdr_key(h)), String.eq(canon(hdr_key(h)), hdr_key(h))),
        Bool.and(Bool.not(List.is_empty(&2, String, hdr_vals(h))), Bool.and(all_clean(hdr_vals(h)), hdrs_csv_ok(rest))))

def hdrs_json_ok(hs: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      Bool.and(utf8_ok(hdr_key(h)), Bool.and(all_utf8(hdr_vals(h)), hdrs_json_ok(rest)))

def maybe_hdrs_ok(+csv: Bool, +m: Maybe<&2, List<&2, Hdr.Header>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{hs}:
      Bool.and(hdrs_ascending(hs), pick(Bool, csv, hdrs_csv_ok(hs), hdrs_json_ok(hs)))

# a result CSV carries unchanged: CSV has no zone (Go reads times back in
# UTC here), no nil body (Go reads "" back as an empty body), and header
# names that Go's reader would canonicalize are already canonical
def csv_ok(+h: Hit.Hit) -> Bool:
  Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Bool.and(Nat.is_lt(code, 65536n), Bool.and(Nat.is_lt(time_nsec(ts), sec()), Bool.and(Nat.is_eq(time_off(ts), 86400n),
  Bool.and(Maybe.is_some(&2, String, body), Bool.and(bytes(body_or_empty(body)),
  Bool.and(all_bytes([attack, err, method, url]), maybe_hdrs_ok(True{}, hdrs)))))))

# a result JSON carries unchanged: an RFC3339 time, UTF-8 text
def json_ok(+h: Hit.Hit) -> Bool:
  Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Bool.and(Nat.is_lt(code, 65536n), Bool.and(valid_time(ts), Bool.and(bytes(body_or_empty(body)),
  Bool.and(all_utf8([attack, err, method, url]), maybe_hdrs_ok(False{}, hdrs)))))

law hit_of_csv:
  for +h: Hit.Hit
  for +rest: String
  for -ok: {csv_ok(h) == True{} : Bool}
  {Hit.of_csv(Hit.to_csv(h) ++ rest) == Some{(h, rest)} : Maybe<&1, Hit.Hit & String>}

law hit_of_json:
  for +h: Hit.Hit
  for +rest: String
  for -ok: {json_ok(h) == True{} : Bool}
  {Hit.of_json(Hit.to_json(h) ++ rest) == Some{(h, rest)} : Maybe<&1, Hit.Hit & String>}

# LAW: decode tells the formats apart by their first character
law hit_decode:
  for +h: Hit.Hit
  for +rest: String
  {Hit.decode(Hit.to_json(h) ++ rest) == Hit.of_json(Hit.to_json(h) ++ rest) : Maybe<&1, Hit.Hit & String>}
  & {Hit.decode(Hit.to_csv(h) ++ rest) == Hit.of_csv(Hit.to_csv(h) ++ rest) : Maybe<&1, Hit.Hit & String>}

def csv_stream(hs: List<&2, Hit.Hit>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      Hit.to_csv(h) ++ csv_stream(rest)

def json_stream(hs: List<&2, Hit.Hit>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      Hit.to_json(h) ++ json_stream(rest)

def all_csv_ok(hs: List<&2, Hit.Hit>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      Bool.and(csv_ok(h), all_csv_ok(rest))

def all_json_ok(hs: List<&2, Hit.Hit>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      Bool.and(json_ok(h), all_json_ok(rest))

# LAW: a whole results stream reads back, in either format
law hit_stream_csv:
  for +hs: List<&2, Hit.Hit>
  for -ok: {all_csv_ok(hs) == True{} : Bool}
  {Hit.decode_all(csv_stream(hs)) == Some{hs} : Maybe<&2, List<&2, Hit.Hit>>}

law hit_stream_json:
  for +hs: List<&2, Hit.Hit>
  for -ok: {all_json_ok(hs) == True{} : Bool}
  {Hit.decode_all(json_stream(hs)) == Some{hs} : Maybe<&2, List<&2, Hit.Hit>>}

# =====================================================================
# Targets (lib/target.bend): URLs and the http targets format
# =====================================================================

def is_host_char(+k: U32) -> Bool:
  Bool.or(is_alnum(k), Bool.or(U32.is_eq(k, 46), Bool.or(U32.is_eq(k, 45), U32.is_eq(k, 95))))

def all_host(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(is_host_char(code(c)), all_host(rest))

# printable, no space, no '#'
def all_path(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.and(in_range32(code(c), 33, 126), Bool.not(U32.is_eq(code(c), 35))), all_path(rest))

def port_ok(+p: Maybe<&2, Nat>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{n}:
      Bool.and(Nat.is_ge(n, 1n), Nat.is_le(n, 65535n))

def port_text(+p: Maybe<&2, Nat>) -> String:
  match p:
    case None{}:
      ""
    case Some{n}:
      ":" ++ Dec.show(n)

def is_hex(+k: U32) -> Bool:
  Bool.or(in_range32(k, 48, 57), Bool.or(in_range32(k, 65, 70), in_range32(k, 97, 102)))

# every % starts a %XX escape (Go's parser rejects the URL otherwise)
def pct_ok.go(+fuel: Nat, +s: String) -> Bool:
  match fuel:
    case 0n:
      True{}
    case 1n+f:
      Bool.and(Bool.or(Bool.not(first_is(s, 37)), Bool.and(is_hex(byte_at(s, 1n)), is_hex(byte_at(s, 2n)))), pct_ok.go(f, String.drop(s, 1n)))

def pct_ok(+s: String) -> Bool:
  pct_ok.go(String.length(s), s)

# an http URL: a host of name characters, a port as written (None: none,
# so 80), and a path from "/" of printable bytes with well-formed escapes
def url_ok(+u: Tgt.Url) -> Bool:
  Tgt.Url{scheme, host, port, path} = u
  Bool.and(String.eq(scheme, "http"), Bool.and(Bool.and(Bool.not(String.is_empty(host)), all_host(host)),
    Bool.and(port_ok(port), Bool.and(String.starts_with(path, "/"), Bool.and(all_path(path), pct_ok(path))))))

# an http URL as written
def url_text(+u: Tgt.Url) -> String:
  Tgt.Url{scheme, host, port, path} = u
  "http://" ++ host ++ port_text(port) ++ path

law url_parse:
  for +u: Tgt.Url
  for -h: {url_ok(u) == True{} : Bool}
  {Tgt.parse_url(url_text(u)) == Done{u} : Result<&2, &2, String, Tgt.Url>}

# LAW: a URL without a path means "/", and https is refused by name
law url_parse_edges:
  for +host: String
  for +rest: String
  for -h: {Bool.and(Bool.not(String.is_empty(host)), all_host(host)) == True{} : Bool}
  {Tgt.parse_url("http://" ++ host) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  & {Tgt.parse_url("https://" ++ rest) == Fail{"https is not supported"} : Result<&2, &2, String, Tgt.Url>}

def is_upper(+k: U32) -> Bool:
  in_range32(k, 65, 90)

def all_upper(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(is_upper(code(c)), all_upper(rest))

def method_ok(+m: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(m)), all_upper(m))

def printable(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(in_range32(code(c), 32, 126), printable(rest))

def tgt_vals_ok(vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case Con{+v, +rest}:
      Bool.and(Bool.and(printable(v), Bool.not(String.is_empty(v))), Bool.and(String.eq(trim_ows(v), v), tgt_vals_ok(rest)))

# a header name a targets file can hold: a token (so no colon or space,
# and it cannot start a comment or a body or read as a method line)
def tgt_key_ok(+k: String) -> Bool:
  Bool.and(token(k), Bool.not(Bool.or(String.starts_with(k, "#"), String.starts_with(k, "@"))))

# a header line a targets file can hold: trimmed non-empty name without a
# colon that does not start a comment or a body; trimmed non-empty values
def tgt_hdrs_ok(hs: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      Bool.and(tgt_key_ok(hdr_key(h)),
      Bool.and(Bool.not(List.is_empty(&2, String, hdr_vals(h))), Bool.and(tgt_vals_ok(hdr_vals(h)), tgt_hdrs_ok(rest))))


def tgt_url(+t: Tgt.Target) -> String:
  Tgt.Target{m, u, hs, b} = t
  u

def tgt_method(+t: Tgt.Target) -> String:
  Tgt.Target{m, u, hs, b} = t
  m

def tgt_hdrs(+t: Tgt.Target) -> List<&2, Hdr.Header>:
  Tgt.Target{m, u, hs, b} = t
  hs

def tgt_body(+t: Tgt.Target) -> Maybe<&2, String>:
  Tgt.Target{m, u, hs, b} = t
  b

def body_path_ok(+b: Maybe<&2, String>) -> Bool:
  match b:
    case None{}:
      True{}
    case Some{p}:
      Bool.and(Bool.and(printable(p), Bool.not(String.is_empty(p))), String.eq(trim_ows(p), p))

def has_key(+k: String, hs: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Con{+h, +rest}:
      Bool.or(String.eq(hdr_key(h), k), has_key(k, rest))

def hdr_names_distinct(hs: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      Bool.and(Bool.not(has_key(hdr_key(h), rest)), hdr_names_distinct(rest))

def url_str_of(+s: String, r: Result<&2, &2, String, Tgt.Url>) -> Bool:
  match r:
    case Done{+u}:
      Bool.and(url_ok(u), String.eq(url_text(u), s))
    case Fail{e}:
      False{}

# a URL string that is an http URL as written
def url_str_ok(+s: String) -> Bool:
  url_str_of(s, Tgt.parse_url(s))

# a target a targets file can hold: an upper-case method, an http URL,
# distinct header names (Go groups a name's lines), a body path
def target_ok(+t: Tgt.Target) -> Bool:
  +u = tgt_url(t)
  Bool.and(method_ok(tgt_method(t)), Bool.and(url_str_ok(u),
    Bool.and(Bool.and(tgt_hdrs_ok(tgt_hdrs(t)), hdr_names_distinct(tgt_hdrs(t))), body_path_ok(tgt_body(t)))))

def targets_ok(ts: List<&2, Tgt.Target>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{+t, +rest}:
      Bool.and(target_ok(t), targets_ok(rest))

def tgt_val_lines(+k: String, vs: List<&2, String>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{+v, +rest}:
      k ++ ": " ++ v ++ "\n" ++ tgt_val_lines(k, rest)

def tgt_hdr_lines(hs: List<&2, Hdr.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      tgt_val_lines(hdr_key(h), hdr_vals(h)) ++ tgt_hdr_lines(rest)

def body_line(+b: Maybe<&2, String>) -> String:
  match b:
    case None{}:
      ""
    case Some{p}:
      "@" ++ p ++ "\n"

# one target in the http format
def target_text(+t: Tgt.Target) -> String:
  tgt_method(t) ++ " " ++ tgt_url(t) ++ "\n" ++ tgt_hdr_lines(tgt_hdrs(t)) ++ body_line(tgt_body(t))

# targets, a blank line between them
def targets_text(ts: List<&2, Tgt.Target>) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{+t, +rest}:
      match rest:
        case Nil{}:
          target_text(t)
        case Con{+u, +more}:
          target_text(t) ++ "\n" ++ targets_text(Con{u, more})

law targets_parse:
  for +ts: List<&2, Tgt.Target>
  for -h: {targets_ok(ts) == True{} : Bool}
  {Tgt.parse_all(targets_text(ts)) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}

# LAW: parsing streams: two files back to back are their targets back to back
law targets_concat:
  for +a: List<&2, Tgt.Target>
  for +b: List<&2, Tgt.Target>
  for -h: {targets_ok(List.append(&2, Tgt.Target, a, b)) == True{} : Bool}
  {Tgt.parse_all(targets_text(a) ++ "\n" ++ targets_text(b)) == Done{List.append(&2, Tgt.Target, a, b)} : Result<&2, &2, String, List<&2, Tgt.Target>>}

# a line before a target that changes nothing: blank, or a comment
def noise_ok(+l: String) -> Bool:
  Bool.and(Bool.and(printable(l), Bool.not(has_char(l, 10))), Bool.or(String.is_empty(trim_ows(l)), String.starts_with(trim_ows(l), "#")))

def all_noise(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{+l, +rest}:
      Bool.and(noise_ok(l), all_noise(rest))

def noise_text(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{+l, +rest}:
      l ++ "\n" ++ noise_text(rest)

# LAW: blank lines and comments before a target never change the parse
law targets_noise:
  for +ns: List<&2, String>
  for +ts: List<&2, Tgt.Target>
  for -h0: {targets_ok(ts) == True{} : Bool}
  for -h1: {all_noise(ns) == True{} : Bool}
  {Tgt.parse_all(noise_text(ns) ++ targets_text(ts)) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}

def drop_upper(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, is_upper(code(c)), drop_upper(rest), SCon{c, rest})

# upper-case letters then a space: Go's startsWithHTTPMethod
def starts_method(+l: String) -> Bool:
  +w = String.take(l, Nat.sub(String.length(l), String.length(drop_upper(l))))
  Bool.and(Bool.not(String.is_empty(w)), String.starts_with(drop_upper(l), " "))

# LAW: Go's errors, word for word: a line with one token is a bad target,
# a first token that is not upper-case letters is a bad method, and a
# header line without a colon is a bad header
law targets_errors:
  for +tok: String
  for +m: String
  for +rest: String
  for +t: Tgt.Target
  for +l: String
  for -h0: {Bool.and(Bool.and(printable(tok), Bool.not(has_char(tok, 32))), Bool.and(Bool.not(String.is_empty(tok)), Bool.not(String.starts_with(tok, "#")))) == True{} : Bool}
  for -h1: {Bool.and(Bool.and(printable(m), Bool.not(has_char(m, 32))), Bool.and(Bool.not(String.is_empty(m)), Bool.not(all_upper(m)))) == True{} : Bool}
  for -h2: {Bool.and(Bool.and(printable(rest), Bool.not(String.is_empty(trim_ows(rest)))), Bool.not(String.starts_with(m, "#"))) == True{} : Bool}
  for -h3: {Bool.and(target_ok(t), Maybe.is_none(&2, String, tgt_body(t))) == True{} : Bool}
  for -h4: {Bool.and(Bool.and(printable(l), Bool.not(has_char(l, 58))), Bool.and(Bool.not(String.is_empty(trim_ows(l))),
     Bool.not(Bool.or(Bool.or(String.starts_with(trim_ows(l), "#"), String.starts_with(trim_ows(l), "@")), starts_method(trim_ows(l)))))) == True{} : Bool}
  {Tgt.parse_all(tok ++ "\n") == Fail{"bad target: " ++ tok} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  & {Tgt.parse_all(m ++ " " ++ rest ++ "\n") == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  & {Tgt.parse_all(target_text(t) ++ l ++ "\n") == Fail{"bad header: " ++ trim_ows(l)} : Result<&2, &2, String, List<&2, Tgt.Target>>}

# append a header's values to the same name in a list, or add it at the end
def add_hdr(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [h]
    case Con{+g, +rest}:
      pick(List<&2, Hdr.Header>, String.eq(hdr_key(g), hdr_key(h)),
        Con{Hdr.Header{hdr_key(g), List.append(&2, String, hdr_vals(g), hdr_vals(h))}, rest}, Con{g, add_hdr(h, rest)})

def add_hdrs(hs: List<&2, Hdr.Header>, base: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      base
    case Con{+h, +rest}:
      add_hdrs(rest, add_hdr(h, base))

# LAW: the attacked target: -header values first, the target's lines after
# them (Go appends to the same name), and -body unless the target has @file
law target_apply:
  for +t: Tgt.Target
  for +hs: List<&2, Hdr.Header>
  for +body: Maybe<&2, String>
  {Tgt.apply(t, hs, body) == Tgt.Target{tgt_method(t), tgt_url(t), add_hdrs(tgt_hdrs(t), hs), Maybe.or(&2, String, tgt_body(t), body)} : Tgt.Target}

# =====================================================================
# HTTP/1.1 (lib/http.bend)
# =====================================================================

def r_code(+r: Http.Resp) -> Nat:
  Http.Resp{c, st, hs, b, k} = r
  c

def r_status(+r: Http.Resp) -> String:
  Http.Resp{c, st, hs, b, k} = r
  st

def r_hdrs(+r: Http.Resp) -> List<&2, Hdr.Header>:
  Http.Resp{c, st, hs, b, k} = r
  hs

def r_body(+r: Http.Resp) -> String:
  Http.Resp{c, st, hs, b, k} = r
  b

def r_keep(+r: Http.Resp) -> Bool:
  Http.Resp{c, st, hs, b, k} = r
  k

def hdr_get(+k: String, hs: List<&2, Hdr.Header>) -> Maybe<&2, List<&2, String>>:
  match hs:
    case Nil{}:
      None{}
    case Con{+h, +rest}:
      pick(Maybe<&2, List<&2, String>>, String.eq(hdr_key(h), k), Some{hdr_vals(h)}, hdr_get(k, rest))

def any_ci(+v: String, vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case Con{+x, +rest}:
      Bool.or(String.eq(String.to_lower(x), String.to_lower(v)), any_ci(v, rest))

def some_has_ci(+v: String, +m: Maybe<&2, List<&2, String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{vs}:
      any_ci(v, vs)

# header k has a value equal to v, ignoring case
def hdr_is(+k: String, +v: String, +hs: List<&2, Hdr.Header>) -> Bool:
  some_has_ci(v, hdr_get(k, hs))

# the response carries "Connection: close"
def says_close(+hs: List<&2, Hdr.Header>) -> Bool:
  hdr_is("Connection", "close", hs)

def resp_hdr_lines(hs: List<&2, Hdr.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      hdr_lines(hdr_key(h), hdr_vals(h)) ++ resp_hdr_lines(rest)

# a status line and headers, as a server writes them
def render_head(+r: Http.Resp) -> String:
  "HTTP/1.1 " ++ r_status(r) ++ "\r\n" ++ resp_hdr_lines(r_hdrs(r)) ++ "\r\n"

def hdrs_resp_ok(hs: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      Bool.and(Bool.and(token(hdr_key(h)), String.eq(canon(hdr_key(h)), hdr_key(h))),
      Bool.and(Bool.and(Bool.not(has_key(hdr_key(h), rest)), Bool.not(List.is_empty(&2, String, hdr_vals(h)))),
      Bool.and(all_clean(hdr_vals(h)), hdrs_resp_ok(rest))))

# a final response Go would hand back as parsed: a status "<code> <reason>",
# canonical distinct header names with clean values, keep-alive exactly
# when the server did not say "Connection: close", and a body read whole
def resp_base_ok(+r: Http.Resp) -> Bool:
  +c = r_code(r)
  Bool.and(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)),
  Bool.and(String.starts_with(r_status(r), Dec.show(c) ++ " "),
  Bool.and(Bool.and(printable(r_status(r)), hdrs_resp_ok(r_hdrs(r))),
  Bool.and(bytes(r_body(r)),
    Bool.not(Bool.or(has_key("Transfer-Encoding", r_hdrs(r)), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))))))))

def same_bool(+a: Bool, +b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

def one_val(+v: String, +m: Maybe<&2, List<&2, String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{vs}:
      match vs:
        case Nil{}:
          False{}
        case Con{+x, +rest}:
          Bool.and(String.eq(x, v), List.is_empty(&2, String, rest))

# header k has exactly the one value v
def vals_are(+k: String, +v: String, +hs: List<&2, Hdr.Header>) -> Bool:
  one_val(v, hdr_get(k, hs))

# framed by Content-Length (one value: the body's length)
def resp_cl_ok(+r: Http.Resp) -> Bool:
  Bool.and(resp_base_ok(r), Bool.and(vals_are("Content-Length", Dec.show(String.length(r_body(r))), r_hdrs(r)),
    same_bool(r_keep(r), Bool.not(says_close(r_hdrs(r))))))

# framed by chunks: no Content-Length (Go drops Transfer-Encoding from the headers)
def resp_te_ok(+r: Http.Resp) -> Bool:
  Bool.and(resp_base_ok(r), Bool.and(Bool.not(has_key("Content-Length", r_hdrs(r))),
    same_bool(r_keep(r), Bool.not(says_close(r_hdrs(r))))))

# framed by the close: no length at all, so never kept
def resp_eof_ok(+r: Http.Resp) -> Bool:
  Bool.and(resp_base_ok(r), Bool.and(Bool.not(has_key("Content-Length", r_hdrs(r))), Bool.not(r_keep(r))))

def render_cl(+r: Http.Resp) -> String:
  render_head(r) ++ r_body(r)

def hex_digits(+fuel: Nat, +n: Nat) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      pick(String, Nat.is_eq(n, 0n), "",
        hex_digits(f, Nat.div(n, 16n)) ++ hexd(U32.from_nat(Nat.mod(n, 16n))))

# n in lower-case hex ("0" for 0)
def hex(+n: Nat) -> String:
  pick(String, Nat.is_eq(n, 0n), "0", hex_digits(n, n))

def chunk(+d: String) -> String:
  hex(String.length(d)) ++ "\r\n" ++ d ++ "\r\n"

# the body cut into chunks of the given sizes (zeros skipped: a zero chunk
# ends the body), the rest in one last chunk
def chunks(sizes: List<&2, Nat>, +body: String) -> String:
  match sizes:
    case Nil{}:
      pick(String, String.is_empty(body), "", chunk(body))
    case Con{+n, +rest}:
      +skip = Bool.or(Nat.is_eq(n, 0n), String.is_empty(body))
      pick(String, skip, "", chunk(String.take(body, n))) ++ chunks(rest, pick(String, skip, body, String.drop(body, n)))

def render_chunked(+r: Http.Resp, +sizes: List<&2, Nat>) -> String:
  "HTTP/1.1 " ++ r_status(r) ++ "\r\n" ++ resp_hdr_lines(r_hdrs(r)) ++ "Transfer-Encoding: chunked\r\n\r\n"
    ++ chunks(sizes, r_body(r)) ++ "0\r\n\r\n"

def parse_of(+mb: Maybe<&2, Nat>, +head: Bool, +s: String) -> Maybe<&1, Result<&1, &1, String, Http.Resp & String>>:
  Http.done(Http.feed(Http.start(mb, head), s))

def parse_eof(+mb: Maybe<&2, Nat>, +head: Bool, +s: String) -> Maybe<&1, Result<&1, &1, String, Http.Resp & String>>:
  Http.done(Http.eof(Http.feed(Http.start(mb, head), s)))

# LAW: a Content-Length response parses back, and what follows it is left
# for the next response on the connection
law http_cl:
  for +r: Http.Resp
  for +rest: String
  for -h: {resp_cl_ok(r) == True{} : Bool}
  {parse_of(None{}, False{}, render_cl(r) ++ rest) == Some{Done{(r, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

# LAW: so does a chunked response, however it is chunked
law http_chunked:
  for +r: Http.Resp
  for +sizes: List<&2, Nat>
  for +rest: String
  for -h: {resp_te_ok(r) == True{} : Bool}
  {parse_of(None{}, False{}, render_chunked(r, sizes) ++ rest) == Some{Done{(r, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

# LAW: a response without a length ends at the close, and not before
law http_until_close:
  for +r: Http.Resp
  for -h: {resp_eof_ok(r) == True{} : Bool}
  {parse_eof(None{}, False{}, render_head(r) ++ r_body(r)) == Some{Done{(r, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  & {parse_of(None{}, False{}, render_head(r) ++ r_body(r)) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

# LAW: the parser never answers before the response is complete
law http_waits:
  for +r: Http.Resp
  for +k: Nat
  for -h0: {resp_cl_ok(r) == True{} : Bool}
  for -h1: {Nat.is_lt(k, String.length(render_cl(r))) == True{} : Bool}
  {parse_of(None{}, False{}, String.take(render_cl(r), k)) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

law http_waits_chunked:
  for +r: Http.Resp
  for +sizes: List<&2, Nat>
  for +k: Nat
  for -h0: {resp_te_ok(r) == True{} : Bool}
  for -h1: {Nat.is_lt(k, String.length(render_chunked(r, sizes))) == True{} : Bool}
  {parse_of(None{}, False{}, String.take(render_chunked(r, sizes), k)) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

# LAW: the parser reads bytes, not reads: feeding in two pieces is feeding once
law http_split:
  for +p: Http.Parse
  for +a: String
  for +b: String
  {Http.feed(Http.feed(p, a), b) == Http.feed(p, a ++ b) : Http.Parse}

# LAW: after the peer closes, the parser always decides: an answer or an error
law http_eof_decides:
  for +p: Http.Parse
  {Maybe.is_some(&1, Result<&1, &1, String, Http.Resp & String>, Http.done(Http.eof(p))) == True{} : Bool}

def with_body(+r: Http.Resp, +b: String) -> Http.Resp:
  Http.Resp{r_code(r), r_status(r), r_hdrs(r), b, r_keep(r)}

# LAW: -max-body keeps the first m bytes (and Go counts only those)
law http_max_body:
  for +r: Http.Resp
  for +m: Nat
  for +rest: String
  for -h: {resp_cl_ok(r) == True{} : Bool}
  {parse_of(Some{m}, False{}, render_cl(r) ++ rest) == Some{Done{(with_body(r, String.take(r_body(r), m)), rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

# LAW: mid-body, the body read so far is at hand (a timeout keeps it)
law http_partial:
  for +r: Http.Resp
  for +k: Nat
  for +m: Maybe<&2, Nat>
  for -h0: {resp_cl_ok(r) == True{} : Bool}
  for -h1: {Nat.is_lt(k, String.length(r_body(r))) == True{} : Bool}
  {Http.partial(Http.feed(Http.start(m, False{}), render_head(r) ++ String.take(r_body(r), k)))
   == String.take(String.take(r_body(r), k), Maybe.default(&2, Nat, m, k)) : String}

# LAW: informational responses (1xx but 101) are skipped
law http_interim:
  for +c: Nat
  for +reason: String
  for +r: Http.Resp
  for +rest: String
  for -h0: {Bool.and(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n))) == True{} : Bool}
  for -h1: {Bool.and(printable(reason), resp_cl_ok(r)) == True{} : Bool}
  {parse_of(None{}, False{}, "HTTP/1.1 " ++ Dec.show(c) ++ " " ++ reason ++ "\r\n\r\n" ++ render_cl(r) ++ rest)
   == parse_of(None{}, False{}, render_cl(r) ++ rest) : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

# a response that has no body whatever its headers say: to HEAD, or 204/304
def resp_nobody_ok(+head: Bool, +r: Http.Resp) -> Bool:
  +c = r_code(r)
  Bool.and(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)),
  Bool.and(Bool.or(head, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))),
  Bool.and(Bool.and(String.starts_with(r_status(r), Dec.show(c) ++ " "), printable(r_status(r))),
  Bool.and(hdrs_resp_ok(r_hdrs(r)), Bool.and(Bool.not(has_key("Transfer-Encoding", r_hdrs(r))),
  Bool.and(String.is_empty(r_body(r)), same_bool(r_keep(r), Bool.not(says_close(r_hdrs(r))))))))))

law http_no_body:
  for +head: Bool
  for +r: Http.Resp
  for +rest: String
  for -h: {resp_nobody_ok(head, r) == True{} : Bool}
  {parse_of(None{}, head, render_head(r) ++ rest) == Some{Done{(r, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

def pad_vals(vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{+v, +rest}:
      Con{" " ++ v ++ "\t", pad_vals(rest)}

def lower_names(hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      Con{Hdr.Header{String.to_lower(hdr_key(h)), pad_vals(hdr_vals(h))}, lower_names(rest)}

# LAW: names in any case come back canonical, and values come back trimmed
law http_lenient:
  for +r: Http.Resp
  for +rest: String
  for -h: {resp_cl_ok(r) == True{} : Bool}
  {parse_of(None{}, False{}, render_cl(Http.Resp{r_code(r), r_status(r), lower_names(r_hdrs(r)), r_body(r), r_keep(r)}) ++ rest)
   == Some{Done{(r, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

# LAW: an HTTP/1.0 response is kept only when it says "Connection: keep-alive"
law http_10:
  for +r: Http.Resp
  for +rest: String
  for -h: {resp_base_ok(r) == True{} : Bool}
  {parse_of(None{}, False{}, "HTTP/1.0 " ++ String.drop(render_cl(r), 9n) ++ rest)
   == parse_of(None{}, False{}, "HTTP/1.1 " ++ String.drop(render_cl(Http.Resp{r_code(r), r_status(r), r_hdrs(r), r_body(r),
        hdr_is("Connection", "keep-alive", r_hdrs(r))}), 9n) ++ rest) : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}

def is_fail(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      match r:
        case Fail{e}:
          True{}
        case Done{v}:
          False{}

# LAW: anything that does not start like a response is an error, at once
law http_garbage:
  for +s: String
  for -h: {Bool.and(Nat.is_ge(String.length(s), 7n), Bool.not(String.starts_with(s, "HTTP/1."))) == True{} : Bool}
  {is_fail(parse_of(None{}, False{}, s)) == True{} : Bool}

# ---------------------------------------------------------------------
# Requests
# ---------------------------------------------------------------------

def url_host(+u: Tgt.Url) -> String:
  Tgt.Url{sc, host, port, path} = u
  host ++ port_text(port)

def url_path(+u: Tgt.Url) -> String:
  Tgt.Url{sc, host, port, path} = u
  path

def hexu(+n: U32) -> String:
  str1(pick(U32, U32.is_lt(n, 10), (48 + n : U32), (55 + n : U32)))

def hex_val(+k: U32) -> U32:
  pick(U32, in_range32(k, 48, 57), (k - 48 : U32), pick(U32, in_range32(k, 65, 70), (k - 55 : U32), (k - 87 : U32)))

def unreserved(+k: U32) -> Bool:
  Bool.or(is_alnum(k), has_char("-._~", k))

# Go's validEncoded: a path Go sends as written
def valid_encoded(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.or(unreserved(code(c)), has_char("!$&'()*+,;=:@/%[]", code(c))), valid_encoded(rest))

# %XX sequences decoded (url_ok guarantees they are well formed)
def unescape.go(+fuel: Nat, +s: String) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      +pct = Bool.and(first_is(s, 37), Nat.is_ge(String.length(s), 3n))
      +v = pick(U32, pct, ((hex_val(byte_at(s, 1n)) * 16 + hex_val(byte_at(s, 2n))) .&. 255 : U32), byte_at(s, 0n))
      pick(String, String.is_empty(s), "", str1(v) ++ unescape.go(f, String.drop(s, pick(Nat, pct, 3n, 1n))))

def unescape(+s: String) -> String:
  unescape.go(String.length(s), s)

# Go's escape(s, encodePath): all but unreserved and $&+,/:;=@ as %XX
def escape_path(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      +k = code(c)
      pick(String, Bool.or(unreserved(k), has_char("$&+,/:;=@", k)), str1(k), "%" ++ hexu((k >> 4n : U32)) ++ hexu((k .&. 15 : U32)))
        ++ escape_path(rest)

def before_q(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 63), "", SCon{c, before_q(rest)})

# the request target Go writes: the path as EscapedPath gives it (as
# written when validly encoded, else re-escaped), then the raw query
def request_uri(+path: String) -> String:
  +p = before_q(path)
  +q = String.drop(path, String.length(p))
  pick(String, valid_encoded(p), p, escape_path(unescape(p))) ++ q

def hdr_get_ci(+k: String, hs: List<&2, Hdr.Header>) -> Maybe<&2, List<&2, String>>:
  match hs:
    case Nil{}:
      None{}
    case Con{+h, +rest}:
      pick(Maybe<&2, List<&2, String>>, String.eq(canon(hdr_key(h)), k), Some{hdr_vals(h)}, hdr_get_ci(k, rest))

def first_of(+d: String, +m: Maybe<&2, List<&2, String>>) -> String:
  match m:
    case None{}:
      d
    case Some{vs}:
      Maybe.default(&2, String, List.head(&2, String, vs), d)

def first_val(+k: String, +hs: List<&2, Hdr.Header>, +d: String) -> String:
  first_of(d, hdr_get_ci(k, hs))

def drop_ci(+k: String, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      +r = drop_ci(k, rest)
      pick(List<&2, Hdr.Header>, String.eq(canon(hdr_key(h)), k), r, Con{h, r})

def needs_length(+m: String, +body: String) -> Bool:
  Bool.or(Bool.not(String.is_empty(body)), Bool.or(String.eq(m, "POST"), Bool.or(String.eq(m, "PUT"), String.eq(m, "PATCH"))))

# the request text Go's transport writes for a target (Go's Accept-Encoding
# is left out on purpose: bodies arrive as the server sent them): the
# request line; Host and User-Agent, from the target's headers when it
# sets them; the length; every other header sorted by name, less the
# framing headers Go never takes from the user; and Connection: close last
def wire_request(+t: Tgt.Target, +u: Tgt.Url, +body: String, +seq: Nat, +name: String, +ka: Bool) -> String:
  +hs = tgt_hdrs(t)
  +extra = pick(List<&2, Hdr.Header>, String.is_empty(name), [], [Hdr.Header{"X-Vegeta-Attack", [name]}])
  +rest = drop_ci("Host", drop_ci("User-Agent", drop_ci("Content-Length", drop_ci("Transfer-Encoding", drop_ci("Trailer",
            add_hdrs(Con{Hdr.Header{"X-Vegeta-Seq", [Dec.show(seq)]}, extra}, hs))))))
  tgt_method(t) ++ " " ++ request_uri(url_path(u)) ++ " HTTP/1.1\r\n"
    ++ "Host: " ++ first_val("Host", hs, url_host(u)) ++ "\r\n"
    ++ "User-Agent: " ++ first_val("User-Agent", hs, "Go-http-client/1.1") ++ "\r\n"
    ++ pick(String, needs_length(tgt_method(t), body), "Content-Length: " ++ Dec.show(String.length(body)) ++ "\r\n", "")
    ++ hdrs_text(sort_hdrs(rest))
    ++ pick(String, ka, "", "Connection: close\r\n") ++ "\r\n" ++ body

law http_request:
  for +t: Tgt.Target
  for +u: Tgt.Url
  for +body: String
  for +seq: Nat
  for +name: String
  for +ka: Bool
  {Http.request(t, u, body, seq, name, ka) == wire_request(t, u, body, seq, name, ka) : String}

# =====================================================================
# Metrics (lib/metrics.bend)
# =====================================================================
#
# Every field of a report is a function of the multiset of results; the
# laws say which function. Two more say an accumulator can be built in
# any shape (add one by one, merge halves in parallel) and any order.

def s_requests(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_requests

def s_success(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_success

def s_codes(+s: Met.Summary) -> List<&2, Sigma<&2, &2, Nat, _ => Nat>>:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_codes

def s_errors(+s: Met.Summary) -> List<&2, String>:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_errors

def s_lat_total(+s: Met.Summary) -> Big.Big:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_lat_total

def s_lat_mean(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_lat_mean

def s_lat_min(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_lat_min

def s_lat_max(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_lat_max

def s_p50(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_p50

def s_p90(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_p90

def s_p95(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_p95

def s_p99(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_p99

def s_bytes_in(+s: Met.Summary) -> Big.Big:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_bytes_in

def s_bytes_out(+s: Met.Summary) -> Big.Big:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_bytes_out

def s_in_mean(+s: Met.Summary) -> F64.F64:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_in_mean

def s_out_mean(+s: Met.Summary) -> F64.F64:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_out_mean

def s_rate(+s: Met.Summary) -> F64.F64:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_rate

def s_throughput(+s: Met.Summary) -> F64.F64:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_throughput

def s_ratio(+s: Met.Summary) -> F64.F64:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_ratio

def s_earliest(+s: Met.Summary) -> Maybe<&2, Civil.Time>:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_earliest

def s_latest(+s: Met.Summary) -> Maybe<&2, Civil.Time>:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_latest

def s_end(+s: Met.Summary) -> Maybe<&2, Civil.Time>:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_end

def s_duration(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_duration

def s_wait(+s: Met.Summary) -> Nat:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_wait

def s_buckets(+s: Met.Summary) -> List<&2, Nat>:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_buckets

def s_hist(+s: Met.Summary) -> List<&2, Nat>:
  Met.Summary{f_requests, f_success, f_codes, f_errors, f_lat_total, f_lat_mean, f_lat_min, f_lat_max, f_p50, f_p90, f_p95, f_p99, f_bytes_in, f_bytes_out, f_in_mean, f_out_mean, f_rate, f_throughput, f_ratio, f_earliest, f_latest, f_end, f_duration, f_wait, f_buckets, f_hist} = s
  f_hist

def h_code(+h: Hit.Hit) -> Nat:
  Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs} = h
  c

def h_ts(+h: Hit.Hit) -> Civil.Time:
  Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs} = h
  t

def h_lat(+h: Hit.Hit) -> Nat:
  Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs} = h
  l

def h_out(+h: Hit.Hit) -> Nat:
  Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs} = h
  bo

def h_in(+h: Hit.Hit) -> Nat:
  Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs} = h
  bi

def h_err(+h: Hit.Hit) -> String:
  Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs} = h
  e

def acc_all(hs: List<&2, Hit.Hit>, +a: Met.Acc) -> Met.Acc:
  match hs:
    case Nil{}:
      a
    case Con{+h, +rest}:
      acc_all(rest, Met.add(a, h))

# the report of some results, adding them one by one
def summary(+bs: List<&2, Nat>, +hs: List<&2, Hit.Hit>) -> Met.Summary:
  Met.close(acc_all(hs, Met.empty(bs)))

# the ways to build an accumulator
type Build is Data:
  BEmpty{}
  BAdd{b: Build, h: Hit.Hit}
  BMerge{l: Build, r: Build}

def build(+bs: List<&2, Nat>, t: Build) -> Met.Acc:
  match t:
    case BEmpty{}:
      Met.empty(bs)
    case BAdd{b, h}:
      Met.add(build(bs, b), h)
    case BMerge{l, r}:
      Met.merge(build(bs, l), build(bs, r))

def leaves(t: Build) -> List<&2, Hit.Hit>:
  match t:
    case BEmpty{}:
      []
    case BAdd{b, h}:
      List.append(&2, Hit.Hit, leaves(b), [h])
    case BMerge{l, r}:
      List.append(&2, Hit.Hit, leaves(l), leaves(r))

# LAW: however an accumulator is built -- one by one, merged in halves on
# every core, in any tree -- its report is the report of its results
law met_build:
  for +bs: List<&2, Nat>
  for +t: Build
  {Met.close(build(bs, t)) == summary(bs, leaves(t)) : Met.Summary}

def is_ok(+c: Nat) -> Bool:
  Bool.and(Nat.is_ge(c, 200n), Nat.is_lt(c, 400n))

def n_ok(hs: List<&2, Hit.Hit>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{+h, +rest}:
      Nat.add(pick(Nat, is_ok(h_code(h)), 1n, 0n), n_ok(rest))

def n_code(+c: Nat, hs: List<&2, Hit.Hit>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{+h, +rest}:
      Nat.add(pick(Nat, Nat.is_eq(h_code(h), c), 1n, 0n), n_code(c, rest))

def sum_lat(hs: List<&2, Hit.Hit>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{+h, +rest}:
      Nat.add(h_lat(h), sum_lat(rest))

def sum_in(hs: List<&2, Hit.Hit>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{+h, +rest}:
      Nat.add(h_in(h), sum_in(rest))

def sum_out(hs: List<&2, Hit.Hit>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{+h, +rest}:
      Nat.add(h_out(h), sum_out(rest))

def lats(hs: List<&2, Hit.Hit>) -> List<&2, Nat>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      Con{h_lat(h), lats(rest)}

def min_of.go(xs: List<&2, Nat>, +d: Nat) -> Nat:
  match xs:
    case Nil{}:
      d
    case Con{+x, +rest}:
      min_of.go(rest, Nat.min(d, x))

def min_of(+d: Nat, +xs: List<&2, Nat>) -> Nat:
  min_of.go(xs, d)

def max_of.go(xs: List<&2, Nat>, +d: Nat) -> Nat:
  match xs:
    case Nil{}:
      d
    case Con{+x, +rest}:
      max_of.go(rest, Nat.max(d, x))

def max_of(+d: Nat, +xs: List<&2, Nat>) -> Nat:
  max_of.go(xs, d)

def starts(hs: List<&2, Hit.Hit>) -> List<&2, Nat>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      Con{total_ns(h_ts(h)), starts(rest)}

def ends(hs: List<&2, Hit.Hit>) -> List<&2, Nat>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      Con{Nat.add(total_ns(h_ts(h)), h_lat(h)), ends(rest)}

def head_or(+d: Nat, +xs: List<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, List.head(&2, Nat, xs), d)

def n_less(+p: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, +rest}:
      Nat.add(pick(Nat, Nat.is_lt(x, p), 1n, 0n), n_less(p, rest))

def n_upto(+p: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, +rest}:
      Nat.add(pick(Nat, Nat.is_le(x, p), 1n, 0n), n_upto(p, rest))

# nearest rank: the ceil(q% of n)-th smallest, counted from 0
def rank(+q: Nat, +n: Nat) -> Nat:
  Nat.sub(Nat.div(Nat.add(Nat.mul(q, n), 99n), 100n), 1n)

# p is the rank-k latency: fewer than k+1 are below it, more than k up to it
def is_rank(+p: Nat, +k: Nat, +xs: List<&2, Nat>) -> Bool:
  Bool.and(Nat.is_le(n_less(p, xs), k), Nat.is_lt(k, n_upto(p, xs)))

def lookup_code(+c: Nat, cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{+p, +rest}:
      (k, v) = p
      pick(Nat, Nat.is_eq(k, c), v, lookup_code(c, rest))

def codes_after(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>, +k: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+p, +rest}:
      (j, v) = p
      Bool.and(Bool.and(Nat.is_lt(k, j), Nat.is_gt(v, 0n)), codes_after(rest, j))

def codes_ascending(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+p, +rest}:
      (k, v) = p
      Bool.and(Nat.is_gt(v, 0n), codes_after(rest, k))

def strs_ascending(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match rest:
        case Nil{}:
          True{}
        case Con{+y, +more}:
          Bool.and(String.is_lt(x, y), strs_ascending(Con{y, more}))

def has_str(+x: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, +rest}:
      Bool.or(String.eq(x, y), has_str(x, rest))

def has_err(+e: String, hs: List<&2, Hit.Hit>) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Con{+h, +rest}:
      Bool.or(String.eq(h_err(h), e), has_err(e, rest))

def utc_at(+ns: Nat) -> Civil.Time:
  Civil.Time{Nat.div(ns, sec()), Nat.mod(ns, sec()), 86400n}

# LAW: counts: requests, successes (2xx and 3xx), and each status code
law met_counts:
  for +bs: List<&2, Nat>
  for +hs: List<&2, Hit.Hit>
  for +c: Nat
  {s_requests(summary(bs, hs)) == List.length(&2, Hit.Hit, hs) : Nat}
  & {s_success(summary(bs, hs)) == n_ok(hs) : Nat}
  & {lookup_code(c, s_codes(summary(bs, hs))) == n_code(c, hs) : Nat}
  & {codes_ascending(s_codes(summary(bs, hs))) == True{} : Bool}

# LAW: the error set: each distinct non-empty error once, sorted (Go keeps
# first-seen order, which depends on which result arrived first)
law met_errors:
  for +bs: List<&2, Nat>
  for +hs: List<&2, Hit.Hit>
  for +e: String
  {strs_ascending(s_errors(summary(bs, hs))) == True{} : Bool}
  & {has_str(e, s_errors(summary(bs, hs))) == Bool.and(Bool.not(String.is_empty(e)), has_err(e, hs)) : Bool}

# LAW: totals, exact at any size
law met_totals:
  for +bs: List<&2, Nat>
  for +hs: List<&2, Hit.Hit>
  {big_val(s_lat_total(summary(bs, hs))) == sum_lat(hs) : Nat}
  & {big_val(s_bytes_in(summary(bs, hs))) == sum_in(hs) : Nat}
  & {big_val(s_bytes_out(summary(bs, hs))) == sum_out(hs) : Nat}
  & {Bool.and(big_ok(s_lat_total(summary(bs, hs))), Bool.and(big_ok(s_bytes_in(summary(bs, hs))), big_ok(s_bytes_out(summary(bs, hs))))) == True{} : Bool}

# LAW: with no results, everything is zero or absent (Go returns early)
law met_empty:
  for +bs: List<&2, Nat>
  {summary(bs, []) == Met.Summary{0n, 0n, [], [], Big.of(0n), 0n, 0n, 0n, 0n, 0n, 0n, 0n, Big.of(0n), Big.of(0n),
     F64.zero(), F64.zero(), F64.zero(), F64.zero(), F64.zero(), None{}, None{}, None{}, 0n, 0n, bs,
     List.replicate(Nat, List.length(&2, Nat, bs), 0n)} : Met.Summary}

# LAW: latencies: the true min and max, and percentiles by nearest rank
# (Go's are t-digest estimates; Go's min also forgets a 0 seen first)
law met_latencies:
  for +bs: List<&2, Nat>
  for +h: Hit.Hit
  for +hs: List<&2, Hit.Hit>
  {s_lat_min(summary(bs, Con{h, hs})) == min_of(h_lat(h), lats(hs)) : Nat}
  & {s_lat_max(summary(bs, Con{h, hs})) == max_of(h_lat(h), lats(hs)) : Nat}
  & {is_rank(s_p50(summary(bs, Con{h, hs})), rank(50n, 1n+List.length(&2, Hit.Hit, hs)), lats(Con{h, hs})) == True{} : Bool}
  & {is_rank(s_p90(summary(bs, Con{h, hs})), rank(90n, 1n+List.length(&2, Hit.Hit, hs)), lats(Con{h, hs})) == True{} : Bool}
  & {is_rank(s_p95(summary(bs, Con{h, hs})), rank(95n, 1n+List.length(&2, Hit.Hit, hs)), lats(Con{h, hs})) == True{} : Bool}
  & {is_rank(s_p99(summary(bs, Con{h, hs})), rank(99n, 1n+List.length(&2, Hit.Hit, hs)), lats(Con{h, hs})) == True{} : Bool}

# LAW: the span: first start, last start, last end (in UTC: the report
# prints them in the local zone), and the durations between them
law met_span:
  for +bs: List<&2, Nat>
  for +h: Hit.Hit
  for +hs: List<&2, Hit.Hit>
  for -ok: {Nat.is_lt(time_nsec(h_ts(h)), sec()) == True{} : Bool}
  {s_earliest(summary(bs, Con{h, hs})) == Some{utc_at(min_of(total_ns(h_ts(h)), starts(hs)))} : Maybe<&2, Civil.Time>}
  & {s_latest(summary(bs, Con{h, hs})) == Some{utc_at(max_of(total_ns(h_ts(h)), starts(hs)))} : Maybe<&2, Civil.Time>}
  & {s_end(summary(bs, Con{h, hs})) == Some{utc_at(max_of(Nat.add(total_ns(h_ts(h)), h_lat(h)), ends(hs)))} : Maybe<&2, Civil.Time>}
  & {s_duration(summary(bs, Con{h, hs})) == Nat.sub(max_of(total_ns(h_ts(h)), starts(hs)), min_of(total_ns(h_ts(h)), starts(hs))) : Nat}
  & {s_wait(summary(bs, Con{h, hs})) == Nat.sub(max_of(Nat.add(total_ns(h_ts(h)), h_lat(h)), ends(hs)), max_of(total_ns(h_ts(h)), starts(hs))) : Nat}

# Go's Duration.Seconds(): float64(d / 1s) + float64(d % 1s) / 1e9
def seconds(+d: Nat) -> F64.F64:
  F64.add(F64.of_nat(Nat.div(d, sec())), F64.div(F64.of_nat(Nat.mod(d, sec())), F64.of_nat(sec())))

# LAW: the float fields are the float64 arithmetic Go does, step by step
law met_floats:
  for +bs: List<&2, Nat>
  for +h: Hit.Hit
  for +hs: List<&2, Hit.Hit>
  {s_rate(summary(bs, Con{h, hs})) == pick(F64.F64, Nat.is_gt(s_duration(summary(bs, Con{h, hs})), 0n),
      F64.div(F64.of_nat(1n+List.length(&2, Hit.Hit, hs)), seconds(s_duration(summary(bs, Con{h, hs})))),
      F64.of_nat(1n+List.length(&2, Hit.Hit, hs))) : F64.F64}
  & {s_throughput(summary(bs, Con{h, hs})) == pick(F64.F64, Nat.is_gt(s_duration(summary(bs, Con{h, hs})), 0n),
      F64.div(F64.of_nat(n_ok(Con{h, hs})), seconds(Nat.add(s_duration(summary(bs, Con{h, hs})), s_wait(summary(bs, Con{h, hs}))))),
      F64.of_nat(n_ok(Con{h, hs}))) : F64.F64}
  & {s_ratio(summary(bs, Con{h, hs})) == F64.div(F64.of_nat(n_ok(Con{h, hs})), F64.of_nat(1n+List.length(&2, Hit.Hit, hs))) : F64.F64}
  & {s_in_mean(summary(bs, Con{h, hs})) == F64.div(F64.of_big(s_bytes_in(summary(bs, Con{h, hs}))), F64.of_nat(1n+List.length(&2, Hit.Hit, hs))) : F64.F64}
  & {s_out_mean(summary(bs, Con{h, hs})) == F64.div(F64.of_big(s_bytes_out(summary(bs, Con{h, hs}))), F64.of_nat(1n+List.length(&2, Hit.Hit, hs))) : F64.F64}
  & {s_lat_mean(summary(bs, Con{h, hs})) == F64.trunc(F64.div(F64.of_big(s_lat_total(summary(bs, Con{h, hs}))), F64.of_nat(1n+List.length(&2, Hit.Hit, hs)))) : Nat}

def nth_or0(+i: Nat, +xs: List<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, xs, i), 0n)

# Go's Histogram.Add: the first bucket i with b_i <= lat < b_(i+1), else
# the last one -- which also takes latencies below the first bound
def bucket_of.go(fuel: Nat, +bs: List<&2, Nat>, +lat: Nat, +i: Nat) -> Nat:
  match fuel:
    case 0n:
      i
    case 1n+f:
      pick(Nat, Bool.and(Nat.is_le(nth_or0(i, bs), lat), Nat.is_lt(lat, nth_or0(1n+i, bs))), i, bucket_of.go(f, bs, lat, 1n+i))

def bucket_of(+bs: List<&2, Nat>, +lat: Nat) -> Nat:
  bucket_of.go(Nat.sub(List.length(&2, Nat, bs), 1n), bs, lat, 0n)

def n_in_bucket(+bs: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, +rest}:
      Nat.add(pick(Nat, Nat.is_eq(bucket_of(bs, x), i), 1n, 0n), n_in_bucket(bs, i, rest))

# LAW: the histogram has one count per bucket, each counting its latencies
law met_hist:
  for +bs: List<&2, Nat>
  for +hs: List<&2, Hit.Hit>
  for +i: Nat
  for -h: {Nat.is_lt(i, List.length(&2, Nat, bs)) == True{} : Bool}
  {s_buckets(summary(bs, hs)) == bs : List<&2, Nat>}
  & {List.length(&2, Nat, s_hist(summary(bs, hs))) == List.length(&2, Nat, bs) : Nat}
  & {nth_or0(i, s_hist(summary(bs, hs))) == n_in_bucket(bs, i, lats(hs)) : Nat}

# =====================================================================
# Rates (lib/pacer.bend): the -rate flag
# =====================================================================

def rate_is(+n: Nat, +p: Nat, +r: Result<&2, &2, String, Pace.Rate>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{x}:
      Pace.Rate{f, q} = x
      Bool.and(Nat.is_eq(f, n), Nat.is_eq(q, p))

def is_rate_fail(+r: Result<&2, &2, String, Pace.Rate>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{x}:
      False{}

def rate_same(+a: Result<&2, &2, String, Pace.Rate>, +b: Result<&2, &2, String, Pace.Rate>) -> Bool:
  match a:
    case Fail{e}:
      is_rate_fail(b)
    case Done{x}:
      Pace.Rate{f, q} = x
      rate_is(f, q, b)

# "N/D" read as Go does: N per the duration D, or an error when D does not
# parse (Go's own error text, from time.ParseDuration)
def rate_with(+n: Nat, +d: Maybe<&2, Nat>, +r: Result<&2, &2, String, Pace.Rate>) -> Bool:
  match d:
    case None{}:
      is_rate_fail(r)
    case Some{p}:
      rate_is(n, p, r)

# LAW: -rate reads as Go's rateFlag: a zero rate is unbounded; a bare
# number is per second; "N/D" is N per duration D (a D that does not parse
# fails); a bare unit, "50/m", reads as "50/1m". ("infinity" is not a
# rate: Go's flag ignores it, see flags_rate.)
law rate_parse:
  for +n: Nat
  for +d: Nat
  for +s: String
  {Pace.parse_rate("0") == Done{Pace.Rate{0n, 0n}} : Result<&2, &2, String, Pace.Rate>}
  & {Pace.parse_rate("0/" ++ s) == Done{Pace.Rate{0n, 0n}} : Result<&2, &2, String, Pace.Rate>}
  & {Pace.parse_rate(Dec.show(1n+n)) == Done{Pace.Rate{1n+n, sec()}} : Result<&2, &2, String, Pace.Rate>}
  & {Bool.or(Bool.and(is_unit_name(s), Bool.not(String.eq(s, greek_mu() ++ "s"))), rate_with(1n+n, Dur.parse(s), Pace.parse_rate(Dec.show(1n+n) ++ "/" ++ s))) == True{} : Bool}
  & {pick(Bool, Bool.and(is_unit_name(s), Bool.not(String.eq(s, greek_mu() ++ "s"))),
       rate_same(Pace.parse_rate(Dec.show(1n+n) ++ "/" ++ s), Pace.parse_rate(Dec.show(1n+n) ++ "/1" ++ s)), True{}) == True{} : Bool}


# LAW: a frequency that is not a number fails as strconv.Atoi does
law rate_parse_error:
  for +f: String
  for +rest: String
  for -h0: {Bool.and(Bool.and(printable(f), Bool.not(all_digits(f))),
     Bool.not(Bool.or(Bool.or(has_char(f, 47), has_char(f, 34)), Bool.or(has_char(f, 92), String.eq(f, "infinity"))))) == True{} : Bool}
  for -h1: {Bool.or(String.is_empty(rest), String.starts_with(rest, "/")) == True{} : Bool}
  for -h2: {Bool.not(Bool.or(first_is(f, 43), first_is(f, 45))) == True{} : Bool}
  {Pace.parse_rate(f ++ rest) == Fail{"strconv.Atoi: parsing \"" ++ f ++ "\": invalid syntax"} : Result<&2, &2, String, Pace.Rate>}

# =====================================================================
# The attack's scheduler (lib/engine.bend)
# =====================================================================
#
# The engine is fed events (the clock read after a nap, a worker done)
# and answers commands. The laws hold for EVERY list of events -- a
# clock that wakes late, early or never, workers that finish in any
# order, events for workers that are not busy -- read off the timeline
# of events and commands the engine produces.

type Item is Data:
  IEv{e: Eng.Ev}
  ICmd{c: Eng.Cmd}

def cmds_items(cs: List<&2, Eng.Cmd>) -> List<&2, Item>:
  match cs:
    case Nil{}:
      []
    case Con{+c, +rest}:
      Con{ICmd{c}, cmds_items(rest)}

def st_of(+r: Sigma<&2, &2, Eng.State, _ => List<&2, Eng.Cmd>>) -> Eng.State:
  (st, cs) = r
  st

def cs_of(+r: Sigma<&2, &2, Eng.State, _ => List<&2, Eng.Cmd>>) -> List<&2, Eng.Cmd>:
  (st, cs) = r
  cs

def steps(evs: List<&2, Eng.Ev>, +c: Eng.Cfg, +st: Eng.State) -> List<&2, Item>:
  match evs:
    case Nil{}:
      []
    case Con{+e, +rest}:
      Con{IEv{e}, List.append(&2, Item, cmds_items(cs_of(Eng.step(c, st, e))), steps(rest, c, st_of(Eng.step(c, st, e))))}

# the timeline: the start's commands, then each event and the commands it drew
def timeline(+c: Eng.Cfg, +evs: List<&2, Eng.Ev>) -> List<&2, Item>:
  List.append(&2, Item, cmds_items(cs_of(Eng.start(c))), steps(evs, c, st_of(Eng.start(c))))

def e_freq(+c: Eng.Cfg) -> Nat:
  Eng.ECfg{f, p, d, w, m, t} = c
  f

def e_per(+c: Eng.Cfg) -> Nat:
  Eng.ECfg{f, p, d, w, m, t} = c
  p

def e_dur(+c: Eng.Cfg) -> Nat:
  Eng.ECfg{f, p, d, w, m, t} = c
  d

def e_workers(+c: Eng.Cfg) -> Nat:
  Eng.ECfg{f, p, d, w, m, t} = c
  w

def e_max(+c: Eng.Cfg) -> Nat:
  Eng.ECfg{f, p, d, w, m, t} = c
  m

def e_targets(+c: Eng.Cfg) -> Nat:
  Eng.ECfg{f, p, d, w, m, t} = c
  t

# a bounded rate, at most one hit per ns (Go's pacer divides by the interval)
def bounded(+c: Eng.Cfg) -> Bool:
  Bool.and(Nat.is_gt(e_freq(c), 0n), Nat.is_ge(e_per(c), e_freq(c)))

# Go's pacer interval: per / freq, in whole nanoseconds
def interval(+c: Eng.Cfg) -> Nat:
  Nat.div(e_per(c), e_freq(c))

# hit i is due at (i + 1) intervals (Go's first hit waits one interval)
def slot(+c: Eng.Cfg, +i: Nat) -> Nat:
  Nat.mul(1n+i, interval(c))

# the hits an attack of this length is scheduled to send: hit i is sent
# only if the previous one went out before the deadline, so the slots are
# i = 0, 1, ... while i intervals is under the duration (Go checks
# elapsed > duration just after the previous hit, so a hit due exactly at
# the deadline never goes: 50/s for 2s is 100 hits)
def scheduled(+c: Eng.Cfg) -> Nat:
  Nat.div(Nat.add(e_dur(c), Nat.sub(interval(c), 1n)), interval(c))

# some target, some worker allowed, and a rate either unbounded or at
# most one hit per ns
def cfg_ok(+c: Eng.Cfg) -> Bool:
  Bool.and(Bool.and(Nat.is_ge(e_targets(c), 1n), Nat.is_ge(e_max(c), 1n)),
    Bool.or(Bool.or(Nat.is_eq(e_freq(c), 0n), Nat.is_eq(e_per(c), 0n)), Nat.is_ge(e_per(c), e_freq(c))))

def initial(+c: Eng.Cfg) -> Nat:
  Nat.min(e_workers(c), e_max(c))

def ev_time(+e: Eng.Ev) -> Nat:
  match e:
    case Eng.Clock{t}:
      t
    case Eng.Freed{w, t}:
      t

# every hit's seq is the number of hits before it
def chk_seq(xs: List<&2, Item>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          chk_seq(rest, n)
        case ICmd{c}:
          match c:
            case Eng.Fire{w, q, g, t}:
              Bool.and(Nat.is_eq(q, n), chk_seq(rest, 1n+n))
            case _:
              chk_seq(rest, n)

law eng_seq:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  {chk_seq(timeline(c, evs), 0n) == True{} : Bool}

# every hit goes out at the time of the event that drew it (0 at the start)
def chk_now(xs: List<&2, Item>, +now: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          chk_now(rest, ev_time(e))
        case ICmd{c}:
          match c:
            case Eng.Fire{w, q, g, t}:
              Bool.and(Nat.is_eq(t, now), chk_now(rest, now))
            case _:
              chk_now(rest, now)

law eng_now:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  {chk_now(timeline(c, evs), 0n) == True{} : Bool}

def chk_early(xs: List<&2, Item>, +c: Eng.Cfg) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          chk_early(rest, c)
        case ICmd{k}:
          match k:
            case Eng.Fire{w, q, g, t}:
              Bool.and(Nat.is_ge(t, slot(c, q)), chk_early(rest, c))
            case _:
              chk_early(rest, c)

# LAW: at a bounded rate, no hit ever goes out before its slot
law eng_never_early:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  for -h: {bounded(c) == True{} : Bool}
  {chk_early(timeline(c, evs), c) == True{} : Bool}

def chk_deadline(xs: List<&2, Item>, +dur: Nat, +last: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          chk_deadline(rest, dur, last)
        case ICmd{k}:
          match k:
            case Eng.Fire{w, q, g, t}:
              Bool.and(Nat.is_lt(last, dur), chk_deadline(rest, dur, t))
            case _:
              chk_deadline(rest, dur, last)

# LAW: a hit goes out only if the previous one went out before the
# deadline (the first always may): Go's check at the top of its loop
law eng_deadline:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  for -h: {Nat.is_gt(e_dur(c), 0n) == True{} : Bool}
  {chk_deadline(timeline(c, evs), e_dur(c), 0n) == True{} : Bool}

def chk_rr(xs: List<&2, Item>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          chk_rr(rest, n)
        case ICmd{k}:
          match k:
            case Eng.Fire{w, q, g, t}:
              Bool.and(Nat.is_eq(g, Nat.mod(q, n)), chk_rr(rest, n))
            case _:
              chk_rr(rest, n)

# LAW: targets are taken round-robin by seq
law eng_round_robin:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  for -h: {cfg_ok(c) == True{} : Bool}
  {chk_rr(timeline(c, evs), e_targets(c)) == True{} : Bool}

def has_nat(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, +rest}:
      Bool.or(Nat.is_eq(x, y), has_nat(x, rest))

def drop_nat(+x: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case Con{+y, +rest}:
      pick(List<&2, Nat>, Nat.is_eq(x, y), rest, Con{y, drop_nat(x, rest)})

# workers: grown one id at a time from 0, never past max-workers; a hit
# goes to a grown worker that is not busy; a worker is busy from its hit
# until it is freed (a free for a worker that is not busy changes nothing)
def chk_workers(xs: List<&2, Item>, +max: Nat, +grown: Nat, +busy: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          match e:
            case Eng.Clock{t}:
              chk_workers(rest, max, grown, busy)
            case Eng.Freed{w, t}:
              chk_workers(rest, max, grown, drop_nat(w, busy))
        case ICmd{k}:
          match k:
            case Eng.Grow{w}:
              Bool.and(Bool.and(Nat.is_eq(w, grown), Nat.is_lt(grown, max)), chk_workers(rest, max, 1n+grown, busy))
            case Eng.Fire{w, q, g, t}:
              Bool.and(Bool.and(Nat.is_lt(w, grown), Bool.not(has_nat(w, busy))), chk_workers(rest, max, grown, Con{w, busy}))
            case _:
              chk_workers(rest, max, grown, busy)

# LAW: worker bookkeeping
law eng_workers:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  {chk_workers(timeline(c, evs), e_max(c), 0n, []) == True{} : Bool}

def grows(+n: Nat, +from: Nat) -> List<&2, Item>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{ICmd{Eng.Grow{from}}, grows(p, 1n+from)}

# LAW: the attack starts with min(workers, max-workers) workers
law eng_initial:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  {List.take(&2, Item, timeline(c, evs), initial(c)) == grows(initial(c), 0n) : List<&2, Item>}

def next_fires(+w: Nat, +xs: List<&2, Item>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          False{}
        case ICmd{k}:
          match k:
            case Eng.Fire{v, q, g, t}:
              Nat.is_eq(v, w)
            case _:
              False{}

def chk_grow(xs: List<&2, Item>, +w0: Nat, +grown: Nat, +busy: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          match e:
            case Eng.Clock{t}:
              chk_grow(rest, w0, grown, busy)
            case Eng.Freed{w, t}:
              chk_grow(rest, w0, grown, drop_nat(w, busy))
        case ICmd{k}:
          match k:
            case Eng.Grow{w}:
              Bool.and(Bool.or(Nat.is_lt(w, w0), Bool.and(Nat.is_eq(List.length(&2, Nat, busy), grown), next_fires(w, rest))),
                chk_grow(rest, w0, 1n+grown, busy))
            case Eng.Fire{w, q, g, t}:
              chk_grow(rest, w0, grown, Con{w, busy})
            case _:
              chk_grow(rest, w0, grown, busy)

# LAW: past the initial workers, a worker is grown only when every worker
# is busy, and it takes the due hit at once (Go spawns one when the tick
# channel would block)
law eng_grow:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  {chk_grow(timeline(c, evs), initial(c), 0n, []) == True{} : Bool}

def no_nap(xs: List<&2, Item>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          no_nap(rest)
        case ICmd{k}:
          match k:
            case Eng.Nap{u}:
              False{}
            case _:
              no_nap(rest)

# LAW: at an unbounded rate (0 hits, or 0 per) the engine never naps
law eng_unbounded:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  for -h: {Bool.or(Nat.is_eq(e_freq(c), 0n), Nat.is_eq(e_per(c), 0n)) == True{} : Bool}
  {no_nap(timeline(c, evs)) == True{} : Bool}

def chk_nap(xs: List<&2, Item>, +c: Eng.Cfg, +next: Nat, +now: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          chk_nap(rest, c, next, ev_time(e))
        case ICmd{k}:
          match k:
            case Eng.Nap{u}:
              Bool.and(Bool.and(Nat.is_eq(u, slot(c, next)), Nat.is_gt(u, now)), chk_nap(rest, c, next, now))
            case Eng.Fire{w, q, g, t}:
              chk_nap(rest, c, 1n+next, now)
            case _:
              chk_nap(rest, c, next, now)

# LAW: a nap is always until the next hit's slot, and never for nothing
law eng_nap:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  for -h: {bounded(c) == True{} : Bool}
  {chk_nap(timeline(c, evs), c, 0n, 0n) == True{} : Bool}

# the engine has decided to stop: a hit went out at or past the deadline
# (Go's check at the top of its loop, just after each send)
def stop_due(+dur: Nat, +last: Maybe<&2, Nat>) -> Bool:
  match last:
    case None{}:
      False{}
    case Some{t}:
      Bool.and(Nat.is_gt(dur, 0n), Nat.is_ge(t, dur))

def chk_quit(xs: List<&2, Item>, +c: Eng.Cfg, +sent: Nat, +quit: Bool, +last: Maybe<&2, Nat>, +busy: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          match e:
            case Eng.Clock{t}:
              chk_quit(rest, c, sent, quit, last, busy)
            case Eng.Freed{w, t}:
              chk_quit(rest, c, sent, quit, last, drop_nat(w, busy))
        case ICmd{k}:
          match k:
            case Eng.Fire{w, q, g, t}:
              Bool.and(Bool.not(quit), chk_quit(rest, c, 1n+sent, quit, Some{t}, Con{w, busy}))
            case Eng.Quit{s, d}:
              Bool.and(Bool.and(Bool.not(quit), Bool.and(stop_due(e_dur(c), last), List.is_empty(&2, Nat, busy))),
                Bool.and(Bool.and(Nat.is_eq(s, sent), pick(Bool, bounded(c), Nat.is_eq(Nat.add(s, d), scheduled(c)), Nat.is_eq(d, 0n))),
                  chk_quit(rest, c, sent, True{}, last, busy)))
            case _:
              Bool.and(Bool.not(quit), chk_quit(rest, c, sent, quit, last, busy))

# LAW: the attack stops once and last, only when a hit has gone out at or
# past the deadline and every worker is done, and it accounts for every
# slot: the hits sent plus the slots dropped (Go drops them silently when
# it falls behind at the deadline) are the schedule
law eng_quit:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  {chk_quit(timeline(c, evs), c, 0n, False{}, None{}, []) == True{} : Bool}

# waiting is legitimate only on a nap, on workers when every allowed one
# is busy, or on the last workers once the stop is decided; and a decided
# stop with no busy worker must have happened
def pending(+c: Eng.Cfg, +nap: Bool, +grown: Nat, +busy: List<&2, Nat>, +quit: Bool, +last: Maybe<&2, Nat>) -> Bool:
  +n = List.length(&2, Nat, busy)
  +stop = stop_due(e_dur(c), last)
  Bool.or(quit, pick(Bool, stop, Nat.is_gt(n, 0n),
    Bool.or(nap, Bool.and(Nat.is_gt(n, 0n), Bool.and(Nat.is_eq(n, grown), Nat.is_eq(grown, e_max(c)))))))

def chk_live(xs: List<&2, Item>, +c: Eng.Cfg, +nap: Bool, +grown: Nat, +busy: List<&2, Nat>, +quit: Bool, +last: Maybe<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      pending(c, nap, grown, busy, quit, last)
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          match e:
            case Eng.Clock{t}:
              Bool.and(pending(c, nap, grown, busy, quit, last), chk_live(rest, c, False{}, grown, busy, quit, last))
            case Eng.Freed{w, t}:
              Bool.and(pending(c, nap, grown, busy, quit, last), chk_live(rest, c, nap, grown, drop_nat(w, busy), quit, last))
        case ICmd{k}:
          match k:
            case Eng.Nap{u}:
              chk_live(rest, c, True{}, grown, busy, quit, last)
            case Eng.Grow{w}:
              chk_live(rest, c, nap, 1n+grown, busy, quit, last)
            case Eng.Fire{w, q, g, t}:
              chk_live(rest, c, nap, grown, Con{w, busy}, quit, Some{t})
            case Eng.Quit{s, d}:
              chk_live(rest, c, nap, grown, busy, True{}, last)

# LAW: the engine never stalls: after the start and after every event it
# waits on a nap, on workers only when all it may have are busy, or on the
# last workers after the deadline; otherwise a due hit has gone out, and
# a decided stop has happened. With eng_nap, eng_never_early and eng_now
# this makes every hit go out at its slot whenever the clock wakes on time
# and a worker is available: no coordinated omission.
law eng_live:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  for -h: {cfg_ok(c) == True{} : Bool}
  {chk_live(timeline(c, evs), c, False{}, 0n, [], False{}, None{}) == True{} : Bool}

def busy_of(xs: List<&2, Item>, +busy: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      busy
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          match e:
            case Eng.Clock{t}:
              busy_of(rest, busy)
            case Eng.Freed{w, t}:
              busy_of(rest, drop_nat(w, busy))
        case ICmd{k}:
          match k:
            case Eng.Fire{w, q, g, t}:
              busy_of(rest, Con{w, busy})
            case _:
              busy_of(rest, busy)

# the end of the nap still open at the end of the timeline, if any
def nap_of(xs: List<&2, Item>, +nap: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      nap
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          match e:
            case Eng.Clock{t}:
              nap_of(rest, None{})
            case Eng.Freed{w, t}:
              nap_of(rest, nap)
        case ICmd{k}:
          match k:
            case Eng.Nap{u}:
              nap_of(rest, Some{u})
            case _:
              nap_of(rest, nap)

def frees(ws: List<&2, Nat>, +t: Nat) -> List<&2, Eng.Ev>:
  match ws:
    case Nil{}:
      []
    case Con{+w, +rest}:
      Con{Eng.Freed{w, t}, frees(rest, t)}

# a round of a responsive environment: the clock reads the later of t and
# the open nap's end, and every busy worker finishes
def respond(fuel: Nat, +c: Eng.Cfg, +evs: List<&2, Eng.Ev>, +t: Nat) -> List<&2, Eng.Ev>:
  match fuel:
    case 0n:
      evs
    case 1n+f:
      +tl = timeline(c, evs)
      +now = Nat.max(t, Maybe.default(&2, Nat, nap_of(tl, None{}), t))
      respond(f, c, List.append(&2, Eng.Ev, evs, Con{Eng.Clock{now}, frees(busy_of(tl, []), now)}), now)

def has_quit(xs: List<&2, Item>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, +rest}:
      match x:
        case IEv{e}:
          has_quit(rest)
        case ICmd{k}:
          match k:
            case Eng.Quit{s, d}:
              True{}
            case _:
              has_quit(rest)

def max_time(evs: List<&2, Eng.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case Con{+e, +rest}:
      Nat.max(ev_time(e), max_time(rest))

# LAW: an attack with a duration ends: from any point, once the clock is
# past the deadline, four rounds of a responsive environment bring the stop
law eng_ends:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  for +t: Nat
  for -h0: {cfg_ok(c) == True{} : Bool}
  for -h1: {Nat.is_gt(e_dur(c), 0n) == True{} : Bool}
  for -h2: {Bool.and(Nat.is_gt(t, e_dur(c)), Nat.is_ge(t, max_time(evs))) == True{} : Bool}
  {has_quit(timeline(c, respond(4n, c, evs, t))) == True{} : Bool}

# =====================================================================
# The HTTP client of a worker (lib/conn.bend)
# =====================================================================
#
# One machine per request, fed what the network did. As with the engine,
# the laws hold for every list of events, read off the timeline.

type CItem is Data:
  CIEv{e: Conn.Ev}
  CICmd{c: Conn.Cmd}

def ccmds_items(cs: List<&2, Conn.Cmd>) -> List<&2, CItem>:
  match cs:
    case Nil{}:
      []
    case Con{+c, +rest}:
      Con{CICmd{c}, ccmds_items(rest)}

def cst_of(+r: Sigma<&2, &2, Conn.State, _ => List<&2, Conn.Cmd>>) -> Conn.State:
  (st, cs) = r
  st

def ccs_of(+r: Sigma<&2, &2, Conn.State, _ => List<&2, Conn.Cmd>>) -> List<&2, Conn.Cmd>:
  (st, cs) = r
  cs

def csteps(evs: List<&2, Conn.Ev>, +c: Conn.Cfg, +st: Conn.State) -> List<&2, CItem>:
  match evs:
    case Nil{}:
      []
    case Con{+e, +rest}:
      Con{CIEv{e}, List.append(&2, CItem, ccmds_items(ccs_of(Conn.step(c, st, e))), csteps(rest, c, cst_of(Conn.step(c, st, e))))}

def ctimeline(+c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>) -> List<&2, CItem>:
  List.append(&2, CItem, ccmds_items(ccs_of(Conn.start(c, r, open))), csteps(evs, c, cst_of(Conn.start(c, r, open))))

def c_ka(+c: Conn.Cfg) -> Bool:
  Conn.CCfg{ka, to, mb, rd} = c
  ka

def c_mb(+c: Conn.Cfg) -> Maybe<&2, Nat>:
  Conn.CCfg{ka, to, mb, rd} = c
  mb

def c_redirects(+c: Conn.Cfg) -> Maybe<&2, Nat>:
  Conn.CCfg{ka, to, mb, rd} = c
  rd

def q_target(+r: Conn.Req) -> Tgt.Target:
  Conn.Req{t, u, ip, b, s, n} = r
  t

def q_url(+r: Conn.Req) -> Tgt.Url:
  Conn.Req{t, u, ip, b, s, n} = r
  u

def q_ip(+r: Conn.Req) -> String:
  Conn.Req{t, u, ip, b, s, n} = r
  ip

def q_body(+r: Conn.Req) -> String:
  Conn.Req{t, u, ip, b, s, n} = r
  b

def q_seq(+r: Conn.Req) -> Nat:
  Conn.Req{t, u, ip, b, s, n} = r
  s

def q_name(+r: Conn.Req) -> String:
  Conn.Req{t, u, ip, b, s, n} = r
  n

def u_port(+u: Tgt.Url) -> Nat:
  Tgt.Url{sc, h, p, pa} = u
  Maybe.default(&2, Nat, p, 80n)

def u_portm(+u: Tgt.Url) -> Maybe<&2, Nat>:
  Tgt.Url{sc, h, p, pa} = u
  p

# the request's text, as Http.request writes it
def q_text(+c: Conn.Cfg, +r: Conn.Req) -> String:
  Http.request(q_target(r), q_url(r), q_body(r), q_seq(r), q_name(r), c_ka(c))

# Go's url.Error op: "Get", "Post"
def op(+m: String) -> String:
  String.take(m, 1n) ++ String.to_lower(String.drop(m, 1n))

def err_prefix(+r: Conn.Req) -> String:
  op(tgt_method(q_target(r))) ++ " \"" ++ tgt_url(q_target(r)) ++ "\": "

# LAW: the first command: send on the open connection, or open one
law conn_first:
  for +c: Conn.Cfg
  for +r: Conn.Req
  for +open: Bool
  {List.head(&2, Conn.Cmd, ccs_of(Conn.start(c, r, open)))
   == Some{pick(Conn.Cmd, open, Conn.Send{q_text(c, r)}, Conn.Open{q_ip(r), u_port(q_url(r))})} : Maybe<&2, Conn.Cmd>}

def chk_cfinish(xs: List<&2, CItem>, +done: Bool) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          chk_cfinish(rest, done)
        case CICmd{k}:
          match k:
            case Conn.Finish{o, keep}:
              Bool.and(Bool.not(done), chk_cfinish(rest, True{}))
            case _:
              Bool.and(Bool.not(done), chk_cfinish(rest, done))

# LAW: a request finishes once, and nothing follows
law conn_finish:
  for +c: Conn.Cfg
  for +r: Conn.Req
  for +open: Bool
  for +evs: List<&2, Conn.Ev>
  {chk_cfinish(ctimeline(c, r, open, evs), False{}) == True{} : Bool}

def chk_open(xs: List<&2, CItem>, +open: Bool) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          match e:
            case Conn.Opened{}:
              chk_open(rest, True{})
            case Conn.OpenFailed{m}:
              chk_open(rest, False{})
            case Conn.SendFailed{m}:
              chk_open(rest, False{})
            case Conn.Eof{}:
              chk_open(rest, False{})
            case _:
              chk_open(rest, open)
        case CICmd{k}:
          match k:
            case Conn.Send{d}:
              Bool.and(open, chk_open(rest, open))
            case Conn.Shut{}:
              chk_open(rest, False{})
            case _:
              chk_open(rest, open)

# LAW: bytes go out only on an open connection
law conn_send_open:
  for +c: Conn.Cfg
  for +r: Conn.Req
  for +open: Bool
  for +evs: List<&2, Conn.Ev>
  {chk_open(ctimeline(c, r, open, evs), open) == True{} : Bool}

def parse_buf(+eof: Bool, +mb: Maybe<&2, Nat>, +head: Bool, +buf: String) -> Maybe<&1, Result<&1, &1, String, Http.Resp & String>>:
  match eof:
    case True{}:
      parse_eof(mb, head, buf)
    case False{}:
      parse_of(mb, head, buf)

def is_redirect(+r: Http.Resp) -> Bool:
  +c = r_code(r)
  Bool.and(Bool.or(Bool.or(Nat.is_eq(c, 301n), Nat.is_eq(c, 302n)), Bool.or(Bool.or(Nat.is_eq(c, 303n), Nat.is_eq(c, 307n)), Nat.is_eq(c, 308n))),
    has_key("Location", r_hdrs(r)))

def strs_eq(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      List.is_empty(&2, String, ys)
    case Con{+x, +xr}:
      match ys:
        case Nil{}:
          False{}
        case Con{+y, +yr}:
          Bool.and(String.eq(x, y), strs_eq(xr, yr))

def hdrs_eq(xs: List<&2, Hdr.Header>, +ys: List<&2, Hdr.Header>) -> Bool:
  match xs:
    case Nil{}:
      List.is_empty(&2, Hdr.Header, ys)
    case Con{+x, +xr}:
      match ys:
        case Nil{}:
          False{}
        case Con{+y, +yr}:
          Bool.and(Bool.and(String.eq(hdr_key(x), hdr_key(y)), strs_eq(hdr_vals(x), hdr_vals(y))), hdrs_eq(xr, yr))

def resp_eq(+a: Http.Resp, +b: Http.Resp) -> Bool:
  Bool.and(Bool.and(Nat.is_eq(r_code(a), r_code(b)), String.eq(r_status(a), r_status(b))),
  Bool.and(Bool.and(hdrs_eq(r_hdrs(a), r_hdrs(b)), String.eq(r_body(a), r_body(b))),
    same_bool(r_keep(a), r_keep(b))))

def answer_of(+ka: Bool, m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, +r: Http.Resp, +keep: Bool) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          False{}
        case Done{p}:
          (r0, lo0) = p
          +r2 = r0
          +lo = lo0
          Bool.and(resp_eq(r2, r), same_bool(keep, Bool.and(Bool.and(r_keep(r), ka), String.is_empty(lo))))

# a finished answer is what the parser makes of the bytes since the
# request went out, and the connection is kept only when both sides allow
# it and nothing extra arrived
def answer_ok(+c: Conn.Cfg, +head: Bool, +buf: String, +eof: Bool, +r: Http.Resp, +keep: Bool) -> Bool:
  answer_of(c_ka(c), parse_buf(eof, c_mb(c), head, buf), r, keep)

# the commands that follow, up to the next event
def batch(xs: List<&2, CItem>) -> List<&2, Conn.Cmd>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          []
        case CICmd{k}:
          Con{k, batch(rest)}

# a response has fully arrived, and it is not a redirect the client follows
def final_resp(+c: Conn.Cfg, m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          False{}
        case Done{p}:
          (r0, lo) = p
          +r = r0
          Bool.not(Bool.and(Maybe.is_some(&2, Nat, c_redirects(c)), is_redirect(r)))

def answers(+c: Conn.Cfg, +head: Bool, +buf: String, +eof: Bool, cs: List<&2, Conn.Cmd>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+k, +rest}:
      match k:
        case Conn.Finish{o, keep}:
          match o:
            case Conn.Answered{r}:
              answer_ok(c, head, buf, eof, r, keep)
            case Conn.Failed{m, pb}:
              False{}
        case _:
          answers(c, head, buf, eof, rest)

# after bytes arrive: once a final response is complete, the client
# answers with it at once
def must_answer(+c: Conn.Cfg, +head: Bool, +buf: String, +eof: Bool, +rest: List<&2, CItem>) -> Bool:
  Bool.or(Bool.not(final_resp(c, parse_buf(eof, c_mb(c), head, buf))), answers(c, head, buf, eof, batch(rest)))

def chk_answer(xs: List<&2, CItem>, +c: Conn.Cfg, +head: Bool, +buf: String, +eof: Bool, +done: Bool) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          match e:
            case Conn.Got{d}:
              Bool.and(Bool.or(done, must_answer(c, head, buf ++ d, eof, rest)), chk_answer(rest, c, head, buf ++ d, eof, done))
            case Conn.Eof{}:
              Bool.and(Bool.or(done, must_answer(c, head, buf, True{}, rest)), chk_answer(rest, c, head, buf, True{}, done))
            case _:
              chk_answer(rest, c, head, buf, eof, done)
        case CICmd{k}:
          match k:
            case Conn.Send{d}:
              chk_answer(rest, c, String.starts_with(d, "HEAD "), "", False{}, done)
            case Conn.Finish{o, keep}:
              match o:
                case Conn.Answered{r}:
                  Bool.and(answer_ok(c, head, buf, eof, r, keep),
                    Bool.and(Bool.or(Maybe.is_none(&2, Nat, c_redirects(c)), Bool.not(is_redirect(r))), chk_answer(rest, c, head, buf, eof, True{})))
                case Conn.Failed{m, pb}:
                  Bool.and(Bool.not(keep), chk_answer(rest, c, head, buf, eof, True{}))
            case _:
              chk_answer(rest, c, head, buf, eof, done)

# LAW: answers are exactly what the parser makes of the bytes, the moment
# a final response is complete; a redirect being followed is not an
# answer; a failure never keeps its connection
law conn_answer:
  for +c: Conn.Cfg
  for +r: Conn.Req
  for +open: Bool
  for +evs: List<&2, Conn.Ev>
  {chk_answer(ctimeline(c, r, open, evs), c, False{}, "", False{}, False{}) == True{} : Bool}

# what the client is waiting on, as the events answer its commands
type Wait is Data:
  Wait{resolve: Bool, open: Bool, send: Bool, recv: Bool, out: Bool, done: Bool}

def w_live(+w: Wait) -> Bool:
  Wait{rs, op, sd, rv, out, done} = w
  Bool.or(Bool.or(done, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)))

def w_ev(+w: Wait, +e: Conn.Ev) -> Wait:
  Wait{rs, op, sd, rv, out, done} = w
  match e:
    case Conn.Resolved{ip}:
      Wait{False{}, op, sd, rv, out, done}
    case Conn.ResolveFailed{m}:
      Wait{False{}, op, sd, rv, out, done}
    case Conn.Opened{}:
      Wait{rs, False{}, sd, rv, out, done}
    case Conn.OpenFailed{m}:
      Wait{rs, False{}, sd, rv, out, done}
    case Conn.Sent{}:
      Wait{rs, op, False{}, rv, True{}, done}
    case Conn.SendFailed{m}:
      Wait{rs, op, False{}, rv, out, done}
    case _:
      Wait{rs, op, sd, False{}, out, done}

def w_cmd(+w: Wait, +k: Conn.Cmd) -> Wait:
  Wait{rs, op, sd, rv, out, done} = w
  match k:
    case Conn.Resolve{h}:
      Wait{True{}, op, sd, rv, False{}, done}
    case Conn.Open{ip, p}:
      Wait{rs, True{}, sd, rv, False{}, done}
    case Conn.Send{d}:
      Wait{rs, op, True{}, rv, False{}, done}
    case Conn.Recv{}:
      Wait{rs, op, sd, True{}, out, done}
    case Conn.Shut{}:
      Wait{rs, op, sd, rv, False{}, done}
    case Conn.Finish{o, keep}:
      Wait{rs, op, sd, rv, out, True{}}

def chk_pending(xs: List<&2, CItem>, +w: Wait) -> Bool:
  match xs:
    case Nil{}:
      w_live(w)
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          Bool.and(w_live(w), chk_pending(rest, w_ev(w, e)))
        case CICmd{k}:
          chk_pending(rest, w_cmd(w, k))

# LAW: an unfinished request is always waiting on something the shell
# will answer: a lookup, a connect, a write, or (once the request is out)
# a read. No request can hang because the client stopped asking.
law conn_live:
  for +c: Conn.Cfg
  for +r: Conn.Req
  for +open: Bool
  for +evs: List<&2, Conn.Ev>
  {chk_pending(ctimeline(c, r, open, evs), Wait{False{}, False{}, False{}, False{}, False{}, False{}}) == True{} : Bool}

def pb_eq(+a: Maybe<&2, String>, +b: Maybe<&2, String>) -> Bool:
  match a:
    case None{}:
      Maybe.is_none(&2, String, b)
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          String.eq(x, y)

def fails_with(+m: String, +pb: Maybe<&2, String>, cs: List<&2, Conn.Cmd>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+k, +rest}:
      match k:
        case Conn.Finish{o, keep}:
          match o:
            case Conn.Failed{m2, pb2}:
              Bool.and(Bool.and(String.eq(m, m2), pb_eq(pb, pb2)), Bool.not(keep))
            case Conn.Answered{a}:
              False{}
        case _:
          fails_with(m, pb, rest)

# Go's texts for a timeout: before the headers are in (a url.Error, with
# the method and URL), or while reading the body (the bare error, and the
# body read so far is kept)
def timeout_text(+r: Conn.Req, +buf: String) -> String:
  pick(String, String.contains(buf, "\r\n\r\n"),
    "context deadline exceeded (Client.Timeout or context cancellation while reading body)",
    err_prefix(r) ++ "context deadline exceeded (Client.Timeout exceeded while awaiting headers)")

def timeout_partial(+c: Conn.Cfg, +head: Bool, +buf: String) -> Maybe<&2, String>:
  pick(Maybe<&2, String>, String.contains(buf, "\r\n\r\n"), Some{Http.partial(Http.feed(Http.start(c_mb(c), head), buf))}, None{})

def dial_text(+r: Conn.Req, +m: String) -> String:
  err_prefix(r) ++ "dial tcp " ++ q_ip(r) ++ ":" ++ Dec.show(u_port(q_url(r))) ++ ": connect: " ++ String.to_lower(m)

def is_fresh(+last: Maybe<&2, String>, +d: String) -> Bool:
  match last:
    case None{}:
      False{}
    case Some{l}:
      Bool.not(String.eq(l, d))

def rd_limit(+m: Maybe<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, m, 0n)


def after_head.go(+fuel: Nat, +s: String) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      pick(String, String.starts_with(s, "\r\n\r\n"), s, after_head.go(f, String.drop(s, 1n)))

def after_head(+s: String) -> String:
  after_head.go(String.length(s), s)

def u_host(+u: Tgt.Url) -> String:
  Tgt.Url{sc, h, p, pa} = u
  h

def last_slash(s: String, +acc: String, +cut: String) -> String:
  match s:
    case SNil{}:
      cut
    case SCon{+c, +rest}:
      +acc2 = acc ++ SCon{c, SNil{}}
      last_slash(rest, acc2, pick(String, U32.is_eq(code(c), 47), acc2, cut))

# the directory of a path: up to and including its last "/"
def dir_of(+p: String) -> String:
  last_slash(p, "", "/")

def rev_drop1(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      rest

# RFC 3986's remove_dot_segments over the segments of an absolute path,
# collected in reverse
def dots(segs: List<&2, String>, +out: List<&2, String>) -> List<&2, String>:
  match segs:
    case Nil{}:
      out
    case Con{+g, +rest}:
      +last = List.is_empty(&2, String, rest)
      +dot = String.eq(g, ".")
      +up = String.eq(g, "..")
      +out2 = pick(List<&2, String>, dot, out, pick(List<&2, String>, up, rev_drop1(out), Con{g, out}))
      dots(rest, pick(List<&2, String>, Bool.and(last, Bool.or(dot, up)), Con{"", out2}, out2))

def remove_dots(+p: String) -> String:
  "/" ++ join_str("/", List.reverse(&2, String, dots(List.drop(&2, String, split_on(47, p), 1n), [])))

# a Location resolved against the request's URL, as Go's URL.ResolveReference
def loc_url(+u: Tgt.Url, +loc: String) -> String:
  +base = "http://" ++ u_host(u) ++ port_text(u_portm(u))
  +bpath = before_q(url_path(u))
  +lpath = before_q(loc)
  +lq = String.drop(loc, String.length(lpath))
  pick(String, Bool.or(String.starts_with(String.to_lower(loc), "http://"), String.starts_with(String.to_lower(loc), "https://")), loc,
  pick(String, String.starts_with(loc, "//"), "http:" ++ loc,
  pick(String, String.starts_with(loc, "/"), base ++ remove_dots(lpath) ++ lq,
  pick(String, String.is_empty(lpath), base ++ bpath ++ pick(String, String.is_empty(lq), String.drop(url_path(u), String.length(bpath)), lq),
    base ++ remove_dots(dir_of(bpath) ++ lpath) ++ lq))))

# a response head that has arrived (its blank line is in), read directly:
# its status code and its Location, for a redirect whose body is pending
def head_text(+buf: String) -> String:
  String.take(buf, Nat.sub(String.length(buf), String.length(after_head(buf))))

def head_code(+buf: String) -> Nat:
  digits_value(String.take(String.drop(buf, 9n), 3n))

def strip_cr(+l: String) -> String:
  pick(String, String.ends_with(l, "\r"), String.take(l, Nat.sub(String.length(l), 1n)), l)

def head_loc_of(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{+l, +rest}:
      +kv = split_on(58, strip_cr(l))
      pick(String, String.eq(canon(trim_ows(Maybe.default(&2, String, List.head(&2, String, kv), ""))), "Location"),
        trim_ows(String.drop(strip_cr(l), 1n+String.length(Maybe.default(&2, String, List.head(&2, String, kv), "")))),
        head_loc_of(rest))

def head_location(+buf: String) -> String:
  head_loc_of(List.drop(&2, String, split_on(10, head_text(buf)), 1n))

# the head in buf is a redirect the client would follow
def head_redirect(+c: Conn.Cfg, +buf: String) -> Bool:
  +k = head_code(buf)
  Bool.and(Bool.and(String.contains(buf, "\r\n\r\n"), Maybe.is_some(&2, Nat, c_redirects(c))),
    Bool.and(Bool.or(Bool.or(Nat.is_eq(k, 301n), Nat.is_eq(k, 302n)), Bool.or(Bool.or(Nat.is_eq(k, 303n), Nat.is_eq(k, 307n)), Nat.is_eq(k, 308n))),
      Bool.not(String.is_empty(head_location(buf)))))

def stop_text(+q: Conn.Req, +loc: String, +n: Nat) -> String:
  op(tgt_method(q_target(q))) ++ " \"" ++ loc ++ "\": stopped after " ++ Dec.show(n) ++ " redirects"

# a timeout once a redirect's head is in: Go has stopped reading it and
# is on the next request (awaiting its headers, named by its URL), unless
# the limit is 0 (then the stop is the error)
def redirect_timeout_text(+c: Conn.Cfg, +q: Conn.Req, +buf: String) -> String:
  +n = rd_limit(c_redirects(c))
  pick(String, Nat.is_eq(n, 0n), stop_text(q, head_location(buf), 0n),
    op(tgt_method(q_target(q))) ++ " \"" ++ loc_url(q_url(q), head_location(buf)) ++ "\": context deadline exceeded (Client.Timeout exceeded while awaiting headers)")

def is_done_parse(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          False{}
        case Done{p}:
          True{}

# before the request finishes (and before any redirect: a redirect's own
# errors name the redirect's URL), a timeout or a failed dial finishes it
# at once, with Go's error text and Go's partial body
def chk_fail(xs: List<&2, CItem>, +c: Conn.Cfg, +r: Conn.Req, +done: Bool, +first: Maybe<&2, String>, +head: Bool, +buf: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          match e:
            case Conn.Late{}:
              Bool.or(done, pick(Bool, head_redirect(c, buf),
                fails_with(redirect_timeout_text(c, r, buf), None{}, batch(rest)),
                fails_with(timeout_text(r, buf), timeout_partial(c, head, buf), batch(rest))))
            case Conn.Eof{}:
              Bool.and(Bool.or(Bool.or(done, Bool.or(Bool.not(String.contains(buf, "\r\n\r\n")), head_redirect(c, buf))),
                  Bool.or(is_done_parse(parse_eof(c_mb(c), head, buf)), fails_with("unexpected EOF", timeout_partial(c, head, buf), batch(rest)))),
                chk_fail(rest, c, r, done, first, head, buf))
            case Conn.OpenFailed{m}:
              Bool.or(done, fails_with(dial_text(r, m), None{}, batch(rest)))
            case Conn.Got{d}:
              chk_fail(rest, c, r, done, first, head, buf ++ d)
            case _:
              chk_fail(rest, c, r, done, first, head, buf)
        case CICmd{k}:
          match k:
            case Conn.Send{d}:
              Bool.or(is_fresh(first, d), chk_fail(rest, c, r, done, Some{d}, String.starts_with(d, "HEAD "), ""))
            case Conn.Finish{o, keep}:
              chk_fail(rest, c, r, True{}, first, head, buf)
            case _:
              chk_fail(rest, c, r, done, first, head, buf)

# LAW: timeouts, failed dials and bodies cut short, with Go's words
law conn_fail:
  for +c: Conn.Cfg
  for +r: Conn.Req
  for +open: Bool
  for +evs: List<&2, Conn.Ev>
  {chk_fail(ctimeline(c, r, open, evs), c, r, False{}, None{}, False{}, "") == True{} : Bool}

def has_key_ci(+k: String, hs: List<&2, Hdr.Header>) -> Bool:
  Maybe.is_some(&2, List<&2, String>, hdr_get_ci(k, hs))

# Go's isReplayable: a request it may send again on a new connection
def replayable(+t: Tgt.Target) -> Bool:
  +m = tgt_method(t)
  Bool.or(Bool.or(Bool.or(String.eq(m, "GET"), String.eq(m, "HEAD")), Bool.or(String.eq(m, "OPTIONS"), String.eq(m, "TRACE"))),
    Bool.or(has_key_ci("Idempotency-Key", tgt_hdrs(t)), has_key_ci("X-Idempotency-Key", tgt_hdrs(t))))

def count_send(+d: String, xs: List<&2, CItem>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          count_send(d, rest)
        case CICmd{k}:
          match k:
            case Conn.Send{d2}:
              Nat.add(pick(Nat, String.eq(d, d2), 1n, 0n), count_send(d, rest))
            case _:
              count_send(d, rest)

def opens(cs: List<&2, Conn.Cmd>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+k, +rest}:
      match k:
        case Conn.Open{ip, p}:
          True{}
        case _:
          opens(rest)

def lost_now(+may: Bool, +sent: Nat, +got: Bool) -> Bool:
  Bool.and(Bool.and(may, Nat.is_eq(sent, 1n)), Bool.not(got))

# Go retries exactly when a request it may replay was lost on a reused
# connection before any byte of an answer: the connection closed, or the
# write failed, after the first send. The retry reconnects at once.
def chk_retry(xs: List<&2, CItem>, +may: Bool, +sent: Nat, +got: Bool) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          match e:
            case Conn.Got{d}:
              chk_retry(rest, may, sent, Bool.or(got, Bool.not(String.is_empty(d))))
            case Conn.Eof{}:
              Bool.and(Bool.or(Bool.not(lost_now(may, sent, got)), opens(batch(rest))), chk_retry(rest, may, sent, got))
            case Conn.SendFailed{m}:
              Bool.and(Bool.or(Bool.not(lost_now(may, sent, got)), opens(batch(rest))), chk_retry(rest, may, sent, got))
            case _:
              chk_retry(rest, may, sent, got)
        case CICmd{k}:
          match k:
            case Conn.Send{d}:
              chk_retry(rest, may, 1n+sent, got)
            case _:
              chk_retry(rest, may, sent, got)

# after the first send: was there a failure before any byte came back?
def lost_unanswered(xs: List<&2, CItem>, +sent: Bool, +got: Bool) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          match e:
            case Conn.Got{d}:
              lost_unanswered(rest, sent, Bool.or(got, Bool.not(String.is_empty(d))))
            case Conn.Eof{}:
              Bool.or(Bool.and(sent, Bool.not(got)), lost_unanswered(rest, sent, got))
            case Conn.SendFailed{m}:
              Bool.or(Bool.and(sent, Bool.not(got)), lost_unanswered(rest, sent, got))
            case _:
              lost_unanswered(rest, sent, got)
        case CICmd{k}:
          match k:
            case Conn.Send{d}:
              pick(Bool, sent, False{}, lost_unanswered(rest, True{}, got))
            case _:
              lost_unanswered(rest, sent, got)

# LAW: a request goes out at most twice, and the second time exactly
# when Go would retry it (see chk_retry)
law conn_retry:
  for +c: Conn.Cfg
  for +r: Conn.Req
  for +open: Bool
  for +evs: List<&2, Conn.Ev>
  {Nat.is_le(count_send(q_text(c, r), ctimeline(c, r, open, evs)),
     pick(Nat, Bool.and(Bool.and(open, replayable(q_target(r))), lost_unanswered(ctimeline(c, r, open, evs), False{}, False{})), 2n, 1n)) == True{} : Bool}
  & {chk_retry(ctimeline(c, r, open, evs), Bool.and(open, replayable(q_target(r))), 0n, False{}) == True{} : Bool}

# Go's redirectBehavior: 301, 302 and 303 turn every method but GET and
# HEAD into GET and drop the body; 307 and 308 keep method and body
def redirect_method(+code: Nat, +m: String) -> String:
  pick(String, Bool.and(Bool.or(Bool.or(Nat.is_eq(code, 301n), Nat.is_eq(code, 302n)), Nat.is_eq(code, 303n)),
      Bool.not(Bool.or(String.eq(m, "GET"), String.eq(m, "HEAD")))), "GET", m)

def redirect_body(+code: Nat, +b: String) -> String:
  pick(String, Bool.or(Nat.is_eq(code, 307n), Nat.is_eq(code, 308n)), b, "")








def location(+r: Http.Resp) -> String:
  first_val("Location", r_hdrs(r), "")

def lower_host(+s: String) -> String:
  String.to_lower(s)

# Go's shouldCopyHeaderOnRedirect: credentials go along only to the same
# host or one of its subdomains (ports aside, case aside)
def same_domain(+src: String, +dst: String) -> Bool:
  +a = lower_host(src)
  +b = lower_host(dst)
  Bool.or(String.eq(a, b), String.ends_with(b, "." ++ a))

def sensitive() -> List<&2, String>:
  ["Authorization", "Www-Authenticate", "Cookie", "Cookie2", "Proxy-Authorization", "Proxy-Authenticate"]

def body_hdrs() -> List<&2, String>:
  ["Content-Type", "Content-Encoding", "Content-Language", "Content-Location"]

def drop_all_ci(ks: List<&2, String>, +hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match ks:
    case Nil{}:
      hs
    case Con{+k, +rest}:
      drop_all_ci(rest, drop_ci(k, hs))

def before_slash(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      pick(String, Bool.or(U32.is_eq(code(c), 47), U32.is_eq(code(c), 63)), "", SCon{c, before_slash(rest)})

def before_colon(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 58), "", SCon{c, before_colon(rest)})

def host_of_url(+s: String) -> String:
  +r = String.drop(s, pick(Nat, String.starts_with(String.to_lower(s), "https://"), 8n, 7n))
  before_colon(before_slash(r))



# the target of the redirect r gets for request t at u, as Go builds it:
# Go's method rules; the headers copied, less credentials when the host
# changes to one outside the original request's domain (Go compares every
# hop with the first request: once stripped, they stay stripped) and less the body's own
# headers when the body is dropped; and a Referer naming the URL
# redirected from, unless the request set its own
def redirect_target(+orig: String, +t: Tgt.Target, +u: Tgt.Url, +r: Http.Resp) -> Tgt.Target:
  +next = loc_url(u, location(r))
  +keep_body = Bool.or(Nat.is_eq(r_code(r), 307n), Nat.is_eq(r_code(r), 308n))
  +hs1 = pick(List<&2, Hdr.Header>, same_domain(orig, host_of_url(next)), tgt_hdrs(t), drop_all_ci(sensitive(), tgt_hdrs(t)))
  +hs2 = pick(List<&2, Hdr.Header>, keep_body, hs1, drop_all_ci(body_hdrs(), hs1))
  +hs3 = pick(List<&2, Hdr.Header>, has_key_ci("Referer", hs2), hs2, List.append(&2, Hdr.Header, hs2, [Hdr.Header{"Referer", [tgt_url(t)]}]))
  Tgt.Target{redirect_method(r_code(r), tgt_method(t)), next, hs3, tgt_body(t)}

def u_of(+d: Tgt.Url, r: Result<&2, &2, String, Tgt.Url>) -> Tgt.Url:
  match r:
    case Done{u}:
      u
    case Fail{e}:
      d

# one hop: from the request (t at u with body b) and the response bytes,
# the next request, if the response is a redirect with a usable Location
type Hop is Data:
  Hop{ok: Bool, t: Tgt.Target, u: Tgt.Url, b: String, code: Nat}

# the redirect a head announces, as a response (its code and Location)
def head_resp(+buf: String) -> Http.Resp:
  Http.Resp{head_code(buf), "", [Hdr.Header{"Location", [head_location(buf)]}], "", False{}}

def digits_of(+v: String) -> Maybe<&2, Nat>:
  pick(Maybe<&2, Nat>, all_digits(v), Some{digits_value(v)}, None{})

def head_cl(ls: List<&2, String>) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      None{}
    case Con{+l, +rest}:
      +kv = split_on(58, strip_cr(l))
      pick(Maybe<&2, Nat>, String.eq(canon(trim_ows(Maybe.default(&2, String, List.head(&2, String, kv), ""))), "Content-Length"),
        digits_of(trim_ows(String.drop(strip_cr(l), 1n+String.length(Maybe.default(&2, String, List.head(&2, String, kv), ""))))),
        head_cl(rest))

def big_body(+m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      Nat.is_gt(n, 2048n)

# Go is done with a redirect's body once it is complete, once 2048 bytes
# of it are read, or at once when its length is over 2048 (io.CopyN of at
# most maxBodySlurpSize, skipped for a larger Content-Length)
def drained(+c: Conn.Cfg, +head: Bool, +buf: String, +eof: Bool) -> Bool:
  Bool.or(Bool.or(big_body(head_cl(List.drop(&2, String, split_on(10, head_text(buf)), 1n))), eof),
    Bool.or(is_done_parse(parse_of(None{}, head, buf)),
      Nat.is_ge(String.length(Http.partial(Http.feed(Http.start(None{}, head), buf))), 2048n)))

def hop_of_head(+orig: String, +t: Tgt.Target, +u: Tgt.Url, +b: String, +buf: String) -> Hop:
  +r = head_resp(buf)
  +nt = redirect_target(orig, t, u, r)
  +ok = Bool.and(is_redirect(r), Result.is_done(&2, &2, String, Tgt.Url, Tgt.parse_url(tgt_url(nt))))
  Hop{ok, nt, u_of(u, Tgt.parse_url(tgt_url(nt))), redirect_body(r_code(r), b), r_code(r)}


def hop_ok(+h: Hop) -> Bool:
  Hop{ok, t, u, b, c} = h
  ok

def hop_t(+h: Hop) -> Tgt.Target:
  Hop{ok, t, u, b, c} = h
  t

def hop_u(+h: Hop) -> Tgt.Url:
  Hop{ok, t, u, b, c} = h
  u

def hop_b(+h: Hop) -> String:
  Hop{ok, t, u, b, c} = h
  b

def progresses(cs: List<&2, Conn.Cmd>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{+k, +rest}:
      match k:
        case Conn.Resolve{h}:
          True{}
        case Conn.Open{ip, p}:
          True{}
        case Conn.Send{d}:
          True{}
        case _:
          progresses(rest)






# a redirect under -redirects=n, once Go is done with its body: below the
# limit the client goes on to the next hop at once; at the limit it fails
# as Go's CheckRedirect
def redirect_due(+c: Conn.Cfg, +q: Conn.Req, +t: Tgt.Target, +u: Tgt.Url, +b: String, +hops: Nat, +head: Bool, +buf: String, +eof: Bool, +rest: List<&2, CItem>) -> Bool:
  +n = rd_limit(c_redirects(c))
  Bool.or(Bool.not(Bool.and(head_redirect(c, buf), drained(c, head, buf, eof))),
    pick(Bool, Nat.is_lt(hops, n), Bool.or(Bool.not(hop_ok(hop_of_head(u_host(q_url(q)), t, u, b, buf))), progresses(batch(rest))),
      fails_with(stop_text(q, head_location(buf), n), None{}, batch(rest))))

# the redirect in the bytes so far is one the client acts on now
def due_now(+c: Conn.Cfg, +head: Bool, +buf: String, +eof: Bool) -> Bool:
  Bool.and(head_redirect(c, buf), drained(c, head, buf, eof))

# every new request after the first is the redirect of the previous
# response, once Go is done with its body (a repeat of the same text is a
# retry); the obligation to act on a redirect holds once per hop (met)
# and never after the request finishes (done)
def chk_redirect(xs: List<&2, CItem>, +c: Conn.Cfg, +q: Conn.Req, +t: Tgt.Target, +u: Tgt.Url, +b: String,
                 +last: Maybe<&2, String>, +hops: Nat, +head: Bool, +buf: String, +eof: Bool, +met: Bool, +done: Bool) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          match e:
            case Conn.Got{d}:
              Bool.and(Bool.or(Bool.or(met, done), redirect_due(c, q, t, u, b, hops, head, buf ++ d, eof, rest)),
                chk_redirect(rest, c, q, t, u, b, last, hops, head, buf ++ d, eof, Bool.or(met, due_now(c, head, buf ++ d, eof)), done))
            case Conn.Eof{}:
              Bool.and(Bool.or(Bool.or(met, done), redirect_due(c, q, t, u, b, hops, head, buf, True{}, rest)),
                chk_redirect(rest, c, q, t, u, b, last, hops, head, buf, True{}, Bool.or(met, due_now(c, head, buf, True{})), done))
            case _:
              chk_redirect(rest, c, q, t, u, b, last, hops, head, buf, eof, met, done)
        case CICmd{k}:
          match k:
            case Conn.Send{d}:
              +hop = hop_of_head(u_host(q_url(q)), t, u, b, buf)
              +fresh = is_fresh(last, d)
              pick(Bool, fresh,
                Bool.and(Bool.and(Bool.and(hop_ok(hop), due_now(c, head, buf, eof)), Nat.is_lt(hops, rd_limit(c_redirects(c)))),
                  Bool.and(String.eq(d, Http.request(hop_t(hop), hop_u(hop), hop_b(hop), q_seq(q), q_name(q), c_ka(c))),
                    chk_redirect(rest, c, q, hop_t(hop), hop_u(hop), hop_b(hop), Some{d}, 1n+hops, String.starts_with(d, "HEAD "), "", False{}, False{}, done))),
                chk_redirect(rest, c, q, t, u, b, Some{d}, hops, String.starts_with(d, "HEAD "), "", False{}, False{}, done))
            case Conn.Finish{o, keep}:
              chk_redirect(rest, c, q, t, u, b, last, hops, head, buf, eof, met, True{})
            case _:
              chk_redirect(rest, c, q, t, u, b, last, hops, head, buf, eof, met, done)

law conn_redirect:
  for +c: Conn.Cfg
  for +q: Conn.Req
  for +open: Bool
  for +evs: List<&2, Conn.Ev>
  {chk_redirect(ctimeline(c, q, open, evs), c, q, q_target(q), q_url(q), q_body(q), None{}, 0n, False{}, "", False{}, False{}, False{}) == True{} : Bool}

# the commands after the last event
def last_batch(xs: List<&2, CItem>, +acc: List<&2, Conn.Cmd>) -> List<&2, Conn.Cmd>:
  match xs:
    case Nil{}:
      acc
    case Con{+x, +rest}:
      match x:
        case CIEv{e}:
          last_batch(rest, [])
        case CICmd{k}:
          last_batch(rest, List.append(&2, Conn.Cmd, acc, [k]))

# LAW: on a fresh connection, a close before any answer is Go's EOF error
law conn_eof:
  for +c: Conn.Cfg
  for +q: Conn.Req
  {fails_with(err_prefix(q) ++ "EOF", None{},
     last_batch(ctimeline(c, q, False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Eof{}]), [])) == True{} : Bool}

# LAW: the result recorded for a request, as Go's hit() fills it in:
# success is 2xx and 3xx, and otherwise the status line is the error;
# bytes in are the body kept (after -max-body); a failure records no code,
# bytes or headers, and the body only as far as it was read
law conn_to_hit:
  for +name: String
  for +seq: Nat
  for +ts: Civil.Time
  for +lat: Nat
  for +m: String
  for +u: String
  for +nb: Nat
  for +r: Http.Resp
  for +e: String
  for +pb: Maybe<&2, String>
  {Conn.to_hit(name, seq, ts, lat, m, u, nb, Conn.Answered{r})
   == Hit.Hit{name, seq, r_code(r), ts, lat, nb, String.length(r_body(r)), pick(String, is_ok(r_code(r)), "", r_status(r)),
       Some{r_body(r)}, m, u, Some{r_hdrs(r)}} : Hit.Hit}
  & {Conn.to_hit(name, seq, ts, lat, m, u, nb, Conn.Failed{e, pb}) == Hit.Hit{name, seq, 0n, ts, lat, 0n, 0n, e, pb, m, u, None{}} : Hit.Hit}

# =====================================================================
# Text at the edges (lib/text.bend)
# =====================================================================

def utf8_char(+k: U32) -> String:
  pick(String, U32.is_lt(k, 128), str1(k),
  pick(String, U32.is_lt(k, 2048), str1((192 .|. (k >> 6n) : U32)) ++ str1((128 .|. (k .&. 63) : U32)),
  pick(String, U32.is_lt(k, 65536), str1((224 .|. (k >> 12n) : U32)) ++ str1((128 .|. ((k >> 6n) .&. 63) : U32)) ++ str1((128 .|. (k .&. 63) : U32)),
    str1((240 .|. (k >> 18n) : U32)) ++ str1((128 .|. ((k >> 12n) .&. 63) : U32)) ++ str1((128 .|. ((k >> 6n) .&. 63) : U32)) ++ str1((128 .|. (k .&. 63) : U32)))))

def utf8_all(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      utf8_char(code(c)) ++ utf8_all(rest)

# LAW: arguments become their UTF-8 bytes, character by character
law text_utf8:
  for +s: String
  {Text.utf8(s) == utf8_all(s) : String}

# =====================================================================
# Tables (lib/tab.bend): text/tabwriter as Vegeta configures it
# =====================================================================
#
# A line is cells ended by tabs, then trailing text. A column is the j-th
# cell of a run of consecutive lines that all have one; each of its cells
# is padded with spaces to the widest in the run plus 2. Width counts
# runes (Go's utf8.RuneCount: a stray byte is one).



def runes.go(+fuel: Nat, +s: String) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      pick(Nat, String.is_empty(s), 0n, 1n+runes.go(f, String.drop(s, Nat.max(1n, utf8_len(s)))))

def runes(+s: String) -> Nat:
  runes.go(String.length(s), s)

# the cells of a line ended by tabs (all but the trailing text)
def tab_cells(+l: String) -> List<&2, String>:
  List.take(&2, String, split_on(9, l), Nat.sub(List.length(&2, String, split_on(9, l)), 1n))

def trailing(+l: String) -> String:
  Maybe.default(&2, String, List.last(&2, String, split_on(9, l)), "")

def n_cells(+l: String) -> Nat:
  List.length(&2, String, tab_cells(l))

def line_at(+ls: List<&2, String>, +i: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ls, i), "")

def cell_w(+ls: List<&2, String>, +i: Nat, +j: Nat) -> Nat:
  runes(Maybe.default(&2, String, List.get(&2, String, tab_cells(line_at(ls, i)), j), ""))

# the widest cell j from line i going up while lines have a cell j
def up_w(fuel: Nat, +ls: List<&2, String>, +i: Nat, +j: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      pick(Nat, Nat.is_gt(n_cells(line_at(ls, i)), j),
        Nat.max(cell_w(ls, i, j), pick(Nat, Nat.is_eq(i, 0n), 0n, up_w(f, ls, Nat.sub(i, 1n), j))), 0n)

def down_w(fuel: Nat, +ls: List<&2, String>, +i: Nat, +j: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      pick(Nat, Nat.is_gt(n_cells(line_at(ls, i)), j), Nat.max(cell_w(ls, i, j), down_w(f, ls, 1n+i, j)), 0n)

def col_w(+ls: List<&2, String>, +i: Nat, +j: Nat) -> Nat:
  +n = List.length(&2, String, ls)
  Nat.add(Nat.max(up_w(n, ls, i, j), down_w(n, ls, i, j)), 2n)

def pad_cells(cs: List<&2, String>, +ls: List<&2, String>, +i: Nat, +j: Nat) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{+c, +rest}:
      c ++ String.repeat(" ", Nat.sub(col_w(ls, i, j), runes(c))) ++ pad_cells(rest, ls, i, 1n+j)

def tab_lines(+fuel: Nat, +ls: List<&2, String>, +i: Nat) -> List<&2, String>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      Con{pad_cells(tab_cells(line_at(ls, i)), ls, i, 0n) ++ trailing(line_at(ls, i)), tab_lines(f, ls, 1n+i)}

def tab_text(+s: String) -> String:
  +ls = split_on(10, s)
  join_str("\n", tab_lines(List.length(&2, String, ls), ls, 0n))

# LAW: the table is its cells padded into aligned columns (for text
# without the escape, vertical-tab and form-feed bytes tabwriter treats
# specially)
law tab_render:
  for +s: String
  for -h: {Bool.or(Bool.or(has_char(s, 255), has_char(s, 11)), has_char(s, 12)) == False{} : Bool}
  {Tab.render(s) == tab_text(s) : String}

# =====================================================================
# Reports (lib/report.bend)
# =====================================================================

def dur(+n: Nat) -> String:
  Dur.show(Dur.round(n))

def fixed2(+x: F64.F64) -> String:
  F64.fixed(2n, x)

def code_of(+p: Sigma<&2, &2, Nat, _ => Nat>) -> Nat:
  (k, v) = p
  k

def insert_code(+p: Sigma<&2, &2, Nat, _ => Nat>, cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> List<&2, Sigma<&2, &2, Nat, _ => Nat>>:
  match cs:
    case Nil{}:
      [p]
    case Con{+q, +rest}:
      pick(List<&2, Sigma<&2, &2, Nat, _ => Nat>>, String.is_lt(Dec.show(code_of(p)), Dec.show(code_of(q))),
        Con{p, Con{q, rest}}, Con{q, insert_code(p, rest)})

# status codes as Go orders them: as strings ("0" < "200" < "503")
def codes_by_text(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> List<&2, Sigma<&2, &2, Nat, _ => Nat>>:
  match cs:
    case Nil{}:
      []
    case Con{+p, +rest}:
      insert_code(p, codes_by_text(rest))

def code_items(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{+p, +rest}:
      (k, v) = p
      Dec.show(k) ++ ":" ++ Dec.show(v) ++ "  " ++ code_items(rest)

def error_lines(es: List<&2, String>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{+e, +rest}:
      e ++ "\n" ++ error_lines(rest)

# Go's NewTextReporter format string, filled in
def text_src(+s: Met.Summary) -> String:
  "Requests\t[total, rate, throughput]\t" ++ Dec.show(s_requests(s)) ++ ", " ++ fixed2(s_rate(s)) ++ ", " ++ fixed2(s_throughput(s)) ++ "\n"
  ++ "Duration\t[total, attack, wait]\t" ++ dur(Nat.add(s_duration(s), s_wait(s))) ++ ", " ++ dur(s_duration(s)) ++ ", " ++ dur(s_wait(s)) ++ "\n"
  ++ "Latencies\t[min, mean, 50, 90, 95, 99, max]\t" ++ dur(s_lat_min(s)) ++ ", " ++ dur(s_lat_mean(s)) ++ ", " ++ dur(s_p50(s)) ++ ", "
     ++ dur(s_p90(s)) ++ ", " ++ dur(s_p95(s)) ++ ", " ++ dur(s_p99(s)) ++ ", " ++ dur(s_lat_max(s)) ++ "\n"
  ++ "Bytes In\t[total, mean]\t" ++ Big.show(s_bytes_in(s)) ++ ", " ++ fixed2(s_in_mean(s)) ++ "\n"
  ++ "Bytes Out\t[total, mean]\t" ++ Big.show(s_bytes_out(s)) ++ ", " ++ fixed2(s_out_mean(s)) ++ "\n"
  ++ "Success\t[ratio]\t" ++ fixed2(F64.mul(s_ratio(s), F64.of_nat(100n))) ++ "%\n"
  ++ "Status Codes\t[code:count]\t" ++ code_items(codes_by_text(s_codes(s))) ++ "\nError Set:\n" ++ error_lines(s_errors(s))

law report_text:
  for +s: Met.Summary
  {Rep.text(s) == Tab.render(text_src(s)) : String}

def with_off(+t: Civil.Time, +off: Nat) -> Civil.Time:
  Civil.Time{time_sec(t), time_nsec(t), off}

# a time as Go's JSON writes it; Go's zero time when there is none
def json_time(+m: Maybe<&2, Civil.Time>, +off: Nat) -> String:
  match m:
    case None{}:
      "\"0001-01-01T00:00:00Z\""
    case Some{t}:
      "\"" ++ Civil.rfc3339(with_off(t, off)) ++ "\""

def json_codes(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> List<&2, String>:
  match cs:
    case Nil{}:
      []
    case Con{+p, +rest}:
      (k, v) = p
      Con{"\"" ++ Dec.show(k) ++ "\":" ++ Dec.show(v), json_codes(rest)}

# Go's Histogram.MarshalJSON, compacted: each bound in ns and its count
def json_buckets(bs: List<&2, Nat>, +cs: List<&2, Nat>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{+b, +rest}:
      Con{"\"" ++ Dec.show(b) ++ "\":" ++ Dec.show(head_or(0n, cs)), json_buckets(rest, List.drop(&2, Nat, cs, 1n))}

def z_e(+z: Rep.Zones) -> Nat:
  Rep.Zones{e, l, n} = z
  e

def z_l(+z: Rep.Zones) -> Nat:
  Rep.Zones{e, l, n} = z
  l

def z_n(+z: Rep.Zones) -> Nat:
  Rep.Zones{e, l, n} = z
  n



def rjesc_ff(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, +rest}:
      match rest:
        case Nil{}:
          jesc(p)
        case Con{+q, +more}:
          jesc(p) ++ "\\f" ++ rjesc_ff(Con{q, more})

def rjesc_parts(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, +rest}:
      match rest:
        case Nil{}:
          rjesc_ff(split_on(12, p))
        case Con{+q, +more}:
          rjesc_ff(split_on(12, p)) ++ "\\b" ++ rjesc_parts(Con{q, more})

# escape run by run: control bytes 8 and 12 short, the rest as easyjson
def rjesc_str(+s: String) -> String:
  pick(String, Bool.or(has_char(s, 8), has_char(s, 12)), rjesc_parts(split_on(8, s)), jesc(s))

# encoding/json's string: easyjson's, but \b and \f are short escapes
def rjson_str(+s: String) -> String:
  "\"" ++ rjesc_str(s) ++ "\""

def rjson_strs(vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{+v, +rest}:
      Con{rjson_str(v), rjson_strs(rest)}

# Go's JSON reporter: encoding/json of Metrics, fields in struct order,
# status codes sorted as strings, times in the local zone
def json_src(+s: Met.Summary, +z: Rep.Zones) -> String:
  "{\"latencies\":{\"total\":" ++ Big.show(s_lat_total(s)) ++ ",\"mean\":" ++ Dec.show(s_lat_mean(s))
  ++ ",\"50th\":" ++ Dec.show(s_p50(s)) ++ ",\"90th\":" ++ Dec.show(s_p90(s)) ++ ",\"95th\":" ++ Dec.show(s_p95(s))
  ++ ",\"99th\":" ++ Dec.show(s_p99(s)) ++ ",\"max\":" ++ Dec.show(s_lat_max(s)) ++ ",\"min\":" ++ Dec.show(s_lat_min(s)) ++ "}"
  ++ pick(String, List.is_empty(&2, Nat, s_buckets(s)), "", ",\"buckets\":{" ++ join_str(",", json_buckets(s_buckets(s), s_hist(s))) ++ "}")
  ++ ",\"bytes_in\":{\"total\":" ++ Big.show(s_bytes_in(s)) ++ ",\"mean\":" ++ F64.json(s_in_mean(s)) ++ "}"
  ++ ",\"bytes_out\":{\"total\":" ++ Big.show(s_bytes_out(s)) ++ ",\"mean\":" ++ F64.json(s_out_mean(s)) ++ "}"
  ++ ",\"earliest\":" ++ json_time(s_earliest(s), z_e(z)) ++ ",\"latest\":" ++ json_time(s_latest(s), z_l(z))
  ++ ",\"end\":" ++ json_time(s_end(s), z_n(z))
  ++ ",\"duration\":" ++ Dec.show(s_duration(s)) ++ ",\"wait\":" ++ Dec.show(s_wait(s))
  ++ ",\"requests\":" ++ Dec.show(s_requests(s)) ++ ",\"rate\":" ++ F64.json(s_rate(s))
  ++ ",\"throughput\":" ++ F64.json(s_throughput(s)) ++ ",\"success\":" ++ F64.json(s_ratio(s))
  ++ ",\"status_codes\":{" ++ join_str(",", json_codes(codes_by_text(s_codes(s)))) ++ "}"
  ++ ",\"errors\":[" ++ join_str(",", rjson_strs(s_errors(s))) ++ "]}\n"

law report_json:
  for +s: Met.Summary
  for +z: Rep.Zones
  {Rep.json(s, z) == json_src(s, z) : String}

# a bucket's upper bound: the next bucket's lower one, or +Inf
def upper_bound(+bs: List<&2, Nat>) -> String:
  match bs:
    case Nil{}:
      "+Inf"
    case Con{+b, +rest}:
      Dur.show(b)

def hist_rows(bs: List<&2, Nat>, +cs: List<&2, Nat>, +total: Nat) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, +rest}:
      +n = head_or(0n, cs)
      +ratio = F64.div(F64.of_nat(n), F64.of_nat(total))
      "[" ++ Dur.show(b) ++ ",\t" ++ upper_bound(rest) ++ "]\t"
        ++ Dec.show(n) ++ "\t" ++ fixed2(F64.mul(ratio, F64.of_nat(100n))) ++ "%\t"
        ++ String.repeat("#", F64.trunc(F64.mul(ratio, F64.of_nat(75n)))) ++ "\n"
        ++ hist_rows(rest, List.drop(&2, Nat, cs, 1n), total)

# Go's NewHistogramReporter (for at least one request: Go divides by the total)
law report_hist:
  for +s: Met.Summary
  for -h: {Nat.is_gt(s_requests(s), 0n) == True{} : Bool}
  {Rep.hist(s) == Tab.render("Bucket\t\t#\t%\tHistogram\n" ++ hist_rows(s_buckets(s), s_hist(s), s_requests(s))) : String}

# =====================================================================
# Flags (lib/flags.bend): Go Vegeta's names, defaults and errors
# =====================================================================

def attack_defaults() -> Flags.Attack:
  Flags.Attack{Pace.Rate{50n, sec()}, 0n, "stdin", "http", "stdout", "", 10n, None{}, None{},
    [], None{}, True{}, None{}, Some{10n}, "csv"}

# LAW: no flags, Go's defaults (and CSV results; no timeout is Go's 30s,
# applied by the shell)
law flags_attack_defaults:
  {Flags.parse_attack([]) == Done{attack_defaults()} : Result<&2, &2, String, Flags.Attack>}

def rate_text(+r: Pace.Rate) -> String:
  Pace.Rate{f, p} = r
  pick(String, Bool.or(Nat.is_eq(f, 0n), Nat.is_eq(p, 0n)), "infinity", Dec.show(f) ++ "/" ++ Dur.show(p))

def opt_nat(+flag: String, +none: String, +m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      flag ++ none
    case Some{n}:
      flag ++ Dec.show(n)

def hdr_val_flags(+k: String, vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{+v, +rest}:
      Con{"-header=" ++ k ++ ": " ++ v, hdr_val_flags(k, rest)}

def hdr_flags(hs: List<&2, Hdr.Header>) -> List<&2, String>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      List.append(&2, String, hdr_val_flags(hdr_key(h), hdr_vals(h)), hdr_flags(rest))

def body_flag(+b: Maybe<&2, String>) -> List<&2, String>:
  match b:
    case None{}:
      []
    case Some{p}:
      ["-body=" ++ p]

def max_workers_flag(+m: Maybe<&2, Nat>) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{n}:
      ["-max-workers=" ++ Dec.show(n)]

def timeout_flag(+m: Maybe<&2, Nat>) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{n}:
      ["-timeout=" ++ Dur.show(n)]

# the canonical command line for some options
def attack_args(+a: Flags.Attack) -> List<&2, String>:
  Flags.Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  List.concat(&2, String, [
    ["-rate=" ++ rate_text(rate), "-duration=" ++ Dur.show(du), "-targets=" ++ tg, "-format=" ++ fm, "-output=" ++ out,
     "-name=" ++ name, "-workers=" ++ Dec.show(w)],
    max_workers_flag(mw), timeout_flag(to), hdr_flags(hs), body_flag(body),
    ["-keepalive=" ++ pick(String, ka, "true", "false"), opt_nat("-max-body=", "-1", mb), opt_nat("-redirects=", "-1", rd), "-encoding=" ++ enc]])

def flag_str_ok(+s: String) -> Bool:
  Bool.and(printable(s), Bool.not(String.is_empty(s)))

def rate_ok(+r: Pace.Rate) -> Bool:
  Pace.Rate{f, p} = r
  Bool.or(Bool.and(Nat.is_eq(f, 0n), Nat.is_eq(p, 0n)), Bool.and(Nat.is_gt(f, 0n), Nat.is_gt(p, 0n)))

# options a command line can carry: printable values, an http format, a
# known encoding, and headers as -header can write them
def attack_ok(+a: Flags.Attack) -> Bool:
  Flags.Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Bool.and(Bool.and(rate_ok(rate), Bool.and(flag_str_ok(tg), flag_str_ok(out))),
  Bool.and(Bool.and(printable(name), String.eq(fm, "http")),
  Bool.and(Bool.and(tgt_hdrs_ok(hs), body_path_ok(body)), Bool.or(String.eq(enc, "csv"), String.eq(enc, "json")))))

# LAW: options survive their command line
law flags_attack_roundtrip:
  for +a: Flags.Attack
  for -h: {attack_ok(a) == True{} : Bool}
  {Flags.parse_attack(attack_args(a)) == Done{a} : Result<&2, &2, String, Flags.Attack>}

# the flags that take a value
def value_flags() -> List<&2, String>:
  ["rate", "duration", "targets", "format", "output", "name", "workers", "max-workers", "timeout", "header",
   "body", "max-body", "redirects", "encoding"]

def nth_str(+i: Nat, +xs: List<&2, String>) -> String:
  Maybe.default(&2, String, List.get(&2, String, xs, i), "")

# LAW: as with Go's flag package, "-k=v", "-k v", "--k=v" and "--k v" are one
law flags_forms:
  for +i: Nat
  for +v: String
  for +rest: List<&2, String>
  for -h: {Nat.is_lt(i, 14n) == True{} : Bool}
  {Flags.parse_attack(Con{"-" ++ nth_str(i, value_flags()), Con{v, rest}}) == Flags.parse_attack(Con{"-" ++ nth_str(i, value_flags()) ++ "=" ++ v, rest}) : Result<&2, &2, String, Flags.Attack>}
  & {Flags.parse_attack(Con{"--" ++ nth_str(i, value_flags()) ++ "=" ++ v, rest}) == Flags.parse_attack(Con{"-" ++ nth_str(i, value_flags()) ++ "=" ++ v, rest}) : Result<&2, &2, String, Flags.Attack>}
  & {Flags.parse_attack(["-keepalive"]) == Flags.parse_attack(["-keepalive=true"]) : Result<&2, &2, String, Flags.Attack>}

# Go Vegeta's attack flags this port does not implement
def unsupported() -> List<&2, String>:
  ["http2", "h2c", "insecure", "lazy", "cert", "key", "root-certs", "chunked", "laddr", "unix-socket",
   "prometheus-addr", "dns-ttl", "session-tickets", "connect-to", "proxy-header", "resolvers",
   "connections", "max-connections"]

# LAW: a Go flag this port lacks is refused by name, and an unknown one as
# Go's flag package words it
law flags_refused:
  for +i: Nat
  for +f: String
  for +rest: List<&2, String>
  for -h0: {Nat.is_lt(i, 18n) == True{} : Bool}
  for -h1: {Bool.and(Bool.and(Bool.and(flag_str_ok(f), Bool.not(has_char(f, 61))), Bool.not(first_is(f, 45))),
     Bool.not(Bool.or(Bool.or(has_str(f, value_flags()), has_str(f, unsupported())),
       Bool.or(String.eq(f, "keepalive"), Bool.or(String.eq(f, "h"), String.eq(f, "help")))))) == True{} : Bool}
  {Flags.parse_attack(Con{"-" ++ nth_str(i, unsupported()), rest}) == Fail{"flag not supported in the Bend port: -" ++ nth_str(i, unsupported())} : Result<&2, &2, String, Flags.Attack>}
  & {Flags.parse_attack(Con{"-" ++ f, rest}) == Fail{"flag provided but not defined: -" ++ f} : Result<&2, &2, String, Flags.Attack>}

# LAW: -rate=infinity is no rate at all to Go's flag (it keeps the
# default), and an unbounded rate needs a worker limit
law flags_rate:
  {Flags.parse_attack(["-rate=infinity"]) == Flags.parse_attack([]) : Result<&2, &2, String, Flags.Attack>}
  & {Flags.parse_attack(["-rate=0"]) == Fail{"-rate=0 requires setting -max-workers"} : Result<&2, &2, String, Flags.Attack>}

# LAW: -header is Go's: split at the first colon, both sides trimmed and
# non-empty, values appended under the name as written
law flags_header:
  for +k: String
  for +v: String
  for +x: String
  for -h0: {Bool.and(tgt_key_ok(k), Bool.and(flag_str_ok(v), String.eq(trim_ows(v), v))) == True{} : Bool}
  for -h1: {Bool.and(printable(x), Bool.not(has_char(x, 58))) == True{} : Bool}
  {Flags.parse_attack(["-header", k ++ ": " ++ v, "-header", k ++ ":" ++ v])
   == Done{Flags.Attack{Pace.Rate{50n, sec()}, 0n, "stdin", "http", "stdout", "", 10n, None{}, None{},
        [Hdr.Header{k, [v, v]}], None{}, True{}, None{}, Some{10n}, "csv"}} : Result<&2, &2, String, Flags.Attack>}
  & {Flags.parse_attack(["-header", x]) == Fail{"header '" ++ x ++ "' has a wrong format"} : Result<&2, &2, String, Flags.Attack>}

# Go's Buckets.UnmarshalText: a 0 bucket is added in front of a positive first bound
def with_zero(+bs: List<&2, Nat>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      []
    case Con{+b, +rest}:
      pick(List<&2, Nat>, Nat.is_gt(b, 0n), Con{0n, Con{b, rest}}, Con{b, rest})

def dur_texts(bs: List<&2, Nat>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{+b, +rest}:
      Con{Dur.show(b), dur_texts(rest)}

def buckets_text(+bs: List<&2, Nat>) -> String:
  "[" ++ join_str(",", dur_texts(bs)) ++ "]"

# LAW: report's flags: text to stdout by default; json, and json or a
# histogram over buckets (given in the type or in -buckets); files are the
# arguments after the flags; unsupported types and -every are refused
law flags_report:
  for +bs: List<&2, Nat>
  for +files: List<&2, String>
  for +out: String
  for -h0: {Bool.not(List.is_empty(&2, Nat, bs)) == True{} : Bool}
  for -h1: {Bool.and(all_bytes(files), Bool.not(List.any(~&2, ~String, ~(f => String.starts_with(f, "-")), files))) == True{} : Bool}
  for -h2: {flag_str_ok(out) == True{} : Bool}
  {Flags.parse_report(files) == Done{Flags.Report{Flags.AsText{}, "stdout", files}} : Result<&2, &2, String, Flags.Report>}
  & {Flags.parse_report(Con{"-type=json", Con{"-output=" ++ out, files}}) == Done{Flags.Report{Flags.AsJson{[]}, out, files}} : Result<&2, &2, String, Flags.Report>}
  & {Flags.parse_report(Con{"-type=json", Con{"-buckets=" ++ buckets_text(bs), files}}) == Done{Flags.Report{Flags.AsJson{with_zero(bs)}, "stdout", files}} : Result<&2, &2, String, Flags.Report>}
  & {Flags.parse_report(Con{"-type=hist" ++ buckets_text(bs), files}) == Done{Flags.Report{Flags.AsHist{with_zero(bs)}, "stdout", files}} : Result<&2, &2, String, Flags.Report>}
  & {Flags.parse_report(Con{"-type=hist", Con{"-buckets=" ++ buckets_text(bs), files}}) == Done{Flags.Report{Flags.AsHist{with_zero(bs)}, "stdout", files}} : Result<&2, &2, String, Flags.Report>}
  & {Flags.parse_report(Con{"-type=hdrplot", files}) == Fail{"report type not supported in the Bend port: hdrplot"} : Result<&2, &2, String, Flags.Report>}
  & {Flags.parse_report(Con{"-every=1s", files}) == Fail{"flag not supported in the Bend port: -every"} : Result<&2, &2, String, Flags.Report>}

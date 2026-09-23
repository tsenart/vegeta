# The constant rate: freq hits per `per` ns; freq = 0 or per = 0 is unbounded.
#
# parse_rate reads -rate as Go Vegeta's rateFlag.Set: "N" is N per second,
# "N/D" N per duration D, where a bare unit ("50/m") counts once; a zero
# frequency is unbounded whatever follows. Errors are Go's texts
# (strconv.Atoi's, time.ParseDuration's). A negative frequency, which Go
# takes and then paces nonsensically, is refused. ("infinity", which Go's
# flag ignores, is the flags' business: see lib/flags.bend.)
import Base
import ./dec.bend as Dec
import ./dur.bend as Dur

type Rate is Data:
  Rate{freq: Nat, per: Nat}

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

# s cut at its first "/": what comes before and after it (after is None
# when there is no "/")
type Cut is Data:
  Cut{head: String, tail: Maybe<&2, String>}

def cut_head(+c: Cut) -> String:
  Cut{h, t} = c
  h

def cut_tail(+c: Cut) -> Maybe<&2, String>:
  Cut{h, t} = c
  t

def cut_cons(+c: Char, +r: Cut) -> Cut:
  Cut{h, t} = r
  Cut{SCon{c, h}, t}

def cut(s: String) -> Cut:
  match s:
    case SNil{}:
      Cut{"", None{}}
    case SCon{+c, +rest}:
      pick(Cut, U32.is_eq(code(c), 47), Cut{"", Some{rest}}, cut_cons(c, cut(rest)))

# Go's %q for the texts at hand: quotes and backslashes escaped
def quote.go(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      pick(String, Bool.or(U32.is_eq(code(c), 34), U32.is_eq(code(c), 92)), "\\" ++ SCon{c, SNil{}}, SCon{c, SNil{}}) ++ quote.go(rest)

def quote(+s: String) -> String:
  "\"" ++ quote.go(s) ++ "\""

def atoi_error(+f: String) -> String:
  "strconv.Atoi: parsing " ++ quote(f) ++ ": invalid syntax"

# the digits after an optional sign
def unsigned(+f: String) -> String:
  pick(String, Bool.or(first_is(f, 43), first_is(f, 45)), String.drop(f, 1n), f)

# the units Go's rateFlag gives a count of 1 ("μs", the Greek mu, is not one)
def bare_unit(+u: String) -> Bool:
  Bool.or(Bool.or(Bool.or(String.eq(u, "ns"), String.eq(u, "us")), Bool.or(String.eq(u, Dur.micro() ++ "s"), String.eq(u, "ms"))),
    Bool.or(Bool.or(String.eq(u, "s"), String.eq(u, "m")), String.eq(u, "h")))

def per_text(+u: String) -> String:
  pick(String, bare_unit(u), "1" ++ u, u)

def hexd(+n: U32) -> String:
  SCon{Chr{pick(U32, U32.is_lt(n, 10), (n + 48 : U32), (n + 87 : U32))}, SNil{}}

# Go's time.quote: bytes outside printable ASCII as \xhh
def tquote.c(+k: U32) -> String:
  pick(String, Bool.or(U32.is_lt(k, 32), U32.is_ge(k, 128)), "\\x" ++ hexd((k >> 4n : U32)) ++ hexd((k .&. 15 : U32)),
    pick(String, Bool.or(U32.is_eq(k, 34), U32.is_eq(k, 92)), "\\" ++ SCon{Chr{k}, SNil{}}, SCon{Chr{k}, SNil{}}))

def tquote.go(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      tquote.c(code(c)) ++ tquote.go(rest)

def tquote(+s: String) -> String:
  "\"" ++ tquote.go(s) ++ "\""

# what time.ParseDuration says of the first term it cannot read: no
# number, no unit, or an unknown one ("" when every term reads: the
# duration is out of range, or negative, which the port refuses)
type Why is Data:
  Why{text: String, rest: String}

def why_text(+w: Why) -> String:
  Why{t, r} = w
  t

def why_rest(+w: Why) -> String:
  Why{t, r} = w
  r

def term_why(+s: String) -> Why:
  +p = Dur.span_digits(s)
  +dot = first_is(Dur.SS.b(p), 46)
  +q = Dur.span_digits(pick(String, dot, String.drop(Dur.SS.b(p), 1n), Dur.SS.b(p)))
  +num = Bool.or(Bool.not(String.is_empty(Dur.SS.a(p))), Bool.and(dot, Bool.not(String.is_empty(Dur.SS.a(q)))))
  +u = Dur.span_unit(Dur.SS.b(q))
  +unit = Dur.SS.a(u)
  Why{pick(String, Bool.not(num), "invalid",
      pick(String, String.is_empty(unit), "missing", pick(String, Dur.is_unit_name(unit), "", "unknown unit " ++ tquote(unit)))),
    Dur.SS.b(u)}

def terms_why(fuel: Nat, stop: Bool, +s: String, +acc: String) -> String:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match stop:
        case True{}:
          acc
        case False{}:
          +w = term_why(s)
          terms_why(f, Bool.or(Bool.not(String.is_empty(why_text(w))), String.is_empty(why_rest(w))), why_rest(w), why_text(w))

def dur_error(+d: String) -> String:
  +t = pick(String, Bool.or(first_is(d, 43), first_is(d, 45)), String.drop(d, 1n), d)
  +w = pick(String, String.is_empty(t), "invalid", terms_why(String.length(t), False{}, t, ""))
  pick(String, String.eq(w, "missing"), "time: missing unit in duration " ++ tquote(d),
    pick(String, String.starts_with(w, "unknown"), "time: " ++ w ++ " in duration " ++ tquote(d), "time: invalid duration " ++ tquote(d)))

def with_per(d: Maybe<&2, Nat>, +f: Nat, +text: String) -> Result<&2, &2, String, Rate>:
  match d:
    case None{}:
      Fail{dur_error(text)}
    case Some{p}:
      Done{Rate{f, p}}

# no "/": per second, 1s (a literal, not a parse: the checker would
# expand the parsed 10^9 into a unary Nat)
def with_tail(t: Maybe<&2, String>, +f: Nat) -> Result<&2, &2, String, Rate>:
  match t:
    case None{}:
      Done{Rate{f, 1000000000n}}
    case Some{+u}:
      with_per(Dur.parse(per_text(u)), f, per_text(u))

def with_freq(zero: Bool, neg: Bool, +f: Nat, +text: String, +t: Maybe<&2, String>) -> Result<&2, &2, String, Rate>:
  match zero:
    case True{}:
      Done{Rate{0n, 0n}}
    case False{}:
      match neg:
        case True{}:
          Fail{"-rate=" ++ text ++ ": a negative rate is not supported in the Bend port"}
        case False{}:
          with_tail(t, f)

def of_number(ok: Bool, +f: String, +t: Maybe<&2, String>) -> Result<&2, &2, String, Rate>:
  match ok:
    case False{}:
      Fail{atoi_error(f)}
    case True{}:
      +v = Dec.value(unsigned(f))
      with_freq(Nat.is_eq(v, 0n), first_is(f, 45), v, f, t)

def parse_rate(s: String) -> Result<&2, &2, String, Rate>:
  +c = cut(s)
  of_number(Dec.all_digits(unsigned(cut_head(c))), cut_head(c), cut_tail(c))

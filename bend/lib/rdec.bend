# Results decoded for the report, fast: a piece of input (whole lines)
# decoded and folded into metrics in one go (report.bend's pieces).
#
# A line in the shape Go's encoders write takes a fast path:
# - CSV: 12 fields, no quote and no CR in the line, no field starting
#   with a space or a byte past ASCII; the numbers all digits (the
#   timestamp up to 23 of them, the others up to 14);
# - JSON: Go's members in Go's order, no spaces, strings of printable
#   ASCII without escapes, numbers up to 14 digits, a headers object of
#   string arrays, and the line ending right after the object.
# On such a line the fast path computes exactly the Hit, and the rest of
# the input, that Hit.decode computes: the same field texts, read into
# the same values (a number's digits are Dec.value's; Hit.nat_ok holds
# for up to 14 digits and Hit.ts_ok for up to 23), handed to the same
# functions for the rest (B64.decode, Hit.hcol, Hit.hput,
# Civil.parse_rfc3339). What makes it fast: the input is read once and
# never held twice (sharing costs more than reading), and a text column
# (error, body, attack, method, url, headers, a timestamp's date and
# zone) that repeats the previous result's is recognized in place and
# shares its text and its decoding (Memo). Any other line, and any line
# the fast path would reject, goes through Hit.decode itself.
#
# tests/result_fast.bend checks all of this against Hit.decode_all.
import Base
import ./hit.bend as Hit
import ./hdr.bend as Hdr
import ./b64.bend as B64
import ./civil.bend as Civil
import ./metrics.bend as Met
import ./sys.bend as Sys

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

def is_digit(+k: U32) -> Bool:
  Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57))

def digit_of(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      is_digit(code(c))

def some_if(ok: Bool, x: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{x}
    case False{}:
      None{}

# ---------------------------------------------------------------------
# Scanning
# ---------------------------------------------------------------------

# the loops' fuel: more steps than any input has bytes (a runtime Nat;
# fuel that is the input itself would share the input with the loop)
def fuel() -> Nat:
  Nat.mul(4294967295n, 65535n)

# a text and the input after it
type SR is Data:
  SR{v: String, rest: String}

# s after the literal p (ok: the last byte compared matched)
def lit.go(p: String, ok: Bool, s: String) -> Maybe<&2, String>:
  match p:
    case SNil{}:
      some_if(ok, s)
    case SCon{pc, pr}:
      match ok:
        case False{}:
          None{}
        case True{}:
          match s:
            case SNil{}:
              None{}
            case SCon{+sc, sr}:
              lit.go(pr, U32.is_eq(code(pc), code(sc)), sr)

def lit(p: String, s: String) -> Maybe<&2, String>:
  lit.go(p, True{}, s)

# s after a text p (and then the byte d, unless d is 256), or s itself
# when it does not start so: the bytes read are p's first ones, and are
# put back from p, so s is read once and never held twice
type PK is Data:
  PHit{rest: String}
  PMiss{s: String}

def pk.back(+full: String, +k: Nat, s: String) -> PK:
  PMiss{String.take(full, k) ++ s}

def pk.end(ok: Bool, +full: String, +k: Nat, +c: Char, s: String) -> PK:
  match ok:
    case True{}:
      PHit{s}
    case False{}:
      pk.back(full, k, SCon{c, s})

def pk.last(+d: U32, +full: String, +k: Nat, s: String) -> PK:
  match s:
    case SNil{}:
      pk.back(full, k, SNil{})
    case SCon{+c, r}:
      pk.end(U32.is_eq(code(c), d), full, k, c, r)

def pk.stop.of(none: Bool, +d: U32, +full: String, +k: Nat, s: String) -> PK:
  match none:
    case True{}:
      PHit{s}
    case False{}:
      pk.last(d, full, k, s)

def pk.stop(+d: U32, +full: String, +k: Nat, s: String) -> PK:
  pk.stop.of(U32.is_eq(d, 256), d, full, k, s)

# p: the text left to compare; ok: the last byte compared (c, the k-th)
# matched
def pk.go(p: String, ok: Bool, +c: Char, +d: U32, +full: String, +k: Nat, s: String) -> PK:
  match p:
    case SNil{}:
      match ok:
        case False{}:
          pk.back(full, Nat.sub(k, 1n), SCon{c, s})
        case True{}:
          pk.stop(d, full, k, s)
    case SCon{pc, pr}:
      match ok:
        case False{}:
          pk.back(full, Nat.sub(k, 1n), SCon{c, s})
        case True{}:
          match s:
            case SNil{}:
              pk.back(full, k, SNil{})
            case SCon{+sc, sr}:
              pk.go(pr, U32.is_eq(code(pc), code(sc)), sc, d, full, Nat.add(k, 1n), sr)

def pk(+p: String, +d: U32, s: String) -> PK:
  pk.go(p, True{}, Chr{0}, d, p, 0n, s)

# the digits s starts with: how many, their value (Dec.value's, kept
# while there are at most 14 of them), and what follows them
type DG is Data:
  DG{n: Nat, v: Nat, rest: String}

# v and then the digit c, when more is set (a match, so no value past
# 2^48 is ever computed: the runtime Nat would abort)
def shift(more: Bool, +v: Nat, +c: Char) -> Nat:
  match more:
    case True{}:
      Nat.add(Nat.mul(v, 10n), U32.to_nat((code(c) - 48 : U32)))
    case False{}:
      v

def digits.go(fuel: Nat, d: Bool, s: String, +n: Nat, +v: Nat) -> DG:
  match fuel:
    case 0n:
      DG{n, v, s}
    case 1n+f:
      match d:
        case False{}:
          DG{n, v, s}
        case True{}:
          match s:
            case SNil{}:
              DG{n, v, ""}
            case SCon{+c, +rest}:
              digits.go(f, digit_of(rest), rest, Nat.add(n, 1n), shift(Nat.is_lt(n, 14n), v, c))

def digits(+s: String) -> DG:
  digits.go(fuel(), digit_of(s), s, 0n, 0n)

# a number's value and the input after it
type NR is Data:
  NR{n: Nat, rest: String}

def num.of(ok: Bool, +v: Nat, rest: String) -> Maybe<&2, NR>:
  match ok:
    case True{}:
      Some{NR{v, rest}}
    case False{}:
      None{}

# 1 to 14 digits: Hit.nat_ok holds of them and Hit.nat_val is their value
def num.dg(+g: DG) -> Maybe<&2, NR>:
  DG{n, v, rest} = g
  num.of(Bool.and(Nat.is_gt(n, 0n), Nat.is_lt(n, 15n)), v, rest)

def num(+s: String) -> Maybe<&2, NR>:
  num.dg(digits(s))

# ---------------------------------------------------------------------
# The previous result's text columns and their decodings: in CSV, hv =
# Hit.hcol(hdrs) and bv = B64.decode(body); in JSON, bv =
# B64.decode(body), and hdrs holds the last few distinct headers objects
# (Go writes a map's members in a random order), each in the fast shape
# with Hit.read_hdrs(text) = Some{(hs, "")}. Each text is one the fast
# path read (so in CSV none holds a comma, a LF, a quote or a CR, nor
# starts with a space; in JSON each is printable ASCII without a quote
# or a backslash).
# ---------------------------------------------------------------------

type CM is Data:
  CM{err: String, body: String, bv: Maybe<&2, String>, attack: String, method: String, url: String,
     hdrs: String, hv: Hit.HCol}

# a headers object's text and its headers
type HE is Data:
  HE{text: String, hs: List<&2, Hdr.Header>}

# the last timestamp read (ok: there is one): its first 19 bytes (date
# and time of day), its zone, and its seconds and offset
type TM is Data:
  TM{ok: Bool, head: String, zone: String, sec: Nat, off: Nat}

type JM is Data:
  JM{attack: String, err: String, body: String, bv: Maybe<&2, String>, method: String, url: String,
     hdrs: List<&2, HE>, ts: TM}

type Memo is Data:
  Memo{c: CM, j: JM}

def memo0() -> Memo:
  Memo{CM{"", "", B64.decode(""), "", "", "", "", Hit.hcol("")}, JM{"", "", "", B64.decode(""), "", "", [HE{"{}", []}], TM{False{}, "", "", 0n, 0n}}}

def m_c(+m: Memo) -> CM:
  Memo{c, j} = m
  c

def m_j(+m: Memo) -> JM:
  Memo{c, j} = m
  j

# a result decoded: the hit, the input after it, the memo after it
type Got is Data:
  Got{h: Hit.Hit, rest: String, m: Memo}

# ---------------------------------------------------------------------
# CSV
# ---------------------------------------------------------------------

# a byte's class: 0 plain, 1 comma, 2 LF, 3 a quote or a CR, 4 the end
def ccls(+k: U32) -> Nat:
  pick(Nat, U32.is_eq(k, 44), 1n, pick(Nat, U32.is_eq(k, 10), 2n,
    pick(Nat, Bool.or(U32.is_eq(k, 34), U32.is_eq(k, 13)), 3n, 0n)))

def ccls_of(+s: String) -> Nat:
  match s:
    case SNil{}:
      4n
    case SCon{+c, +rest}:
      ccls(code(c))

def field.end(ok: Bool, s: String, cur: String) -> Maybe<&2, SR>:
  match ok:
    case True{}:
      match s:
        case SNil{}:
          None{}
        case SCon{c, rest}:
          Some{SR{String.reverse(cur), rest}}
    case False{}:
      None{}

# the field s starts with (cur: so far, reversed), up to the class d
# ends it (1 a comma, 2 a LF), and the input after that; k is the class
# of s's first byte
def field.go(fuel: Nat, k: Nat, +d: Nat, s: String, cur: String) -> Maybe<&2, SR>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match k:
        case 0n:
          match s:
            case SNil{}:
              None{}
            case SCon{c, +rest}:
              field.go(f, ccls_of(rest), d, rest, SCon{c, cur})
        case 1n+k1:
          field.end(Nat.is_eq(1n+k1, d), s, cur)

# a field Csv.parse_row takes as it is: empty, or not starting with a
# space rune (Go's TrimLeadingSpace) or any byte past ASCII
def start_ok(+f: String) -> Bool:
  match f:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(U32.is_lt(code(c), 128), Bool.not(Bool.or(U32.is_eq(code(c), 32), Bool.and(U32.is_ge(code(c), 9), U32.is_le(code(c), 13)))))

def field.ok(ok: Bool, v: String, rest: String) -> Maybe<&2, SR>:
  match ok:
    case True{}:
      Some{SR{v, rest}}
    case False{}:
      None{}

def field.chk(r: Maybe<&2, SR>) -> Maybe<&2, SR>:
  match r:
    case None{}:
      None{}
    case Some{SR{+v, rest}}:
      field.ok(start_ok(v), v, rest)

def field(+d: Nat, +s: String) -> Maybe<&2, SR>:
  field.chk(field.go(fuel(), ccls_of(s), d, s, ""))

def dbyte(+d: Nat) -> U32:
  pick(U32, Nat.is_eq(d, 1n), 44, 10)

# a text column ended by d: pv again, or the field read
def col.of(hit: PK, +pv: String, +d: Nat) -> Maybe<&2, SR>:
  match hit:
    case PHit{rest}:
      Some{SR{pv, rest}}
    case PMiss{s}:
      field(d, s)

def col(+pv: String, +d: Nat, s: String) -> Maybe<&2, SR>:
  col.of(pk(pv, dbyte(d), s), pv, d)

def num.comma(r: Maybe<&2, NR>) -> Maybe<&2, NR>:
  match r:
    case None{}:
      None{}
    case Some{NR{n, +rest}}:
      num.of(first_is(rest, 44), n, String.drop(rest, 1n))

# a number field: 1 to 14 digits, then a comma
def cnum(+s: String) -> Maybe<&2, NR>:
  num.comma(num(s))

# the timestamp field's digits, n of them: (seconds, nanoseconds) as
# Hit.ts_val reads them (all but the last 9 digits, the last 9); i counts
# down the seconds' digits
type TS is Data:
  TS{s: Nat, ns: Nat}

def ts.go(n: Nat, s: String, +i: Nat, +sec: Nat, +ns: Nat) -> TS:
  match n:
    case 0n:
      TS{sec, ns}
    case 1n+p:
      match s:
        case SNil{}:
          TS{sec, ns}
        case SCon{+c, rest}:
          +in_s = Nat.is_gt(i, 0n)
          ts.go(p, rest, Nat.sub(i, 1n), shift(in_s, sec, c), shift(Bool.not(in_s), ns, c))

type TR is Data:
  TR{t: TS, rest: String}

def ts.of(ok: Bool, +n: Nat, +s: String, rest: String) -> Maybe<&2, TR>:
  match ok:
    case True{}:
      Some{TR{ts.go(n, s, Nat.sub(n, 9n), 0n, 0n), String.drop(rest, 1n)}}
    case False{}:
      None{}

# 1 to 23 digits (Hit.ts_ok holds), then a comma
def ts.dg(+g: DG, +s: String) -> Maybe<&2, TR>:
  DG{n, v, rest} = g
  ts.of(Bool.and(Bool.and(Nat.is_gt(n, 0n), Nat.is_lt(n, 24n)), first_is(rest, 44)), n, s, rest)

def cts(+s: String) -> Maybe<&2, TR>:
  ts.dg(digits(s), s)

# the body and header columns, each with its decoding from the memo when
# the text repeats
type BR is Data:
  BR{v: String, dec: Maybe<&2, String>, rest: String}

def cm_body(+m: CM) -> String:
  CM{err, body, bv, attack, method, url, hdrs, hv} = m
  body

def cm_hdrs(+m: CM) -> String:
  CM{err, body, bv, attack, method, url, hdrs, hv} = m
  hdrs

def cm_hv(+m: CM) -> Hit.HCol:
  CM{err, body, bv, attack, method, url, hdrs, hv} = m
  hv

def cm_err(+m: CM) -> String:
  CM{err, body, bv, attack, method, url, hdrs, hv} = m
  err

def cm_attack(+m: CM) -> String:
  CM{err, body, bv, attack, method, url, hdrs, hv} = m
  attack

def cm_method(+m: CM) -> String:
  CM{err, body, bv, attack, method, url, hdrs, hv} = m
  method

def cm_url(+m: CM) -> String:
  CM{err, body, bv, attack, method, url, hdrs, hv} = m
  url

def br.read(r: Maybe<&2, SR>) -> Maybe<&2, BR>:
  match r:
    case None{}:
      None{}
    case Some{SR{+v, rest}}:
      Some{BR{v, B64.decode(v), rest}}

def br.of(hit: PK, +m: CM) -> Maybe<&2, BR>:
  match hit:
    case PHit{rest}:
      CM{err, body, bv, attack, method, url, hdrs, hv} = m
      Some{BR{body, bv, rest}}
    case PMiss{s}:
      br.read(field(1n, s))

def cbody(s: String, +m: CM) -> Maybe<&2, BR>:
  br.of(pk(cm_body(m), 44, s), m)

type HC is Data:
  HC{v: String, hc: Hit.HCol, rest: String}

def hc.read(r: Maybe<&2, SR>) -> Maybe<&2, HC>:
  match r:
    case None{}:
      None{}
    case Some{SR{+v, rest}}:
      Some{HC{v, Hit.hcol(v), rest}}

def hc.of(hit: PK, +m: CM) -> Maybe<&2, HC>:
  match hit:
    case PHit{rest}:
      Some{HC{cm_hdrs(m), cm_hv(m), rest}}
    case PMiss{s}:
      hc.read(field(2n, s))

def chdrs(s: String, +m: CM) -> Maybe<&2, HC>:
  hc.of(pk(cm_hdrs(m), 10, s), m)

# A record, a field at a time: each step takes what the last one read,
# and the input after it, which it hands on (the input is never held
# twice: sharing it would cost more than reading it). At the end,
# Hit.csv.rec's verdict and hit, from the values read.
def c.hit(ok: Bool, +ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +at: String, +sq: Nat, +me: String, +ur: String, +hv: String, +hc: Hit.HCol, +m: Memo, rest: String) -> Maybe<&2, Got>:
  match ok:
    case True{}:
      TS{sec, ns} = ts
      Some{Got{Hit.Hit{at, sq, cd, Civil.Time{sec, ns, 86400n}, lat, bo, bi, er, Some{Maybe.default(&2, String, bdec, "")}, me, ur, Hit.hcol_hs(hc)},
        rest, Memo{CM{er, bv, bdec, at, me, ur, hv, hc}, m_j(m)}}}
    case False{}:
      None{}

def c.hd(+ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +at: String, +sq: Nat, +me: String, +ur: String, +m: Memo, r: Maybe<&2, HC>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{HC{hv, +hc, rest}}:
      c.hit(Bool.and(Nat.is_lt(cd, 65536n), Bool.and(Maybe.is_some(&2, String, bdec), Hit.hcol_ok(hc))),
        ts, cd, lat, bo, bi, er, bv, bdec, at, sq, me, ur, hv, hc, m, rest)

def c.ur(+ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +at: String, +sq: Nat, +me: String, +m: Memo, r: Maybe<&2, SR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{SR{ur, rest}}:
      c.hd(ts, cd, lat, bo, bi, er, bv, bdec, at, sq, me, ur, m, chdrs(rest, m_c(m)))

def c.me(+ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +at: String, +sq: Nat, +m: Memo, r: Maybe<&2, SR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{SR{me, rest}}:
      c.ur(ts, cd, lat, bo, bi, er, bv, bdec, at, sq, me, m, col(cm_url(m_c(m)), 1n, rest))

def c.sq(+ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +at: String, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{sq, rest}}:
      c.me(ts, cd, lat, bo, bi, er, bv, bdec, at, sq, m, col(cm_method(m_c(m)), 1n, rest))

def c.at(+ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +m: Memo, r: Maybe<&2, SR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{SR{at, rest}}:
      c.sq(ts, cd, lat, bo, bi, er, bv, bdec, at, m, cnum(rest))

def c.bd(+ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +m: Memo, r: Maybe<&2, BR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{BR{bv, bdec, rest}}:
      c.at(ts, cd, lat, bo, bi, er, bv, bdec, m, col(cm_attack(m_c(m)), 1n, rest))

def c.er(+ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +m: Memo, r: Maybe<&2, SR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{SR{er, rest}}:
      c.bd(ts, cd, lat, bo, bi, er, m, cbody(rest, m_c(m)))

def c.bi(+ts: TS, +cd: Nat, +lat: Nat, +bo: Nat, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{bi, rest}}:
      c.er(ts, cd, lat, bo, bi, m, col(cm_err(m_c(m)), 1n, rest))

def c.bo(+ts: TS, +cd: Nat, +lat: Nat, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{bo, rest}}:
      c.bi(ts, cd, lat, bo, m, cnum(rest))

def c.lat(+ts: TS, +cd: Nat, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{lat, rest}}:
      c.bo(ts, cd, lat, m, cnum(rest))

def c.cd(+ts: TS, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{cd, rest}}:
      c.lat(ts, cd, m, cnum(rest))

def c.ts(+m: Memo, r: Maybe<&2, TR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{TR{ts, rest}}:
      c.cd(ts, m, cnum(rest))

def fcsv(+s: String, +m: Memo) -> Maybe<&2, Got>:
  c.ts(m, cts(s))

# ---------------------------------------------------------------------
# JSON
# ---------------------------------------------------------------------

def jm_attack(+m: JM) -> String:
  JM{attack, err, body, bv, method, url, hdrs, ts} = m
  attack

def jm_err(+m: JM) -> String:
  JM{attack, err, body, bv, method, url, hdrs, ts} = m
  err

def jm_body(+m: JM) -> String:
  JM{attack, err, body, bv, method, url, hdrs, ts} = m
  body

def jm_bv(+m: JM) -> Maybe<&2, String>:
  JM{attack, err, body, bv, method, url, hdrs, ts} = m
  bv

def jm_method(+m: JM) -> String:
  JM{attack, err, body, bv, method, url, hdrs, ts} = m
  method

def jm_url(+m: JM) -> String:
  JM{attack, err, body, bv, method, url, hdrs, ts} = m
  url

def jm_hdrs(+m: JM) -> List<&2, HE>:
  JM{attack, err, body, bv, method, url, hdrs, ts} = m
  hdrs

def jm_ts(+m: JM) -> TM:
  JM{attack, err, body, bv, method, url, hdrs, ts} = m
  ts

# a string byte: printable ASCII but a quote or a backslash (Json.read_str
# copies it as it is)
def jbyte(+k: U32) -> Bool:
  Bool.and(Bool.and(U32.is_ge(k, 32), U32.is_le(k, 127)), Bool.and(Bool.not(U32.is_eq(k, 92)), Bool.not(U32.is_eq(k, 34))))

# a string byte's class: 0 jbyte, 1 the closing quote, 3 anything else
def jcls(+k: U32) -> Nat:
  pick(Nat, U32.is_eq(k, 34), 1n, pick(Nat, jbyte(k), 0n, 3n))

def jcls_of(+s: String) -> Nat:
  match s:
    case SNil{}:
      3n
    case SCon{+c, +rest}:
      jcls(code(c))

# the rest of a string after its opening quote: its bytes (what
# Json.read_str reads, none being escaped) and the input after its
# closing quote
def jstr.go(fuel: Nat, k: Nat, s: String, cur: String) -> Maybe<&2, SR>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match k:
        case 0n:
          match s:
            case SNil{}:
              None{}
            case SCon{c, +rest}:
              jstr.go(f, jcls_of(rest), rest, SCon{c, cur})
        case 1n+k1:
          match k1:
            case 0n:
              match s:
                case SNil{}:
                  None{}
                case SCon{c, rest}:
                  Some{SR{String.reverse(cur), rest}}
            case 1n+k2:
              None{}

def jstr(+s: String) -> Maybe<&2, SR>:
  jstr.go(fuel(), jcls_of(s), s, "")

# a string member's value (after its opening quote): pv again, or read
def jcol.of(hit: PK, +pv: String) -> Maybe<&2, SR>:
  match hit:
    case PHit{rest}:
      Some{SR{pv, rest}}
    case PMiss{s}:
      jstr(s)

def jcol(+pv: String, s: String) -> Maybe<&2, SR>:
  jcol.of(pk(pv, 34, s), pv)

def jbody.read(r: Maybe<&2, SR>) -> Maybe<&2, BR>:
  match r:
    case None{}:
      None{}
    case Some{SR{+v, rest}}:
      Some{BR{v, B64.decode(v), rest}}

def jbody.of(hit: PK, +m: JM) -> Maybe<&2, BR>:
  match hit:
    case PHit{rest}:
      Some{BR{jm_body(m), jm_bv(m), rest}}
    case PMiss{s}:
      jbody.read(jstr(s))

def jbody(s: String, +m: JM) -> Maybe<&2, BR>:
  jbody.of(pk(jm_body(m), 34, s), m)

# the headers object in the fast shape, {} or {"k":["v",...],...}, a
# byte at a time. States: 10 before '{', 0 after it, 1 in a key, 2 after
# the key, 3 after ':', 4 after '[', 5 in a value, 6 after a value, 7
# after ',' in an array, 8 after ']', 9 after ',' between members; 100
# after the closing '}', 99 not the fast shape
def obj.next(+st: Nat, +k: U32) -> Nat:
  +q = U32.is_eq(k, 34)
  pick(Nat, Nat.is_eq(st, 10n), pick(Nat, U32.is_eq(k, 123), 0n, 99n),
  pick(Nat, Nat.is_eq(st, 0n), pick(Nat, q, 1n, pick(Nat, U32.is_eq(k, 125), 100n, 99n)),
  pick(Nat, Nat.is_eq(st, 1n), pick(Nat, q, 2n, pick(Nat, jbyte(k), 1n, 99n)),
  pick(Nat, Nat.is_eq(st, 2n), pick(Nat, U32.is_eq(k, 58), 3n, 99n),
  pick(Nat, Nat.is_eq(st, 3n), pick(Nat, U32.is_eq(k, 91), 4n, 99n),
  pick(Nat, Nat.is_eq(st, 4n), pick(Nat, q, 5n, pick(Nat, U32.is_eq(k, 93), 8n, 99n)),
  pick(Nat, Nat.is_eq(st, 5n), pick(Nat, q, 6n, pick(Nat, jbyte(k), 5n, 99n)),
  pick(Nat, Nat.is_eq(st, 6n), pick(Nat, U32.is_eq(k, 44), 7n, pick(Nat, U32.is_eq(k, 93), 8n, 99n)),
  pick(Nat, Nat.is_eq(st, 7n), pick(Nat, q, 5n, 99n),
  pick(Nat, Nat.is_eq(st, 8n), pick(Nat, U32.is_eq(k, 44), 9n, pick(Nat, U32.is_eq(k, 125), 100n, 99n)),
  pick(Nat, Nat.is_eq(st, 9n), pick(Nat, q, 1n, 99n),
    99n)))))))))))

# 0 go on, 1 done, 2 not the fast shape
def obj.mode(+st: Nat) -> Nat:
  pick(Nat, Nat.is_eq(st, 100n), 1n, pick(Nat, Nat.is_eq(st, 99n), 2n, 0n))

# the object's text (cur: so far, reversed) and the input after it
def obj.go(fuel: Nat, mode: Nat, +st: Nat, s: String, cur: String) -> Maybe<&2, SR>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match mode:
        case 0n:
          match s:
            case SNil{}:
              None{}
            case SCon{+c, rest}:
              +nst = obj.next(st, code(c))
              obj.go(f, obj.mode(nst), nst, rest, SCon{c, cur})
        case 1n+m1:
          match m1:
            case 0n:
              Some{SR{String.reverse(cur), s}}
            case 1n+m2:
              None{}

def obj(+s: String) -> Maybe<&2, SR>:
  obj.go(fuel(), 0n, 10n, s, "")

# the headers member's value: the object's text, its headers, and the
# input after it
type HR is Data:
  HR{hs: List<&2, Hdr.Header>, rest: String, es: List<&2, HE>}

def he_text(+e: HE) -> String:
  HE{text, hs} = e
  text

def he_hs(+e: HE) -> List<&2, Hdr.Header>:
  HE{text, hs} = e
  hs

def hdrs.fin(done: Bool, +key: String, +hs: List<&2, Hdr.Header>, rest: String, +es: List<&2, HE>) -> Maybe<&2, HR>:
  match done:
    case True{}:
      Some{HR{hs, rest, Con{HE{key, hs}, List.take(&2, HE, es, 11n)}}}
    case False{}:
      None{}

def hdrs.read(r: Maybe<&1, List<&2, Hdr.Header> & String>, +key: String, rest: String, +es: List<&2, HE>) -> Maybe<&2, HR>:
  match r:
    case None{}:
      None{}
    case Some{(hs, left)}:
      hdrs.fin(String.is_empty(left), key, hs, rest, es)

# Hit.read_hdrs of an object in the fast shape, read as it reads one:
# each member's values (in order) put under its name with Hit.hput, from
# the first member to the last. A value list or an object being read: the
# values (last first) or headers so far, what is left, and where it is: 0
# after the opening bracket, 1 after an element, 4 after a comma, 2 done,
# 3 failed
type VS is Data:
  VS{vs: List<&2, String>, s: String, cut: Nat}

def vs.val(+vs: List<&2, String>, m: Maybe<&2, SR>) -> VS:
  match m:
    case None{}:
      VS{vs, "", 3n}
    case Some{SR{v, rest}}:
      VS{Con{v, vs}, rest, 1n}

def vs.quote(q: Bool, +vs: List<&2, String>, +s: String, +alt: VS) -> VS:
  match q:
    case True{}:
      vs.val(vs, jstr(String.drop(s, 1n)))
    case False{}:
      alt

def vs.step(+vs: List<&2, String>, +s: String, +cut: Nat) -> VS:
  pick(VS, Nat.is_eq(cut, 1n),
    pick(VS, first_is(s, 44), VS{vs, String.drop(s, 1n), 4n},
      pick(VS, first_is(s, 93), VS{vs, String.drop(s, 1n), 2n}, VS{vs, "", 3n})),
    vs.quote(first_is(s, 34), vs, s,
      pick(VS, Bool.and(Nat.is_eq(cut, 0n), first_is(s, 93)), VS{vs, String.drop(s, 1n), 2n}, VS{vs, "", 3n})))

type LV is Data:
  LV{vs: List<&2, String>, rest: String}

def vs.loop(fuel: Nat, st: VS) -> Maybe<&2, LV>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match st:
        case VS{+vs, +s, +cut}:
          match cut:
            case 2n:
              Some{LV{List.reverse(&2, String, vs), s}}
            case 3n:
              None{}
            case _:
              vs.loop(f, vs.step(vs, s, cut))

# the values after '['
def vals(+s: String) -> Maybe<&2, LV>:
  vs.loop(fuel(), VS{[], s, 0n})

type HB is Data:
  HB{hs: List<&2, Hdr.Header>, s: String, cut: Nat}

def hb.vals(+hs: List<&2, Hdr.Header>, +k: String, m: Maybe<&2, LV>) -> HB:
  match m:
    case None{}:
      HB{hs, "", 3n}
    case Some{LV{vs, rest}}:
      HB{Hit.hput(k, vs, hs), rest, 1n}

def hb.vals2(+hs: List<&2, Hdr.Header>, +k: String, m: Maybe<&2, String>) -> HB:
  match m:
    case None{}:
      HB{hs, "", 3n}
    case Some{rest}:
      hb.vals(hs, k, vals(rest))

def hb.colon(+hs: List<&2, Hdr.Header>, m: Maybe<&2, SR>) -> HB:
  match m:
    case None{}:
      HB{hs, "", 3n}
    case Some{SR{v, rest}}:
      hb.vals2(hs, v, lit(":[", rest))

def hb.member(q: Bool, +hs: List<&2, Hdr.Header>, +s: String, +alt: HB) -> HB:
  match q:
    case True{}:
      hb.colon(hs, jstr(String.drop(s, 1n)))
    case False{}:
      alt

def hb.step(+hs: List<&2, Hdr.Header>, +s: String, +cut: Nat) -> HB:
  pick(HB, Nat.is_eq(cut, 1n),
    pick(HB, first_is(s, 44), HB{hs, String.drop(s, 1n), 4n},
      pick(HB, first_is(s, 125), HB{hs, String.drop(s, 1n), 2n}, HB{hs, "", 3n})),
    hb.member(first_is(s, 34), hs, s,
      pick(HB, Bool.and(Nat.is_eq(cut, 0n), first_is(s, 125)), HB{hs, String.drop(s, 1n), 2n}, HB{hs, "", 3n})))

def hb.loop(fuel: Nat, st: HB) -> Maybe<&1, List<&2, Hdr.Header> & String>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match st:
        case HB{+hs, +s, +cut}:
          match cut:
            case 2n:
              Some{(hs, s)}
            case 3n:
              None{}
            case _:
              hb.loop(f, hb.step(hs, s, cut))

# the headers of the object t starts with, and what follows it
def hobj(+t: String) -> Maybe<&1, List<&2, Hdr.Header> & String>:
  hb.loop(fuel(), HB{[], String.drop(t, 1n), 0n})

def hdrs.miss(o: Maybe<&2, SR>, +es: List<&2, HE>) -> Maybe<&2, HR>:
  match o:
    case None{}:
      None{}
    case Some{SR{+v, rest}}:
      hdrs.read(hobj(v), v, rest, es)

# s after the first object of es it starts with, and that object's
# headers (hs: those of the object r was tried on), or s
type HF is Data:
  HFHit{hs: List<&2, Hdr.Header>, rest: String}
  HFMiss{s: String}

def hfind(es: List<&2, HE>, r: PK, +hs: List<&2, Hdr.Header>) -> HF:
  match es:
    case Nil{}:
      match r:
        case PHit{rest}:
          HFHit{hs, rest}
        case PMiss{s}:
          HFMiss{s}
    case Con{+e, more}:
      match r:
        case PHit{rest}:
          HFHit{hs, rest}
        case PMiss{s}:
          hfind(more, pk(he_text(e), 256, s), he_hs(e))

def hdrs.of(f: HF, +es: List<&2, HE>) -> Maybe<&2, HR>:
  match f:
    case HFHit{hs, rest}:
      Some{HR{hs, rest, es}}
    case HFMiss{s}:
      hdrs.miss(obj(s), es)

# Hit.read_hdrs(s) for an object in the fast shape (from the memo when s
# starts with one of its objects, which then is the whole of s's object)
def jhdrs(s: String, +m: JM) -> Maybe<&2, HR>:
  +es = jm_hdrs(m)
  hdrs.of(hfind(es, PMiss{s}, []), es)

# The timestamp member's value. Civil.parse_rfc3339 reads the date and
# the time of day (date_ok, clock_ok, local86) from the first 19 bytes
# only, and the offset (zone_ok, zone_off) from the zone only: a
# timestamp with the memo's first 19 bytes and zone parses as the memo's
# did, but for its fraction (frac_ok, frac_ns). Any other is parsed.
type TSR is Data:
  TSR{t: Maybe<&2, Civil.Time>, rest: String, tm: TM}

def tm_ok(+t: TM) -> Bool:
  TM{ok, head, zone, sec, off} = t
  ok

def tm_head(+t: TM) -> String:
  TM{ok, head, zone, sec, off} = t
  head

def tm_zone(+t: TM) -> String:
  TM{ok, head, zone, sec, off} = t
  zone

def tm_sec(+t: TM) -> Nat:
  TM{ok, head, zone, sec, off} = t
  sec

def tm_off(+t: TM) -> Nat:
  TM{ok, head, zone, sec, off} = t
  off

def tm_of(t: Maybe<&2, Civil.Time>, +x: String, +tm: TM) -> TM:
  match t:
    case None{}:
      tm
    case Some{+v}:
      TM{True{}, String.take(x, 19n), Civil.FZ.zone(Civil.split_frac(String.drop(x, 19n))), Civil.time_sec(v), Civil.time_off(v)}

# x, the whole timestamp, parsed
def jt.full(+x: String, rest: String, +tm: TM) -> TSR:
  +t = Civil.parse_rfc3339(x)
  TSR{t, rest, tm_of(t, x, tm)}

def jt.frac(same: Bool, +r: String, +fz: Civil.FZ, rest: String, +tm: TM) -> TSR:
  match same:
    case True{}:
      TSR{pick(Maybe<&2, Civil.Time>, Civil.frac_ok(r, Civil.FZ.frac(fz)), Some{Civil.Time{tm_sec(tm), Civil.frac_ns(Civil.FZ.frac(fz)), tm_off(tm)}}, None{}),
        rest, tm}
    case False{}:
      jt.full(tm_head(tm) ++ r, rest, tm)

# r: the timestamp after the memo's first 19 bytes
def jt.after(m: Maybe<&2, SR>, +tm: TM) -> Maybe<&2, TSR>:
  match m:
    case None{}:
      None{}
    case Some{SR{+v, rest}}:
      +fz = Civil.split_frac(v)
      Some{jt.frac(String.eq(Civil.FZ.zone(fz), tm_zone(tm)), v, fz, rest, tm)}

def jt.whole(m: Maybe<&2, SR>, +tm: TM) -> Maybe<&2, TSR>:
  match m:
    case None{}:
      None{}
    case Some{SR{v, rest}}:
      Some{jt.full(v, rest, tm)}

def jt.of(hit: PK, +tm: TM) -> Maybe<&2, TSR>:
  match hit:
    case PHit{r}:
      jt.after(jstr(r), tm)
    case PMiss{s}:
      jt.whole(jstr(s), tm)

def jt.head(ok: Bool, +head: String, s: String) -> PK:
  match ok:
    case True{}:
      pk(head, 256, s)
    case False{}:
      PMiss{s}

# the value after its opening quote: Civil.parse_rfc3339 of it, and the
# input after its closing quote
def jts(s: String, +tm: TM) -> Maybe<&2, TSR>:
  jt.of(jt.head(tm_ok(tm), tm_head(tm), s), tm)

def num.m(x: Maybe<&2, String>) -> Maybe<&2, NR>:
  match x:
    case None{}:
      None{}
    case Some{s}:
      num(s)

# the literal p, then a number
def num.l(p: String, s: String) -> Maybe<&2, NR>:
  num.m(lit(p, s))

def jts.m(x: Maybe<&2, String>, +tm: TM) -> Maybe<&2, TSR>:
  match x:
    case None{}:
      None{}
    case Some{s}:
      jts(s, tm)

def jts.l(p: String, s: String, +tm: TM) -> Maybe<&2, TSR>:
  jts.m(lit(p, s), tm)

def jcol.m(x: Maybe<&2, String>, +pv: String) -> Maybe<&2, SR>:
  match x:
    case None{}:
      None{}
    case Some{s}:
      jcol(pv, s)

def jcol.l(p: String, s: String, +pv: String) -> Maybe<&2, SR>:
  jcol.m(lit(p, s), pv)

def jbody.m(x: Maybe<&2, String>, +j: JM) -> Maybe<&2, BR>:
  match x:
    case None{}:
      None{}
    case Some{s}:
      jbody(s, j)

def jbody.l(p: String, s: String, +j: JM) -> Maybe<&2, BR>:
  jbody.m(lit(p, s), j)

def jhdrs.m(x: Maybe<&2, String>, +j: JM) -> Maybe<&2, HR>:
  match x:
    case None{}:
      None{}
    case Some{s}:
      jhdrs(s, j)

def jhdrs.l(p: String, s: String, +j: JM) -> Maybe<&2, HR>:
  jhdrs.m(lit(p, s), j)

# One result object on one line, as Go's encoder writes it, a member at
# a time (as for CSV above); at the end, the verdict and the hit of
# Hit.decode's JSON reader.
def j.hit(ok: Bool, +at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +me: String, +ur: String, +hs: List<&2, Hdr.Header>, +es: List<&2, HE>, +m: Memo, rest: String) -> Maybe<&2, Got>:
  match ok:
    case True{}:
      Some{Got{Hit.Hit{at, sq, cd, Maybe.default(&2, Civil.Time, t, Civil.Time{0n, 0n, 86400n}), lat, bo, bi, er, bdec, me, ur, Some{hs}},
        rest, Memo{m_c(m), JM{at, er, bv, bdec, me, ur, es, tm}}}}
    case False{}:
      None{}

def j.end(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +me: String, +ur: String, +hs: List<&2, Hdr.Header>, +es: List<&2, HE>, +m: Memo, r: Maybe<&2, String>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{rest}:
      j.hit(Bool.and(Nat.is_lt(cd, 65536n), Bool.and(Maybe.is_some(&2, Civil.Time, t), Maybe.is_some(&2, String, bdec))),
        at, sq, cd, t, tm, lat, bo, bi, er, bv, bdec, me, ur, hs, es, m, rest)

def j.hd(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +me: String, +ur: String, +m: Memo, r: Maybe<&2, HR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{HR{hs, rest, es}}:
      j.end(at, sq, cd, t, tm, lat, bo, bi, er, bv, bdec, me, ur, hs, es, m, lit("}\n", rest))

def j.ur(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +me: String, +m: Memo, r: Maybe<&2, SR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{SR{ur, rest}}:
      j.hd(at, sq, cd, t, tm, lat, bo, bi, er, bv, bdec, me, ur, m, jhdrs.l(",\"headers\":", rest, m_j(m)))

def j.me(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +bv: String, +bdec: Maybe<&2, String>, +m: Memo, r: Maybe<&2, SR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{SR{me, rest}}:
      j.ur(at, sq, cd, t, tm, lat, bo, bi, er, bv, bdec, me, m, jcol.l(",\"url\":\"", rest, jm_url(m_j(m))))

def j.bd(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +bo: Nat, +bi: Nat, +er: String, +m: Memo, r: Maybe<&2, BR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{BR{bv, bdec, rest}}:
      j.me(at, sq, cd, t, tm, lat, bo, bi, er, bv, bdec, m, jcol.l(",\"method\":\"", rest, jm_method(m_j(m))))

def j.er(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +bo: Nat, +bi: Nat, +m: Memo, r: Maybe<&2, SR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{SR{er, rest}}:
      j.bd(at, sq, cd, t, tm, lat, bo, bi, er, m, jbody.l(",\"body\":\"", rest, m_j(m)))

def j.bi(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +bo: Nat, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{bi, rest}}:
      j.er(at, sq, cd, t, tm, lat, bo, bi, m, jcol.l(",\"error\":\"", rest, jm_err(m_j(m))))

def j.bo(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +lat: Nat, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{bo, rest}}:
      j.bi(at, sq, cd, t, tm, lat, bo, m, num.l(",\"bytes_in\":", rest))

def j.lat(+at: String, +sq: Nat, +cd: Nat, +t: Maybe<&2, Civil.Time>, +tm: TM, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{lat, rest}}:
      j.bo(at, sq, cd, t, tm, lat, m, num.l(",\"bytes_out\":", rest))

def j.ts(+at: String, +sq: Nat, +cd: Nat, +m: Memo, r: Maybe<&2, TSR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{TSR{t, rest, tm}}:
      j.lat(at, sq, cd, t, tm, m, num.l(",\"latency\":", rest))

def j.cd(+at: String, +sq: Nat, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{cd, rest}}:
      j.ts(at, sq, cd, m, jts.l(",\"timestamp\":\"", rest, jm_ts(m_j(m))))

def j.sq(+at: String, +m: Memo, r: Maybe<&2, NR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{NR{sq, rest}}:
      j.cd(at, sq, m, num.l(",\"code\":", rest))

def j.at(+m: Memo, r: Maybe<&2, SR>) -> Maybe<&2, Got>:
  match r:
    case None{}:
      None{}
    case Some{SR{at, rest}}:
      j.sq(at, m, num.l(",\"seq\":", rest))

def fjson(+s: String, +m: Memo) -> Maybe<&2, Got>:
  j.at(m, jcol.l("{\"attack\":\"", s, jm_attack(m_j(m))))

# ---------------------------------------------------------------------
# A piece
# ---------------------------------------------------------------------

def fast(js: Bool, +s: String, +m: Memo) -> Maybe<&2, Got>:
  match js:
    case True{}:
      fjson(s, m)
    case False{}:
      fcsv(s, m)

# the metrics so far, the input left, the memo, and whether to go on (0),
# done (1) or failed (2: the input left is the record that failed on)
type St is Data:
  St{acc: Met.Acc, rest: String, m: Memo, cut: Nat}

def st.slow(+acc: Met.Acc, +m: Memo, r: Maybe<&1, Hit.Hit & String>, s: String) -> St:
  match r:
    case None{}:
      St{acc, s, m, 2n}
    case Some{(h, rest)}:
      St{Met.add(acc, h), rest, m, 0n}

def st.fast(+acc: Met.Acc, +s: String, +m: Memo, g: Maybe<&2, Got>) -> St:
  match g:
    case Some{Got{h, rest, m2}}:
      St{Met.add(acc, h), rest, m2, 0n}
    case None{}:
      st.slow(acc, m, Hit.decode(s), s)

def st.step(done: Bool, +acc: Met.Acc, +s: String, +m: Memo) -> St:
  match done:
    case True{}:
      St{acc, "", m, 1n}
    case False{}:
      st.fast(acc, s, m, fast(first_is(s, 123), s, m))

# the input decoded: all of it, or up to a record that fails (the metrics
# before it, and the input from it on)
type Res is Data:
  AOk{acc: Met.Acc}
  ABad{acc: Met.Acc, rest: String}

def loop(fuel: Nat, st: St) -> Res:
  match fuel:
    case 0n:
      St{acc, rest, m, cut} = st
      ABad{acc, rest}
    case 1n+f:
      match st:
        case St{+acc, +rest, +m, cut}:
          match cut:
            case 0n:
              loop(f, st.step(String.is_empty(Hit.skip_ws(rest)), acc, rest, m))
            case 1n+k:
              match k:
                case 0n:
                  AOk{acc}
                case 1n+j:
                  ABad{acc, rest}

# the results in s added to acc, as folding Met.add over
# Hit.decode_all(s) adds them when it is Some. When it is None, the
# results before the record it fails on, and the input from that record
# on: Hit.decode_all reads each record from its own bytes (and one past
# its end at most), so on s ++ t it reads those same results, and then
# what it reads from that record on.
def add_all.m(s: String, +acc: Met.Acc, +m: Memo) -> Res:
  loop(fuel(), St{acc, s, m, 0n})

def add_all(s: String, +acc: Met.Acc) -> Res:
  add_all.m(s, acc, memo0())

# ---------------------------------------------------------------------
# A piece as its lines (Sys.read_pieces'): each line in a fast shape is
# read on its own, from its own bytes, which nothing else holds (holding
# the input for Hit.decode would share every byte of it, and sharing
# costs more than reading). The first line that is not, and all after it,
# go to add_all as one text.
# ---------------------------------------------------------------------

# a line tried: read (what the fast path read, and the memo after it), or
# not
type Try is Data:
  TGot{h: Hit.Hit, m: Memo}
  TNo{}

def try.end(done: Bool, h: Hit.Hit, +m: Memo) -> Try:
  match done:
    case True{}:
      TGot{h, m}
    case False{}:
      TNo{}

def try.got(g: Maybe<&2, Got>) -> Try:
  match g:
    case None{}:
      TNo{}
    case Some{Got{h, rest, m}}:
      try.end(String.is_empty(rest), h, m)

# the first byte's kind: 0 '{', 1 another byte that is no blank, 2 a
# blank or none (Hit.decode_all would skip blanks first: add_all does)
def kind(+s: String) -> Nat:
  match s:
    case SNil{}:
      2n
    case SCon{+c, +rest}:
      pick(Nat, U32.is_eq(code(c), 123), 0n,
        pick(Nat, Bool.or(Bool.or(U32.is_eq(code(c), 32), U32.is_eq(code(c), 9)), Bool.or(U32.is_eq(code(c), 13), U32.is_eq(code(c), 10))), 2n, 1n))

def try.of(k: Nat, s: String, +m: Memo) -> Try:
  match k:
    case 0n:
      try.got(fjson(s, m))
    case 1n+j:
      match j:
        case 0n:
          try.got(fcsv(s, m))
        case 1n+i:
          TNo{}

# a line, read by the fast path from its start to its end
def try(+s: String, +m: Memo) -> Try:
  try.of(kind(s), s, m)

# rest: the lines after w; t: w tried
def lines.go(rest: List<&2, List<&2, U32>>, t: Try, +w: List<&2, U32>, +acc: Met.Acc, +m: Memo) -> Res:
  match rest:
    case Nil{}:
      match t:
        case TGot{h, m2}:
          AOk{Met.add(acc, h)}
        case TNo{}:
          add_all.m(Sys.Packed.bytes(w), acc, m)
    case Con{+w2, rest2}:
      match t:
        case TGot{h, +m2}:
          lines.go(rest2, try(Sys.Packed.bytes(w2), m2), w2, Met.add(acc, h), m2)
        case TNo{}:
          add_all.m(Sys.Packed.bytes(w) ++ Sys.Packed.bytes(w2) ++ Sys.Packed.text(rest2), acc, m)

def add_lines.m(ls: List<&2, List<&2, U32>>, +acc: Met.Acc, +m: Memo) -> Res:
  match ls:
    case Nil{}:
      AOk{acc}
    case Con{+w, rest}:
      lines.go(rest, try(Sys.Packed.bytes(w), m), w, acc, m)

# add_all of the text of the lines
def add_lines(ls: List<&2, List<&2, U32>>, +acc: Met.Acc) -> Res:
  add_lines.m(ls, acc, memo0())

# A piece's lines read by the fast path alone, each line read from bytes
# nothing else holds: the metrics of all of them, or of those before the
# first line it does not read (its index j). add_lines then reads the
# piece from that line on (from the lines again), as it would have: the
# lines before are one record each.
type Fast is Data:
  FAll{acc: Met.Acc}
  FStop{acc: Met.Acc, j: U32}

# rest: the lines after the one t tried, the j-th
def fast.go(rest: List<&2, List<&2, U32>>, t: Try, +acc: Met.Acc, +j: U32) -> Fast:
  match rest:
    case Nil{}:
      match t:
        case TGot{h, m}:
          FAll{Met.add(acc, h)}
        case TNo{}:
          FStop{acc, j}
    case Con{w, more}:
      match t:
        case TGot{h, +m}:
          fast.go(more, try(Sys.Packed.bytes(w), m), Met.add(acc, h), (j + 1 : U32))
        case TNo{}:
          FStop{acc, j}

def add_fast(ls: List<&2, List<&2, U32>>, +acc: Met.Acc) -> Fast:
  match ls:
    case Nil{}:
      FAll{acc}
    case Con{w, rest}:
      fast.go(rest, try(Sys.Packed.bytes(w), memo0()), acc, 0)

# ---------------------------------------------------------------------
# The same loop, keeping the hits (for tests: Hit.decode_all(s) itself)
# ---------------------------------------------------------------------

type SH is Data:
  SH{hs: List<&2, Hit.Hit>, rest: String, m: Memo, cut: Nat}

def sh.slow(+hs: List<&2, Hit.Hit>, +m: Memo, r: Maybe<&1, Hit.Hit & String>) -> SH:
  match r:
    case None{}:
      SH{hs, "", m, 2n}
    case Some{(h, rest)}:
      SH{Con{h, hs}, rest, m, 0n}

def sh.fast(+hs: List<&2, Hit.Hit>, +s: String, +m: Memo, g: Maybe<&2, Got>) -> SH:
  match g:
    case Some{Got{h, rest, m2}}:
      SH{Con{h, hs}, rest, m2, 0n}
    case None{}:
      sh.slow(hs, m, Hit.decode(s))

def sh.step(done: Bool, +hs: List<&2, Hit.Hit>, +s: String, +m: Memo) -> SH:
  match done:
    case True{}:
      SH{hs, "", m, 1n}
    case False{}:
      sh.fast(hs, s, m, fast(first_is(s, 123), s, m))

def sh.loop(fuel: Nat, st: SH) -> Maybe<&2, List<&2, Hit.Hit>>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match st:
        case SH{+hs, +rest, +m, cut}:
          match cut:
            case 0n:
              sh.loop(f, sh.step(String.is_empty(Hit.skip_ws(rest)), hs, rest, m))
            case 1n+k:
              match k:
                case 0n:
                  Some{List.reverse(&2, Hit.Hit, hs)}
                case 1n+j:
                  None{}

def decode_all(+s: String) -> Maybe<&2, List<&2, Hit.Hit>>:
  sh.loop(fuel(), SH{[], s, memo0(), 0n})

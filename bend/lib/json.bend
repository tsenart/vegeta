# JSON strings as easyjson writes them (HTML-safe escaping), and read
# back as encoding/json reads them.
#
# esc follows the json_str law's helpers (jesc_head, jesc_len, jesc.go),
# except that cont does not measure the string: byte_at is 0 past the
# end, which is never a continuation byte. str writes the same text front
# to back (esc_into), ASCII bytes without esc_head's strict pick chains.
import Base
import ./text.bend as Text

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def str1(k: U32) -> String:
  SCon{Chr{k}, SNil{}}

def in_range32(+k: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(k, lo), U32.is_le(k, hi))

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

# ---------------------------------------------------------------------
# Writing
# ---------------------------------------------------------------------

def hexd(+n: U32) -> String:
  str1(pick(U32, U32.is_lt(n, 10), (48 + n : U32), (87 + n : U32)))

def cont(+s: String, +i: Nat) -> Bool:
  in_range32(byte_at(s, i), 128, 191)

# the length of the valid UTF-8 sequence s starts with, or 0 (each link
# of a pick chain has a def of its own, so a proof can name the branches)
def utf8_len.8(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  pick(Nat, Bool.and(U32.is_eq(b0, 244), Bool.and(in_range32(b1, 128, 143), Bool.and(c2, c3))), 4n, 0n)

def utf8_len.7(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  pick(Nat, Bool.and(in_range32(b0, 241, 243), Bool.and(c1, Bool.and(c2, c3))), 4n, utf8_len.8(b0, b1, c1, c2, c3))

def utf8_len.6(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  pick(Nat, Bool.and(U32.is_eq(b0, 240), Bool.and(in_range32(b1, 144, 191), Bool.and(c2, c3))), 4n, utf8_len.7(b0, b1, c1, c2, c3))

def utf8_len.5(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  pick(Nat, Bool.and(U32.is_eq(b0, 237), Bool.and(in_range32(b1, 128, 159), c2)), 3n, utf8_len.6(b0, b1, c1, c2, c3))

def utf8_len.4(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  pick(Nat, Bool.and(Bool.or(in_range32(b0, 225, 236), in_range32(b0, 238, 239)), Bool.and(c1, c2)), 3n, utf8_len.5(b0, b1, c1, c2, c3))

def utf8_len.3(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  pick(Nat, Bool.and(U32.is_eq(b0, 224), Bool.and(in_range32(b1, 160, 191), c2)), 3n, utf8_len.4(b0, b1, c1, c2, c3))

def utf8_len.2(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  pick(Nat, Bool.and(in_range32(b0, 194, 223), c1), 2n, utf8_len.3(b0, b1, c1, c2, c3))

def utf8_len.of(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  pick(Nat, U32.is_lt(b0, 128), 1n, utf8_len.2(b0, b1, c1, c2, c3))

def utf8_len(+s: String) -> Nat:
  utf8_len.of(byte_at(s, 0n), byte_at(s, 1n), cont(s, 1n), cont(s, 2n), cont(s, 3n))

# one ASCII byte, escaped
def esc_ascii.6(+k: U32) -> String:
  pick(String, Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))),
    "\\u00" ++ hexd((k >> 4n : U32)) ++ hexd((k .&. 15 : U32)),
    str1(k))

def esc_ascii.5(+k: U32) -> String:
  pick(String, U32.is_eq(k, 9), "\\t", esc_ascii.6(k))

def esc_ascii.4(+k: U32) -> String:
  pick(String, U32.is_eq(k, 13), "\\r", esc_ascii.5(k))

def esc_ascii.3(+k: U32) -> String:
  pick(String, U32.is_eq(k, 10), "\\n", esc_ascii.4(k))

def esc_ascii.2(+k: U32) -> String:
  pick(String, U32.is_eq(k, 92), "\\\\", esc_ascii.3(k))

def esc_ascii(+k: U32) -> String:
  pick(String, U32.is_eq(k, 34), "\\\"", esc_ascii.2(k))

# the text for what s starts with (n is utf8_len(s), b0..b2 its bytes)...
def esc_sep(+b2: U32) -> String:
  pick(String, U32.is_eq(b2, 168), "8", "9")

def esc_head.4(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String) -> String:
  pick(String, Bool.and(Nat.is_eq(n, 3n), Bool.and(U32.is_eq(b0, 226), Bool.and(U32.is_eq(b1, 128),
      Bool.or(U32.is_eq(b2, 168), U32.is_eq(b2, 169))))),
    "\\u202" ++ esc_sep(b2),
    String.take(s, n))

def esc_head.3(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String) -> String:
  pick(String, Nat.is_eq(n, 1n), esc_ascii(b0), esc_head.4(n, b0, b1, b2, s))

def esc_head.2(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String) -> String:
  pick(String, Nat.is_eq(n, 0n), "\\ufffd", esc_head.3(n, b0, b1, b2, s))

def esc_head.of(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String) -> String:
  pick(String, String.is_empty(s), "", esc_head.2(n, b0, b1, b2, s))

def esc_head(+s: String) -> String:
  esc_head.of(utf8_len(s), byte_at(s, 0n), byte_at(s, 1n), byte_at(s, 2n), s)

# ...and how many bytes it takes (a stray byte is one)
def esc_len(+s: String) -> Nat:
  Nat.max(1n, utf8_len(s))

def esc.go(+fuel: Nat, +s: String) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      esc_head(s) ++ esc.go(f, String.drop(s, esc_len(s)))

def esc(+s: String) -> String:
  esc.go(String.length(s), s)

# esc as str writes it: front to back onto the text t that follows, an
# ASCII byte through a chain of matches (only the chosen branch builds
# anything), any other unit as esc_head says

def hexc(+n: U32) -> Char:
  Chr{pick(U32, U32.is_lt(n, 10), (48 + n : U32), (87 + n : U32))}

def ea.6(c: Bool, +k: U32, t: String) -> String:
  match c:
    case True{}:
      SCon{'\\', SCon{'u', SCon{'0', SCon{'0', SCon{hexc((k >> 4n : U32)), SCon{hexc((k .&. 15 : U32)), t}}}}}}
    case False{}:
      SCon{Chr{k}, t}

def ea.5(c: Bool, +k: U32, t: String) -> String:
  match c:
    case True{}:
      SCon{'\\', SCon{'t', t}}
    case False{}:
      ea.6(Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))), k, t)

def ea.4(c: Bool, +k: U32, t: String) -> String:
  match c:
    case True{}:
      SCon{'\\', SCon{'r', t}}
    case False{}:
      ea.5(U32.is_eq(k, 9), k, t)

def ea.3(c: Bool, +k: U32, t: String) -> String:
  match c:
    case True{}:
      SCon{'\\', SCon{'n', t}}
    case False{}:
      ea.4(U32.is_eq(k, 13), k, t)

def ea.2(c: Bool, +k: U32, t: String) -> String:
  match c:
    case True{}:
      SCon{'\\', SCon{'\\', t}}
    case False{}:
      ea.3(U32.is_eq(k, 10), k, t)

def ea(c: Bool, +k: U32, t: String) -> String:
  match c:
    case True{}:
      SCon{'\\', SCon{'"', t}}
    case False{}:
      ea.2(U32.is_eq(k, 92), k, t)

# esc_ascii(k) ++ t
def esc_ascii_into(+k: U32, t: String) -> String:
  ea(U32.is_eq(k, 34), k, t)

# the unit s = SCon{c, rest} starts with, escaped, then t (a: k < 128)...
def unit_into(a: Bool, +k: U32, +c: Char, +rest: String, t: String) -> String:
  match a:
    case True{}:
      esc_ascii_into(k, t)
    case False{}:
      esc_head(SCon{c, rest}) ++ t

# ...and what follows that unit
def next(a: Bool, +c: Char, +rest: String) -> String:
  match a:
    case True{}:
      rest
    case False{}:
      String.drop(SCon{c, rest}, esc_len(SCon{c, rest}))

# esc.go(fuel, s) ++ t
def esc_into(fuel: Nat, s: String, t: String) -> String:
  match fuel:
    case 0n:
      t
    case 1n+f:
      match s:
        case SNil{}:
          t
        case SCon{+c, +rest}:
          +a = U32.is_lt(code(c), 128)
          unit_into(a, code(c), c, rest, esc_into(f, next(a, c, rest), t))

# str(s) ++ t
def str_into(+s: String, t: String) -> String:
  SCon{'"', esc_into(String.length(s), s, SCon{'"', t})}

def str(+s: String) -> String:
  str_into(s, "")

# ---------------------------------------------------------------------
# Reading
#
# One unit at a time, classified as the writer classifies it: a valid
# multi-byte sequence is copied, a stray byte becomes U+FFFD (as Go's
# decoder does), an ASCII byte is a quote, an escape, a control byte (an
# error) or itself. The loop's fuel is the input itself: every unit
# takes at least one byte.
# ---------------------------------------------------------------------

type JCut is Data:
  JsMore{}
  JsDone{}
  JsBad{}

# a unit's bytes (in order), what follows it, and whether to go on
type JU is Data:
  JU{out: String, rest: String, cut: JCut}

# the first n bytes of s, and what follows them (by n first, so that
# n = 0 needs nothing of s)
def taken(n: Nat, s: String) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          SCon{h, taken(p, t)}

def dropn(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          dropn(p, t)

# a hex digit's value, or 16
def hexv(+k: U32) -> U32:
  pick(U32, in_range32(k, 48, 57), (k - 48 : U32),
  pick(U32, in_range32(k, 97, 102), (k - 87 : U32),
  pick(U32, in_range32(k, 65, 70), (k - 55 : U32), 16)))

# the four hex digits at index i, or 65536
def hex4(+s: String, +i: Nat) -> U32:
  +a = hexv(byte_at(s, i))
  +b = hexv(byte_at(s, Nat.add(i, 1n)))
  +c = hexv(byte_at(s, Nat.add(i, 2n)))
  +d = hexv(byte_at(s, Nat.add(i, 3n)))
  pick(U32, Bool.and(Bool.and(U32.is_lt(a, 16), U32.is_lt(b, 16)), Bool.and(U32.is_lt(c, 16), U32.is_lt(d, 16))),
    ((a << 12n) .|. (b << 8n) .|. (c << 4n) .|. d : U32), 65536)

# after "\u": u starts with the hex digits; a surrogate pair is one code
# point, a lone surrogate is U+FFFD (as in Go)
def uesc(+u: String) -> JU:
  +h = hex4(u, 0n)
  +l = hex4(u, 6n)
  pick(JU, U32.is_eq(h, 65536), JU{"", u, JsBad{}},
  pick(JU, Bool.and(Bool.and(in_range32(h, 55296, 56319), in_range32(l, 56320, 57343)),
                    Bool.and(U32.is_eq(byte_at(u, 4n), 92), U32.is_eq(byte_at(u, 5n), 117))),
    JU{Text.char((65536 + ((h - 55296) << 10n) + (l - 56320) : U32)), dropn(10n, u), JsMore{}},
  pick(JU, in_range32(h, 55296, 57343),
    JU{Text.char(65533), dropn(4n, u), JsMore{}},
    JU{Text.char(h), dropn(4n, u), JsMore{}})))

# after a backslash, followed by t (the branches that cost something sit
# behind a match on their verdict: compiled code is strict)
def escape.u(c: Bool, +t: String, +r: String) -> JU:
  match c:
    case True{}:
      uesc(r)
    case False{}:
      JU{"", t, JsBad{}}

def escape(+t: String) -> JU:
  +e = byte_at(t, 0n)
  +r = dropn(1n, t)
  pick(JU, Bool.or(U32.is_eq(e, 34), Bool.or(U32.is_eq(e, 92), U32.is_eq(e, 47))), JU{str1(e), r, JsMore{}},
  pick(JU, U32.is_eq(e, 98), JU{str1(8), r, JsMore{}},
  pick(JU, U32.is_eq(e, 102), JU{str1(12), r, JsMore{}},
  pick(JU, U32.is_eq(e, 110), JU{str1(10), r, JsMore{}},
  pick(JU, U32.is_eq(e, 114), JU{str1(13), r, JsMore{}},
  pick(JU, U32.is_eq(e, 116), JU{str1(9), r, JsMore{}},
    escape.u(U32.is_eq(e, 117), t, r)))))))

# an ASCII byte k, followed by t
def unit.ascii.3(+k: U32, +t: String) -> JU:
  pick(JU, U32.is_lt(k, 32), JU{"", t, JsBad{}}, JU{str1(k), t, JsMore{}})

def unit.ascii.2(c: Bool, +k: U32, +t: String) -> JU:
  match c:
    case True{}:
      escape(t)
    case False{}:
      unit.ascii.3(k, t)

def unit.ascii(+k: U32, +t: String) -> JU:
  pick(JU, U32.is_eq(k, 34), JU{"", t, JsDone{}}, unit.ascii.2(U32.is_eq(k, 92), k, t))

def unit.of.2(c: Bool, +n: Nat, +s: String) -> JU:
  match c:
    case True{}:
      unit.ascii(byte_at(s, 0n), dropn(1n, s))
    case False{}:
      JU{taken(n, s), dropn(n, s), JsMore{}}

# the unit s starts with, n being utf8_len(s) (the empty input is an error)
def unit.of(c: Bool, +n: Nat, +s: String) -> JU:
  match c:
    case True{}:
      JU{SCon{Chr{239}, SCon{Chr{191}, SCon{Chr{189}, SNil{}}}}, dropn(1n, s), JsMore{}}
    case False{}:
      unit.of.2(Nat.is_eq(n, 1n), n, s)

def unit.n(+n: Nat, +s: String) -> JU:
  unit.of(Nat.is_eq(n, 0n), n, s)

def unit(+s: String) -> JU:
  unit.n(utf8_len(s), s)

# acc holds the bytes so far, reversed
def read.go(fuel: String, acc: String, u: JU) -> Maybe<&1, String & String>:
  match fuel:
    case SNil{}:
      None{}
    case SCon{c, f}:
      match u:
        case JU{out, rest, cut}:
          match cut:
            case JsMore{}:
              read.go(f, String.reverse.go(out, acc), unit(rest))
            case JsDone{}:
              Some{(String.reverse(acc), rest)}
            case JsBad{}:
              None{}

def read_str.of(quote: Bool, +t: String) -> Maybe<&1, String & String>:
  match quote:
    case True{}:
      read.go(SCon{Chr{0}, t}, "", unit(t))
    case False{}:
      None{}

# the string literal s starts with, decoded, and what follows it
def read_str(s: String) -> Maybe<&1, String & String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      read_str.of(U32.is_eq(code(c), 34), t)

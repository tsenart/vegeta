# JSON strings as easyjson writes them (HTML-safe escaping), and read
# back as encoding/json reads them.
#
# str follows the json_str law's helpers (jesc_head, jesc_len, jesc.go),
# except that cont does not measure the string: byte_at is 0 past the
# end, which is never a continuation byte.
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

# the length of the valid UTF-8 sequence s starts with, or 0
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
def esc_ascii(+k: U32) -> String:
  pick(String, U32.is_eq(k, 34), "\\\"",
  pick(String, U32.is_eq(k, 92), "\\\\",
  pick(String, U32.is_eq(k, 10), "\\n",
  pick(String, U32.is_eq(k, 13), "\\r",
  pick(String, U32.is_eq(k, 9), "\\t",
  pick(String, Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))),
    "\\u00" ++ hexd((k >> 4n : U32)) ++ hexd((k .&. 15 : U32)),
    str1(k)))))))

# the text for what s starts with...
def esc_head(+s: String) -> String:
  +n = utf8_len(s)
  +b0 = byte_at(s, 0n)
  pick(String, String.is_empty(s), "",
  pick(String, Nat.is_eq(n, 0n), "\\ufffd",
  pick(String, Nat.is_eq(n, 1n), esc_ascii(b0),
  pick(String, Bool.and(Nat.is_eq(n, 3n), Bool.and(U32.is_eq(b0, 226), Bool.and(U32.is_eq(byte_at(s, 1n), 128),
      Bool.or(U32.is_eq(byte_at(s, 2n), 168), U32.is_eq(byte_at(s, 2n), 169))))),
    "\\u202" ++ pick(String, U32.is_eq(byte_at(s, 2n), 168), "8", "9"),
    String.take(s, n)))))

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

def str(s: String) -> String:
  "\"" ++ esc(s) ++ "\""

# ---------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------

type JCut is Data:
  JsMore{}
  JsDone{}
  JsBad{}

# the bytes read so far (reversed), what is left, the cut
type JRd is Data:
  JRd{acc: String, rest: String, cut: JCut}

# s reversed onto acc
def push(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      acc
    case SCon{c, rest}:
      push(rest, SCon{c, acc})

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
def uesc(+acc: String, +u: String) -> JRd:
  +h = hex4(u, 0n)
  +l = hex4(u, 6n)
  pick(JRd, U32.is_eq(h, 65536), JRd{acc, u, JsBad{}},
  pick(JRd, Bool.and(Bool.and(in_range32(h, 55296, 56319), in_range32(l, 56320, 57343)),
                     Bool.and(U32.is_eq(byte_at(u, 4n), 92), U32.is_eq(byte_at(u, 5n), 117))),
    JRd{push(Text.char((65536 + ((h - 55296) << 10n) + (l - 56320) : U32)), acc), String.drop(u, 10n), JsMore{}},
  pick(JRd, in_range32(h, 55296, 57343),
    JRd{push(Text.char(65533), acc), String.drop(u, 4n), JsMore{}},
    JRd{push(Text.char(h), acc), String.drop(u, 4n), JsMore{}})))

# after a backslash, followed by t
def escape(+acc: String, +t: String) -> JRd:
  +e = byte_at(t, 0n)
  +r = String.drop(t, 1n)
  pick(JRd, Bool.or(U32.is_eq(e, 34), Bool.or(U32.is_eq(e, 92), U32.is_eq(e, 47))), JRd{SCon{Chr{e}, acc}, r, JsMore{}},
  pick(JRd, U32.is_eq(e, 98), JRd{SCon{Chr{8}, acc}, r, JsMore{}},
  pick(JRd, U32.is_eq(e, 102), JRd{SCon{Chr{12}, acc}, r, JsMore{}},
  pick(JRd, U32.is_eq(e, 110), JRd{SCon{Chr{10}, acc}, r, JsMore{}},
  pick(JRd, U32.is_eq(e, 114), JRd{SCon{Chr{13}, acc}, r, JsMore{}},
  pick(JRd, U32.is_eq(e, 116), JRd{SCon{Chr{9}, acc}, r, JsMore{}},
  pick(JRd, U32.is_eq(e, 117), uesc(acc, r),
    JRd{acc, t, JsBad{}})))))))

# one byte k of the string's body, followed by t (raw bytes are copied)
def body_byte(+k: U32, +acc: String, +t: String) -> JRd:
  pick(JRd, U32.is_eq(k, 34), JRd{acc, t, JsDone{}},
  pick(JRd, U32.is_eq(k, 92), escape(acc, t),
  pick(JRd, U32.is_lt(k, 32), JRd{acc, t, JsBad{}},
    JRd{SCon{Chr{k}, acc}, t, JsMore{}})))

def step(acc: String, s: String) -> JRd:
  match s:
    case SNil{}:
      JRd{acc, "", JsBad{}}
    case SCon{c, t}:
      body_byte(code(c), acc, t)

def read.go(fuel: String, st: JRd) -> Maybe<&1, String & String>:
  match fuel:
    case SNil{}:
      None{}
    case SCon{c, f}:
      match st:
        case JRd{acc, rest, cut}:
          match cut:
            case JsMore{}:
              read.go(f, step(acc, rest))
            case JsDone{}:
              Some{(String.reverse(acc), rest)}
            case JsBad{}:
              None{}

def read_str.of(quote: Bool, +t: String) -> Maybe<&1, String & String>:
  match quote:
    case True{}:
      read.go(SCon{Chr{0}, t}, JRd{"", t, JsMore{}})
    case False{}:
      None{}

# the string literal s starts with, decoded, and what follows it
def read_str(s: String) -> Maybe<&1, String & String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      read_str.of(U32.is_eq(code(c), 34), t)

# Standard base64 with padding.
#
# encode works three bytes at a time, as the b64_* laws state it; decode
# reads four characters at a time and accepts only canonical input (the
# length a multiple of 4, padding only at the end, unused bits zero).
import Base

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

# the character for a six-bit value (each link of the pick chain has a
# def of its own, so a proof can name the branches)
def char.code4(+i: U32) -> U32:
  pick(U32, U32.is_eq(i, 62), 43, 47)

def char.code3(+i: U32) -> U32:
  pick(U32, U32.is_lt(i, 62), (i - 4 : U32), char.code4(i))

def char.code2(+i: U32) -> U32:
  pick(U32, U32.is_lt(i, 52), (71 + i : U32), char.code3(i))

def char.code(+i: U32) -> U32:
  pick(U32, U32.is_lt(i, 26), (65 + i : U32), char.code2(i))

def char(+i: U32) -> String:
  str1(char.code(i))

def three(+a: U32, +b: U32, +c: U32) -> String:
  char((a >> 2n : U32)) ++ char((((a .&. 3) << 4n) .|. (b >> 4n) : U32))
    ++ char((((b .&. 15) << 2n) .|. (c >> 6n) : U32)) ++ char((c .&. 63 : U32))

def two(+a: U32, +b: U32) -> String:
  char((a >> 2n : U32)) ++ char((((a .&. 3) << 4n) .|. (b >> 4n) : U32)) ++ char(((b .&. 15) << 2n : U32)) ++ "="

def one(+a: U32) -> String:
  char((a >> 2n : U32)) ++ char(((a .&. 3) << 4n : U32)) ++ "=="

# three bytes as four characters, then t (the text of three(a, b, c) ++ t,
# built in place)
def three_into(+a: U32, +b: U32, +c: U32, t: String) -> String:
  SCon{Chr{char.code((a >> 2n : U32))}, SCon{Chr{char.code((((a .&. 3) << 4n) .|. (b >> 4n) : U32))},
    SCon{Chr{char.code((((b .&. 15) << 2n) .|. (c >> 6n) : U32))}, SCon{Chr{char.code((c .&. 63 : U32))}, t}}}}

def encode(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+a, +r1}:
      match r1:
        case SNil{}:
          one(code(a))
        case SCon{+b, +r2}:
          match r2:
            case SNil{}:
              two(code(a), code(b))
            case SCon{+c, +r3}:
              three_into(code(a), code(b), code(c), encode(r3))

# encode(s) ++ t
def encode_into(s: String, t: String) -> String:
  match s:
    case SNil{}:
      t
    case SCon{a, r1}:
      match r1:
        case SNil{}:
          one(code(a)) ++ t
        case SCon{b, r2}:
          match r2:
            case SNil{}:
              two(code(a), code(b)) ++ t
            case SCon{c, r3}:
              three_into(code(a), code(b), code(c), encode_into(r3, t))

# the six-bit value of a character, or 64 when it is not in the alphabet
def value(+k: U32) -> U32:
  pick(U32, in_range32(k, 65, 90), (k - 65 : U32),
  pick(U32, in_range32(k, 97, 122), (k - 71 : U32),
  pick(U32, in_range32(k, 48, 57), (k + 4 : U32),
  pick(U32, U32.is_eq(k, 43), 62,
  pick(U32, U32.is_eq(k, 47), 63, 64)))))

def ok6(+v: U32) -> Bool:
  U32.is_lt(v, 64)

def prepend(p: String, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{p ++ x}

# Bytes are assembled bit by bit (decode's values are below 64, so their
# low six bits are all there is): the words stay symbolic-friendly for
# the proofs, where arithmetic on an opaque byte gets stuck.
def bit0(v: U32) -> Bool:
  match v:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          b0

def bit1(v: U32) -> Bool:
  match v:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              b1

def bit2(v: U32) -> Bool:
  match v:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  b2

def bit3(v: U32) -> Bool:
  match v:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      b3

def bit4(v: U32) -> Bool:
  match v:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      match w4:
                        case WCon{b4, w5}:
                          b4

def bit5(v: U32) -> Bool:
  match v:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      match w4:
                        case WCon{b4, w5}:
                          match w5:
                            case WCon{b5, w6}:
                              b5

def zeros24() -> Word(24n):
  WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}

# the byte with bits b0 (lowest) .. b7
def mk8(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, zeros24()}}}}}}}}}

# (a << 2) | (b >> 4)
def byte1(+a: U32, +b: U32) -> U32:
  mk8(bit4(b), bit5(b), bit0(a), bit1(a), bit2(a), bit3(a), bit4(a), bit5(a))

# ((b & 15) << 4) | (c >> 2)
def byte2(+b: U32, +c: U32) -> U32:
  mk8(bit2(c), bit3(c), bit4(c), bit5(c), bit0(b), bit1(b), bit2(b), bit3(b))

# ((c & 3) << 6) | d
def byte3(+c: U32, +d: U32) -> U32:
  mk8(bit0(d), bit1(d), bit2(d), bit3(d), bit4(d), bit5(d), bit0(c), bit1(c))

def bytes3(+a: U32, +b: U32, +c: U32, +d: U32) -> String:
  str1(byte1(a, b)) ++ str1(byte2(b, c)) ++ str1(byte3(c, d))

def bytes2(+a: U32, +b: U32, +c: U32) -> String:
  str1(byte1(a, b)) ++ str1(byte2(b, c))

def bytes1(+a: U32, +b: U32) -> String:
  str1(byte1(a, b))

# a padded quad (only the last): "xxx=" with the low two bits of the
# third value zero, or "xx==" with the low four bits of the second zero
def padded(+oa: Bool, +ob: Bool, +oc: Bool, +last: Bool, +a: U32, +b: U32, +c: U32, +kc: U32, +kd: U32) -> Maybe<&2, String>:
  pick(Maybe<&2, String>,
    Bool.and(last, Bool.and(Bool.and(oa, ob), Bool.and(Bool.and(oc, U32.is_eq(kd, 61)),
      Bool.and(Bool.not(bit0(c)), Bool.not(bit1(c)))))),
    Some{bytes2(a, b, c)},
  pick(Maybe<&2, String>,
    Bool.and(last, Bool.and(Bool.and(oa, ob), Bool.and(Bool.and(U32.is_eq(kc, 61), U32.is_eq(kd, 61)),
      Bool.and(Bool.and(Bool.not(bit0(b)), Bool.not(bit1(b))), Bool.and(Bool.not(bit2(b)), Bool.not(bit3(b))))))),
    Some{bytes1(a, b)},
    None{}))

def quad.full(full: Bool, +oa: Bool, +ob: Bool, +oc: Bool, +a: U32, +b: U32, +c: U32, +d: U32, +kc: U32, +kd: U32, +last: Bool, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match full:
    case True{}:
      prepend(bytes3(a, b, c, d), rest)
    case False{}:
      padded(oa, ob, oc, last, a, b, c, kc, kd)

def quad.of(+oa: Bool, +ob: Bool, +oc: Bool, +od: Bool, +a: U32, +b: U32, +c: U32, +d: U32, +kc: U32, +kd: U32, +last: Bool, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  quad.full(Bool.and(Bool.and(oa, ob), Bool.and(oc, od)), oa, ob, oc, a, b, c, d, kc, kd, last, rest)

# four values (64 for a character outside the alphabet), the last two
# characters, whether this is the last quad, and the rest decoded
def quad(+a: U32, +b: U32, +c: U32, +d: U32, +kc: U32, +kd: U32, +last: Bool, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  quad.of(ok6(a), ok6(b), ok6(c), ok6(d), a, b, c, d, kc, kd, last, rest)

def decode(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      Some{""}
    case SCon{+a, +r1}:
      match r1:
        case SNil{}:
          None{}
        case SCon{+b, +r2}:
          match r2:
            case SNil{}:
              None{}
            case SCon{+c, +r3}:
              match r3:
                case SNil{}:
                  None{}
                case SCon{+d, +r4}:
                  quad(value(code(a)), value(code(b)), value(code(c)), value(code(d)), code(c), code(d), String.is_empty(r4), decode(r4))

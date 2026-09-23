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

# the character for a six-bit value
def char(+i: U32) -> String:
  str1(pick(U32, U32.is_lt(i, 26), (65 + i : U32),
       pick(U32, U32.is_lt(i, 52), (71 + i : U32),
       pick(U32, U32.is_lt(i, 62), (i - 4 : U32),
       pick(U32, U32.is_eq(i, 62), 43, 47)))))

def three(+a: U32, +b: U32, +c: U32) -> String:
  char((a >> 2n : U32)) ++ char((((a .&. 3) << 4n) .|. (b >> 4n) : U32))
    ++ char((((b .&. 15) << 2n) .|. (c >> 6n) : U32)) ++ char((c .&. 63 : U32))

def two(+a: U32, +b: U32) -> String:
  char((a >> 2n : U32)) ++ char((((a .&. 3) << 4n) .|. (b >> 4n) : U32)) ++ char(((b .&. 15) << 2n : U32)) ++ "="

def one(+a: U32) -> String:
  char((a >> 2n : U32)) ++ char(((a .&. 3) << 4n : U32)) ++ "=="

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
              three(code(a), code(b), code(c)) ++ encode(r3)

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

def bytes3(+a: U32, +b: U32, +c: U32, +d: U32) -> String:
  str1((((a << 2n) .|. (b >> 4n)) .&. 255 : U32)) ++ str1((((b .&. 15) << 4n) .|. (c >> 2n) : U32))
    ++ str1((((c .&. 3) << 6n) .|. d : U32))

def bytes2(+a: U32, +b: U32, +c: U32) -> String:
  str1((((a << 2n) .|. (b >> 4n)) .&. 255 : U32)) ++ str1((((b .&. 15) << 4n) .|. (c >> 2n) : U32))

def bytes1(+a: U32, +b: U32) -> String:
  str1((((a << 2n) .|. (b >> 4n)) .&. 255 : U32))

# a padded quad (only the last): "xxx=" with the low two bits of the
# third value zero, or "xx==" with the low four bits of the second zero
def padded(+last: Bool, +a: U32, +b: U32, +c: U32, +d: U32, +kc: U32, +kd: U32) -> Maybe<&2, String>:
  pick(Maybe<&2, String>,
    Bool.and(last, Bool.and(Bool.and(ok6(a), ok6(b)), Bool.and(Bool.and(ok6(c), U32.is_eq(kd, 61)), U32.is_eq((c .&. 3 : U32), 0)))),
    Some{bytes2(a, b, c)},
  pick(Maybe<&2, String>,
    Bool.and(last, Bool.and(Bool.and(ok6(a), ok6(b)), Bool.and(Bool.and(U32.is_eq(kc, 61), U32.is_eq(kd, 61)), U32.is_eq((b .&. 15 : U32), 0)))),
    Some{bytes1(a, b)},
    None{}))

def quad.of(full: Bool, +last: Bool, +a: U32, +b: U32, +c: U32, +d: U32, +kc: U32, +kd: U32, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match full:
    case True{}:
      prepend(bytes3(a, b, c, d), rest)
    case False{}:
      padded(last, a, b, c, d, kc, kd)

def quad(+ka: U32, +kb: U32, +kc: U32, +kd: U32, +last: Bool, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  +a = value(ka)
  +b = value(kb)
  +c = value(kc)
  +d = value(kd)
  quad.of(Bool.and(Bool.and(ok6(a), ok6(b)), Bool.and(ok6(c), ok6(d))), last, a, b, c, d, kc, kd, rest)

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
                  quad(code(a), code(b), code(c), code(d), String.is_empty(r4), decode(r4))

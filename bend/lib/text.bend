# Text at the edges: arguments arrive as code points; lib works on bytes.
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

# the UTF-8 bytes of code point k (each pick has a def of its own, so a
# proof can name the branches)
def char.two(+k: U32) -> String:
  str1((192 .|. (k >> 6n) : U32)) ++ str1((128 .|. (k .&. 63) : U32))

def char.three(+k: U32) -> String:
  str1((224 .|. (k >> 12n) : U32)) ++ str1((128 .|. ((k >> 6n) .&. 63) : U32)) ++ str1((128 .|. (k .&. 63) : U32))

def char.four(+k: U32) -> String:
  str1((240 .|. (k >> 18n) : U32)) ++ str1((128 .|. ((k >> 12n) .&. 63) : U32)) ++ str1((128 .|. ((k >> 6n) .&. 63) : U32)) ++ str1((128 .|. (k .&. 63) : U32))

def char.3(+k: U32) -> String:
  pick(String, U32.is_lt(k, 65536), char.three(k), char.four(k))

def char.2(+k: U32) -> String:
  pick(String, U32.is_lt(k, 2048), char.two(k), char.3(k))

def char(+k: U32) -> String:
  pick(String, U32.is_lt(k, 128), str1(k), char.2(k))

# code points to their UTF-8 bytes
def utf8(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      char(code(c)) ++ utf8(rest)

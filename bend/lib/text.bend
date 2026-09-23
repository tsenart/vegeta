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

# the UTF-8 bytes of code point k
def char(+k: U32) -> String:
  pick(String, U32.is_lt(k, 128), str1(k),
  pick(String, U32.is_lt(k, 2048), str1((192 .|. (k >> 6n) : U32)) ++ str1((128 .|. (k .&. 63) : U32)),
  pick(String, U32.is_lt(k, 65536), str1((224 .|. (k >> 12n) : U32)) ++ str1((128 .|. ((k >> 6n) .&. 63) : U32)) ++ str1((128 .|. (k .&. 63) : U32)),
    str1((240 .|. (k >> 18n) : U32)) ++ str1((128 .|. ((k >> 12n) .&. 63) : U32)) ++ str1((128 .|. ((k >> 6n) .&. 63) : U32)) ++ str1((128 .|. (k .&. 63) : U32)))))

# code points to their UTF-8 bytes
def utf8(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      char(code(c)) ++ utf8(rest)

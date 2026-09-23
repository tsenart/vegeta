import Base
import ../.build/laws_helpers.bend as L

def hx(+n: U32) -> String:
  L.hexd((n >> 4n : U32)) ++ L.hexd((n .&. 15 : U32))

def vis(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{c, +rest}:
      +k = L.code(c)
      L.pick(String, Bool.and(U32.is_ge(k, 32), U32.is_lt(k, 127)), SCon{Chr{k}, SNil{}},
        L.pick(String, U32.is_eq(k, 10), "\\n", "\\x" ++ hx(k))) ++ vis(rest)



def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(vis("\"" ++ L.jesc("a\"<\n" ++ L.str1(1) ++ L.str1(195) ++ L.str1(169) ++ L.str1(226) ++ L.str1(128) ++ L.str1(168) ++ L.str1(255) ++ "&") ++ "\""))
    IO.print(vis(L.tab_text("Requests\t[total, rate, throughput]\t10, 5.00, 5.00\nDuration\t[total, attack, wait]\t2s, 2s, 364.1" ++ L.micro() ++ "s\nBucket\t\t#\nx\ty\n\nStatus Codes\t[code:count]\t200:10  \nError Set:\n")))

#|"a\"\u003c\n\u0001\xc3\xa9\u2028\ufffd\u0026"
#|Requests  [total, rate, throughput]  10, 5.00, 5.00\nDuration  [total, attack, wait]      2s, 2s, 364.1\xc2\xb5s\nBucket                               #\nx         y\n\nStatus Codes  [code:count]  200:10  \nError Set:\n

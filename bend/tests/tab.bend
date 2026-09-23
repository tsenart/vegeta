# Tab.render against Go's text/tabwriter (NewWriter(w, 0, 8, 2, ' ',
# StripEscape), Go 1.26): the #| lines are Go's output for the same input,
# quoted as below (a newline as \n, a byte from 128 as \xhh)
import Base
import ../lib/tab.bend as Tab

def code(c: Char) -> U32:
  Chr{k} = c
  k

def hexd(+n: U32) -> String:
  SCon{Chr{Tab.pick(U32, U32.is_lt(n, 10), (n + 48 : U32), (n + 87 : U32))}, SNil{}}

def quote.c(+k: U32) -> String:
  Tab.pick(String, U32.is_eq(k, 10), "\\n",
  Tab.pick(String, U32.is_ge(k, 128), "\\x" ++ hexd((k >> 4n : U32)) ++ hexd((k .&. 15 : U32)), SCon{Chr{k}, SNil{}}))

def quote.go(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      quote.c(code(c)) ++ quote.go(rest)

def show(+s: String) -> String:
  "\"" ++ quote.go(Tab.render(s)) ++ "\""

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show("a\tb\tc\naaa\tbb\tc\n"))
    IO.print(show("x\ty\nxxxx\n\tz\tw\nlong cell\tq\n"))
    IO.print(show(SCon{Chr{194}, SCon{Chr{181}, SNil{}}} ++ "s\tx\nab\ty\n"))
    IO.print(show(SCon{Chr{128}, SCon{Chr{128}, SNil{}}} ++ "\tx\nabc\ty\n"))
    IO.print(show("a\tb"))
    IO.print(show(""))
    IO.print(show("\n\n"))
    IO.print(show("k\t\tv\tw\nkk\t\t\tww\n\n1\t2\n"))
    IO.print(show("Bucket\t\t#\t%\tHistogram\n[0s,\t1ms]\t0\t0.00%\t\n[1ms,\t+Inf]\t3\t100.00%\t###\n"))
    IO.print(show("a\tb\n\tc\td\n\t\te\n"))
#|"a    b   c\naaa  bb  c\n"
#|"x  y\nxxxx\n           z  w\nlong cell  q\n"
#|"\xc2\xb5s  x\nab  y\n"
#|"\x80\x80   x\nabc  y\n"
#|"a  b"
#|""
#|"\n\n"
#|"k     v  w\nkk       ww\n\n1  2\n"
#|"Bucket         #  %        Histogram\n[0s,    1ms]   0  0.00%    \n[1ms,   +Inf]  3  100.00%  ###\n"
#|"a  b\n   c  d\n      e\n"

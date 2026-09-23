# Pace.parse_rate against Go Vegeta's rateFlag.Set (Go 1.26, run by hand
# on a copy of flags.go's Set): per in ns; "µs" is the micro sign (C2 B5),
# "μs" the Greek mu (CE BC). Then what Go takes and the port refuses: a
# negative rate, a negative or too long per.
import Base
import ../lib/dec.bend as Dec
import ../lib/dur.bend as Dur
import ../lib/pacer.bend as Pace

def show.of(+s: String, +r: Result<&2, &2, String, Pace.Rate>) -> String:
  match r:
    case Fail{e}:
      "[" ++ Pace.tquote.go(s) ++ "] -> error " ++ e
    case Done{x}:
      Pace.Rate{f, p} = x
      "[" ++ Pace.tquote.go(s) ++ "] -> " ++ Dec.show(f) ++ "/" ++ Dec.show(p)

def show(+s: String) -> String:
  show.of(s, Pace.parse_rate(s))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show("0"))
    IO.print(show("0/xyz"))
    IO.print(show("5"))
    IO.print(show("5/s"))
    IO.print(show("5/1s"))
    IO.print(show("5/ms"))
    IO.print(show("5/" ++ Dur.micro() ++ "s"))
    IO.print(show("5/" ++ Dur.greek_mu() ++ "s"))
    IO.print(show("5/2s"))
    IO.print(show("5/1.5s"))
    IO.print(show("5/0s"))
    IO.print(show("abc"))
    IO.print(show(""))
    IO.print(show("5/"))
    IO.print(show("5/x"))
    IO.print(show("5/5"))
    IO.print(show("+5"))
    IO.print(show("-0"))
    IO.print(show("007/m"))
    IO.print(show("1/2/3"))
    IO.print(show("10/h"))
    IO.print(show("3/1m30s"))
    IO.print(show("x/1s"))
    IO.print(show("5 /s"))
    IO.print(show("1e3"))
    IO.print(show("infinity"))
    IO.print(show("5/1s2"))
    IO.print(show("5/.s"))
    IO.print(show("-5"))
    IO.print(show("5/-1s"))
    IO.print(show("5/100h"))
#|[0] -> 0/0
#|[0/xyz] -> 0/0
#|[5] -> 5/1000000000
#|[5/s] -> 5/1000000000
#|[5/1s] -> 5/1000000000
#|[5/ms] -> 5/1000000
#|[5/\xc2\xb5s] -> 5/1000
#|[5/\xce\xbcs] -> error time: invalid duration "\xce\xbcs"
#|[5/2s] -> 5/2000000000
#|[5/1.5s] -> 5/1500000000
#|[5/0s] -> 5/0
#|[abc] -> error strconv.Atoi: parsing "abc": invalid syntax
#|[] -> error strconv.Atoi: parsing "": invalid syntax
#|[5/] -> error time: invalid duration ""
#|[5/x] -> error time: invalid duration "x"
#|[5/5] -> error time: missing unit in duration "5"
#|[+5] -> 5/1000000000
#|[-0] -> 0/0
#|[007/m] -> 7/60000000000
#|[1/2/3] -> error time: unknown unit "/" in duration "2/3"
#|[10/h] -> 10/3600000000000
#|[3/1m30s] -> 3/90000000000
#|[x/1s] -> error strconv.Atoi: parsing "x": invalid syntax
#|[5 /s] -> error strconv.Atoi: parsing "5 ": invalid syntax
#|[1e3] -> error strconv.Atoi: parsing "1e3": invalid syntax
#|[infinity] -> error strconv.Atoi: parsing "infinity": invalid syntax
#|[5/1s2] -> error time: missing unit in duration "1s2"
#|[5/.s] -> error time: invalid duration ".s"
#|[-5] -> error -rate=-5: a negative rate is not supported in the Bend port
#|[5/-1s] -> error time: invalid duration "-1s"
#|[5/100h] -> error time: invalid duration "100h"

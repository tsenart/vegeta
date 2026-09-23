# Dur against Go (golden/dur.txt, from scripts/gen-dur-golden.go), then
# the port's deviations from Go (LAWS dur_ok): no negative durations but
# -0, nothing from 281474 s up. Output goes out as bytes ("µ" is C2 B5).
import Base
import ../lib/dur.bend as Dur
import ../lib/sys.bend as Sys

# "~" stands for the bytes of "µ", "^" for those of "μ"
def bytes(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      Dur.pick(String, U32.is_eq(Dur.code(c), 126), Dur.micro(),
        Dur.pick(String, U32.is_eq(Dur.code(c), 94), Dur.greek_mu(), SCon{c, SNil{}})) ++ bytes(rest)

def m(+x: Maybe<&2, Nat>) -> String:
  match x:
    case None{}:
      "None"
    case Some{n}:
      Nat.show(n)

def show(+n: Nat) -> String:
  "show " ++ Nat.show(n) ++ " " ++ Dur.show(n) ++ " " ++ Nat.show(Dur.round(n)) ++ " " ++ m(Dur.parse(Dur.show(n)))

def parse(+s: String) -> String:
  "parse [" ++ bytes(s) ++ "] " ++ m(Dur.parse(bytes(s)))

def main() -> IO(Unit):
  do IO<Unit>:
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 1n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 999n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 1000n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 1001n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 1500n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 25833n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 326000n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 364103n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 423778n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(0n, 1000000n), 999999n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(1n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(1n, 1000000n), 500n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(1n, 1000000n), 519000n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(16n, 1000000n), 501000n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(999n, 1000000n), 999999n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(1000n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(1000n, 1000000n), 1n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(1500n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(1999n, 1000000n), 999999n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(59999n, 1000000n), 999999n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(60000n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(61500n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(3599999n, 1000000n), 999999n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(3600000n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(3629999n, 1000000n), 999999n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(3630000n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(3661500n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(90061000n, 1000000n), 0n)) ++ "\n")
    Sys.Out.write(show(Nat.add(Nat.mul(281473999n, 1000000n), 999999n)) ++ "\n")
    Sys.Out.write(parse("0") ++ "\n")
    Sys.Out.write(parse("-0") ++ "\n")
    Sys.Out.write(parse("+0") ++ "\n")
    Sys.Out.write(parse("+5s") ++ "\n")
    Sys.Out.write(parse("1.5s") ++ "\n")
    Sys.Out.write(parse(".5s") ++ "\n")
    Sys.Out.write(parse("5.s") ++ "\n")
    Sys.Out.write(parse("1h30m") ++ "\n")
    Sys.Out.write(parse("1h30m45.5s") ++ "\n")
    Sys.Out.write(parse("") ++ "\n")
    Sys.Out.write(parse("1") ++ "\n")
    Sys.Out.write(parse("5x") ++ "\n")
    Sys.Out.write(parse("5sec") ++ "\n")
    Sys.Out.write(parse("1us") ++ "\n")
    Sys.Out.write(parse("1~s") ++ "\n")
    Sys.Out.write(parse("1^s") ++ "\n")
    Sys.Out.write(parse("1.5~s") ++ "\n")
    Sys.Out.write(parse("0.1ns") ++ "\n")
    Sys.Out.write(parse("1.0000000001s") ++ "\n")
    Sys.Out.write(parse("100ms") ++ "\n")
    Sys.Out.write(parse("2.5h") ++ "\n")
    Sys.Out.write(parse("0.333333333333333h") ++ "\n")
    Sys.Out.write(parse("1.123456789012345678901h") ++ "\n")
    Sys.Out.write(parse("-0s") ++ "\n")
    Sys.Out.write(parse("-0.000h") ++ "\n")
    Sys.Out.write(parse("+-5s") ++ "\n")
    Sys.Out.write(parse("-+5s") ++ "\n")
    Sys.Out.write(parse("1.s5m") ++ "\n")
    Sys.Out.write(parse("3m0.5s") ++ "\n")
    Sys.Out.write(parse("78h11m13.999999999s") ++ "\n")
    Sys.Out.write(parse("0.000000001h") ++ "\n")
    Sys.Out.write(parse("4.444444444444444444m") ++ "\n")
    Sys.Out.write(parse("1h1h") ++ "\n")
    Sys.Out.write(parse(".s") ++ "\n")
    Sys.Out.write(parse("1.2.3s") ++ "\n")
    Sys.Out.write(parse("s") ++ "\n")
    Sys.Out.write(parse("1m0") ++ "\n")
    Sys.Out.write(parse("00001s") ++ "\n")
    Sys.Out.write(parse("0.9999999999999999h") ++ "\n")
    Sys.Out.write(parse("281473.999999999s") ++ "\n")
    Sys.Out.write(parse("12345.6789ms") ++ "\n")
    Sys.Out.write(parse("7.77777us") ++ "\n")
    Sys.Out.write(parse("+0.5m") ++ "\n")
    Sys.Out.write(parse("-5s") ++ "\n")
    Sys.Out.write(parse("-1.5s") ++ "\n")
    Sys.Out.write(parse("-") ++ "\n")
    Sys.Out.write(parse("+") ++ "\n")
    Sys.Out.write(parse("281474s") ++ "\n")
    Sys.Out.write(parse("78h11m14s") ++ "\n")
    Sys.Out.write(parse("281473.9999999999s") ++ "\n")
    Sys.Out.write(parse("4000000h") ++ "\n")
    Sys.Out.write(parse("99999999999999999999h") ++ "\n")
    Sys.Out.write(parse("0.00000000000000000000000000001h") ++ "\n")
    Sys.Out.write(parse("1h-5s") ++ "\n")

#|show 0 0s 0 0
#|show 1 1ns 1 1
#|show 999 999ns 999 999
#|show 1000 1µs 1000 1000
#|show 1001 1.001µs 1001 1001
#|show 1500 1.5µs 1500 1500
#|show 25833 25.833µs 25833 25833
#|show 326000 326µs 326000 326000
#|show 364103 364.103µs 364103 364103
#|show 423778 423.778µs 423778 423778
#|show 999999 999.999µs 999999 999999
#|show 1000000 1ms 1000000 1000000
#|show 1000500 1.0005ms 1001000 1000500
#|show 1519000 1.519ms 1519000 1519000
#|show 16501000 16.501ms 16501000 16501000
#|show 999999999 999.999999ms 1000000000 999999999
#|show 1000000000 1s 1000000000 1000000000
#|show 1000000001 1.000000001s 1000000000 1000000001
#|show 1500000000 1.5s 1500000000 1500000000
#|show 1999999999 1.999999999s 2000000000 1999999999
#|show 59999999999 59.999999999s 60000000000 59999999999
#|show 60000000000 1m0s 60000000000 60000000000
#|show 61500000000 1m1.5s 62000000000 61500000000
#|show 3599999999999 59m59.999999999s 3600000000000 3599999999999
#|show 3600000000000 1h0m0s 3600000000000 3600000000000
#|show 3629999999999 1h0m29.999999999s 3600000000000 3629999999999
#|show 3630000000000 1h0m30s 3660000000000 3630000000000
#|show 3661500000000 1h1m1.5s 3660000000000 3661500000000
#|show 90061000000000 25h1m1s 90060000000000 90061000000000
#|show 281473999999999 78h11m13.999999999s 281460000000000 281473999999999
#|parse [0] 0
#|parse [-0] 0
#|parse [+0] 0
#|parse [+5s] 5000000000
#|parse [1.5s] 1500000000
#|parse [.5s] 500000000
#|parse [5.s] 5000000000
#|parse [1h30m] 5400000000000
#|parse [1h30m45.5s] 5445500000000
#|parse [] None
#|parse [1] None
#|parse [5x] None
#|parse [5sec] None
#|parse [1us] 1000
#|parse [1µs] 1000
#|parse [1μs] 1000
#|parse [1.5µs] 1500
#|parse [0.1ns] 0
#|parse [1.0000000001s] 1000000000
#|parse [100ms] 100000000
#|parse [2.5h] 9000000000000
#|parse [0.333333333333333h] 1199999999999
#|parse [1.123456789012345678901h] 4044444440444
#|parse [-0s] 0
#|parse [-0.000h] 0
#|parse [+-5s] None
#|parse [-+5s] None
#|parse [1.s5m] 301000000000
#|parse [3m0.5s] 180500000000
#|parse [78h11m13.999999999s] 281473999999999
#|parse [0.000000001h] 3600
#|parse [4.444444444444444444m] 266666666666
#|parse [1h1h] 7200000000000
#|parse [.s] None
#|parse [1.2.3s] None
#|parse [s] None
#|parse [1m0] None
#|parse [00001s] 1000000000
#|parse [0.9999999999999999h] 3600000000000
#|parse [281473.999999999s] 281473999999999
#|parse [12345.6789ms] 12345678900
#|parse [7.77777us] 7777
#|parse [+0.5m] 30000000000
#|parse [-5s] None
#|parse [-1.5s] None
#|parse [-] None
#|parse [+] None
#|parse [281474s] None
#|parse [78h11m14s] None
#|parse [281473.9999999999s] 281473999999999
#|parse [4000000h] None
#|parse [99999999999999999999h] None
#|parse [0.00000000000000000000000000001h] 0
#|parse [1h-5s] None

# Effects: the ns clock never goes back and moves across a sleep, wall
# time is sane, the offset at the wall's second matches the wall's, and
# DNS resolves an IP literal to itself and localhost to 127.0.0.1, and
# fails on a name that cannot exist.
import Base
import ../lib/sys.bend as Sys

def show_dns(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{ip}:
      ip
    case Fail{(code, msg)}:
      "fail " ++ U32.show(code) ++ " " ++ msg

def is_fail(r: Result<&1, &1, U32 & String, String>) -> Bool:
  match r:
    case Done{ip}:
      False{}
    case Fail{e}:
      True{}

# 2023-11-14 < sec < 2100-01-01, nsec < 1e9, |offset| <= 14h
def wall_ok(+sec: Nat, +nsec: Nat, +off: U32) -> Bool:
  Nat.is_lt(1700000000n, sec) && Nat.is_lt(sec, 4102444800n)
    && Nat.is_lt(nsec, 1000000000n) && (36000 <= off : U32)
    && (off <= 136800 : U32)

def wall_check.go(+sec: Nat, r: Nat & U32) -> IO(Unit):
  (+nsec, +off) = r
  do IO<Unit>:
    IO.print("wall " ++ Bool.show(wall_ok(sec, nsec, off)))
    o : Nat <- Sys.Clock.offset_at(sec)
    IO.print("offset " ++ Bool.show(Nat.is_eq(o, U32.to_nat(off))))

def wall_check(w: Nat & Nat & U32) -> IO(Unit):
  (sec, rest) = w
  wall_check.go(sec, rest)

def main() -> IO(Unit):
  do IO<Unit>:
    +a : Nat <- Sys.Clock.mono_ns()
    +b : Nat <- Sys.Clock.mono_ns()
    +c : Nat <- Sys.Clock.mono_ns()
    IO.sleep(1)
    d : Nat <- Sys.Clock.mono_ns()
    IO.print("mono " ++ Bool.show(Nat.is_le(a, b) && Nat.is_le(b, c) && Nat.is_lt(c, d)))
    w : Nat & Nat & U32 <- Sys.Clock.wall()
    wall_check(w)
    r : Result<&1, &1, U32 & String, String> <- Sys.Dns.resolve("127.0.0.1")
    IO.print("literal " ++ show_dns(r))
    l : Result<&1, &1, U32 & String, String> <- Sys.Dns.resolve("localhost")
    IO.print("localhost " ++ show_dns(l))
    x : Result<&1, &1, U32 & String, String> <- Sys.Dns.resolve("no-such-host.invalid")
    IO.print("invalid " ++ Bool.show(is_fail(x)))

#|mono True
#|wall True
#|offset True
#|literal 127.0.0.1
#|localhost 127.0.0.1
#|invalid True

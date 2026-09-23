# Clock.sleep_ns: a 3 ms sleep takes 3 to 50 ms by the ns clock, and a
# sleeping computation does not hold up the others: a 30 ms sleeper forked
# first finishes after a 3 ms one forked second, which returns in time.
import Base
import ../lib/sys.bend as Sys

def within(+a: Nat, +b: Nat) -> Bool:
  +d = Nat.sub(b, a)
  Nat.is_le(3000000n, d) && Nat.is_le(d, 50000000n)

def nap(ms: Nat, tag: String) -> IO(String):
  do IO<String>:
    Sys.Clock.sleep_ns(Nat.mul(ms, 1000000n))
    return tag

def main() -> IO(Unit):
  do IO<Unit>:
    a : Nat <- Sys.Clock.mono_ns()
    Sys.Clock.sleep_ns(3000000n)
    b : Nat <- Sys.Clock.mono_ns()
    IO.print("sleep " ++ Bool.show(within(a, b)))
    c : Nat <- Sys.Clock.mono_ns()
    Sys.Clock.sleep_ns(0n)
    d : Nat <- Sys.Clock.mono_ns()
    IO.print("zero " ++ Bool.show(Nat.is_lt(Nat.sub(d, c), 3000000n)))
    +e : Nat <- Sys.Clock.mono_ns()
    slow : Chan(String) <- IO.fork(String, nap(40n, "slow"))
    fast : Chan(String) <- IO.fork(String, nap(3n, "fast"))
    x : String <- IO.join(String, fast)
    f : Nat <- Sys.Clock.mono_ns()
    IO.print(x ++ " " ++ Bool.show(Nat.is_lt(Nat.sub(f, e), 30000000n)))
    y : String <- IO.join(String, slow)
    g : Nat <- Sys.Clock.mono_ns()
    IO.print(y ++ " " ++ Bool.show(Nat.is_le(40000000n, Nat.sub(g, e))))

#|sleep True
#|zero True
#|fast True
#|slow True

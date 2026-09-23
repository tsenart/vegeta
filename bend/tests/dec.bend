import Base
import ../lib/dec.bend as Dec

def m(+x: Maybe<&2, Nat>) -> String:
  match x:
    case None{}:
      "None"
    case Some{n}:
      "Some " ++ Nat.show(n)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Dec.show(0n))
    IO.print(Dec.show(7n))
    IO.print(Dec.show(10n))
    IO.print(Dec.show(4294967295n))
    IO.print(Dec.show(Nat.mul(281474n, 1000000000n)))
    IO.print(Dec.pad(9n, 42n))
    IO.print(Dec.pad(2n, 12345n))
    IO.print(m(Dec.read("007")))
    IO.print(m(Dec.read("")))
    IO.print(m(Dec.read("1a")))
    IO.print(m(Dec.read("281474000000000")))

#|0
#|7
#|10
#|4294967295
#|281474000000000
#|000000042
#|12345
#|Some 7
#|None
#|None
#|Some 281474000000000

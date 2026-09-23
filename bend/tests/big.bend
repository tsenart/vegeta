import Base
import ../lib/big.bend as Big

def s(+b: Big.Big) -> String:
  Big.show(b)

def c(+x: Cmp) -> String:
  match x:
    case LT{}:
      "LT"
    case EQ{}:
      "EQ"
    case GT{}:
      "GT"

def t12() -> Big.Big:
  Big.mul(Big.of(1000000n), Big.of(1000000n))

def f40() -> Big.Big:
  Big.mul(Big.mul(Big.of(4294967295n), Big.of(4294967295n)), Big.of(99991n))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(s(Big.mul(Big.of(4294967295n), Big.of(4294967295n))))
    IO.print(s(Big.add(Big.of(9999n), Big.of(1n))))
    IO.print(s(Big.div(t12(), Big.of(7n))))
    IO.print(s(Big.mod(t12(), Big.of(7n))))
    IO.print(s(Big.of(0n)))
    IO.print(s(Big.of(Nat.mul(281474n, 1000000000n))))
    IO.print(s(Big.add(Big.of(0n), Big.of(0n))) ++ " " ++ s(Big.mul(Big.of(0n), Big.of(12345n))) ++ " " ++ s(Big.mul(Big.of(10000n), Big.of(10000n))))
    IO.print(s(f40()))
    IO.print(s(Big.div(f40(), Big.of(4294967295n))) ++ " " ++ s(Big.mod(f40(), Big.of(4294967295n))))
    IO.print(s(Big.div(f40(), Big.add(t12(), Big.of(12345n)))) ++ " " ++ s(Big.mod(f40(), Big.add(t12(), Big.of(12345n)))))
    IO.print(s(Big.div(Big.of(5n), t12())) ++ " " ++ s(Big.mod(Big.of(5n), t12())) ++ " " ++ s(Big.div(t12(), t12())) ++ " " ++ s(Big.mod(t12(), t12())))
    IO.print(c(Big.cmp(Big.of(5n), Big.of(7n))) ++ c(Big.cmp(t12(), t12())) ++ c(Big.cmp(t12(), Big.of(99999n))) ++ c(Big.cmp(Big.of(0n), Big.of(0n))) ++ c(Big.cmp(Big.of(10001n), Big.of(10000n))))
    IO.print(c(Big.cmp(Big.Big{[5n, 0n, 0n]}, Big.Big{[5n]})) ++ c(Big.cmp(Big.Big{[10000n]}, Big.Big{[0n, 1n]})) ++ c(Big.cmp(Big.Big{[12345n]}, Big.Big{[2344n, 1n]})))
    IO.print(s(Big.sub(t12(), Big.of(1n))) ++ " " ++ s(Big.sub(Big.of(10000n), Big.of(10000n))))

#|18446744065119617025
#|10000
#|142857142857
#|1
#|0
#|281474000000000
#|0 0 100000000
#|1844508385815375625946775
#|429458074794345 0
#|1844508363044 919884168595
#|0 5 1 0
#|LTEQGTEQGT
#|EQEQGT
#|999999999999 0

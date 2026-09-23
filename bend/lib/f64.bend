# Exact float64 emulation: value = m * 2^e (neg = False) or m / 2^e (neg = True). STUB.
import Base
import ./big.bend as Big

type F64 is Data:
  F64{m: Big.Big, e: Nat, neg: Bool}

def zero() -> F64:
  F64{Big.of(0n), 0n, False{}}

def of_big(+b: Big.Big) -> F64:
  zero()

def of_nat(n: Nat) -> F64:
  of_big(Big.of(n))

def add(+a: F64, +b: F64) -> F64:
  a

def mul(+a: F64, +b: F64) -> F64:
  a

def div(+a: F64, +b: F64) -> F64:
  a

# toward zero, as Go's time.Duration(f) conversion
def trunc(+x: F64) -> Nat:
  0n

def fixed(d: Nat, +x: F64) -> String:
  "0"

def json(+x: F64) -> String:
  "0"

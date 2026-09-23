# Big naturals: little-endian base-10000 limbs. STUB.
import Base

type Big is Data:
  Big{limbs: List<&2, Nat>}

def of(n: Nat) -> Big:
  Big{[]}

def add(+a: Big, +b: Big) -> Big:
  a

def mul(+a: Big, +b: Big) -> Big:
  a

def div(+a: Big, +b: Big) -> Big:
  a

def mod(+a: Big, +b: Big) -> Big:
  a

def cmp(+a: Big, +b: Big) -> Cmp:
  EQ{}

def show(+b: Big) -> String:
  "0"

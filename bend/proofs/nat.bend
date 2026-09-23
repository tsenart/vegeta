# Arithmetic lemmas over Base's Nat, shared by every proof file.
# (Ported from Bend's demos/proof_numerics, which proves the same facts
# for its own Num with the same definitions as Base.)
import Base

def add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %add_zero(b) : {b == _ : Nat}
      {==}
    case 1n+p:
      %add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(p, Nat.add(b, c)) == 1n+_ : Nat}
      {==}

# the middle terms of a triple sum swap
def add_swap(x: Nat, +y: Nat, +z: Nat) -> {Nat.add(x, Nat.add(y, z)) == Nat.add(y, Nat.add(x, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(y, Nat.add(q, z)) : {1n+Nat.add(q, Nat.add(y, z)) == _ : Nat}
      %add_swap(q, y, z) : {1n+Nat.add(q, Nat.add(y, z)) == 1n+_ : Nat}
      {==}

def mul_zero(a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero(p)

def mul_succ(+a: Nat, +b: Nat) -> {Nat.add(a, Nat.mul(a, b)) == Nat.mul(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %mul_succ(p, b) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+Nat.add(b, _) : Nat}
      %add_swap(p, b, Nat.mul(p, b)) : {1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

def mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      %mul_zero(b) : {_ == Nat.mul(b, 0n) : Nat}
      {==}
    case 1n++p:
      %mul_succ(b, p) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

def mul_dist(a: Nat, -b: Nat, +c: Nat) -> {Nat.add(Nat.mul(a, c), Nat.mul(b, c)) == Nat.mul(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_dist(p, b, c) : {Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) == Nat.add(c, _) : Nat}
      %add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)) : {_ == Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))) : Nat}
      {==}

# ---------------------------------------------------------------------
# Successor, and refuting 1+x == 0
# ---------------------------------------------------------------------

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, pred, 1n+a, 1n+b, e)

def is_zero_t(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def no_zero(-x: Nat, e: {1n+x == 0n : Nat}) -> Empty:
  %e : is_zero_t(_)
  Unit{}

# ---------------------------------------------------------------------
# Order
# ---------------------------------------------------------------------

# r + m == b puts r below 1 + b
def lt_of_add(r: Nat, -m: Nat, b: Nat, e: {Nat.add(r, m) == b : Nat}) -> {Nat.is_lt(r, 1n+b) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+rp:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+rp, 1n) == True{} : Bool}, no_zero(Nat.add(rp, m), e))
        case 1n+bp:
          lt_of_add(rp, m, bp, succ_inj(Nat.add(rp, m), bp, e))

# ---------------------------------------------------------------------
# Division: Base's divmod loop is Euclid's
# ---------------------------------------------------------------------

def dm_q(p: Nat & Nat) -> Nat:
  Nat.div.fin(p)

def dm_r(p: Nat & Nat) -> Nat:
  Nat.mod.fin(p)

# the loop keeps q*(1+b) + r fixed, while r + m == b
def dm_eq(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +b: Nat, +inv: {Nat.add(r, m) == b : Nat})
  -> {Nat.add(n, Nat.add(Nat.mul(d, 1n+b), r))
      == Nat.add(Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), 1n+b), Nat.mod.fin(Nat.divmod.go(n, m, d, r))) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          %dm_eq(np, r, 1n+d, 0n, b, Equal.trans(Nat, r, Nat.add(r, 0n), b, add_zero(r), inv))
            : {1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)) == _ : Nat}
          %add_zero(Nat.add(1n+b, Nat.mul(d, 1n+b)))
            : {1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)) == Nat.add(np, _) : Nat}
          %add_succ(np, Nat.add(b, Nat.mul(d, 1n+b)))
            : {1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)) == _ : Nat}
          %Equal.trans(Nat, r, Nat.add(r, 0n), b, add_zero(r), inv)
            : {1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)) == 1n+Nat.add(np, Nat.add(_, Nat.mul(d, 1n+b))) : Nat}
          %add_comm(Nat.mul(d, 1n+b), r)
            : {1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)) == 1n+Nat.add(np, _) : Nat}
          {==}
        case 1n+mp:
          %dm_eq(np, mp, d, 1n+r, b, Equal.trans(Nat, 1n+Nat.add(r, mp), Nat.add(r, 1n+mp), b, add_succ(r, mp), inv))
            : {1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)) == _ : Nat}
          %add_succ(Nat.mul(d, 1n+b), r)
            : {1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)) == Nat.add(np, _) : Nat}
          %add_succ(np, Nat.add(Nat.mul(d, 1n+b), r))
            : {1n+Nat.add(np, Nat.add(Nat.mul(d, 1n+b), r)) == _ : Nat}
          {==}

# the remainder stays below 1+b
def dm_lt(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +b: Nat, +inv: {Nat.add(r, m) == b : Nat})
  -> {Nat.is_lt(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), 1n+b) == True{} : Bool}:
  match n:
    case 0n:
      lt_of_add(r, m, b, inv)
    case 1n+np:
      match m:
        case 0n:
          dm_lt(np, r, 1n+d, 0n, b, Equal.trans(Nat, r, Nat.add(r, 0n), b, add_zero(r), inv))
        case 1n+mp:
          dm_lt(np, mp, d, 1n+r, b, Equal.trans(Nat, 1n+Nat.add(r, mp), Nat.add(r, 1n+mp), b, add_succ(r, mp), inv))

# Euclid for Base's Nat.div and Nat.mod by a positive divisor 1+b
def div_mod_eq(+n: Nat, +b: Nat) -> {n == Nat.add(Nat.mul(Nat.div(n, 1n+b), 1n+b), Nat.mod(n, 1n+b)) : Nat}:
  %dm_eq(n, b, 0n, 0n, b, {==}) : {n == _ : Nat}
  add_zero(n)

def mod_lt(+n: Nat, +b: Nat) -> {Nat.is_lt(Nat.mod(n, 1n+b), 1n+b) == True{} : Bool}:
  dm_lt(n, b, 0n, 0n, b, {==})

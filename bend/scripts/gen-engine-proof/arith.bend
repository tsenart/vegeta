# ---------------------------------------------------------------------
# Division facts for the schedule: k intervals under the duration leave
# room for hit k in the schedule
# ---------------------------------------------------------------------

def go_skip(k: Nat, +y: Nat, +m: Nat, +d: Nat, +r: Nat)
  -> {Nat.divmod.go(Nat.add(k, y), Nat.add(k, m), d, r) == Nat.divmod.go(y, m, d, Nat.add(k, r)) : Nat & Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+q):
      %Equal.sym(Nat, 1n+Nat.add(q, r), Nat.add(q, 1n+r), N.add_succ(q, r)) : {Nat.divmod.go(Nat.add(q, y), Nat.add(q, m), d, 1n+r) == Nat.divmod.go(y, m, d, _) : Nat & Nat}
      go_skip(q, y, m, d, 1n+r)

def go_shift(n: Nat, m: Nat, +d: Nat, +r: Nat) -> {Nat.div.fin(Nat.divmod.go(n, m, 1n+d, r)) == 1n+Nat.div.fin(Nat.divmod.go(n, m, d, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          go_shift(np, r, 1n+d, 0n)
        case 1n+mp:
          go_shift(np, mp, d, 1n+r)

def div_step(+y: Nat, +j: Nat) -> {Nat.div(Nat.add(1n+j, y), 1n+j) == 1n+Nat.div(y, 1n+j) : Nat}:
  %Equal.sym(Nat, 1n+Nat.add(j, y), Nat.add(j, 1n+y), N.add_succ(j, y)) : {Nat.div.fin(Nat.divmod.go(_, j, 0n, 0n)) == 1n+Nat.div(y, 1n+j) : Nat}
  %Equal.sym(Nat, j, Nat.add(j, 0n), N.add_zero(j)) : {Nat.div.fin(Nat.divmod.go(Nat.add(j, 1n+y), _, 0n, 0n)) == 1n+Nat.div(y, 1n+j) : Nat}
  %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(j, 1n+y), Nat.add(j, 0n), 0n, 0n), Nat.divmod.go(1n+y, 0n, 0n, Nat.add(j, 0n)), go_skip(j, 1n+y, 0n, 0n, 0n)) : {Nat.div.fin(_) == 1n+Nat.div(y, 1n+j) : Nat}
  %N.add_zero(j) : {Nat.div.fin(Nat.divmod.go(y, _, 1n, 0n)) == 1n+Nat.div(y, 1n+j) : Nat}
  go_shift(y, j, 0n, 0n)

def le_zero(q: Nat) -> {Nat.is_le(0n, q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_zero(x: Nat) -> {x == Nat.sub(x, 0n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a + b <= x: x is a + (x - a), and b <= x - a
def le_split(a: Nat, -b: Nat, x: Nat, e: {Nat.is_le(Nat.add(a, b), x) == True{} : Bool}) -> {x == Nat.add(a, Nat.sub(x, a)) : Nat}:
  match a x:
    case 0n _:
      sub_zero(x)
    case 1n+p 0n:
      Empty.absurd({0n == Nat.add(1n+p, 0n) : Nat}, N.false_ne_true(e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, q, Nat.add(p, Nat.sub(q, p)), le_split(p, b, q, e))

def le_split2(a: Nat, -b: Nat, x: Nat, e: {Nat.is_le(Nat.add(a, b), x) == True{} : Bool}) -> {Nat.is_le(b, Nat.sub(x, a)) == True{} : Bool}:
  match a x:
    case 0n _:
      %sub_zero(x) : {Nat.is_le(b, _) == True{} : Bool}
      e
    case 1n+p 0n:
      bool_absurd(Nat.is_le(b, 0n), True{}, e)
    case 1n+p 1n+q:
      le_split2(p, b, q, e)

# m intervals of 1+j within x: m <= x / (1+j)
def mul_le_div(m: Nat, +x: Nat, +j: Nat, e: {Nat.is_le(Nat.mul(m, 1n+j), x) == True{} : Bool}) -> {Nat.is_le(m, Nat.div(x, 1n+j)) == True{} : Bool}:
  match m:
    case 0n:
      le_zero(Nat.div(x, 1n+j))
    case 1n+(+p):
      +e2 = e
      %Equal.sym(Nat, x, Nat.add(1n+j, Nat.sub(x, 1n+j)), le_split(1n+j, Nat.mul(p, 1n+j), x, e2)) : {Nat.is_le(1n+p, Nat.div(_, 1n+j)) == True{} : Bool}
      %Equal.sym(Nat, Nat.div(Nat.add(1n+j, Nat.sub(x, 1n+j)), 1n+j), 1n+Nat.div(Nat.sub(x, 1n+j), 1n+j), div_step(Nat.sub(x, 1n+j), j))
        : {Nat.is_le(1n+p, _) == True{} : Bool}
      mul_le_div(p, Nat.sub(x, 1n+j), j, le_split2(1n+j, Nat.mul(p, 1n+j), x, e2))

def lt_le_succ(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      e
    case 0n 1n+q:
      le_zero(q)
    case 1n+p 0n:
      e
    case 1n+p 1n+q:
      lt_le_succ(p, q, e)

def le_add_l(j: Nat, +a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(j, a), Nat.add(j, b)) == True{} : Bool}:
  match j:
    case 0n:
      e
    case 1n+q:
      le_add_l(q, a, b, e)

# k intervals of 1+j under d: hit k is in the schedule of d
def sched_ok(+k: Nat, +j: Nat, +d: Nat, e: {Nat.is_lt(Nat.mul(k, 1n+j), d) == True{} : Bool})
  -> {Nat.is_le(1n+k, Nat.div(Nat.add(d, j), 1n+j)) == True{} : Bool}:
  mul_le_div(1n+k, Nat.add(d, j), j,
    Equal.trans(Bool, Nat.is_le(1n+Nat.add(j, Nat.mul(k, 1n+j)), Nat.add(d, j)), Nat.is_le(Nat.add(j, 1n+Nat.mul(k, 1n+j)), Nat.add(j, d)), True{},
      Equal.trans(Bool, Nat.is_le(1n+Nat.add(j, Nat.mul(k, 1n+j)), Nat.add(d, j)), Nat.is_le(Nat.add(j, 1n+Nat.mul(k, 1n+j)), Nat.add(d, j)), Nat.is_le(Nat.add(j, 1n+Nat.mul(k, 1n+j)), Nat.add(j, d)),
        Equal.cong(Nat, Bool, z => Nat.is_le(z, Nat.add(d, j)), 1n+Nat.add(j, Nat.mul(k, 1n+j)), Nat.add(j, 1n+Nat.mul(k, 1n+j)), N.add_succ(j, Nat.mul(k, 1n+j))),
        Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(j, 1n+Nat.mul(k, 1n+j)), z), Nat.add(d, j), Nat.add(j, d), N.add_comm(d, j))),
      le_add_l(j, 1n+Nat.mul(k, 1n+j), d, lt_le_succ(Nat.mul(k, 1n+j), d, e))))

def add_sub(s: Nat, S: Nat, e: {Nat.is_le(s, S) == True{} : Bool}) -> {Nat.add(s, Nat.sub(S, s)) == S : Nat}:
  match s S:
    case 0n _:
      Equal.sym(Nat, S, Nat.sub(S, 0n), sub_zero(S))
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, 0n) == 0n : Nat}, N.false_ne_true(e))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, Nat.sub(q, p)), q, add_sub(p, q, e))

def ge_le(a: Nat, b: Nat) -> {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ge_le(p, q)

def le_lt_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      e2
    case 0n 1n+q 0n:
      e2
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      bool_absurd(Nat.is_lt(1n+p, c), True{}, e1)
    case 1n+p 1n+q 0n:
      e2
    case 1n+p 1n+q 1n+r:
      le_lt_trans(p, q, r, e1, e2)

def gt0_lt(d: Nat, e: {Nat.is_gt(d, 0n) == True{} : Bool}) -> {Nat.is_lt(0n, d) == True{} : Bool}:
  match d:
    case 0n:
      e
    case 1n+q:
      {==}

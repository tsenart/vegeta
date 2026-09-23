# Proofs of the big-natural laws (big_*).
#
# A caution that shapes every proof here: LAWS' limbs_val multiplies as
# Nat.mul(10000n, v), literal first, so the checker unfolds it into 10^4
# additions. That is fine once, but a list with two known limbs under
# limbs_val (or 10000 * (x + 10000 * y)) normalizes to ~10^8 nodes and
# never finishes. So no goal ever holds limbs_val of a list whose tail was
# matched: lib/big.bend decides cons_nz and shift1 on a Bool parameter,
# and proofs split lists through such verdicts, not by matching.
import Base
import ../LAWS.bend as L
import ../lib/dec.bend as Dec
import ../lib/big.bend as Big
import ./nat.bend as PNat

# ---------------------------------------------------------------------
# Booleans and lists
# ---------------------------------------------------------------------

def and_l(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(h))

def and_r(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, PNat.false_ne_true(h))

def and_i(-a: Bool, -b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# and(a, b) is false with b true: a is false
def and_f(a: Bool, -b: Bool, +hb: {b == True{} : Bool}, +h: {False{} == Bool.and(a, b) : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PNat.false_ne_true(Equal.trans(Bool, False{}, b, True{}, h, hb)))

def nil_of_empty(ls: List<&2, Nat>, +h: {List.is_empty(&2, Nat, ls) == True{} : Bool}) -> {ls == Nil{} : List<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Empty.absurd({Con{x, t} == Nil{} : List<&2, Nat>}, PNat.false_ne_true(h))

def zero_of_eq(n: Nat, +h: {Nat.is_eq(n, 0n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Empty.absurd({1n+p == 0n : Nat}, PNat.false_ne_true(h))

def gt_of_ne(n: Nat, +h: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {Nat.is_gt(n, 0n) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_gt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n++p:
      {==}

# ---------------------------------------------------------------------
# Trimming high zero limbs
# ---------------------------------------------------------------------

def val_cons_nz.of(d: Bool, +h: Nat, +r: List<&2, Nat>, +hd: {d == Bool.and(Nat.is_eq(h, 0n), List.is_empty(&2, Nat, r)) : Bool})
  -> {L.limbs_val(Big.cons_nz.of(d, h, r)) == Nat.add(h, Nat.mul(10000n, L.limbs_val(r))) : Nat}:
  match d:
    case False{}:
      {==}
    case True{}:
      +a = Nat.is_eq(h, 0n)
      +b = List.is_empty(&2, Nat, r)
      +hab = Equal.sym(Bool, True{}, Bool.and(a, b), hd)
      %Equal.sym(List<&2, Nat>, r, Nil{}, nil_of_empty(r, and_r(a, b, hab))) : {0n == Nat.add(h, Nat.mul(10000n, L.limbs_val(_))) : Nat}
      %Equal.sym(Nat, h, 0n, zero_of_eq(h, and_l(a, b, hab))) : {0n == Nat.add(_, Nat.mul(10000n, 0n)) : Nat}
      {==}

def val_cons_nz(+h: Nat, +r: List<&2, Nat>) -> {L.limbs_val(Big.cons_nz(h, r)) == Nat.add(h, Nat.mul(10000n, L.limbs_val(r))) : Nat}:
  val_cons_nz.of(Bool.and(Nat.is_eq(h, 0n), List.is_empty(&2, Nat, r)), h, r, {==})

def val_trim(ls: List<&2, Nat>) -> {L.limbs_val(Big.trim(ls)) == L.limbs_val(ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Nat, L.limbs_val(Big.cons_nz(h, Big.trim(t))), Nat.add(h, Nat.mul(10000n, L.limbs_val(Big.trim(t)))), val_cons_nz(h, Big.trim(t)))
        : {_ == Nat.add(h, Nat.mul(10000n, L.limbs_val(t))) : Nat}
      %Equal.sym(Nat, L.limbs_val(Big.trim(t)), L.limbs_val(t), val_trim(t))
        : {Nat.add(h, Nat.mul(10000n, _)) == Nat.add(h, Nat.mul(10000n, L.limbs_val(t))) : Nat}
      {==}

def lnz_tail(+h: Nat, t: List<&2, Nat>, +hl: {L.last_nonzero(Con{h, t}) == True{} : Bool}) -> {L.last_nonzero(t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+g, +more}:
      hl

def lnz_con(+h: Nat, t: List<&2, Nat>, +hh: {Nat.is_gt(h, 0n) == True{} : Bool}, +ht: {L.last_nonzero(t) == True{} : Bool})
  -> {L.last_nonzero(Con{h, t}) == True{} : Bool}:
  match t:
    case Nil{}:
      hh
    case Con{+g, +more}:
      ht

# Con{h, t} keeps a nonzero top when h or t is not zero
def lnz_con_ne(+h: Nat, t: List<&2, Nat>, +hd: {False{} == Bool.and(Nat.is_eq(h, 0n), List.is_empty(&2, Nat, t)) : Bool},
  +ht: {L.last_nonzero(t) == True{} : Bool}) -> {L.last_nonzero(Con{h, t}) == True{} : Bool}:
  match t:
    case Nil{}:
      gt_of_ne(h, and_f(Nat.is_eq(h, 0n), True{}, {==}, hd))
    case Con{+g, +more}:
      ht

def lnz_cons_nz.of(d: Bool, +h: Nat, +r: List<&2, Nat>, +hd: {d == Bool.and(Nat.is_eq(h, 0n), List.is_empty(&2, Nat, r)) : Bool},
  +hr: {L.last_nonzero(r) == True{} : Bool}) -> {L.last_nonzero(Big.cons_nz.of(d, h, r)) == True{} : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      lnz_con_ne(h, r, hd, hr)

def lnz_trim(ls: List<&2, Nat>) -> {L.last_nonzero(Big.trim(ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      lnz_cons_nz.of(Bool.and(Nat.is_eq(h, 0n), List.is_empty(&2, Nat, Big.trim(t))), h, Big.trim(t), {==}, lnz_trim(t))

def ok_cons_nz.of(d: Bool, +h: Nat, +r: List<&2, Nat>, +hh: {Nat.is_lt(h, 10000n) == True{} : Bool}, +hr: {L.limbs_ok(r) == True{} : Bool})
  -> {L.limbs_ok(Big.cons_nz.of(d, h, r)) == True{} : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      and_i(Nat.is_lt(h, 10000n), L.limbs_ok(r), hh, hr)

def ok_trim(ls: List<&2, Nat>, +h: {L.limbs_ok(ls) == True{} : Bool}) -> {L.limbs_ok(Big.trim(ls)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ok_cons_nz.of(Bool.and(Nat.is_eq(x, 0n), List.is_empty(&2, Nat, Big.trim(t))), x, Big.trim(t),
        and_l(Nat.is_lt(x, 10000n), L.limbs_ok(t), h),
        ok_trim(t, and_r(Nat.is_lt(x, 10000n), L.limbs_ok(t), h)))

# a list of base-10000 digits, trimmed, is a canonical Big
def big_ok_trim(+ls: List<&2, Nat>, +h: {L.limbs_ok(ls) == True{} : Bool}) -> {L.big_ok(Big.Big{Big.trim(ls)}) == True{} : Bool}:
  and_i(L.limbs_ok(Big.trim(ls)), L.last_nonzero(Big.trim(ls)), ok_trim(ls, h), lnz_trim(ls))

# ---------------------------------------------------------------------
# Arithmetic
# ---------------------------------------------------------------------

def add_zero_r(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  Equal.sym(Nat, a, Nat.add(a, 0n), PNat.add_zero(a))

def mul_one(v: Nat) -> {Nat.mul(v, 1n) == v : Nat}:
  match v:
    case 0n:
      {==}
    case 1n++p:
      %mul_one(p) : {1n+Nat.mul(p, 1n) == 1n+_ : Nat}
      {==}

def mul_dist_l(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  %PNat.mul_comm(Nat.add(b, c), a) : {_ == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}
  %PNat.mul_dist(b, c, a) : {_ == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}
  %PNat.mul_comm(a, b) : {Nat.add(_, Nat.mul(c, a)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}
  %PNat.mul_comm(a, c) : {Nat.add(Nat.mul(a, b), _) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}
  {==}

def mul_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %PNat.mul_dist(b, Nat.mul(p, b), c) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      %mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

def le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      {==}

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      le_refl(p)

def le_trans(a: Nat, b: Nat, c: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      le_zero(c)
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, PNat.false_ne_true(h1))
        case 1n++bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, PNat.false_ne_true(h2))
            case 1n++cp:
              le_trans(ap, bp, cp, h1, h2)

def le_add(x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      le_zero(y)
    case 1n++p:
      le_add(p, y)

def le_add_l(+x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(y, x)) == True{} : Bool}:
  %PNat.add_comm(x, y) : {Nat.is_le(x, _) == True{} : Bool}
  le_add(x, y)

def le_mul(+p: Nat, +b: Nat) -> {Nat.is_le(p, Nat.mul(p, 2n+b)) == True{} : Bool}:
  %PNat.mul_comm(2n+b, p) : {Nat.is_le(p, _) == True{} : Bool}
  le_add(p, Nat.add(p, Nat.mul(b, p)))

# q <= m when 1 + m = q (2 + b) + r
def div_shrink.go(q: Nat, +r: Nat, +m: Nat, +b: Nat, e: {1n+m == Nat.add(Nat.mul(q, 2n+b), r) : Nat}) -> {Nat.is_le(q, m) == True{} : Bool}:
  match q:
    case 0n:
      le_zero(m)
    case 1n++p:
      +w = Nat.add(Nat.add(b, Nat.mul(p, 2n+b)), r)
      %Equal.sym(Nat, m, 1n+w, PNat.succ_inj(m, 1n+w, e)) : {Nat.is_le(1n+p, _) == True{} : Bool}
      +h1 = le_mul(p, b)
      +h2 = le_add_l(Nat.mul(p, 2n+b), b)
      +h3 = le_add(Nat.add(b, Nat.mul(p, 2n+b)), r)
      le_trans(p, Nat.mul(p, 2n+b), w, h1, le_trans(Nat.mul(p, 2n+b), Nat.add(b, Nat.mul(p, 2n+b)), w, h2, h3))

def div_shrink(+m: Nat) -> {Nat.is_le(Nat.div(1n+m, 10000n), m) == True{} : Bool}:
  div_shrink.go(Nat.div(1n+m, 10000n), Nat.mod(1n+m, 10000n), m, 9998n, PNat.div_mod_eq(1n+m, 9999n))

# ---------------------------------------------------------------------
# Carries
# ---------------------------------------------------------------------

# r + 10000 q == n, for n = q 10000 + r
def recombine(+n: Nat) -> {Nat.add(Nat.mod(n, 10000n), Nat.mul(10000n, Nat.div(n, 10000n))) == n : Nat}:
  %Equal.sym(Nat, n, Nat.add(Nat.mul(Nat.div(n, 10000n), 10000n), Nat.mod(n, 10000n)), PNat.div_mod_eq(n, 9999n))
    : {Nat.add(Nat.mod(n, 10000n), Nat.mul(10000n, Nat.div(n, 10000n))) == _ : Nat}
  %PNat.mul_comm(Nat.div(n, 10000n), 10000n) : {Nat.add(Nat.mod(n, 10000n), _) == Nat.add(Nat.mul(Nat.div(n, 10000n), 10000n), Nat.mod(n, 10000n)) : Nat}
  PNat.add_comm(Nat.mod(n, 10000n), Nat.mul(Nat.div(n, 10000n), 10000n))

# the limbs of a carry c (fuel 1 + f, f >= c) denote c
def carry_val(f: Nat, +c: Nat, +hf: {Nat.is_le(c, f) == True{} : Bool})
  -> {L.limbs_val(Big.carry.rest(1n+f, Nat.is_eq(c, 0n), c)) == c : Nat}:
  match f:
    case 0n:
      match c:
        case 0n:
          {==}
        case 1n++m:
          Empty.absurd({L.limbs_val(Big.carry.rest(1n, False{}, 1n+m)) == 1n+m : Nat}, PNat.false_ne_true(hf))
    case 1n++g:
      match c:
        case 0n:
          {==}
        case 1n++m:
          +q = Nat.div(1n+m, 10000n)
          %Equal.sym(Nat, L.limbs_val(Big.carry.rest(1n+g, Nat.is_eq(q, 0n), q)), q, carry_val(g, q, le_trans(q, m, g, div_shrink(m), hf)))
            : {Nat.add(Nat.mod(1n+m, 10000n), Nat.mul(10000n, _)) == 1n+m : Nat}
          recombine(1n+m)

def carry_rest_ok(f: Nat, s: Bool, +c: Nat) -> {L.limbs_ok(Big.carry.rest(f, s, c)) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n++g:
      match s:
        case True{}:
          {==}
        case False{}:
          and_i(Nat.is_lt(Nat.mod(c, 10000n), 10000n), L.limbs_ok(Big.carry.rest(g, Nat.is_eq(Nat.div(c, 10000n), 0n), Nat.div(c, 10000n))),
            PNat.mod_lt(c, 9999n), carry_rest_ok(g, Nat.is_eq(Nat.div(c, 10000n), 0n), Nat.div(c, 10000n)))

def of_val(+n: Nat) -> {L.limbs_val(Big.trim(Big.carry.rest(1n+n, Nat.is_eq(n, 0n), n))) == n : Nat}:
  +ls = Big.carry.rest(1n+n, Nat.is_eq(n, 0n), n)
  %Equal.sym(Nat, L.limbs_val(Big.trim(ls)), L.limbs_val(ls), val_trim(ls)) : {_ == n : Nat}
  carry_val(n, n, le_refl(n))

def L.big_of(n):
  (of_val(n), big_ok_trim(Big.carry.rest(1n+n, Nat.is_eq(n, 0n), n), carry_rest_ok(1n+n, Nat.is_eq(n, 0n), n)))

# r + B (V + q) == (h + B V) + c, when r + B q == h + c
def alg_carry(+b: Nat, +h: Nat, +c: Nat, +v: Nat, +q: Nat, +r: Nat, e: {Nat.add(r, Nat.mul(b, q)) == Nat.add(h, c) : Nat})
  -> {Nat.add(r, Nat.mul(b, Nat.add(v, q))) == Nat.add(Nat.add(h, Nat.mul(b, v)), c) : Nat}:
  %Equal.sym(Nat, Nat.mul(b, Nat.add(v, q)), Nat.add(Nat.mul(b, v), Nat.mul(b, q)), mul_dist_l(b, v, q))
    : {Nat.add(r, _) == Nat.add(Nat.add(h, Nat.mul(b, v)), c) : Nat}
  %PNat.add_swap(Nat.mul(b, v), r, Nat.mul(b, q)) : {_ == Nat.add(Nat.add(h, Nat.mul(b, v)), c) : Nat}
  %Equal.sym(Nat, Nat.add(r, Nat.mul(b, q)), Nat.add(h, c), e) : {Nat.add(Nat.mul(b, v), _) == Nat.add(Nat.add(h, Nat.mul(b, v)), c) : Nat}
  Equal.trans(Nat, Nat.add(Nat.mul(b, v), Nat.add(h, c)), Nat.add(h, Nat.add(Nat.mul(b, v), c)), Nat.add(Nat.add(h, Nat.mul(b, v)), c),
    PNat.add_swap(Nat.mul(b, v), h, c), PNat.add_assoc(h, Nat.mul(b, v), c))

# (x + y) + (a + b) == (x + a) + (y + b)
def add4(+x: Nat, +y: Nat, +a: Nat, +b: Nat) -> {Nat.add(Nat.add(x, y), Nat.add(a, b)) == Nat.add(Nat.add(x, a), Nat.add(y, b)) : Nat}:
  %PNat.add_assoc(x, y, Nat.add(a, b)) : {_ == Nat.add(Nat.add(x, a), Nat.add(y, b)) : Nat}
  %PNat.add_assoc(x, a, Nat.add(y, b)) : {Nat.add(x, Nat.add(y, Nat.add(a, b))) == _ : Nat}
  %PNat.add_swap(y, a, b) : {Nat.add(x, Nat.add(y, Nat.add(a, b))) == Nat.add(x, _) : Nat}
  {==}

# (x + y) + B (X + Y) == (x + B X) + (y + B Y)
def regroup(+b: Nat, +x: Nat, +y: Nat, +vx: Nat, +vy: Nat)
  -> {Nat.add(Nat.add(x, y), Nat.mul(b, Nat.add(vx, vy))) == Nat.add(Nat.add(x, Nat.mul(b, vx)), Nat.add(y, Nat.mul(b, vy))) : Nat}:
  %Equal.sym(Nat, Nat.mul(b, Nat.add(vx, vy)), Nat.add(Nat.mul(b, vx), Nat.mul(b, vy)), mul_dist_l(b, vx, vy))
    : {Nat.add(Nat.add(x, y), _) == Nat.add(Nat.add(x, Nat.mul(b, vx)), Nat.add(y, Nat.mul(b, vy))) : Nat}
  add4(x, y, Nat.mul(b, vx), Nat.mul(b, vy))

def carry_go_val(ls: List<&2, Nat>, +c: Nat) -> {L.limbs_val(Big.carry.go(ls, c)) == Nat.add(L.limbs_val(ls), c) : Nat}:
  match ls:
    case Nil{}:
      carry_val(c, c, le_refl(c))
    case Con{+h, +t}:
      +s = Nat.add(h, c)
      %Equal.sym(Nat, L.limbs_val(Big.carry.go(t, Nat.div(s, 10000n))), Nat.add(L.limbs_val(t), Nat.div(s, 10000n)), carry_go_val(t, Nat.div(s, 10000n)))
        : {Nat.add(Nat.mod(s, 10000n), Nat.mul(10000n, _)) == Nat.add(Nat.add(h, Nat.mul(10000n, L.limbs_val(t))), c) : Nat}
      alg_carry(10000n, h, c, L.limbs_val(t), Nat.div(s, 10000n), Nat.mod(s, 10000n), recombine(s))

def carry_go_ok(ls: List<&2, Nat>, +c: Nat) -> {L.limbs_ok(Big.carry.go(ls, c)) == True{} : Bool}:
  match ls:
    case Nil{}:
      carry_rest_ok(1n+c, Nat.is_eq(c, 0n), c)
    case Con{+h, +t}:
      +s = Nat.add(h, c)
      and_i(Nat.is_lt(Nat.mod(s, 10000n), 10000n), L.limbs_ok(Big.carry.go(t, Nat.div(s, 10000n))),
        PNat.mod_lt(s, 9999n), carry_go_ok(t, Nat.div(s, 10000n)))

def add_go_val(xs: List<&2, Nat>, ys: List<&2, Nat>, +c: Nat)
  -> {L.limbs_val(Big.add.go(xs, ys, c)) == Nat.add(Nat.add(L.limbs_val(xs), L.limbs_val(ys)), c) : Nat}:
  match xs:
    case Nil{}:
      carry_go_val(ys, c)
    case Con{+x, +xt}:
      match ys:
        case Nil{}:
          %PNat.add_zero(L.limbs_val(Con{x, xt})) : {L.limbs_val(Big.carry.go(Con{x, xt}, c)) == Nat.add(_, c) : Nat}
          carry_go_val(Con{x, xt}, c)
        case Con{+y, +yt}:
          +s = Nat.add(Nat.add(x, y), c)
          +vx = L.limbs_val(xt)
          +vy = L.limbs_val(yt)
          %Equal.sym(Nat, L.limbs_val(Big.add.go(xt, yt, Nat.div(s, 10000n))), Nat.add(Nat.add(vx, vy), Nat.div(s, 10000n)), add_go_val(xt, yt, Nat.div(s, 10000n)))
            : {Nat.add(Nat.mod(s, 10000n), Nat.mul(10000n, _)) == Nat.add(Nat.add(Nat.add(x, Nat.mul(10000n, vx)), Nat.add(y, Nat.mul(10000n, vy))), c) : Nat}
          %regroup(10000n, x, y, vx, vy)
            : {Nat.add(Nat.mod(s, 10000n), Nat.mul(10000n, Nat.add(Nat.add(vx, vy), Nat.div(s, 10000n)))) == Nat.add(_, c) : Nat}
          alg_carry(10000n, Nat.add(x, y), c, Nat.add(vx, vy), Nat.div(s, 10000n), Nat.mod(s, 10000n), recombine(s))

def add_go_ok(xs: List<&2, Nat>, ys: List<&2, Nat>, +c: Nat) -> {L.limbs_ok(Big.add.go(xs, ys, c)) == True{} : Bool}:
  match xs:
    case Nil{}:
      carry_go_ok(ys, c)
    case Con{+x, +xt}:
      match ys:
        case Nil{}:
          carry_go_ok(Con{x, xt}, c)
        case Con{+y, +yt}:
          +s = Nat.add(Nat.add(x, y), c)
          and_i(Nat.is_lt(Nat.mod(s, 10000n), 10000n), L.limbs_ok(Big.add.go(xt, yt, Nat.div(s, 10000n))),
            PNat.mod_lt(s, 9999n), add_go_ok(xt, yt, Nat.div(s, 10000n)))

def add_val(+la: List<&2, Nat>, +lb: List<&2, Nat>)
  -> {L.limbs_val(Big.trim(Big.add.go(la, lb, 0n))) == Nat.add(L.limbs_val(la), L.limbs_val(lb)) : Nat}:
  %Equal.sym(Nat, L.limbs_val(Big.trim(Big.add.go(la, lb, 0n))), L.limbs_val(Big.add.go(la, lb, 0n)), val_trim(Big.add.go(la, lb, 0n)))
    : {_ == Nat.add(L.limbs_val(la), L.limbs_val(lb)) : Nat}
  %Equal.sym(Nat, Nat.add(L.limbs_val(la), L.limbs_val(lb)), Nat.add(Nat.add(L.limbs_val(la), L.limbs_val(lb)), 0n), PNat.add_zero(Nat.add(L.limbs_val(la), L.limbs_val(lb))))
    : {L.limbs_val(Big.add.go(la, lb, 0n)) == _ : Nat}
  add_go_val(la, lb, 0n)

def L.big_add(a, b, ha, hb):
  match a:
    case Big.Big{la}:
      match b:
        case Big.Big{lb}:
          (add_val(la, lb), big_ok_trim(Big.add.go(la, lb, 0n), add_go_ok(la, lb, 0n)))

# ---------------------------------------------------------------------
# Multiplication
# ---------------------------------------------------------------------

def mul_small_val(ys: List<&2, Nat>, +k: Nat, +c: Nat)
  -> {L.limbs_val(Big.mul_small.go(ys, k, c)) == Nat.add(Nat.mul(L.limbs_val(ys), k), c) : Nat}:
  match ys:
    case Nil{}:
      carry_val(c, c, le_refl(c))
    case Con{+y, +yt}:
      +s = Nat.add(Nat.mul(y, k), c)
      +vy = L.limbs_val(yt)
      %Equal.sym(Nat, L.limbs_val(Big.mul_small.go(yt, k, Nat.div(s, 10000n))), Nat.add(Nat.mul(vy, k), Nat.div(s, 10000n)), mul_small_val(yt, k, Nat.div(s, 10000n)))
        : {Nat.add(Nat.mod(s, 10000n), Nat.mul(10000n, _)) == Nat.add(Nat.mul(Nat.add(y, Nat.mul(10000n, vy)), k), c) : Nat}
      %PNat.mul_dist(y, Nat.mul(10000n, vy), k)
        : {Nat.add(Nat.mod(s, 10000n), Nat.mul(10000n, Nat.add(Nat.mul(vy, k), Nat.div(s, 10000n)))) == Nat.add(_, c) : Nat}
      %Equal.sym(Nat, Nat.mul(Nat.mul(10000n, vy), k), Nat.mul(10000n, Nat.mul(vy, k)), mul_assoc(10000n, vy, k))
        : {Nat.add(Nat.mod(s, 10000n), Nat.mul(10000n, Nat.add(Nat.mul(vy, k), Nat.div(s, 10000n)))) == Nat.add(Nat.add(Nat.mul(y, k), _), c) : Nat}
      alg_carry(10000n, Nat.mul(y, k), c, Nat.mul(vy, k), Nat.div(s, 10000n), Nat.mod(s, 10000n), recombine(s))

def mul_small_ok(ys: List<&2, Nat>, +k: Nat, +c: Nat) -> {L.limbs_ok(Big.mul_small.go(ys, k, c)) == True{} : Bool}:
  match ys:
    case Nil{}:
      carry_rest_ok(1n+c, Nat.is_eq(c, 0n), c)
    case Con{+y, +yt}:
      +s = Nat.add(Nat.mul(y, k), c)
      and_i(Nat.is_lt(Nat.mod(s, 10000n), 10000n), L.limbs_ok(Big.mul_small.go(yt, k, Nat.div(s, 10000n))),
        PNat.mod_lt(s, 9999n), mul_small_ok(yt, k, Nat.div(s, 10000n)))

# the value of mul_small(Big{ls}, k)
def mul_small_big(+ls: List<&2, Nat>, +k: Nat) -> {L.limbs_val(Big.limbs(Big.mul_small(Big.Big{ls}, k))) == Nat.mul(L.limbs_val(ls), k) : Nat}:
  +m = Big.mul_small.go(ls, k, 0n)
  %Equal.sym(Nat, L.limbs_val(Big.trim(m)), L.limbs_val(m), val_trim(m)) : {_ == Nat.mul(L.limbs_val(ls), k) : Nat}
  %Equal.sym(Nat, Nat.mul(L.limbs_val(ls), k), Nat.add(Nat.mul(L.limbs_val(ls), k), 0n), PNat.add_zero(Nat.mul(L.limbs_val(ls), k)))
    : {L.limbs_val(m) == _ : Nat}
  mul_small_val(ls, k, 0n)

def mul_small_big_ok(+ls: List<&2, Nat>, +k: Nat) -> {L.big_ok(Big.mul_small(Big.Big{ls}, k)) == True{} : Bool}:
  big_ok_trim(Big.mul_small.go(ls, k, 0n), mul_small_ok(ls, k, 0n))

def shift_val.of(e: Bool, +ls: List<&2, Nat>, +he: {e == List.is_empty(&2, Nat, ls) : Bool})
  -> {L.limbs_val(Big.shift1.of(e, ls)) == Nat.mul(10000n, L.limbs_val(ls)) : Nat}:
  match e:
    case True{}:
      %Equal.sym(List<&2, Nat>, ls, Nil{}, nil_of_empty(ls, Equal.sym(Bool, True{}, List.is_empty(&2, Nat, ls), he)))
        : {0n == Nat.mul(10000n, L.limbs_val(_)) : Nat}
      {==}
    case False{}:
      {==}

def shift_val(+ls: List<&2, Nat>) -> {L.limbs_val(Big.shift1(ls)) == Nat.mul(10000n, L.limbs_val(ls)) : Nat}:
  shift_val.of(List.is_empty(&2, Nat, ls), ls, {==})

def mul_go_val(xs: List<&2, Nat>, +lb: List<&2, Nat>) -> {L.limbs_val(Big.mul.go(xs, Big.Big{lb})) == Nat.mul(L.limbs_val(xs), L.limbs_val(lb)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      +vb = L.limbs_val(lb)
      +vx = L.limbs_val(xt)
      +a = Big.limbs(Big.mul_small(Big.Big{lb}, x))
      +sh = Big.shift1(Big.mul.go(xt, Big.Big{lb}))
      +rhs = Nat.mul(Nat.add(x, Nat.mul(10000n, vx)), vb)
      %Equal.sym(Nat, L.limbs_val(Big.add.go(a, sh, 0n)), Nat.add(Nat.add(L.limbs_val(a), L.limbs_val(sh)), 0n), add_go_val(a, sh, 0n))
        : {_ == rhs : Nat}
      %PNat.add_zero(Nat.add(L.limbs_val(a), L.limbs_val(sh))) : {_ == rhs : Nat}
      %Equal.sym(Nat, L.limbs_val(a), Nat.mul(vb, x), mul_small_big(lb, x)) : {Nat.add(_, L.limbs_val(sh)) == rhs : Nat}
      %Equal.sym(Nat, L.limbs_val(sh), Nat.mul(10000n, L.limbs_val(Big.mul.go(xt, Big.Big{lb}))), shift_val(Big.mul.go(xt, Big.Big{lb})))
        : {Nat.add(Nat.mul(vb, x), _) == rhs : Nat}
      %Equal.sym(Nat, L.limbs_val(Big.mul.go(xt, Big.Big{lb})), Nat.mul(vx, vb), mul_go_val(xt, lb))
        : {Nat.add(Nat.mul(vb, x), Nat.mul(10000n, _)) == rhs : Nat}
      %PNat.mul_dist(x, Nat.mul(10000n, vx), vb) : {Nat.add(Nat.mul(vb, x), Nat.mul(10000n, Nat.mul(vx, vb))) == _ : Nat}
      %Equal.sym(Nat, Nat.mul(Nat.mul(10000n, vx), vb), Nat.mul(10000n, Nat.mul(vx, vb)), mul_assoc(10000n, vx, vb))
        : {Nat.add(Nat.mul(vb, x), Nat.mul(10000n, Nat.mul(vx, vb))) == Nat.add(Nat.mul(x, vb), _) : Nat}
      %PNat.mul_comm(x, vb) : {Nat.add(_, Nat.mul(10000n, Nat.mul(vx, vb))) == Nat.add(Nat.mul(x, vb), Nat.mul(10000n, Nat.mul(vx, vb))) : Nat}
      {==}

def mul_go_ok(xs: List<&2, Nat>, +b: Big.Big) -> {L.limbs_ok(Big.mul.go(xs, b)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      add_go_ok(Big.limbs(Big.mul_small(b, x)), Big.shift1(Big.mul.go(xt, b)), 0n)

def mul_val(+la: List<&2, Nat>, +lb: List<&2, Nat>)
  -> {L.limbs_val(Big.trim(Big.mul.go(la, Big.Big{lb}))) == Nat.mul(L.limbs_val(la), L.limbs_val(lb)) : Nat}:
  %Equal.sym(Nat, L.limbs_val(Big.trim(Big.mul.go(la, Big.Big{lb}))), L.limbs_val(Big.mul.go(la, Big.Big{lb})), val_trim(Big.mul.go(la, Big.Big{lb})))
    : {_ == Nat.mul(L.limbs_val(la), L.limbs_val(lb)) : Nat}
  mul_go_val(la, lb)

def L.big_mul(a, b, ha, hb):
  match a:
    case Big.Big{la}:
      match b:
        case Big.Big{lb}:
          (mul_val(la, lb), big_ok_trim(Big.mul.go(la, Big.Big{lb}), mul_go_ok(la, Big.Big{lb})))

# ---------------------------------------------------------------------
# Comparison
# ---------------------------------------------------------------------

def cmp_zero_l(v: Nat, +h: {Nat.is_gt(v, 0n) == True{} : Bool}) -> {Nat.cmp(0n, v) == LT{} : Cmp}:
  match v:
    case 0n:
      Empty.absurd({Nat.cmp(0n, 0n) == LT{} : Cmp}, PNat.false_ne_true(h))
    case 1n++p:
      {==}

def cmp_zero_r(v: Nat, +h: {Nat.is_gt(v, 0n) == True{} : Bool}) -> {Nat.cmp(v, 0n) == GT{} : Cmp}:
  match v:
    case 0n:
      Empty.absurd({Nat.cmp(0n, 0n) == GT{} : Cmp}, PNat.false_ne_true(h))
    case 1n++p:
      {==}

def gt_add_mul(y: Nat, v: Nat, +h: {Nat.is_gt(v, 0n) == True{} : Bool}) -> {Nat.is_gt(Nat.add(y, Nat.mul(10000n, v)), 0n) == True{} : Bool}:
  match y:
    case 0n:
      match v:
        case 0n:
          Empty.absurd({Nat.is_gt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++p:
          {==}
    case 1n++q:
      {==}

def lnz_single(+y: Nat, yt: List<&2, Nat>, +he: {List.is_empty(&2, Nat, yt) == True{} : Bool}, +hl: {L.last_nonzero(Con{y, yt}) == True{} : Bool})
  -> {Nat.is_gt(y, 0n) == True{} : Bool}:
  match yt:
    case Nil{}:
      hl
    case Con{+g, +more}:
      Empty.absurd({Nat.is_gt(y, 0n) == True{} : Bool}, PNat.false_ne_true(he))

def pos.of(e: Bool, +y: Nat, +yt: List<&2, Nat>, +he: {e == List.is_empty(&2, Nat, yt) : Bool},
  +hl: {L.last_nonzero(Con{y, yt}) == True{} : Bool},
  ih: {L.last_nonzero(yt) == True{} : Bool} -> {List.is_empty(&2, Nat, yt) == False{} : Bool} -> {Nat.is_gt(L.limbs_val(yt), 0n) == True{} : Bool})
  -> {Nat.is_gt(Nat.add(y, Nat.mul(10000n, L.limbs_val(yt))), 0n) == True{} : Bool}:
  match e:
    case True{}:
      +he2 = Equal.sym(Bool, True{}, List.is_empty(&2, Nat, yt), he)
      %Equal.sym(List<&2, Nat>, yt, Nil{}, nil_of_empty(yt, he2)) : {Nat.is_gt(Nat.add(y, Nat.mul(10000n, L.limbs_val(_))), 0n) == True{} : Bool}
      %PNat.add_zero(y) : {Nat.is_gt(_, 0n) == True{} : Bool}
      lnz_single(y, yt, he2, hl)
    case False{}:
      gt_add_mul(y, L.limbs_val(yt), ih(lnz_tail(y, yt, hl), Equal.sym(Bool, False{}, List.is_empty(&2, Nat, yt), he)))

# a nonempty list with a nonzero top denotes more than 0
def pos(ls: List<&2, Nat>, +hl: {L.last_nonzero(ls) == True{} : Bool}, +hne: {List.is_empty(&2, Nat, ls) == False{} : Bool})
  -> {Nat.is_gt(L.limbs_val(ls), 0n) == True{} : Bool}:
  match ls:
    case Nil{}:
      Empty.absurd({Nat.is_gt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, hne)))
    case Con{+y, +yt}:
      pos.of(List.is_empty(&2, Nat, yt), y, yt, {==}, hl, h1 => h2 => pos(yt, h1, h2))

def cmp_cancel(b: Nat, -x: Nat, -y: Nat) -> {Nat.cmp(Nat.add(b, x), Nat.add(b, y)) == Nat.cmp(x, y) : Cmp}:
  match b:
    case 0n:
      {==}
    case 1n++p:
      cmp_cancel(p, x, y)

def cmp_lt_base(x: Nat, b: Nat, -w: Nat, +h: {Nat.is_lt(x, b) == True{} : Bool}) -> {Nat.cmp(x, Nat.add(b, w)) == LT{} : Cmp}:
  match x:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(0n, w) == LT{} : Cmp}, PNat.false_ne_true(h))
        case 1n++p:
          {==}
    case 1n++xp:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(1n+xp, w) == LT{} : Cmp}, PNat.false_ne_true(h))
        case 1n++p:
          cmp_lt_base(xp, p, w, h)

def cmp_gt_base(y: Nat, b: Nat, -w: Nat, +h: {Nat.is_lt(y, b) == True{} : Bool}) -> {Nat.cmp(Nat.add(b, w), y) == GT{} : Cmp}:
  match y:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(w, 0n) == GT{} : Cmp}, PNat.false_ne_true(h))
        case 1n++p:
          {==}
    case 1n++yp:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(w, 1n+yp) == GT{} : Cmp}, PNat.false_ne_true(h))
        case 1n++p:
          cmp_gt_base(yp, p, w, h)

# comparing x + B a with y + B b (digits x, y below B): the high parts first
def lex(a: Nat, c: Nat, +x: Nat, +y: Nat, +b: Nat, +hx: {Nat.is_lt(x, b) == True{} : Bool}, +hy: {Nat.is_lt(y, b) == True{} : Bool})
  -> {Nat.cmp(Nat.add(x, Nat.mul(b, a)), Nat.add(y, Nat.mul(b, c))) == Big.cmp_then(Nat.cmp(a, c), Nat.cmp(x, y)) : Cmp}:
  match a:
    case 0n:
      match c:
        case 0n:
          %Equal.sym(Nat, Nat.mul(b, 0n), 0n, PNat.mul_zero(b)) : {Nat.cmp(Nat.add(x, _), Nat.add(y, _)) == Nat.cmp(x, y) : Cmp}
          %PNat.add_zero(x) : {Nat.cmp(_, Nat.add(y, 0n)) == Nat.cmp(x, y) : Cmp}
          %PNat.add_zero(y) : {Nat.cmp(x, _) == Nat.cmp(x, y) : Cmp}
          {==}
        case 1n++cp:
          %Equal.sym(Nat, Nat.mul(b, 0n), 0n, PNat.mul_zero(b)) : {Nat.cmp(Nat.add(x, _), Nat.add(y, Nat.mul(b, 1n+cp))) == LT{} : Cmp}
          %PNat.add_zero(x) : {Nat.cmp(_, Nat.add(y, Nat.mul(b, 1n+cp))) == LT{} : Cmp}
          %PNat.mul_succ(b, cp) : {Nat.cmp(x, Nat.add(y, _)) == LT{} : Cmp}
          %PNat.add_swap(b, y, Nat.mul(b, cp)) : {Nat.cmp(x, _) == LT{} : Cmp}
          cmp_lt_base(x, b, Nat.add(y, Nat.mul(b, cp)), hx)
    case 1n++ap:
      match c:
        case 0n:
          %Equal.sym(Nat, Nat.mul(b, 0n), 0n, PNat.mul_zero(b)) : {Nat.cmp(Nat.add(x, Nat.mul(b, 1n+ap)), Nat.add(y, _)) == GT{} : Cmp}
          %PNat.add_zero(y) : {Nat.cmp(Nat.add(x, Nat.mul(b, 1n+ap)), _) == GT{} : Cmp}
          %PNat.mul_succ(b, ap) : {Nat.cmp(Nat.add(x, _), y) == GT{} : Cmp}
          %PNat.add_swap(b, x, Nat.mul(b, ap)) : {Nat.cmp(_, y) == GT{} : Cmp}
          cmp_gt_base(y, b, Nat.add(x, Nat.mul(b, ap)), hy)
        case 1n++cp:
          %PNat.mul_succ(b, ap) : {Nat.cmp(Nat.add(x, _), Nat.add(y, Nat.mul(b, 1n+cp))) == Big.cmp_then(Nat.cmp(ap, cp), Nat.cmp(x, y)) : Cmp}
          %PNat.mul_succ(b, cp) : {Nat.cmp(Nat.add(x, Nat.add(b, Nat.mul(b, ap))), Nat.add(y, _)) == Big.cmp_then(Nat.cmp(ap, cp), Nat.cmp(x, y)) : Cmp}
          %PNat.add_swap(b, x, Nat.mul(b, ap)) : {Nat.cmp(_, Nat.add(y, Nat.add(b, Nat.mul(b, cp)))) == Big.cmp_then(Nat.cmp(ap, cp), Nat.cmp(x, y)) : Cmp}
          %PNat.add_swap(b, y, Nat.mul(b, cp)) : {Nat.cmp(Nat.add(b, Nat.add(x, Nat.mul(b, ap))), _) == Big.cmp_then(Nat.cmp(ap, cp), Nat.cmp(x, y)) : Cmp}
          %Equal.sym(Cmp, Nat.cmp(Nat.add(b, Nat.add(x, Nat.mul(b, ap))), Nat.add(b, Nat.add(y, Nat.mul(b, cp)))), Nat.cmp(Nat.add(x, Nat.mul(b, ap)), Nat.add(y, Nat.mul(b, cp))),
              cmp_cancel(b, Nat.add(x, Nat.mul(b, ap)), Nat.add(y, Nat.mul(b, cp))))
            : {_ == Big.cmp_then(Nat.cmp(ap, cp), Nat.cmp(x, y)) : Cmp}
          lex(ap, cp, x, y, b, hx, hy)

# cmp.go on canonical lists is the comparison of their values
def cmp_go(xs: List<&2, Nat>, ys: List<&2, Nat>, +okx: {L.limbs_ok(xs) == True{} : Bool}, +lx: {L.last_nonzero(xs) == True{} : Bool},
  +oky: {L.limbs_ok(ys) == True{} : Bool}, +ly: {L.last_nonzero(ys) == True{} : Bool})
  -> {Big.cmp.go(xs, ys) == Nat.cmp(L.limbs_val(xs), L.limbs_val(ys)) : Cmp}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case Con{+y, +yt}:
          Equal.sym(Cmp, Nat.cmp(0n, L.limbs_val(Con{y, yt})), LT{}, cmp_zero_l(L.limbs_val(Con{y, yt}), pos(Con{y, yt}, ly, {==})))
    case Con{+x, +xt}:
      match ys:
        case Nil{}:
          Equal.sym(Cmp, Nat.cmp(L.limbs_val(Con{x, xt}), 0n), GT{}, cmp_zero_r(L.limbs_val(Con{x, xt}), pos(Con{x, xt}, lx, {==})))
        case Con{+y, +yt}:
          +hx = and_l(Nat.is_lt(x, 10000n), L.limbs_ok(xt), okx)
          +hy = and_l(Nat.is_lt(y, 10000n), L.limbs_ok(yt), oky)
          +ih = cmp_go(xt, yt, and_r(Nat.is_lt(x, 10000n), L.limbs_ok(xt), okx), lnz_tail(x, xt, lx),
            and_r(Nat.is_lt(y, 10000n), L.limbs_ok(yt), oky), lnz_tail(y, yt, ly))
          %Equal.sym(Cmp, Big.cmp.go(xt, yt), Nat.cmp(L.limbs_val(xt), L.limbs_val(yt)), ih)
            : {Big.cmp_then(_, Nat.cmp(x, y)) == Nat.cmp(Nat.add(x, Nat.mul(10000n, L.limbs_val(xt))), Nat.add(y, Nat.mul(10000n, L.limbs_val(yt)))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(Nat.add(x, Nat.mul(10000n, L.limbs_val(xt))), Nat.add(y, Nat.mul(10000n, L.limbs_val(yt)))),
            Big.cmp_then(Nat.cmp(L.limbs_val(xt), L.limbs_val(yt)), Nat.cmp(x, y)),
            lex(L.limbs_val(xt), L.limbs_val(yt), x, y, 10000n, hx, hy))

def norm_val(+ls: List<&2, Nat>) -> {L.limbs_val(Big.norm(ls)) == L.limbs_val(ls) : Nat}:
  +c = Big.carry.go(ls, 0n)
  %Equal.sym(Nat, L.limbs_val(Big.trim(c)), L.limbs_val(c), val_trim(c)) : {_ == L.limbs_val(ls) : Nat}
  %add_zero_r(L.limbs_val(ls)) : {L.limbs_val(c) == _ : Nat}
  carry_go_val(ls, 0n)

def cmp_big(+la: List<&2, Nat>, +lb: List<&2, Nat>) -> {Big.cmp(Big.Big{la}, Big.Big{lb}) == Nat.cmp(L.limbs_val(la), L.limbs_val(lb)) : Cmp}:
  +na = Big.norm(la)
  +nb = Big.norm(lb)
  +h = cmp_go(na, nb, ok_trim(Big.carry.go(la, 0n), carry_go_ok(la, 0n)), lnz_trim(Big.carry.go(la, 0n)),
    ok_trim(Big.carry.go(lb, 0n), carry_go_ok(lb, 0n)), lnz_trim(Big.carry.go(lb, 0n)))
  %norm_val(la) : {Big.cmp.go(na, nb) == Nat.cmp(_, L.limbs_val(lb)) : Cmp}
  %norm_val(lb) : {Big.cmp.go(na, nb) == Nat.cmp(L.limbs_val(na), _) : Cmp}
  h

def L.big_cmp(a, b):
  match a:
    case Big.Big{la}:
      match b:
        case Big.Big{lb}:
          cmp_big(la, lb)

# ---------------------------------------------------------------------
# Order
# ---------------------------------------------------------------------

def le_cancel(c: Nat, -a: Nat, -b: Nat) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == Nat.is_le(a, b) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      le_cancel(p, a, b)

def le_add_mono(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.add(c, a), Nat.add(c, b)), Nat.is_le(a, b), True{}, le_cancel(c, a, b), h)

def le_rw_l(-x: Nat, -y: Nat, -b: Nat, e: {x == y : Nat}, +h: {Nat.is_le(x, b) == True{} : Bool}) -> {Nat.is_le(y, b) == True{} : Bool}:
  %e : {Nat.is_le(_, b) == True{} : Bool}
  h

def le_rw_r(-a: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, +h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(a, y) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

def le_add_mono_r(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  le_rw_l(Nat.add(c, a), Nat.add(a, c), Nat.add(b, c), PNat.add_comm(c, a),
    le_rw_r(Nat.add(c, a), Nat.add(c, b), Nat.add(b, c), PNat.add_comm(c, b), le_add_mono(c, a, b, h)))

def le_add_both(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(c, d) == True{} : Bool})
  -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  le_trans(Nat.add(a, c), Nat.add(a, d), Nat.add(b, d), le_add_mono(a, c, d, h2), le_add_mono_r(d, a, b, h1))

def lt_to_le(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          le_zero(bp)
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(2n+ap, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          lt_to_le(ap, bp, h)

def le_to_lt(a: Nat, b: Nat, +h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          {==}
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          le_to_lt(ap, bp, h)

def nlt_le(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n++ap:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          nlt_le(ap, bp, h)

def nle_lt(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
        case 1n++bp:
          Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n++ap:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          nle_lt(ap, bp, h)

def le0(z: Nat, +h: {Nat.is_le(z, 0n) == True{} : Bool}) -> {z == 0n : Nat}:
  match z:
    case 0n:
      {==}
    case 1n++p:
      Empty.absurd({1n+p == 0n : Nat}, PNat.false_ne_true(h))

def lt_le_absurd(e: Nat, b: Nat, +h1: {Nat.is_lt(e, b) == True{} : Bool}, +h2: {Nat.is_le(b, e) == True{} : Bool}) -> Empty:
  match e:
    case 0n:
      match b:
        case 0n:
          PNat.false_ne_true(h1)
        case 1n++bp:
          PNat.false_ne_true(h2)
    case 1n++ep:
      match b:
        case 0n:
          PNat.false_ne_true(h1)
        case 1n++bp:
          lt_le_absurd(ep, bp, h1, h2)

# a B <= c B + e with e < B: a <= c
def floor(a: Nat, c: Nat, +b: Nat, +e: Nat, +he: {Nat.is_lt(e, b) == True{} : Bool},
  +h: {Nat.is_le(Nat.mul(a, b), Nat.add(Nat.mul(c, b), e)) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      le_zero(c)
    case 1n++ap:
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool},
            lt_le_absurd(e, b, he, le_trans(b, Nat.add(b, Nat.mul(ap, b)), e, le_add(b, Nat.mul(ap, b)), h)))
        case 1n++cp:
          +h2 = le_rw_r(Nat.add(b, Nat.mul(ap, b)), Nat.add(Nat.add(b, Nat.mul(cp, b)), e), Nat.add(b, Nat.add(Nat.mul(cp, b), e)),
            Equal.sym(Nat, Nat.add(b, Nat.add(Nat.mul(cp, b), e)), Nat.add(Nat.add(b, Nat.mul(cp, b)), e), PNat.add_assoc(b, Nat.mul(cp, b), e)), h)
          floor(ap, cp, b, e, he,
            Equal.trans(Bool, Nat.is_le(Nat.mul(ap, b), Nat.add(Nat.mul(cp, b), e)), Nat.is_le(Nat.add(b, Nat.mul(ap, b)), Nat.add(b, Nat.add(Nat.mul(cp, b), e))), True{},
              Equal.sym(Bool, Nat.is_le(Nat.add(b, Nat.mul(ap, b)), Nat.add(b, Nat.add(Nat.mul(cp, b), e))), Nat.is_le(Nat.mul(ap, b), Nat.add(Nat.mul(cp, b), e)),
                le_cancel(b, Nat.mul(ap, b), Nat.add(Nat.mul(cp, b), e))), h2))

def add_sub(u: Nat, z: Nat, +h: {Nat.is_le(u, z) == True{} : Bool}) -> {Nat.add(u, Nat.sub(z, u)) == z : Nat}:
  match u:
    case 0n:
      match z:
        case 0n:
          {==}
        case 1n++zp:
          {==}
    case 1n++up:
      match z:
        case 0n:
          Empty.absurd({Nat.add(1n+up, 0n) == 0n : Nat}, PNat.false_ne_true(h))
        case 1n++zp:
          %add_sub(up, zp, h) : {1n+Nat.add(up, Nat.sub(zp, up)) == 1n+_ : Nat}
          {==}

# ---------------------------------------------------------------------
# Subtraction
# ---------------------------------------------------------------------

def perm5(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat)
  -> {Nat.add(Nat.add(Nat.add(a, b), c), Nat.add(d, e)) == Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(b, e)) : Nat}:
  +rhs = Nat.add(Nat.add(Nat.add(a, c), d), Nat.add(b, e))
  %PNat.add_assoc(a, b, c) : {Nat.add(_, Nat.add(d, e)) == rhs : Nat}
  %PNat.add_comm(c, b) : {Nat.add(Nat.add(a, _), Nat.add(d, e)) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b), PNat.add_assoc(a, c, b)) : {Nat.add(_, Nat.add(d, e)) == rhs : Nat}
  %PNat.add_assoc(Nat.add(a, c), b, Nat.add(d, e)) : {_ == rhs : Nat}
  %PNat.add_swap(d, b, e) : {Nat.add(Nat.add(a, c), _) == rhs : Nat}
  PNat.add_assoc(Nat.add(a, c), d, Nat.add(b, e))

def perm4(+x: Nat, +p: Nat, +q: Nat, +r: Nat) -> {Nat.add(x, Nat.add(Nat.add(p, q), r)) == Nat.add(Nat.add(x, q), Nat.add(p, r)) : Nat}:
  %PNat.add_assoc(p, q, r) : {Nat.add(x, _) == Nat.add(Nat.add(x, q), Nat.add(p, r)) : Nat}
  %PNat.add_swap(q, p, r) : {Nat.add(x, _) == Nat.add(Nat.add(x, q), Nat.add(p, r)) : Nat}
  PNat.add_assoc(x, q, Nat.add(p, r))

def perm3(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(Nat.add(a, b), c), d) == Nat.add(Nat.add(Nat.add(a, c), d), b) : Nat}:
  +rhs = Nat.add(Nat.add(Nat.add(a, c), d), b)
  %PNat.add_assoc(a, b, c) : {Nat.add(_, d) == rhs : Nat}
  %PNat.add_comm(c, b) : {Nat.add(Nat.add(a, _), d) == rhs : Nat}
  %Equal.sym(Nat, Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b), PNat.add_assoc(a, c, b)) : {Nat.add(_, d) == rhs : Nat}
  %PNat.add_assoc(Nat.add(a, c), b, d) : {_ == rhs : Nat}
  %PNat.add_comm(d, b) : {Nat.add(Nat.add(a, c), _) == rhs : Nat}
  PNat.add_assoc(Nat.add(a, c), d, b)

def add_cong_r(-c: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}) -> {Nat.add(c, x) == Nat.add(c, y) : Nat}:
  %e : {Nat.add(c, x) == Nat.add(c, _) : Nat}
  {==}

def add_cong_l(-a: Nat, -a2: Nat, -c: Nat, e: {a == a2 : Nat}) -> {Nat.add(a, c) == Nat.add(a2, c) : Nat}:
  %e : {Nat.add(a, c) == Nat.add(_, c) : Nat}
  {==}

# ys == hd0(ys) + 10000 tl0(ys)
def val_split(ys: List<&2, Nat>) -> {L.limbs_val(ys) == Nat.add(Big.hd0(ys), Nat.mul(10000n, L.limbs_val(Big.tl0(ys)))) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      {==}

def hd0_lt(ys: List<&2, Nat>, +h: {L.limbs_ok(ys) == True{} : Bool}) -> {Nat.is_lt(Big.hd0(ys), 10000n) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      and_l(Nat.is_lt(y, 10000n), L.limbs_ok(t), h)

def tl0_ok(ys: List<&2, Nat>, +h: {L.limbs_ok(ys) == True{} : Bool}) -> {L.limbs_ok(Big.tl0(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      and_r(Nat.is_lt(y, 10000n), L.limbs_ok(t), h)

# the value step: (vy + w) + (hd + b R) == x + b X
def sub_core(+b: Nat, +vy: Nat, +y: Nat, +w: Nat, +hd: Nat, +x: Nat, +wp: Nat, +ry: Nat, +rr: Nat, +rx: Nat,
  +hvy: {vy == Nat.add(y, Nat.mul(b, ry)) : Nat},
  i: {Nat.add(Nat.add(y, w), hd) == Nat.add(x, Nat.mul(b, wp)) : Nat},
  ih: {Nat.add(Nat.add(ry, wp), rr) == rx : Nat})
  -> {Nat.add(Nat.add(vy, w), Nat.add(hd, Nat.mul(b, rr))) == Nat.add(x, Nat.mul(b, rx)) : Nat}:
  +lhs = Nat.add(Nat.add(Nat.add(y, Nat.mul(b, ry)), w), Nat.add(hd, Nat.mul(b, rr)))
  %Equal.sym(Nat, vy, Nat.add(y, Nat.mul(b, ry)), hvy) : {Nat.add(Nat.add(_, w), Nat.add(hd, Nat.mul(b, rr))) == Nat.add(x, Nat.mul(b, rx)) : Nat}
  %ih : {lhs == Nat.add(x, Nat.mul(b, _)) : Nat}
  %Equal.sym(Nat, Nat.mul(b, Nat.add(Nat.add(ry, wp), rr)), Nat.add(Nat.mul(b, Nat.add(ry, wp)), Nat.mul(b, rr)), mul_dist_l(b, Nat.add(ry, wp), rr))
    : {lhs == Nat.add(x, _) : Nat}
  %Equal.sym(Nat, Nat.mul(b, Nat.add(ry, wp)), Nat.add(Nat.mul(b, ry), Nat.mul(b, wp)), mul_dist_l(b, ry, wp))
    : {lhs == Nat.add(x, Nat.add(_, Nat.mul(b, rr))) : Nat}
  %Equal.sym(Nat, Nat.add(x, Nat.add(Nat.add(Nat.mul(b, ry), Nat.mul(b, wp)), Nat.mul(b, rr))), Nat.add(Nat.add(x, Nat.mul(b, wp)), Nat.add(Nat.mul(b, ry), Nat.mul(b, rr))),
      perm4(x, Nat.mul(b, ry), Nat.mul(b, wp), Nat.mul(b, rr)))
    : {lhs == _ : Nat}
  %i : {lhs == Nat.add(_, Nat.add(Nat.mul(b, ry), Nat.mul(b, rr))) : Nat}
  perm5(y, Nat.mul(b, ry), w, hd, Nat.mul(b, rr))

# ((y + b ry) + w) + hd == x + (wp + ry) b
def sub_floor.l(+b: Nat, +y: Nat, +w: Nat, +hd: Nat, +x: Nat, +wp: Nat, +ry: Nat,
  i: {Nat.add(Nat.add(y, w), hd) == Nat.add(x, Nat.mul(b, wp)) : Nat})
  -> {Nat.add(Nat.add(Nat.add(y, Nat.mul(b, ry)), w), hd) == Nat.add(x, Nat.mul(Nat.add(wp, ry), b)) : Nat}:
  +rhs = Nat.add(x, Nat.mul(Nat.add(wp, ry), b))
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(y, Nat.mul(b, ry)), w), hd), Nat.add(Nat.add(Nat.add(y, w), hd), Nat.mul(b, ry)), perm3(y, Nat.mul(b, ry), w, hd))
    : {_ == rhs : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(y, w), hd), Nat.add(x, Nat.mul(b, wp)), i) : {Nat.add(_, Nat.mul(b, ry)) == rhs : Nat}
  %PNat.mul_comm(b, Nat.add(wp, ry)) : {Nat.add(Nat.add(x, Nat.mul(b, wp)), Nat.mul(b, ry)) == Nat.add(x, _) : Nat}
  %Equal.sym(Nat, Nat.mul(b, Nat.add(wp, ry)), Nat.add(Nat.mul(b, wp), Nat.mul(b, ry)), mul_dist_l(b, wp, ry))
    : {Nat.add(Nat.add(x, Nat.mul(b, wp)), Nat.mul(b, ry)) == Nat.add(x, _) : Nat}
  Equal.sym(Nat, Nat.add(x, Nat.add(Nat.mul(b, wp), Nat.mul(b, ry))), Nat.add(Nat.add(x, Nat.mul(b, wp)), Nat.mul(b, ry)), PNat.add_assoc(x, Nat.mul(b, wp), Nat.mul(b, ry)))

# (x + b rx) + hd == x + (rx b + hd)
def sub_floor.r(+b: Nat, +x: Nat, +rx: Nat, +hd: Nat) -> {Nat.add(Nat.add(x, Nat.mul(b, rx)), hd) == Nat.add(x, Nat.add(Nat.mul(rx, b), hd)) : Nat}:
  %PNat.mul_comm(b, rx) : {Nat.add(Nat.add(x, Nat.mul(b, rx)), hd) == Nat.add(x, Nat.add(_, hd)) : Nat}
  Equal.sym(Nat, Nat.add(x, Nat.add(Nat.mul(b, rx), hd)), Nat.add(Nat.add(x, Nat.mul(b, rx)), hd), PNat.add_assoc(x, Nat.mul(b, rx), hd))

# the borrow step: ry + wp <= rx
def sub_floor(+b: Nat, +vy: Nat, +y: Nat, +w: Nat, +hd: Nat, +x: Nat, +wp: Nat, +ry: Nat, +rx: Nat,
  +hvy: {vy == Nat.add(y, Nat.mul(b, ry)) : Nat},
  i: {Nat.add(Nat.add(y, w), hd) == Nat.add(x, Nat.mul(b, wp)) : Nat},
  +hdlt: {Nat.is_lt(hd, b) == True{} : Bool},
  +h: {Nat.is_le(Nat.add(vy, w), Nat.add(x, Nat.mul(b, rx))) == True{} : Bool})
  -> {Nat.is_le(Nat.add(ry, wp), rx) == True{} : Bool}:
  +h0 = le_rw_l(Nat.add(vy, w), Nat.add(Nat.add(y, Nat.mul(b, ry)), w), Nat.add(x, Nat.mul(b, rx)), add_cong_l(vy, Nat.add(y, Nat.mul(b, ry)), w, hvy), h)
  +h1 = le_add_mono_r(hd, Nat.add(Nat.add(y, Nat.mul(b, ry)), w), Nat.add(x, Nat.mul(b, rx)), h0)
  +h2 = le_rw_l(Nat.add(Nat.add(Nat.add(y, Nat.mul(b, ry)), w), hd), Nat.add(x, Nat.mul(Nat.add(wp, ry), b)), Nat.add(Nat.add(x, Nat.mul(b, rx)), hd),
    sub_floor.l(b, y, w, hd, x, wp, ry, i), h1)
  +h3 = le_rw_r(Nat.add(x, Nat.mul(Nat.add(wp, ry), b)), Nat.add(Nat.add(x, Nat.mul(b, rx)), hd), Nat.add(x, Nat.add(Nat.mul(rx, b), hd)),
    sub_floor.r(b, x, rx, hd), h2)
  +h4 = Equal.trans(Bool, Nat.is_le(Nat.mul(Nat.add(wp, ry), b), Nat.add(Nat.mul(rx, b), hd)),
    Nat.is_le(Nat.add(x, Nat.mul(Nat.add(wp, ry), b)), Nat.add(x, Nat.add(Nat.mul(rx, b), hd))), True{},
    Equal.sym(Bool, Nat.is_le(Nat.add(x, Nat.mul(Nat.add(wp, ry), b)), Nat.add(x, Nat.add(Nat.mul(rx, b), hd))), Nat.is_le(Nat.mul(Nat.add(wp, ry), b), Nat.add(Nat.mul(rx, b), hd)),
      le_cancel(x, Nat.mul(Nat.add(wp, ry), b), Nat.add(Nat.mul(rx, b), hd))), h3)
  le_rw_l(Nat.add(wp, ry), Nat.add(ry, wp), rx, PNat.add_comm(wp, ry), floor(Nat.add(wp, ry), rx, b, hd, hdlt, h4))

# the digit of x - (y + w), borrowing 10000 when x < y + w
def sub_I(lo: Bool, +x: Nat, +y: Nat, +w: Nat, +hlo: {lo == Nat.is_lt(x, Nat.add(y, w)) : Bool},
  +hy: {Nat.is_lt(y, 10000n) == True{} : Bool}, +hw: {Nat.is_le(w, 1n) == True{} : Bool})
  -> {Nat.add(Nat.add(y, w), Nat.sub(Nat.add(x, Big.pick(Nat, lo, 10000n, 0n)), Nat.add(y, w))) == Nat.add(x, Big.pick(Nat, lo, 10000n, 0n)) : Nat}:
  match lo:
    case True{}:
      +h1 = le_rw_r(Nat.add(y, w), Nat.add(y, 1n), Nat.add(1n, y), PNat.add_comm(y, 1n), le_add_mono(y, w, 1n, hw))
      +h2 = le_trans(Nat.add(y, w), 1n+y, 10000n, h1, lt_to_le(y, 10000n, hy))
      add_sub(Nat.add(y, w), Nat.add(x, 10000n), le_trans(Nat.add(y, w), 10000n, Nat.add(x, 10000n), h2, le_add_l(10000n, x)))
    case False{}:
      +h1 = nlt_le(x, Nat.add(y, w), Equal.sym(Bool, False{}, Nat.is_lt(x, Nat.add(y, w)), hlo))
      add_sub(Nat.add(y, w), Nat.add(x, 0n), le_rw_r(Nat.add(y, w), x, Nat.add(x, 0n), PNat.add_zero(x), h1))

def sub_wp(lo: Bool) -> {Nat.is_le(Big.pick(Nat, lo, 1n, 0n), 1n) == True{} : Bool}:
  match lo:
    case True{}:
      {==}
    case False{}:
      {==}

# 1 + (x + 10000) == u + (1 + hd), from u + hd == x + 10000
def sub_hd_eq(+u: Nat, +hd: Nat, +x: Nat, i: {Nat.add(u, hd) == Nat.add(x, 10000n) : Nat})
  -> {Nat.add(1n+x, 10000n) == Nat.add(u, 1n+hd) : Nat}:
  %PNat.add_succ(u, hd) : {Nat.add(1n+x, 10000n) == _ : Nat}
  %Equal.sym(Nat, Nat.add(u, hd), Nat.add(x, 10000n), i) : {Nat.add(1n+x, 10000n) == 1n+_ : Nat}
  {==}

def sub_hdlt(lo: Bool, +x: Nat, +y: Nat, +w: Nat, +hlo: {lo == Nat.is_lt(x, Nat.add(y, w)) : Bool},
  +hx: {Nat.is_lt(x, 10000n) == True{} : Bool}, +hy: {Nat.is_lt(y, 10000n) == True{} : Bool}, +hw: {Nat.is_le(w, 1n) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(Nat.add(x, Big.pick(Nat, lo, 10000n, 0n)), Nat.add(y, w)), 10000n) == True{} : Bool}:
  match lo:
    case True{}:
      +u = Nat.add(y, w)
      +hd = Nat.sub(Nat.add(x, 10000n), u)
      +i = sub_I(True{}, x, y, w, hlo, hy, hw)
      +h1 = le_add_mono_r(10000n, 1n+x, u, lt_to_le(x, u, Equal.sym(Bool, True{}, Nat.is_lt(x, u), hlo)))
      +h2 = le_rw_l(Nat.add(1n+x, 10000n), Nat.add(u, 1n+hd), Nat.add(u, 10000n), sub_hd_eq(u, hd, x, i), h1)
      le_to_lt(hd, 10000n, Equal.trans(Bool, Nat.is_le(1n+hd, 10000n), Nat.is_le(Nat.add(u, 1n+hd), Nat.add(u, 10000n)), True{},
        Equal.sym(Bool, Nat.is_le(Nat.add(u, 1n+hd), Nat.add(u, 10000n)), Nat.is_le(1n+hd, 10000n), le_cancel(u, 1n+hd, 10000n)), h2))
    case False{}:
      +u = Nat.add(y, w)
      +hd = Nat.sub(Nat.add(x, 0n), u)
      +i = sub_I(False{}, x, y, w, hlo, hy, hw)
      +e = Equal.trans(Nat, Nat.add(u, hd), Nat.add(x, 0n), x, i, add_zero_r(x))
      +h1 = le_rw_r(hd, Nat.add(u, hd), x, e, le_add_l(hd, u))
      le_to_lt(hd, 10000n, le_trans(1n+hd, 1n+x, 10000n, h1, lt_to_le(x, 10000n, hx)))

# the borrow in limbs: b or 0 is b times 1 or 0
def bwl(lo: Bool, +b: Nat) -> {Big.pick(Nat, lo, b, 0n) == Nat.mul(b, Big.pick(Nat, lo, 1n, 0n)) : Nat}:
  match lo:
    case True{}:
      Equal.sym(Nat, Nat.mul(b, 1n), b, mul_one(b))
    case False{}:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, PNat.mul_zero(b))

def sub_val(xs: List<&2, Nat>, +ys: List<&2, Nat>, +w: Nat, +okx: {L.limbs_ok(xs) == True{} : Bool}, +oky: {L.limbs_ok(ys) == True{} : Bool},
  +hw: {Nat.is_le(w, 1n) == True{} : Bool}, +h: {Nat.is_le(Nat.add(L.limbs_val(ys), w), L.limbs_val(xs)) == True{} : Bool})
  -> {Nat.add(Nat.add(L.limbs_val(ys), w), L.limbs_val(Big.sub.go(xs, ys, w))) == L.limbs_val(xs) : Nat}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(L.limbs_val(ys), w), 0n, le0(Nat.add(L.limbs_val(ys), w), h)) : {Nat.add(_, 0n) == 0n : Nat}
      {==}
    case Con{+x, +xt}:
      +y = Big.hd0(ys)
      +lo = Nat.is_lt(x, Nat.add(y, w))
      +hd = Nat.sub(Nat.add(x, Big.pick(Nat, lo, 10000n, 0n)), Nat.add(y, w))
      +wp = Big.pick(Nat, lo, 1n, 0n)
      +hx = and_l(Nat.is_lt(x, 10000n), L.limbs_ok(xt), okx)
      +i = Equal.trans(Nat, Nat.add(Nat.add(y, w), hd), Nat.add(x, Big.pick(Nat, lo, 10000n, 0n)), Nat.add(x, Nat.mul(10000n, wp)),
        sub_I(lo, x, y, w, {==}, hd0_lt(ys, oky), hw), add_cong_r(x, Big.pick(Nat, lo, 10000n, 0n), Nat.mul(10000n, wp), bwl(lo, 10000n)))
      +hdlt = sub_hdlt(lo, x, y, w, {==}, hx, hd0_lt(ys, oky), hw)
      +hle = sub_floor(10000n, L.limbs_val(ys), y, w, hd, x, wp, L.limbs_val(Big.tl0(ys)), L.limbs_val(xt), val_split(ys), i, hdlt, h)
      +ih = sub_val(xt, Big.tl0(ys), wp, and_r(Nat.is_lt(x, 10000n), L.limbs_ok(xt), okx), tl0_ok(ys, oky), sub_wp(lo), hle)
      sub_core(10000n, L.limbs_val(ys), y, w, hd, x, wp, L.limbs_val(Big.tl0(ys)), L.limbs_val(Big.sub.go(xt, Big.tl0(ys), wp)), L.limbs_val(xt),
        val_split(ys), i, ih)

def sub_ok(xs: List<&2, Nat>, +ys: List<&2, Nat>, +w: Nat, +okx: {L.limbs_ok(xs) == True{} : Bool}, +oky: {L.limbs_ok(ys) == True{} : Bool},
  +hw: {Nat.is_le(w, 1n) == True{} : Bool}) -> {L.limbs_ok(Big.sub.go(xs, ys, w)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      +y = Big.hd0(ys)
      +lo = Nat.is_lt(x, Nat.add(y, w))
      +wp = Big.pick(Nat, lo, 1n, 0n)
      and_i(Nat.is_lt(Nat.sub(Nat.add(x, Big.pick(Nat, lo, 10000n, 0n)), Nat.add(y, w)), 10000n), L.limbs_ok(Big.sub.go(xt, Big.tl0(ys), wp)),
        sub_hdlt(lo, x, y, w, {==}, and_l(Nat.is_lt(x, 10000n), L.limbs_ok(xt), okx), hd0_lt(ys, oky), hw),
        sub_ok(xt, Big.tl0(ys), wp, and_r(Nat.is_lt(x, 10000n), L.limbs_ok(xt), okx), tl0_ok(ys, oky), sub_wp(lo)))

# ---------------------------------------------------------------------
# Division: the quotient digit
# ---------------------------------------------------------------------

def not_gt_le(c: Cmp) -> {Bool.not(Cmp.is_gt(c)) == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# le on canonical Bigs is <= on their values
def le_big(+xs: List<&2, Nat>, +ys: List<&2, Nat>, +okx: {L.limbs_ok(xs) == True{} : Bool}, +lx: {L.last_nonzero(xs) == True{} : Bool},
  +oky: {L.limbs_ok(ys) == True{} : Bool}, +ly: {L.last_nonzero(ys) == True{} : Bool})
  -> {Big.le(Big.Big{xs}, Big.Big{ys}) == Nat.is_le(L.limbs_val(xs), L.limbs_val(ys)) : Bool}:
  %Equal.sym(Cmp, Big.cmp.go(xs, ys), Nat.cmp(L.limbs_val(xs), L.limbs_val(ys)), cmp_go(xs, ys, okx, lx, oky, ly))
    : {Bool.not(Cmp.is_gt(_)) == Nat.is_le(L.limbs_val(xs), L.limbs_val(ys)) : Bool}
  not_gt_le(Nat.cmp(L.limbs_val(xs), L.limbs_val(ys)))

def lt_rw_r(-a: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, +h: {Nat.is_lt(a, x) == True{} : Bool}) -> {Nat.is_lt(a, y) == True{} : Bool}:
  %e : {Nat.is_lt(a, _) == True{} : Bool}
  h

def lt_rw_l(-x: Nat, -y: Nat, -b: Nat, e: {x == y : Nat}, +h: {Nat.is_lt(x, b) == True{} : Bool}) -> {Nat.is_lt(y, b) == True{} : Bool}:
  %e : {Nat.is_lt(_, b) == True{} : Bool}
  h

def mul_cong_r(-c: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}) -> {Nat.mul(c, x) == Nat.mul(c, y) : Nat}:
  %e : {Nat.mul(c, x) == Nat.mul(c, _) : Nat}
  {==}

def le_val_eq(-x: Nat, -y: Nat, -r: Nat, e: {x == y : Nat}) -> {Nat.is_le(x, r) == Nat.is_le(y, r) : Bool}:
  %e : {Nat.is_le(x, r) == Nat.is_le(_, r) : Bool}
  {==}

def lt0(v: Nat, +h: {Nat.is_lt(v, 0n) == True{} : Bool}) -> Empty:
  match v:
    case 0n:
      PNat.false_ne_true(h)
    case 1n++p:
      PNat.false_ne_true(h)

def le_mul_mono(c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(c, a), Nat.mul(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      le_add_both(a, b, Nat.mul(p, a), Nat.mul(p, b), h, le_mul_mono(p, a, b, h))

def succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def gt_lt(v: Nat, +h: {Nat.is_gt(v, 0n) == True{} : Bool}) -> {Nat.is_lt(0n, v) == True{} : Bool}:
  match v:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n++p:
      {==}

def lt_le_trans(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  le_to_lt(a, c, le_trans(1n+a, b, c, lt_to_le(a, b, h1), h2))

def le_lt_trans(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  le_to_lt(a, c, le_trans(1n+a, 1n+b, c, h1, lt_to_le(b, c, h2)))

def lt_mul_cancel.of(v: Bool, +vb: Nat, +d: Nat, +b: Nat, +hv: {v == Nat.is_lt(d, b) : Bool},
  +h: {Nat.is_lt(Nat.mul(vb, d), Nat.mul(vb, b)) == True{} : Bool}) -> {Nat.is_lt(d, b) == True{} : Bool}:
  match v:
    case True{}:
      Equal.sym(Bool, True{}, Nat.is_lt(d, b), hv)
    case False{}:
      Empty.absurd({Nat.is_lt(d, b) == True{} : Bool},
        lt_le_absurd(Nat.mul(vb, d), Nat.mul(vb, b), h, le_mul_mono(vb, b, d, nlt_le(d, b, Equal.sym(Bool, False{}, Nat.is_lt(d, b), hv)))))

def lt_mul_cancel(+vb: Nat, +d: Nat, +b: Nat, +h: {Nat.is_lt(Nat.mul(vb, d), Nat.mul(vb, b)) == True{} : Bool}) -> {Nat.is_lt(d, b) == True{} : Bool}:
  lt_mul_cancel.of(Nat.is_lt(d, b), vb, d, b, {==}, h)

def recomb(+n: Nat, +b: Nat) -> {Nat.add(Nat.mod(n, 1n+b), Nat.mul(1n+b, Nat.div(n, 1n+b))) == n : Nat}:
  %Equal.sym(Nat, n, Nat.add(Nat.mul(Nat.div(n, 1n+b), 1n+b), Nat.mod(n, 1n+b)), PNat.div_mod_eq(n, b))
    : {Nat.add(Nat.mod(n, 1n+b), Nat.mul(1n+b, Nat.div(n, 1n+b))) == _ : Nat}
  %PNat.mul_comm(Nat.div(n, 1n+b), 1n+b)
    : {Nat.add(Nat.mod(n, 1n+b), _) == Nat.add(Nat.mul(Nat.div(n, 1n+b), 1n+b), Nat.mod(n, 1n+b)) : Nat}
  PNat.add_comm(Nat.mod(n, 1n+b), Nat.mul(Nat.div(n, 1n+b), 1n+b))

# a reusable pair of facts
def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def P2.fst(-A: Data, -B: Data, +p: P2(A, B)) -> A:
  (a, b) = p
  a

def P2.snd(-A: Data, -B: Data, +p: P2(A, B)) -> B:
  (a, b) = p
  b

def ge_le(a: Nat, b: Nat, +h: {Nat.is_ge(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n++ap:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          ge_le(ap, bp, h)

def nge_lt(a: Nat, b: Nat, +h: {Nat.is_ge(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
        case 1n++bp:
          {==}
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
        case 1n++bp:
          nge_lt(ap, bp, h)

def sub_le0(a: Nat, b: Nat, +h: {Nat.is_le(Nat.sub(a, b), 0n) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a:
    case 0n:
      le_zero(b)
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          sub_le0(ap, bp, h)

def le_antisym(a: Nat, b: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          Empty.absurd({0n == 1n+bp : Nat}, PNat.false_ne_true(h2))
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({1n+ap == 0n : Nat}, PNat.false_ne_true(h1))
        case 1n++bp:
          succ_cong(ap, bp, le_antisym(ap, bp, h1, h2))

def succ_pred(+lo: Nat, m: Nat, +h: {Nat.is_lt(lo, m) == True{} : Bool}) -> {1n+Nat.sub(m, 1n) == m : Nat}:
  match m:
    case 0n:
      Empty.absurd({1n+Nat.sub(0n, 1n) == 0n : Nat}, lt0(lo, h))
    case 1n++p:
      match p:
        case 0n:
          {==}
        case 1n++q:
          {==}

def le_pred(lo: Nat, m: Nat, +h: {Nat.is_lt(lo, m) == True{} : Bool}) -> {Nat.is_le(lo, Nat.sub(m, 1n)) == True{} : Bool}:
  match lo:
    case 0n:
      le_zero(Nat.sub(m, 1n))
    case 1n++lp:
      match m:
        case 0n:
          Empty.absurd({Nat.is_le(1n+lp, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++mp:
          match mp:
            case 0n:
              Empty.absurd({Nat.is_le(1n+lp, 0n) == True{} : Bool}, lt0(lp, h))
            case 1n++mq:
              lt_to_le(lp, 1n+mq, h)

def le_succ(a: Nat) -> {Nat.is_le(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      le_succ(p)

def lt_succ_le(+a: Nat, +b: Nat, +f: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, 1n+f) == True{} : Bool}) -> {Nat.is_le(a, f) == True{} : Bool}:
  le_trans(1n+a, b, 1n+f, lt_to_le(a, b, h1), h2)

# lo + x == lo + y shape: a < b, both above lo, gives a - lo < b - lo
def sub_lt_l(+a: Nat, +b: Nat, +lo: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(lo, a) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(a, lo), Nat.sub(b, lo)) == True{} : Bool}:
  +x = Nat.sub(a, lo)
  +y = Nat.sub(b, lo)
  +hb = le_trans(lo, a, b, h2, le_trans(a, 1n+a, b, le_succ(a), lt_to_le(a, b, h1)))
  +l1 = le_rw_l(1n+a, Nat.add(lo, 1n+x), b,
    Equal.trans(Nat, 1n+a, 1n+Nat.add(lo, x), Nat.add(lo, 1n+x), succ_cong(a, Nat.add(lo, x), Equal.sym(Nat, Nat.add(lo, x), a, add_sub(lo, a, h2))), PNat.add_succ(lo, x)),
    lt_to_le(a, b, h1))
  +l2 = le_rw_r(Nat.add(lo, 1n+x), b, Nat.add(lo, y), Equal.sym(Nat, Nat.add(lo, y), b, add_sub(lo, b, hb)), l1)
  le_to_lt(x, y, Equal.trans(Bool, Nat.is_le(1n+x, y), Nat.is_le(Nat.add(lo, 1n+x), Nat.add(lo, y)), True{},
    Equal.sym(Bool, Nat.is_le(Nat.add(lo, 1n+x), Nat.add(lo, y)), Nat.is_le(1n+x, y), le_cancel(lo, 1n+x, y)), l2))

# lo < m <= hi: hi - m < hi - lo
def sub_lt_r(+hi: Nat, +lo: Nat, +m: Nat, +h1: {Nat.is_lt(lo, m) == True{} : Bool}, +h2: {Nat.is_le(m, hi) == True{} : Bool})
  -> {Nat.is_lt(Nat.sub(hi, m), Nat.sub(hi, lo)) == True{} : Bool}:
  +x = Nat.sub(hi, m)
  +y = Nat.sub(hi, lo)
  +hl = le_trans(lo, 1n+lo, hi, le_succ(lo), le_trans(1n+lo, m, hi, lt_to_le(lo, m, h1), h2))
  +l1 = le_add_mono_r(x, 1n+lo, m, lt_to_le(lo, m, h1))
  +l2 = le_rw_r(1n+Nat.add(lo, x), Nat.add(m, x), Nat.add(lo, y),
    Equal.trans(Nat, Nat.add(m, x), hi, Nat.add(lo, y), add_sub(m, hi, h2), Equal.sym(Nat, Nat.add(lo, y), hi, add_sub(lo, hi, hl))), l1)
  +l3 = le_rw_l(1n+Nat.add(lo, x), Nat.add(lo, 1n+x), Nat.add(lo, y), PNat.add_succ(lo, x), l2)
  le_to_lt(x, y, Equal.trans(Bool, Nat.is_le(1n+x, y), Nat.is_le(Nat.add(lo, 1n+x), Nat.add(lo, y)), True{},
    Equal.sym(Bool, Nat.is_le(Nat.add(lo, 1n+x), Nat.add(lo, y)), Nat.is_le(1n+x, y), le_cancel(lo, 1n+x, y)), l3))

def two_eq(+x: Nat) -> {Nat.mul(x, 2n) == Nat.add(x, x) : Nat}:
  Equal.trans(Nat, Nat.mul(x, 2n), Nat.mul(2n, x), Nat.add(x, x), PNat.mul_comm(x, 2n), add_cong_r(x, Nat.add(x, 0n), x, add_zero_r(x)))

# (lo + hi) + 1 == 1 + (lo + hi)
def s_eq(+lo: Nat, +hi: Nat) -> {Nat.add(Nat.add(lo, hi), 1n) == 1n+Nat.add(lo, hi) : Nat}:
  PNat.add_comm(Nat.add(lo, hi), 1n)

# the midpoint of lo < hi, rounded up, lies in lo+1 .. hi
def mid_le(+lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool})
  -> {Nat.is_le(Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n), hi) == True{} : Bool}:
  +s = Nat.add(Nat.add(lo, hi), 1n)
  +q = Nat.div(s, 2n)
  +r = Nat.mod(s, 2n)
  +a = le_rw_r(Nat.mul(2n, q), Nat.add(r, Nat.mul(2n, q)), s, recomb(s, 1n), le_add_l(Nat.mul(2n, q), r))
  +b = le_rw_l(Nat.add(1n+lo, hi), s, Nat.add(hi, hi), Equal.sym(Nat, s, 1n+Nat.add(lo, hi), s_eq(lo, hi)), le_add_mono_r(hi, 1n+lo, hi, lt_to_le(lo, hi, h)))
  +c = le_trans(Nat.mul(2n, q), s, Nat.add(hi, hi), a, b)
  +c2 = le_rw_l(Nat.mul(2n, q), Nat.mul(q, 2n), Nat.add(hi, hi), PNat.mul_comm(2n, q), c)
  +c3 = le_rw_r(Nat.mul(q, 2n), Nat.add(hi, hi), Nat.add(Nat.mul(hi, 2n), 0n),
    Equal.trans(Nat, Nat.add(hi, hi), Nat.mul(hi, 2n), Nat.add(Nat.mul(hi, 2n), 0n), Equal.sym(Nat, Nat.mul(hi, 2n), Nat.add(hi, hi), two_eq(hi)), PNat.add_zero(Nat.mul(hi, 2n))), c2)
  floor(q, hi, 2n, 0n, {==}, c3)

def mid_gt(+lo: Nat, +hi: Nat, +h: {Nat.is_lt(lo, hi) == True{} : Bool})
  -> {Nat.is_lt(lo, Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n)) == True{} : Bool}:
  +s = Nat.add(Nat.add(lo, hi), 1n)
  +q = Nat.div(s, 2n)
  +r = Nat.mod(s, 2n)
  +d1 = le_add_mono_r(Nat.mul(2n, q), r, 1n, lt_to_le(r, 2n, PNat.mod_lt(s, 1n)))
  +d2 = le_rw_l(Nat.add(r, Nat.mul(2n, q)), s, 1n+Nat.mul(2n, q), recomb(s, 1n), d1)
  +d3 = le_rw_l(s, 1n+Nat.add(lo, hi), 1n+Nat.mul(2n, q), s_eq(lo, hi), d2)
  +e1 = le_add_mono(1n+lo, 1n+lo, hi, lt_to_le(lo, hi, h))
  +e2 = le_trans(Nat.add(1n+lo, 1n+lo), 1n+Nat.add(lo, hi), 1n+Nat.mul(2n, q), e1, d3)
  +e3 = le_rw_l(Nat.add(1n+lo, 1n+lo), Nat.mul(1n+lo, 2n), 1n+Nat.mul(2n, q), Equal.sym(Nat, Nat.mul(1n+lo, 2n), Nat.add(1n+lo, 1n+lo), two_eq(1n+lo)), e2)
  +e4 = le_rw_r(Nat.mul(1n+lo, 2n), 1n+Nat.mul(2n, q), Nat.add(Nat.mul(q, 2n), 1n),
    Equal.trans(Nat, 1n+Nat.mul(2n, q), 1n+Nat.mul(q, 2n), Nat.add(Nat.mul(q, 2n), 1n), succ_cong(Nat.mul(2n, q), Nat.mul(q, 2n), PNat.mul_comm(2n, q)), PNat.add_comm(1n, Nat.mul(q, 2n))), e3)
  le_to_lt(lo, q, floor(1n+lo, q, 2n, 1n, {==}, e4))

def qs.spec(+lb: List<&2, Nat>, +lr: List<&2, Nat>, +dd: Nat) -> Data:
  P2({Nat.is_le(Nat.mul(L.limbs_val(lb), dd), L.limbs_val(lr)) == True{} : Bool}, {Nat.is_lt(L.limbs_val(lr), Nat.mul(L.limbs_val(lb), 1n+dd)) == True{} : Bool})

# lo == hi: the search is done
def qs.done(+lb: List<&2, Nat>, +lo: Nat, +hi: Nat, +lr: List<&2, Nat>,
  +i1: {Nat.is_le(Nat.mul(L.limbs_val(lb), lo), L.limbs_val(lr)) == True{} : Bool},
  +i2: {Nat.is_lt(L.limbs_val(lr), Nat.mul(L.limbs_val(lb), 1n+hi)) == True{} : Bool},
  +e: {lo == hi : Nat}) -> qs.spec(lb, lr, lo):
  (i1, lt_rw_r(L.limbs_val(lr), Nat.mul(L.limbs_val(lb), 1n+hi), Nat.mul(L.limbs_val(lb), 1n+lo),
    mul_cong_r(L.limbs_val(lb), 1n+hi, 1n+lo, succ_cong(hi, lo, Equal.sym(Nat, lo, hi, e))), i2))

def qs.step(ok: Bool, +fp: Nat, +lb: List<&2, Nat>, +lo: Nat, +hi: Nat, +lr: List<&2, Nat>,
  +hok: {ok == Big.le(Big.mul_small(Big.Big{lb}, Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n)), Big.Big{lr}) : Bool},
  +okb: {L.limbs_ok(lb) == True{} : Bool}, +okr: {L.limbs_ok(lr) == True{} : Bool}, +lnr: {L.last_nonzero(lr) == True{} : Bool},
  +i1: {Nat.is_le(Nat.mul(L.limbs_val(lb), lo), L.limbs_val(lr)) == True{} : Bool},
  +i2: {Nat.is_lt(L.limbs_val(lr), Nat.mul(L.limbs_val(lb), 1n+hi)) == True{} : Bool},
  +hlt: {Nat.is_lt(lo, hi) == True{} : Bool},
  +hf: {Nat.is_le(Nat.sub(hi, lo), 1n+fp) == True{} : Bool},
  ih: @lo2:Nat -> @hi2:Nat -> {Nat.is_le(Nat.mul(L.limbs_val(lb), lo2), L.limbs_val(lr)) == True{} : Bool}
      -> {Nat.is_lt(L.limbs_val(lr), Nat.mul(L.limbs_val(lb), 1n+hi2)) == True{} : Bool}
      -> {Nat.is_le(lo2, hi2) == True{} : Bool}
      -> {Nat.is_le(Nat.sub(hi2, lo2), fp) == True{} : Bool}
      -> qs.spec(lb, lr, Big.qsearch(lb, fp, Nat.is_ge(lo2, hi2), lo2, hi2, Big.Big{lb}, Big.Big{lr})))
  -> qs.spec(lb, lr, Big.qsearch(lb, fp,
       Nat.is_ge(Big.pick(Nat, ok, Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n), lo), Big.pick(Nat, ok, hi, Nat.sub(Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n), 1n))),
       Big.pick(Nat, ok, Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n), lo), Big.pick(Nat, ok, hi, Nat.sub(Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n), 1n)),
       Big.Big{lb}, Big.Big{lr})):
  match ok:
    case True{}:
      +vb = L.limbs_val(lb)
      +vr = L.limbs_val(lr)
      +mid = Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n)
      +m = Big.limbs(Big.mul_small(Big.Big{lb}, mid))
      +okm = mul_small_big_ok(lb, mid)
      +hle = le_big(m, lr, and_l(L.limbs_ok(m), L.last_nonzero(m), okm), and_r(L.limbs_ok(m), L.last_nonzero(m), okm), okr, lnr)
      +hm = le_val_eq(L.limbs_val(m), Nat.mul(vb, mid), vr, mul_small_big(lb, mid))
      +ht = Equal.trans(Bool, Nat.is_le(Nat.mul(vb, mid), vr), Nat.is_le(L.limbs_val(m), vr), True{}, Equal.sym(Bool, Nat.is_le(L.limbs_val(m), vr), Nat.is_le(Nat.mul(vb, mid), vr), hm),
        Equal.trans(Bool, Nat.is_le(L.limbs_val(m), vr), Big.le(Big.Big{m}, Big.Big{lr}), True{}, Equal.sym(Bool, Big.le(Big.Big{m}, Big.Big{lr}), Nat.is_le(L.limbs_val(m), vr), hle),
          Equal.sym(Bool, True{}, Big.le(Big.Big{m}, Big.Big{lr}), hok)))
      +hml = mid_le(lo, hi, hlt)
      ih(mid, hi, ht, i2, hml, lt_succ_le(Nat.sub(hi, mid), Nat.sub(hi, lo), fp, sub_lt_r(hi, lo, mid, mid_gt(lo, hi, hlt), hml), hf))
    case False{}:
      +vb = L.limbs_val(lb)
      +vr = L.limbs_val(lr)
      +mid = Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n)
      +m = Big.limbs(Big.mul_small(Big.Big{lb}, mid))
      +okm = mul_small_big_ok(lb, mid)
      +hle = le_big(m, lr, and_l(L.limbs_ok(m), L.last_nonzero(m), okm), and_r(L.limbs_ok(m), L.last_nonzero(m), okm), okr, lnr)
      +hm = le_val_eq(L.limbs_val(m), Nat.mul(vb, mid), vr, mul_small_big(lb, mid))
      +hf2 = Equal.trans(Bool, Nat.is_le(Nat.mul(vb, mid), vr), Nat.is_le(L.limbs_val(m), vr), False{}, Equal.sym(Bool, Nat.is_le(L.limbs_val(m), vr), Nat.is_le(Nat.mul(vb, mid), vr), hm),
        Equal.trans(Bool, Nat.is_le(L.limbs_val(m), vr), Big.le(Big.Big{m}, Big.Big{lr}), False{}, Equal.sym(Bool, Big.le(Big.Big{m}, Big.Big{lr}), Nat.is_le(L.limbs_val(m), vr), hle),
          Equal.sym(Bool, False{}, Big.le(Big.Big{m}, Big.Big{lr}), hok)))
      +hgt = mid_gt(lo, hi, hlt)
      +hml = mid_le(lo, hi, hlt)
      +sp = succ_pred(lo, mid, hgt)
      +i2b = lt_rw_r(vr, Nat.mul(vb, mid), Nat.mul(vb, 1n+Nat.sub(mid, 1n)), mul_cong_r(vb, mid, 1n+Nat.sub(mid, 1n), Equal.sym(Nat, 1n+Nat.sub(mid, 1n), mid, sp)),
        nle_lt(Nat.mul(vb, mid), vr, hf2))
      +i3b = le_pred(lo, mid, hgt)
      +hm1 = le_to_lt(Nat.sub(mid, 1n), hi, le_rw_l(mid, 1n+Nat.sub(mid, 1n), hi, Equal.sym(Nat, 1n+Nat.sub(mid, 1n), mid, sp), hml))
      ih(lo, Nat.sub(mid, 1n), i1, i2b, i3b, lt_succ_le(Nat.sub(Nat.sub(mid, 1n), lo), Nat.sub(hi, lo), fp, sub_lt_l(Nat.sub(mid, 1n), hi, lo, hm1, i3b), hf))

# the bisection finds the quotient digit: vb d <= vr < vb (1 + d)
def qs_spec(lb: List<&2, Nat>, f: Nat, stop: Bool, +lo: Nat, +hi: Nat, +lr: List<&2, Nat>,
  +okb: {L.limbs_ok(lb) == True{} : Bool}, +okr: {L.limbs_ok(lr) == True{} : Bool}, +lnr: {L.last_nonzero(lr) == True{} : Bool},
  +i1: {Nat.is_le(Nat.mul(L.limbs_val(lb), lo), L.limbs_val(lr)) == True{} : Bool},
  +i2: {Nat.is_lt(L.limbs_val(lr), Nat.mul(L.limbs_val(lb), 1n+hi)) == True{} : Bool},
  +i3: {Nat.is_le(lo, hi) == True{} : Bool},
  +hs: {stop == Nat.is_ge(lo, hi) : Bool},
  +hf: {Nat.is_le(Nat.sub(hi, lo), f) == True{} : Bool})
  -> qs.spec(lb, lr, Big.qsearch(lb, f, stop, lo, hi, Big.Big{lb}, Big.Big{lr})):
  match lb:
    case Nil{}:
      Empty.absurd(qs.spec(Nil{}, lr, Big.qsearch(Nil{}, f, stop, lo, hi, Big.Big{Nil{}}, Big.Big{lr})), lt0(L.limbs_val(lr), i2))
    case Con{+g, +more}:
      match f:
        case 0n:
          qs.done(Con{g, more}, lo, hi, lr, i1, i2, le_antisym(lo, hi, i3, sub_le0(hi, lo, hf)))
        case 1n++fp:
          match stop:
            case True{}:
              qs.done(Con{g, more}, lo, hi, lr, i1, i2, le_antisym(lo, hi, i3, ge_le(lo, hi, Equal.sym(Bool, True{}, Nat.is_ge(lo, hi), hs))))
            case False{}:
              qs.step(Big.le(Big.mul_small(Big.Big{Con{g, more}}, Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n)), Big.Big{lr}), fp, Con{g, more}, lo, hi, lr, {==},
                okb, okr, lnr, i1, i2, nge_lt(lo, hi, Equal.sym(Bool, False{}, Nat.is_ge(lo, hi), hs)), hf,
                +lo2 => +hi2 => e1 => e2 => e3 => e4 => qs_spec(Con{g, more}, fp, Nat.is_ge(lo2, hi2), lo2, hi2, lr, okb, okr, lnr, e1, e2, e3, {==}, e4))
# ---------------------------------------------------------------------
# Division: the long-division step
# ---------------------------------------------------------------------

# h + b vr < vb b, for h < b and vr < vb (b symbolic: closed products of
# 10000 would expand into terms deep enough to overflow the checker)
def r2_bound.g(+b: Nat, +h: Nat, +vr: Nat, +vb: Nat, +hh: {Nat.is_lt(h, b) == True{} : Bool}, +hr: {Nat.is_lt(vr, vb) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(h, Nat.mul(b, vr)), Nat.mul(vb, b)) == True{} : Bool}:
  +a2 = le_add_mono_r(Nat.mul(b, vr), 1n+h, b, lt_to_le(h, b, hh))
  +a2b = le_rw_r(1n+Nat.add(h, Nat.mul(b, vr)), Nat.add(b, Nat.mul(b, vr)), Nat.mul(b, 1n+vr), PNat.mul_succ(b, vr), a2)
  +a3 = le_rw_r(Nat.mul(b, 1n+vr), Nat.mul(b, vb), Nat.mul(vb, b), PNat.mul_comm(b, vb), le_mul_mono(b, 1n+vr, vb, lt_to_le(vr, vb, hr)))
  le_to_lt(Nat.add(h, Nat.mul(b, vr)), Nat.mul(vb, b), le_trans(1n+Nat.add(h, Nat.mul(b, vr)), Nat.mul(b, 1n+vr), Nat.mul(vb, b), a2b, a3))

def r2_bound(+h: Nat, +vr: Nat, +vb: Nat, +hh: {Nat.is_lt(h, 10000n) == True{} : Bool}, +hr: {Nat.is_lt(vr, vb) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(h, Nat.mul(10000n, vr)), Nat.mul(vb, 10000n)) == True{} : Bool}:
  r2_bound.g(10000n, h, vr, vb, hh, hr)

# (a + c) + r == (a + r) + c
def swap_last(+a: Nat, +c: Nat, +r: Nat) -> {Nat.add(Nat.add(a, c), r) == Nat.add(Nat.add(a, r), c) : Nat}:
  %PNat.add_assoc(a, c, r) : {_ == Nat.add(Nat.add(a, r), c) : Nat}
  %PNat.add_comm(r, c) : {Nat.add(a, _) == Nat.add(Nat.add(a, r), c) : Nat}
  PNat.add_assoc(a, r, c)

def alg_div(+b: Nat, +d: Nat, +vq: Nat, +vb: Nat, +rr: Nat, +h: Nat, +vr: Nat, +v: Nat,
  e1: {Nat.add(Nat.add(Nat.mul(vb, d), 0n), rr) == Nat.add(h, Nat.mul(b, vr)) : Nat},
  e2: {Nat.add(Nat.mul(vq, vb), vr) == v : Nat})
  -> {Nat.add(Nat.mul(Nat.add(d, Nat.mul(b, vq)), vb), rr) == Nat.add(h, Nat.mul(b, v)) : Nat}:
  +lhs = Nat.add(Nat.mul(Nat.add(d, Nat.mul(b, vq)), vb), rr)
  +x = Nat.mul(b, Nat.mul(vq, vb))
  +y = Nat.mul(b, vr)
  %e2 : {lhs == Nat.add(h, Nat.mul(b, _)) : Nat}
  %Equal.sym(Nat, Nat.mul(b, Nat.add(Nat.mul(vq, vb), vr)), Nat.add(x, y), mul_dist_l(b, Nat.mul(vq, vb), vr)) : {lhs == Nat.add(h, _) : Nat}
  %PNat.add_comm(y, x) : {lhs == Nat.add(h, _) : Nat}
  %Equal.sym(Nat, Nat.add(h, Nat.add(y, x)), Nat.add(Nat.add(h, y), x), PNat.add_assoc(h, y, x)) : {lhs == _ : Nat}
  %e1 : {lhs == Nat.add(_, x) : Nat}
  %PNat.add_zero(Nat.mul(vb, d)) : {lhs == Nat.add(Nat.add(_, rr), x) : Nat}
  %PNat.mul_dist(d, Nat.mul(b, vq), vb) : {Nat.add(_, rr) == Nat.add(Nat.add(Nat.mul(vb, d), rr), x) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(b, vq), vb), x, mul_assoc(b, vq, vb)) : {Nat.add(Nat.add(Nat.mul(d, vb), _), rr) == Nat.add(Nat.add(Nat.mul(vb, d), rr), x) : Nat}
  %PNat.mul_comm(vb, d) : {Nat.add(Nat.add(_, x), rr) == Nat.add(Nat.add(Nat.mul(vb, d), rr), x) : Nat}
  swap_last(Nat.mul(vb, d), x, rr)

def add00_cong(-a: Nat, -a2: Nat, -r: Nat, e: {a == a2 : Nat}) -> {Nat.add(Nat.add(a, 0n), r) == Nat.add(Nat.add(a2, 0n), r) : Nat}:
  %e : {Nat.add(Nat.add(a, 0n), r) == Nat.add(Nat.add(_, 0n), r) : Nat}
  {==}

def DSa(+acc: Big.QR, +vb: Nat, +v: Nat) -> Data:
  {Nat.add(Nat.mul(L.limbs_val(Big.QR.q(acc)), vb), L.big_val(Big.QR.r(acc))) == v : Nat}

def DSb(+acc: Big.QR, +vb: Nat) -> Data:
  {Nat.is_lt(L.big_val(Big.QR.r(acc)), vb) == True{} : Bool}

def DSc(+acc: Big.QR) -> Data:
  {L.big_ok(Big.QR.r(acc)) == True{} : Bool}

def DSd(+acc: Big.QR) -> Data:
  {L.limbs_ok(Big.QR.q(acc)) == True{} : Bool}

# what long division keeps: Euclid's equation so far, the remainder below
# the divisor and canonical, the quotient's limbs digits
def DSpec(+acc: Big.QR, +vb: Nat, +v: Nat) -> Data:
  P2(P2(DSa(acc, vb, v), DSb(acc, vb)), P2(DSc(acc), DSd(acc)))

def ds_a(+acc: Big.QR, +vb: Nat, +v: Nat, +p: DSpec(acc, vb, v)) -> DSa(acc, vb, v):
  P2.fst(DSa(acc, vb, v), DSb(acc, vb), P2.fst(P2(DSa(acc, vb, v), DSb(acc, vb)), P2(DSc(acc), DSd(acc)), p))

def ds_b(+acc: Big.QR, +vb: Nat, +v: Nat, +p: DSpec(acc, vb, v)) -> DSb(acc, vb):
  P2.snd(DSa(acc, vb, v), DSb(acc, vb), P2.fst(P2(DSa(acc, vb, v), DSb(acc, vb)), P2(DSc(acc), DSd(acc)), p))

def ds_c(+acc: Big.QR, +vb: Nat, +v: Nat, +p: DSpec(acc, vb, v)) -> DSc(acc):
  P2.fst(DSc(acc), DSd(acc), P2.snd(P2(DSa(acc, vb, v), DSb(acc, vb)), P2(DSc(acc), DSd(acc)), p))

def ds_d(+acc: Big.QR, +vb: Nat, +v: Nat, +p: DSpec(acc, vb, v)) -> DSd(acc):
  P2.snd(DSc(acc), DSd(acc), P2.snd(P2(DSa(acc, vb, v), DSb(acc, vb)), P2(DSc(acc), DSd(acc)), p))

def step_val(+dd: Nat, +vq: Nat, +vb: Nat, +s: List<&2, Nat>, +h: Nat, +vr: Nat, +v: Nat,
  e1: {Nat.add(Nat.add(Nat.mul(vb, dd), 0n), L.limbs_val(s)) == Nat.add(h, Nat.mul(10000n, vr)) : Nat},
  e2: {Nat.add(Nat.mul(vq, vb), vr) == v : Nat})
  -> {Nat.add(Nat.mul(Nat.add(dd, Nat.mul(10000n, vq)), vb), L.limbs_val(Big.trim(s))) == Nat.add(h, Nat.mul(10000n, v)) : Nat}:
  %Equal.sym(Nat, L.limbs_val(Big.trim(s)), L.limbs_val(s), val_trim(s)) : {Nat.add(Nat.mul(Nat.add(dd, Nat.mul(10000n, vq)), vb), _) == Nat.add(h, Nat.mul(10000n, v)) : Nat}
  alg_div(10000n, dd, vq, vb, L.limbs_val(s), h, vr, v, e1, e2)

def e1b(+a: Nat, -rr: Nat, -vr2: Nat, -w: Nat, e1: {Nat.add(Nat.add(a, 0n), rr) == w : Nat}, +hx: {vr2 == w : Nat}) -> {vr2 == Nat.add(a, rr) : Nat}:
  %Equal.sym(Nat, vr2, w, hx) : {_ == Nat.add(a, rr) : Nat}
  %e1 : {_ == Nat.add(a, rr) : Nat}
  %PNat.add_zero(a) : {Nat.add(_, rr) == Nat.add(a, rr) : Nat}
  {==}

def mul_succ_r(+vb: Nat, +dd: Nat) -> {Nat.mul(vb, Nat.add(dd, 1n)) == Nat.add(Nat.mul(vb, dd), vb) : Nat}:
  %Equal.sym(Nat, Nat.mul(vb, Nat.add(dd, 1n)), Nat.add(Nat.mul(vb, dd), Nat.mul(vb, 1n)), mul_dist_l(vb, dd, 1n)) : {_ == Nat.add(Nat.mul(vb, dd), vb) : Nat}
  %mul_one(vb) : {Nat.add(Nat.mul(vb, dd), Nat.mul(vb, 1n)) == Nat.add(Nat.mul(vb, dd), _) : Nat}
  {==}

def step_rem(+dd: Nat, +vb: Nat, +rr: Nat, +vr2: Nat, eq: {vr2 == Nat.add(Nat.mul(vb, dd), rr) : Nat},
  dlt: {Nat.is_lt(vr2, Nat.mul(vb, 1n+dd)) == True{} : Bool}) -> {Nat.is_lt(rr, vb) == True{} : Bool}:
  +a = Nat.mul(vb, dd)
  +l2 = le_rw_r(1n+vr2, Nat.mul(vb, 1n+dd), Nat.add(a, vb), Equal.trans(Nat, Nat.mul(vb, 1n+dd), Nat.add(vb, a), Nat.add(a, vb), Equal.sym(Nat, Nat.add(vb, a), Nat.mul(vb, 1n+dd), PNat.mul_succ(vb, dd)), PNat.add_comm(vb, a)), lt_to_le(vr2, Nat.mul(vb, 1n+dd), dlt))
  +l3 = le_rw_l(1n+vr2, Nat.add(a, 1n+rr), Nat.add(a, vb), Equal.trans(Nat, 1n+vr2, 1n+Nat.add(a, rr), Nat.add(a, 1n+rr), succ_cong(vr2, Nat.add(a, rr), eq), PNat.add_succ(a, rr)), l2)
  le_to_lt(rr, vb, Equal.trans(Bool, Nat.is_le(1n+rr, vb), Nat.is_le(Nat.add(a, 1n+rr), Nat.add(a, vb)), True{},
    Equal.sym(Bool, Nat.is_le(Nat.add(a, 1n+rr), Nat.add(a, vb)), Nat.is_le(1n+rr, vb), le_cancel(a, 1n+rr, vb)), l3))

def step_body2(+h: Nat, +q: List<&2, Nat>, +lr: List<&2, Nat>, +lb: List<&2, Nat>, +v: Nat,
  +hh: {Nat.is_lt(h, 10000n) == True{} : Bool}, +okb: {L.limbs_ok(lb) == True{} : Bool},
  +sa: {Nat.add(Nat.mul(L.limbs_val(q), L.limbs_val(lb)), L.limbs_val(lr)) == v : Nat},
  +sb: {Nat.is_lt(L.limbs_val(lr), L.limbs_val(lb)) == True{} : Bool},
  +sc: {L.big_ok(Big.Big{lr}) == True{} : Bool},
  +sd: {L.limbs_ok(q) == True{} : Bool},
  +qs: qs.spec(lb, Big.trim(Con{h, lr}), Big.qsearch(lb, 10000n, False{}, 0n, 9999n, Big.Big{lb}, Big.Big{Big.trim(Con{h, lr})})))
  -> DSpec(Big.div.step(h, Big.Big{lb}, Big.QR{q, Big.Big{lr}}), L.limbs_val(lb), Nat.add(h, Nat.mul(10000n, v))):
  +dd0 = Big.qsearch(lb, 10000n, False{}, 0n, 9999n, Big.Big{lb}, Big.Big{Big.trim(Con{h, lr})})
  +dle = P2.fst({Nat.is_le(Nat.mul(L.limbs_val(lb), dd0), L.limbs_val(Big.trim(Con{h, lr}))) == True{} : Bool}, {Nat.is_lt(L.limbs_val(Big.trim(Con{h, lr})), Nat.mul(L.limbs_val(lb), 1n+dd0)) == True{} : Bool}, qs)
  +dlt = P2.snd({Nat.is_le(Nat.mul(L.limbs_val(lb), dd0), L.limbs_val(Big.trim(Con{h, lr}))) == True{} : Bool}, {Nat.is_lt(L.limbs_val(Big.trim(Con{h, lr})), Nat.mul(L.limbs_val(lb), 1n+dd0)) == True{} : Bool}, qs)
  +vb = L.limbs_val(lb)
  +vr = L.limbs_val(lr)
  +x2 = Big.trim(Con{h, lr})
  +vr2 = L.limbs_val(x2)
  +hx2 = val_trim(Con{h, lr})
  +okx2 = big_ok_trim(Con{h, lr}, and_i(Nat.is_lt(h, 10000n), L.limbs_ok(lr), hh, and_l(L.limbs_ok(lr), L.last_nonzero(lr), sc)))
  +okx2a = and_l(L.limbs_ok(x2), L.last_nonzero(x2), okx2)
  +okx2b = and_r(L.limbs_ok(x2), L.last_nonzero(x2), okx2)
  +bound = lt_rw_l(Nat.add(h, Nat.mul(10000n, vr)), vr2, Nat.mul(vb, 10000n), Equal.sym(Nat, vr2, Nat.add(h, Nat.mul(10000n, vr)), hx2), r2_bound(h, vr, vb, hh, sb))
  +q1 = le_rw_l(0n, Nat.mul(vb, 0n), vr2, Equal.sym(Nat, Nat.mul(vb, 0n), 0n, PNat.mul_zero(vb)), le_zero(vr2))
  +dd = dd0
  +hdb = lt_mul_cancel(vb, dd, 10000n, le_lt_trans(Nat.mul(vb, dd), vr2, Nat.mul(vb, 10000n), dle, bound))
  +m = Big.limbs(Big.mul_small(Big.Big{lb}, dd))
  +okm = mul_small_big_ok(lb, dd)
  +hm = mul_small_big(lb, dd)
  +hsub = le_rw_l(Nat.mul(vb, dd), Nat.add(L.limbs_val(m), 0n), vr2,
    Equal.trans(Nat, Nat.mul(vb, dd), L.limbs_val(m), Nat.add(L.limbs_val(m), 0n), Equal.sym(Nat, L.limbs_val(m), Nat.mul(vb, dd), hm), PNat.add_zero(L.limbs_val(m))), dle)
  +okma = and_l(L.limbs_ok(m), L.last_nonzero(m), okm)
  +sv = sub_val(x2, m, 0n, okx2a, okma, {==}, hsub)
  +s = Big.sub.go(x2, m, 0n)
  +rr = L.limbs_val(s)
  +e1 = Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(vb, dd), 0n), rr), vr2, Nat.add(h, Nat.mul(10000n, vr)),
    Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(vb, dd), 0n), rr), Nat.add(Nat.add(L.limbs_val(m), 0n), rr), vr2,
      add00_cong(Nat.mul(vb, dd), L.limbs_val(m), rr, Equal.sym(Nat, L.limbs_val(m), Nat.mul(vb, dd), hm)), sv), hx2)
  +na = step_val(dd, L.limbs_val(q), vb, s, h, vr, v, e1, sa)
  +nb = lt_rw_l(rr, L.limbs_val(Big.trim(s)), vb, Equal.sym(Nat, L.limbs_val(Big.trim(s)), rr, val_trim(s)), step_rem(dd, vb, rr, vr2, e1b(Nat.mul(vb, dd), rr, vr2, Nat.add(h, Nat.mul(10000n, vr)), e1, hx2), dlt))
  ((na, nb), (big_ok_trim(s, sub_ok(x2, m, 0n, okx2a, okma, {==})), and_i(Nat.is_lt(dd, 10000n), L.limbs_ok(q), hdb, sd)))

def step_body(+h: Nat, +q: List<&2, Nat>, +lr: List<&2, Nat>, +lb: List<&2, Nat>, +v: Nat,
  +hh: {Nat.is_lt(h, 10000n) == True{} : Bool}, +okb: {L.limbs_ok(lb) == True{} : Bool},
  +sa: {Nat.add(Nat.mul(L.limbs_val(q), L.limbs_val(lb)), L.limbs_val(lr)) == v : Nat},
  +sb: {Nat.is_lt(L.limbs_val(lr), L.limbs_val(lb)) == True{} : Bool},
  +sc: {L.big_ok(Big.Big{lr}) == True{} : Bool},
  +sd: {L.limbs_ok(q) == True{} : Bool})
  -> DSpec(Big.div.step(h, Big.Big{lb}, Big.QR{q, Big.Big{lr}}), L.limbs_val(lb), Nat.add(h, Nat.mul(10000n, v))):
  +vb = L.limbs_val(lb)
  +vr = L.limbs_val(lr)
  +x2 = Big.trim(Con{h, lr})
  +vr2 = L.limbs_val(x2)
  +hx2 = val_trim(Con{h, lr})
  +okx2 = big_ok_trim(Con{h, lr}, and_i(Nat.is_lt(h, 10000n), L.limbs_ok(lr), hh, and_l(L.limbs_ok(lr), L.last_nonzero(lr), sc)))
  +okx2a = and_l(L.limbs_ok(x2), L.last_nonzero(x2), okx2)
  +okx2b = and_r(L.limbs_ok(x2), L.last_nonzero(x2), okx2)
  +bound = lt_rw_l(Nat.add(h, Nat.mul(10000n, vr)), vr2, Nat.mul(vb, 10000n), Equal.sym(Nat, vr2, Nat.add(h, Nat.mul(10000n, vr)), hx2), r2_bound(h, vr, vb, hh, sb))
  +q1 = le_rw_l(0n, Nat.mul(vb, 0n), vr2, Equal.sym(Nat, Nat.mul(vb, 0n), 0n, PNat.mul_zero(vb)), le_zero(vr2))
  step_body2(h, q, lr, lb, v, hh, okb, sa, sb, sc, sd, qs_spec(lb, 10000n, False{}, 0n, 9999n, x2, okb, okx2a, okx2b, q1, bound, le_zero(9999n), {==}, le_succ(9999n)))

def step_on(+h: Nat, acc: Big.QR, +lb: List<&2, Nat>, +v: Nat,
  +hh: {Nat.is_lt(h, 10000n) == True{} : Bool}, +okb: {L.limbs_ok(lb) == True{} : Bool}, +ih: DSpec(acc, L.limbs_val(lb), v))
  -> DSpec(Big.div.step(h, Big.Big{lb}, acc), L.limbs_val(lb), Nat.add(h, Nat.mul(10000n, v))):
  match acc:
    case Big.QR{+q, +r}:
      match r:
        case Big.Big{+lr}:
          +acc2 = {Big.QR{q, Big.Big{lr}} : Big.QR}
          +vb = L.limbs_val(lb)
          step_body(h, q, lr, lb, v, hh, okb, ds_a(acc2, vb, v, ih), ds_b(acc2, vb, v, ih), ds_c(acc2, vb, v, ih), ds_d(acc2, vb, v, ih))

def div_go(ls: List<&2, Nat>, +lb: List<&2, Nat>, +okls: {L.limbs_ok(ls) == True{} : Bool}, +okb: {L.limbs_ok(lb) == True{} : Bool},
  +hb: {Nat.is_gt(L.limbs_val(lb), 0n) == True{} : Bool}) -> DSpec(Big.div.go(ls, Big.Big{lb}), L.limbs_val(lb), L.limbs_val(ls)):
  match ls:
    case Nil{}:
      (({==}, gt_lt(L.limbs_val(lb), hb)), ({==}, {==}))
    case Con{+h, +t}:
      step_on(h, Big.div.go(t, Big.Big{lb}), lb, L.limbs_val(t), and_l(Nat.is_lt(h, 10000n), L.limbs_ok(t), okls), okb,
        div_go(t, lb, and_r(Nat.is_lt(h, 10000n), L.limbs_ok(t), okls), okb, hb))

def divmod_val(+la: List<&2, Nat>, +lb: List<&2, Nat>, +q: List<&2, Nat>, +r: Big.Big,
  sa: {Nat.add(Nat.mul(L.limbs_val(q), L.limbs_val(lb)), L.big_val(r)) == L.limbs_val(la) : Nat})
  -> {Nat.add(Nat.mul(L.limbs_val(Big.trim(q)), L.limbs_val(lb)), L.big_val(r)) == L.limbs_val(la) : Nat}:
  %Equal.sym(Nat, L.limbs_val(Big.trim(q)), L.limbs_val(q), val_trim(q)) : {Nat.add(Nat.mul(_, L.limbs_val(lb)), L.big_val(r)) == L.limbs_val(la) : Nat}
  sa

def divmod_fin(+la: List<&2, Nat>, +lb: List<&2, Nat>, +ds: DSpec(Big.div.go(la, Big.Big{lb}), L.limbs_val(lb), L.limbs_val(la)))
  -> {Nat.add(Nat.mul(L.big_val(Big.div(Big.Big{la}, Big.Big{lb})), L.limbs_val(lb)), L.big_val(Big.mod(Big.Big{la}, Big.Big{lb}))) == L.limbs_val(la) : Nat}
  & {Nat.is_lt(L.big_val(Big.mod(Big.Big{la}, Big.Big{lb})), L.limbs_val(lb)) == True{} : Bool}
  & {L.big_ok(Big.div(Big.Big{la}, Big.Big{lb})) == True{} : Bool}
  & {L.big_ok(Big.mod(Big.Big{la}, Big.Big{lb})) == True{} : Bool}:
  +x = Big.div.go(la, Big.Big{lb})
  +vb = L.limbs_val(lb)
  +va = L.limbs_val(la)
  (divmod_val(la, lb, Big.QR.q(x), Big.QR.r(x), ds_a(x, vb, va, ds)), ds_b(x, vb, va, ds), big_ok_trim(Big.QR.q(x), ds_d(x, vb, va, ds)), ds_c(x, vb, va, ds))

def L.big_divmod(a, b, ha, hb, hz):
  match a:
    case Big.Big{+la}:
      match b:
        case Big.Big{+lb}:
          divmod_fin(la, lb, div_go(la, lb, and_l(L.limbs_ok(la), L.last_nonzero(la), ha), and_l(L.limbs_ok(lb), L.last_nonzero(lb), hb), hz))

# ---------------------------------------------------------------------
# Decimal text: Dec.show peels a limb's four digits
# ---------------------------------------------------------------------

def cmp_refl(n: Nat) -> {Nat.cmp(n, n) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      cmp_refl(p)

def not_eq_t(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

def lt_ne_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : not_eq_t(_)
  Unit{}

def gt_ne_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : not_eq_t(_)
  Unit{}

def cmp_eq(x: Nat, y: Nat, +h: {Nat.cmp(x, y) == EQ{} : Cmp}) -> {x == y : Nat}:
  match x:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n++q:
          Empty.absurd({0n == 1n+q : Nat}, lt_ne_eq(h))
    case 1n++p:
      match y:
        case 0n:
          Empty.absurd({1n+p == 0n : Nat}, gt_ne_eq(h))
        case 1n++q:
          succ_cong(p, q, cmp_eq(p, q, h))

def then_eq_l(a: Cmp, -b: Cmp, +h: {Big.cmp_then(a, b) == EQ{} : Cmp}) -> {a == EQ{} : Cmp}:
  match a:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, lt_ne_eq(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, gt_ne_eq(h))

def then_eq_r(a: Cmp, -b: Cmp, +h: {Big.cmp_then(a, b) == EQ{} : Cmp}) -> {b == EQ{} : Cmp}:
  match a:
    case LT{}:
      Empty.absurd({b == EQ{} : Cmp}, lt_ne_eq(h))
    case EQ{}:
      h
    case GT{}:
      Empty.absurd({b == EQ{} : Cmp}, gt_ne_eq(h))

def du_x(+n: Nat, +q: Nat, +r: Nat, +e: {n == Nat.add(r, Nat.mul(10n, q)) : Nat})
  -> {Nat.cmp(Nat.add(r, Nat.mul(10n, q)), Nat.add(Nat.mod(n, 10n), Nat.mul(10n, Nat.div(n, 10n)))) == EQ{} : Cmp}:
  %e : {Nat.cmp(_, Nat.add(Nat.mod(n, 10n), Nat.mul(10n, Nat.div(n, 10n)))) == EQ{} : Cmp}
  %Equal.sym(Nat, Nat.add(Nat.mod(n, 10n), Nat.mul(10n, Nat.div(n, 10n))), n, recomb(n, 9n)) : {Nat.cmp(n, _) == EQ{} : Cmp}
  cmp_refl(n)

# n = r + 10 q with r < 10: q and r are n's Euclid quotient and remainder
def du_cmp(+n: Nat, +q: Nat, +r: Nat, +e: {n == Nat.add(r, Nat.mul(10n, q)) : Nat}, +hr: {Nat.is_lt(r, 10n) == True{} : Bool})
  -> {Big.cmp_then(Nat.cmp(q, Nat.div(n, 10n)), Nat.cmp(r, Nat.mod(n, 10n))) == EQ{} : Cmp}:
  Equal.trans(Cmp, Big.cmp_then(Nat.cmp(q, Nat.div(n, 10n)), Nat.cmp(r, Nat.mod(n, 10n))),
    Nat.cmp(Nat.add(r, Nat.mul(10n, q)), Nat.add(Nat.mod(n, 10n), Nat.mul(10n, Nat.div(n, 10n)))), EQ{},
    Equal.sym(Cmp, Nat.cmp(Nat.add(r, Nat.mul(10n, q)), Nat.add(Nat.mod(n, 10n), Nat.mul(10n, Nat.div(n, 10n)))),
      Big.cmp_then(Nat.cmp(q, Nat.div(n, 10n)), Nat.cmp(r, Nat.mod(n, 10n))),
      lex(q, Nat.div(n, 10n), r, Nat.mod(n, 10n), 10n, hr, PNat.mod_lt(n, 9n))),
    du_x(n, q, r, e))

def du_div(+n: Nat, +q: Nat, +r: Nat, +e: {n == Nat.add(r, Nat.mul(10n, q)) : Nat}, +hr: {Nat.is_lt(r, 10n) == True{} : Bool})
  -> {Nat.div(n, 10n) == q : Nat}:
  Equal.sym(Nat, q, Nat.div(n, 10n), cmp_eq(q, Nat.div(n, 10n), then_eq_l(Nat.cmp(q, Nat.div(n, 10n)), Nat.cmp(r, Nat.mod(n, 10n)), du_cmp(n, q, r, e, hr))))

def du_mod(+n: Nat, +q: Nat, +r: Nat, +e: {n == Nat.add(r, Nat.mul(10n, q)) : Nat}, +hr: {Nat.is_lt(r, 10n) == True{} : Bool})
  -> {Nat.mod(n, 10n) == r : Nat}:
  Equal.sym(Nat, r, Nat.mod(n, 10n), cmp_eq(r, Nat.mod(n, 10n), then_eq_r(Nat.cmp(q, Nat.div(n, 10n)), Nat.cmp(r, Nat.mod(n, 10n)), du_cmp(n, q, r, e, hr))))

def le_nlt(a: Nat, b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          Empty.absurd({Nat.is_lt(0n, 1n+bp) == False{} : Bool}, PNat.false_ne_true(h))
    case 1n++ap:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          le_nlt(ap, bp, h)

def gt_le1(q: Nat, +h: {Nat.is_gt(q, 0n) == True{} : Bool}) -> {Nat.is_le(1n, q) == True{} : Bool}:
  match q:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n++p:
      le_zero(p)

def nlt10(+n: Nat, +q: Nat, +r: Nat, +e: {n == Nat.add(r, Nat.mul(10n, q)) : Nat}, +hq: {Nat.is_gt(q, 0n) == True{} : Bool})
  -> {Nat.is_lt(n, 10n) == False{} : Bool}:
  +h1 = le_trans(10n, Nat.mul(10n, q), Nat.add(r, Nat.mul(10n, q)), le_mul_mono(10n, 1n, q, gt_le1(q, hq)), le_add_l(Nat.mul(10n, q), r))
  le_nlt(n, 10n, le_rw_r(10n, Nat.add(r, Nat.mul(10n, q)), n, Equal.sym(Nat, n, Nat.add(r, Nat.mul(10n, q)), e), h1))

# one digit off the bottom: show.go on r + 10 q (q > 0) pushes r and goes on with q
def show_step(+ff: Nat, +n: Nat, +q: Nat, +r: Nat, +acc: String, +e: {n == Nat.add(r, Nat.mul(10n, q)) : Nat},
  +hr: {Nat.is_lt(r, 10n) == True{} : Bool}, +hq: {Nat.is_gt(q, 0n) == True{} : Bool})
  -> {Dec.show.go(1n+ff, False{}, n, acc) == Dec.show.go(ff, False{}, q, SCon{Dec.digit_chr(r), acc}) : String}:
  +rhs = Dec.show.go(ff, False{}, q, SCon{Dec.digit_chr(r), acc})
  %Equal.sym(Bool, Nat.is_lt(n, 10n), False{}, nlt10(n, q, r, e, hq))
    : {Dec.show.go(ff, _, Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}) == rhs : String}
  %Equal.sym(Nat, Nat.div(n, 10n), q, du_div(n, q, r, e, hr))
    : {Dec.show.go(ff, False{}, _, SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}) == rhs : String}
  %Equal.sym(Nat, Nat.mod(n, 10n), r, du_mod(n, q, r, e, hr))
    : {Dec.show.go(ff, False{}, q, SCon{Dec.digit_chr(_), acc}) == rhs : String}
  {==}

def div_shrink10(+m: Nat) -> {Nat.is_le(Nat.div(1n+m, 10n), m) == True{} : Bool}:
  div_shrink.go(Nat.div(1n+m, 10n), Nat.mod(1n+m, 10n), m, 8n, PNat.div_mod_eq(1n+m, 9n))

def lt10(n: Nat, +h: {Nat.is_le(n, 0n) == True{} : Bool}) -> {Nat.is_lt(n, 10n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Empty.absurd({Nat.is_lt(1n+p, 10n) == True{} : Bool}, PNat.false_ne_true(h))

def fuel0(g: Nat, +n: Nat, +acc: String, +hf: {Nat.is_le(n, 0n) == True{} : Bool})
  -> {Dec.show.go(1n, False{}, n, acc) == Dec.show.go(1n+g, False{}, n, acc) : String}:
  match g:
    case 0n:
      {==}
    case 1n++gp:
      %Equal.sym(Nat, n, 0n, le0(n, hf)) : {Dec.show.go(1n, False{}, _, acc) == Dec.show.go(2n+gp, False{}, _, acc) : String}
      {==}

def fuel.of(c: Bool, +fp: Nat, g: Nat, n: Nat, +acc: String, +hc: {c == Nat.is_lt(n, 10n) : Bool},
  +hf: {Nat.is_le(n, 1n+fp) == True{} : Bool}, +hg: {Nat.is_le(n, g) == True{} : Bool},
  ih: @g2:Nat -> {Nat.is_le(Nat.div(n, 10n), fp) == True{} : Bool} -> {Nat.is_le(Nat.div(n, 10n), g2) == True{} : Bool}
      -> {Dec.show.go(1n+fp, False{}, Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}) == Dec.show.go(1n+g2, False{}, Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}) : String})
  -> {Dec.show.go(1n+fp, c, Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}) == Dec.show.go(g, c, Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}) : String}:
  match c:
    case True{}:
      match g:
        case 0n:
          {==}
        case 1n++gp:
          {==}
    case False{}:
      match g:
        case 0n:
          Empty.absurd({Dec.show.go(1n+fp, False{}, Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}) == Dec.show.go(0n, False{}, Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}) : String},
            PNat.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(n, 10n), True{}, hc, lt10(n, hg))))
        case 1n++gp:
          match n:
            case 0n:
              Empty.absurd({Dec.show.go(1n+fp, False{}, 0n, SCon{Dec.digit_chr(0n), acc}) == Dec.show.go(1n+gp, False{}, 0n, SCon{Dec.digit_chr(0n), acc}) : String},
                PNat.false_ne_true(hc))
            case 1n++m:
              ih(gp, le_trans(Nat.div(1n+m, 10n), m, fp, div_shrink10(m), hf), le_trans(Nat.div(1n+m, 10n), m, gp, div_shrink10(m), hg))

# the fuel does not matter once it covers n
def fuel(f: Nat, g: Nat, +n: Nat, +acc: String, +hf: {Nat.is_le(n, f) == True{} : Bool}, +hg: {Nat.is_le(n, g) == True{} : Bool})
  -> {Dec.show.go(1n+f, False{}, n, acc) == Dec.show.go(1n+g, False{}, n, acc) : String}:
  match f:
    case 0n:
      fuel0(g, n, acc, hf)
    case 1n++fp:
      fuel.of(Nat.is_lt(n, 10n), fp, g, n, acc, {==}, hf, hg,
        g2 => h1 => h2 => fuel(fp, g2, Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}, h1, h2))

# show.go only prepends to its accumulator (as proofs/dec.bend's go_app;
# importing that file here overflows the checker's stack)
def go_app(f: Nat, b: Bool, +n: Nat, acc: String, +t: String)
  -> {String.append(Dec.show.go(f, b, n, acc), t) == Dec.show.go(f, b, n, String.append(acc, t)) : String}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match b:
        case True{}:
          {==}
        case False{}:
          go_app(g, Nat.is_lt(n, 10n), Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}, t)

# h + (b c) V == d + b (hq + c V), when d + b hq == h
def split(+b: Nat, +c: Nat, +d: Nat, +hq: Nat, +h: Nat, +v: Nat, eh: {Nat.add(d, Nat.mul(b, hq)) == h : Nat})
  -> {Nat.add(h, Nat.mul(Nat.mul(b, c), v)) == Nat.add(d, Nat.mul(b, Nat.add(hq, Nat.mul(c, v)))) : Nat}:
  +rhs = Nat.add(d, Nat.mul(b, Nat.add(hq, Nat.mul(c, v))))
  %eh : {Nat.add(_, Nat.mul(Nat.mul(b, c), v)) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(b, c), v), Nat.mul(b, Nat.mul(c, v)), mul_assoc(b, c, v)) : {Nat.add(Nat.add(d, Nat.mul(b, hq)), _) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(b, Nat.add(hq, Nat.mul(c, v))), Nat.add(Nat.mul(b, hq), Nat.mul(b, Nat.mul(c, v))), mul_dist_l(b, hq, Nat.mul(c, v)))
    : {Nat.add(Nat.add(d, Nat.mul(b, hq)), Nat.mul(b, Nat.mul(c, v))) == Nat.add(d, _) : Nat}
  Equal.sym(Nat, Nat.add(d, Nat.add(Nat.mul(b, hq), Nat.mul(b, Nat.mul(c, v)))), Nat.add(Nat.add(d, Nat.mul(b, hq)), Nat.mul(b, Nat.mul(c, v))),
    PNat.add_assoc(d, Nat.mul(b, hq), Nat.mul(b, Nat.mul(c, v))))

# n < 10 k: n / 10 < k
def dbound(+n: Nat, +k: Nat, +h: {Nat.is_lt(n, Nat.mul(10n, k)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(n, 10n), k) == True{} : Bool}:
  +q = Nat.div(n, 10n)
  +le1 = le_rw_r(Nat.mul(10n, q), Nat.add(Nat.mod(n, 10n), Nat.mul(10n, q)), n, recomb(n, 9n), le_add_l(Nat.mul(10n, q), Nat.mod(n, 10n)))
  lt_mul_cancel(10n, q, k, le_lt_trans(Nat.mul(10n, q), n, Nat.mul(10n, k), le1, h))

def gt_add_mul_g(y: Nat, +b: Nat, v: Nat, +h: {Nat.is_gt(v, 0n) == True{} : Bool}) -> {Nat.is_gt(Nat.add(y, Nat.mul(1n+b, v)), 0n) == True{} : Bool}:
  match y:
    case 0n:
      match v:
        case 0n:
          Empty.absurd({Nat.is_gt(Nat.mul(1n+b, 0n), 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++p:
          {==}
    case 1n++q:
      {==}

def le_v(+v: Nat, +h: Nat) -> {Nat.is_le(v, Nat.add(h, Nat.mul(10000n, v))) == True{} : Bool}:
  le_trans(v, Nat.mul(10000n, v), Nat.add(h, Nat.mul(10000n, v)),
    le_rw_r(v, Nat.mul(v, 10000n), Nat.mul(10000n, v), PNat.mul_comm(v, 10000n), le_mul(v, 9998n)),
    le_add_l(Nat.mul(10000n, v), h))

# the text of h + 10000 v (v > 0, h < 10000) is v's, then h's four digits
def show_limb(+v: Nat, +h: Nat, +hv: {Nat.is_gt(v, 0n) == True{} : Bool}, +hh: {Nat.is_lt(h, 10000n) == True{} : Bool})
  -> {String.append(Dec.show(v), Big.pad4(h)) == Dec.show(Nat.add(h, Nat.mul(10000n, v))) : String}:
  +h1 = Nat.div(h, 10n)
  +h2 = Nat.div(h1, 10n)
  +d0 = Nat.mod(h, 10n)
  +d1 = Nat.mod(h1, 10n)
  +d2 = Nat.mod(h2, 10n)
  +d3 = Nat.div(h2, 10n)
  +n0 = Nat.add(h, Nat.mul(10000n, v))
  +n1 = Nat.add(h1, Nat.mul(1000n, v))
  +n2 = Nat.add(h2, Nat.mul(100n, v))
  +n3 = Nat.add(d3, Nat.mul(10n, v))
  +a0 = {SCon{Dec.digit_chr(d0), SNil{}} : String}
  +a1 = {SCon{Dec.digit_chr(d1), a0} : String}
  +a2 = {SCon{Dec.digit_chr(d2), a1} : String}
  +p4 = Big.pad4(h)
  +s0 = show_step(Nat.add(4n, n0), n0, n1, d0, "", split(10n, 1000n, d0, h1, h, v, recomb(h, 9n)), PNat.mod_lt(h, 9n), gt_add_mul_g(h1, 999n, v, hv))
  +s1 = show_step(Nat.add(3n, n0), n1, n2, d1, a0, split(10n, 100n, d1, h2, h1, v, recomb(h1, 9n)), PNat.mod_lt(h1, 9n), gt_add_mul_g(h2, 99n, v, hv))
  +s2 = show_step(Nat.add(2n, n0), n2, n3, d2, a1, split(10n, 10n, d2, d3, h2, v, recomb(h2, 9n)), PNat.mod_lt(h2, 9n), gt_add_mul_g(d3, 9n, v, hv))
  +s3 = show_step(Nat.add(1n, n0), n3, v, d3, a2, {==}, dbound(h2, 10n, dbound(h1, 100n, dbound(h, 1000n, hh))), hv)
  +f1 = fuel(n0, Nat.add(4n, n0), n0, "", le_refl(n0), le_add_l(n0, 4n))
  +f2 = fuel(n0, v, v, "", le_v(v, h), le_refl(v))
  +ga = go_app(1n+n0, False{}, v, "", p4)
  +lhs = String.append(Dec.show(v), p4)
  %Equal.sym(String, Dec.show.go(1n+n0, False{}, n0, ""), Dec.show.go(1n+Nat.add(4n, n0), False{}, n0, ""), f1) : {lhs == _ : String}
  %Equal.sym(String, Dec.show.go(1n+Nat.add(4n, n0), False{}, n0, ""), Dec.show.go(Nat.add(4n, n0), False{}, n1, a0), s0) : {lhs == _ : String}
  %Equal.sym(String, Dec.show.go(1n+Nat.add(3n, n0), False{}, n1, a0), Dec.show.go(Nat.add(3n, n0), False{}, n2, a1), s1) : {lhs == _ : String}
  %Equal.sym(String, Dec.show.go(1n+Nat.add(2n, n0), False{}, n2, a1), Dec.show.go(Nat.add(2n, n0), False{}, n3, a2), s2) : {lhs == _ : String}
  %Equal.sym(String, Dec.show.go(1n+Nat.add(1n, n0), False{}, n3, a2), Dec.show.go(Nat.add(1n, n0), False{}, v, SCon{Dec.digit_chr(d3), a2}), s3) : {lhs == _ : String}
  %ga : {lhs == _ : String}
  %Equal.sym(String, Dec.show.go(1n+n0, False{}, v, ""), Dec.show.go(1n+v, False{}, v, ""), f2) : {lhs == String.append(_, p4) : String}
  {==}

def show_cons(e: Bool, +h: Nat, +t: List<&2, Nat>, +he: {e == List.is_empty(&2, Nat, t) : Bool},
  +hh: {Nat.is_lt(h, 10000n) == True{} : Bool}, +hl: {L.last_nonzero(Con{h, t}) == True{} : Bool})
  -> {Big.show.cons(e, h, Dec.show(L.limbs_val(t))) == Dec.show(Nat.add(h, Nat.mul(10000n, L.limbs_val(t)))) : String}:
  match e:
    case True{}:
      %Equal.sym(List<&2, Nat>, t, Nil{}, nil_of_empty(t, Equal.sym(Bool, True{}, List.is_empty(&2, Nat, t), he)))
        : {Dec.show(h) == Dec.show(Nat.add(h, Nat.mul(10000n, L.limbs_val(_)))) : String}
      %PNat.add_zero(h) : {Dec.show(h) == Dec.show(_) : String}
      {==}
    case False{}:
      show_limb(L.limbs_val(t), h, pos(t, lnz_tail(h, t, hl), Equal.sym(Bool, False{}, List.is_empty(&2, Nat, t), he)), hh)

def show_go(ls: List<&2, Nat>, +ok: {L.limbs_ok(ls) == True{} : Bool}, +lz: {L.last_nonzero(ls) == True{} : Bool})
  -> {Big.show.go(ls) == Dec.show(L.limbs_val(ls)) : String}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(String, Big.show.go(t), Dec.show(L.limbs_val(t)), show_go(t, and_r(Nat.is_lt(h, 10000n), L.limbs_ok(t), ok), lnz_tail(h, t, lz)))
        : {Big.show.cons(List.is_empty(&2, Nat, t), h, _) == Dec.show(Nat.add(h, Nat.mul(10000n, L.limbs_val(t)))) : String}
      show_cons(List.is_empty(&2, Nat, t), h, t, {==}, and_l(Nat.is_lt(h, 10000n), L.limbs_ok(t), ok), lz)

def show_big(+ls: List<&2, Nat>, +h: {L.big_ok(Big.Big{ls}) == True{} : Bool}) -> {Big.show(Big.Big{ls}) == Dec.show(L.limbs_val(ls)) : String}:
  show_go(ls, and_l(L.limbs_ok(ls), L.last_nonzero(ls), h), and_r(L.limbs_ok(ls), L.last_nonzero(ls), h))

def L.big_show(b, h):
  match b:
    case Big.Big{+ls}:
      show_big(ls, h)

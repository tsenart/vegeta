# Proofs of the double laws (f64_*).
import Base
import ../LAWS.bend as L
import ../lib/big.bend as Big
import ../lib/f64.bend as F64
import ./nat.bend as PNat
import ./big.bend as PBig
import ../lib/dec.bend as Dec
import ./dec.bend as PDec

def L.f64_of_nat(n):
  {==}

# ---------------------------------------------------------------------
# f64_trunc: trunc is the quotient of LAWS' f_num by f_den
# ---------------------------------------------------------------------

def to_nat.go(ls: List<&2, Nat>) -> {Big.to_nat.go(ls) == L.limbs_val(ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %to_nat.go(t) : {Nat.add(h, Nat.mul(10000n, Big.to_nat.go(t))) == Nat.add(h, Nat.mul(10000n, _)) : Nat}
      {==}

def to_nat(b: Big.Big) -> {Big.to_nat(b) == L.big_val(b) : Nat}:
  match b:
    case Big.Big{+ls}:
      to_nat.go(ls)

def pos_pow2.of(v: Nat, h: {Nat.is_gt(v, 0n) == True{} : Bool}) -> {Nat.is_gt(Nat.add(v, Nat.add(v, 0n)), 0n) == True{} : Bool}:
  match v:
    case 0n:
      Empty.absurd({Nat.is_gt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n++p:
      {==}

def pos_pow2(n: Nat) -> {Nat.is_gt(Nat.pow(2n, n), 0n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      pos_pow2.of(Nat.pow(2n, p), pos_pow2(p))

# lib's doubling (mul_small) and LAWS' (Big.mul by 2) both give b 2^n
def vfast(n: Nat, +b: Big.Big) -> {L.big_val(F64.bshl(n, b)) == Nat.mul(L.big_val(b), Nat.pow(2n, n)) : Nat}:
  match n:
    case 0n:
      Equal.sym(Nat, Nat.mul(L.big_val(b), 1n), L.big_val(b), PBig.mul_one(L.big_val(b)))
    case 1n++p:
      match b:
        case Big.Big{+ls}:
          +ms = Big.mul_small(Big.Big{ls}, 2n)
          +v = L.limbs_val(ls)
          %Equal.sym(Nat, L.big_val(F64.bshl(p, ms)), Nat.mul(L.big_val(ms), Nat.pow(2n, p)), vfast(p, ms)) : {_ == Nat.mul(v, Nat.pow(2n, 1n+p)) : Nat}
          %Equal.sym(Nat, L.big_val(ms), Nat.mul(v, 2n), PBig.mul_small_big(ls, 2n)) : {Nat.mul(_, Nat.pow(2n, p)) == Nat.mul(v, Nat.pow(2n, 1n+p)) : Nat}
          PBig.mul_assoc(v, 2n, Nat.pow(2n, p))

def vlaw(n: Nat, +b: Big.Big) -> {L.big_val(L.bshl(n, b)) == Nat.mul(L.big_val(b), Nat.pow(2n, n)) : Nat}:
  match n:
    case 0n:
      Equal.sym(Nat, Nat.mul(L.big_val(b), 1n), L.big_val(b), PBig.mul_one(L.big_val(b)))
    case 1n++p:
      match b:
        case Big.Big{+ls}:
          +ms = Big.mul(Big.Big{ls}, Big.of(2n))
          +v = L.limbs_val(ls)
          %Equal.sym(Nat, L.big_val(L.bshl(p, ms)), Nat.mul(L.big_val(ms), Nat.pow(2n, p)), vlaw(p, ms)) : {_ == Nat.mul(v, Nat.pow(2n, 1n+p)) : Nat}
          %Equal.sym(Nat, L.big_val(ms), Nat.mul(v, 2n), PBig.mul_val(ls, Big.limbs(Big.of(2n)))) : {Nat.mul(_, Nat.pow(2n, p)) == Nat.mul(v, Nat.pow(2n, 1n+p)) : Nat}
          PBig.mul_assoc(v, 2n, Nat.pow(2n, p))

def bshl_ok(n: Nat, +b: Big.Big, +h: {L.big_ok(b) == True{} : Bool}) -> {L.big_ok(F64.bshl(n, b)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n++p:
      match b:
        case Big.Big{+ls}:
          bshl_ok(p, Big.mul_small(Big.Big{ls}, 2n), PBig.mul_small_big_ok(ls, 2n))

def lbshl_ok(n: Nat, +b: Big.Big, +h: {L.big_ok(b) == True{} : Bool}) -> {L.big_ok(L.bshl(n, b)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n++p:
      match b:
        case Big.Big{+ls}:
          lbshl_ok(p, Big.mul(Big.Big{ls}, Big.of(2n)), PBig.big_ok_trim(Big.mul.go(ls, Big.of(2n)), PBig.mul_go_ok(ls, Big.of(2n))))

def eu.x(+va: Nat, +b: Nat, +q: Nat, +r: Nat, +e2: {Nat.add(r, Nat.mul(1n+b, q)) == va : Nat})
  -> {Nat.cmp(Nat.add(r, Nat.mul(1n+b, q)), Nat.add(Nat.mod(va, 1n+b), Nat.mul(1n+b, Nat.div(va, 1n+b)))) == EQ{} : Cmp}:
  %Equal.sym(Nat, Nat.add(r, Nat.mul(1n+b, q)), va, e2) : {Nat.cmp(_, Nat.add(Nat.mod(va, 1n+b), Nat.mul(1n+b, Nat.div(va, 1n+b)))) == EQ{} : Cmp}
  %Equal.sym(Nat, Nat.add(Nat.mod(va, 1n+b), Nat.mul(1n+b, Nat.div(va, 1n+b))), va, PBig.recomb(va, b)) : {Nat.cmp(va, _) == EQ{} : Cmp}
  PBig.cmp_refl(va)

# Euclid's quotient is unique: q vb + r == va with r < vb makes q va / vb
def eu(+va: Nat, vb: Nat, +q: Nat, +r: Nat, +e: {Nat.add(Nat.mul(q, vb), r) == va : Nat}, +hr: {Nat.is_lt(r, vb) == True{} : Bool})
  -> {q == Nat.div(va, vb) : Nat}:
  match vb:
    case 0n:
      Empty.absurd({q == Nat.div(va, 0n) : Nat}, PBig.lt0(r, hr))
    case 1n++b:
      +dv = Nat.div(va, 1n+b)
      +md = Nat.mod(va, 1n+b)
      +e2 = Equal.trans(Nat, Nat.add(r, Nat.mul(1n+b, q)), Nat.add(Nat.mul(q, 1n+b), r), va,
        Equal.trans(Nat, Nat.add(r, Nat.mul(1n+b, q)), Nat.add(Nat.mul(1n+b, q), r), Nat.add(Nat.mul(q, 1n+b), r),
          PNat.add_comm(r, Nat.mul(1n+b, q)), PBig.add_cong_l(Nat.mul(1n+b, q), Nat.mul(q, 1n+b), r, PNat.mul_comm(1n+b, q))), e)
      +x = eu.x(va, b, q, r, e2)
      +c = Equal.trans(Cmp, Big.cmp_then(Nat.cmp(q, dv), Nat.cmp(r, md)), Nat.cmp(Nat.add(r, Nat.mul(1n+b, q)), Nat.add(md, Nat.mul(1n+b, dv))), EQ{},
        Equal.sym(Cmp, Nat.cmp(Nat.add(r, Nat.mul(1n+b, q)), Nat.add(md, Nat.mul(1n+b, dv))), Big.cmp_then(Nat.cmp(q, dv), Nat.cmp(r, md)),
          PBig.lex(q, dv, r, md, 1n+b, hr, PNat.mod_lt(va, b))), x)
      PBig.cmp_eq(q, dv, PBig.then_eq_l(Nat.cmp(q, dv), Nat.cmp(r, md), c))

def dv.of(+a: Big.Big, +b: Big.Big,
  dm: {Nat.add(Nat.mul(L.big_val(Big.div(a, b)), L.big_val(b)), L.big_val(Big.mod(a, b))) == L.big_val(a) : Nat}
  & {Nat.is_lt(L.big_val(Big.mod(a, b)), L.big_val(b)) == True{} : Bool}
  & {L.big_ok(Big.div(a, b)) == True{} : Bool}
  & {L.big_ok(Big.mod(a, b)) == True{} : Bool})
  -> {L.big_val(Big.div(a, b)) == Nat.div(L.big_val(a), L.big_val(b)) : Nat}:
  (c1, rest) = dm
  (c2, rest2) = rest
  eu(L.big_val(a), L.big_val(b), L.big_val(Big.div(a, b)), L.big_val(Big.mod(a, b)), c1, c2)

# the quotient's value is that of the values
def dv(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool},
  +hz: {Nat.is_gt(L.big_val(b), 0n) == True{} : Bool}) -> {L.big_val(Big.div(a, b)) == Nat.div(L.big_val(a), L.big_val(b)) : Nat}:
  dv.of(a, b, L.big_divmod(a, b, ha, hb, hz))

def div_cong(-a: Nat, -a2: Nat, -b: Nat, -b2: Nat, ea: {a == a2 : Nat}, eb: {b == b2 : Nat}) -> {Nat.div(a, b) == Nat.div(a2, b2) : Nat}:
  %ea : {Nat.div(a, b) == Nat.div(_, b2) : Nat}
  %eb : {Nat.div(a, b) == Nat.div(a, _) : Nat}
  {==}

def dv_eq(+a: Big.Big, +b: Big.Big, +a2: Big.Big, +b2: Big.Big,
  +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool}, +hz: {Nat.is_gt(L.big_val(b), 0n) == True{} : Bool},
  +ha2: {L.big_ok(a2) == True{} : Bool}, +hb2: {L.big_ok(b2) == True{} : Bool}, +hz2: {Nat.is_gt(L.big_val(b2), 0n) == True{} : Bool},
  +ea: {L.big_val(a) == L.big_val(a2) : Nat}, +eb: {L.big_val(b) == L.big_val(b2) : Nat})
  -> {Big.to_nat(Big.div(a, b)) == L.big_val(Big.div(a2, b2)) : Nat}:
  Equal.trans(Nat, Big.to_nat(Big.div(a, b)), L.big_val(Big.div(a, b)), L.big_val(Big.div(a2, b2)), to_nat(Big.div(a, b)),
    Equal.trans(Nat, L.big_val(Big.div(a, b)), Nat.div(L.big_val(a), L.big_val(b)), L.big_val(Big.div(a2, b2)), dv(a, b, ha, hb, hz),
      Equal.trans(Nat, Nat.div(L.big_val(a), L.big_val(b)), Nat.div(L.big_val(a2), L.big_val(b2)), L.big_val(Big.div(a2, b2)),
        div_cong(L.big_val(a), L.big_val(a2), L.big_val(b), L.big_val(b2), ea, eb),
        Equal.sym(Nat, L.big_val(Big.div(a2, b2)), Nat.div(L.big_val(a2), L.big_val(b2)), dv(a2, b2, ha2, hb2, hz2)))))

def gt_rw(-x: Nat, -y: Nat, e: {x == y : Nat}, h: {Nat.is_gt(x, 0n) == True{} : Bool}) -> {Nat.is_gt(y, 0n) == True{} : Bool}:
  %e : {Nat.is_gt(_, 0n) == True{} : Bool}
  h

def tr(+m: Big.Big, +e: Nat, neg: Bool, +okm: {L.big_ok(m) == True{} : Bool})
  -> {F64.trunc(F64.F64{m, e, neg}) == L.big_val(Big.div(L.f_num(F64.F64{m, e, neg}), L.f_den(F64.F64{m, e, neg}))) : Nat}:
  match neg:
    case True{}:
      +one = Big.of(1n)
      +dd = F64.bshl(e, one)
      +ld = L.bshl(e, one)
      +ev = Equal.trans(Nat, L.big_val(dd), Nat.mul(1n, Nat.pow(2n, e)), L.big_val(ld), vfast(e, one), Equal.sym(Nat, L.big_val(ld), Nat.mul(1n, Nat.pow(2n, e)), vlaw(e, one)))
      +hz = gt_rw(Nat.pow(2n, e), L.big_val(dd),
        Equal.trans(Nat, Nat.pow(2n, e), Nat.mul(1n, Nat.pow(2n, e)), L.big_val(dd), PNat.add_zero(Nat.pow(2n, e)), Equal.sym(Nat, L.big_val(dd), Nat.mul(1n, Nat.pow(2n, e)), vfast(e, one))),
        pos_pow2(e))
      dv_eq(m, dd, m, ld, okm, bshl_ok(e, one, {==}), hz, okm, lbshl_ok(e, one, {==}), gt_rw(L.big_val(dd), L.big_val(ld), ev, hz), {==}, ev)
    case False{}:
      +dn = F64.bshl(e, m)
      +ln = L.bshl(e, m)
      +ev = Equal.trans(Nat, L.big_val(dn), Nat.mul(L.big_val(m), Nat.pow(2n, e)), L.big_val(ln), vfast(e, m), Equal.sym(Nat, L.big_val(ln), Nat.mul(L.big_val(m), Nat.pow(2n, e)), vlaw(e, m)))
      dv_eq(dn, Big.of(1n), ln, Big.of(1n), bshl_ok(e, m, okm), {==}, {==}, lbshl_ok(e, m, okm), {==}, {==}, ev, {==})

def okm(+m: Big.Big, +e: Nat, +neg: Bool, +h0: {L.is_double(F64.F64{m, e, neg}) == True{} : Bool}) -> {L.big_ok(m) == True{} : Bool}:
  PBig.and_l(L.big_ok(m), L.pick(Bool, L.b_zero(m), Bool.and(Nat.is_eq(e, 0n), Bool.not(neg)),
    Bool.and(Bool.not(L.b_zero(Big.mod(m, L.B(2n)))), Bool.and(Nat.is_le(L.bitlen(m), 53n),
      L.pick(Bool, neg, Bool.and(Nat.is_gt(e, 0n), Nat.is_le(e, 1074n)), Nat.is_le(Nat.add(e, L.bitlen(m)), 1024n))))), h0)

def L.f64_trunc(x, h0, h1):
  match x:
    case F64.F64{+m, +e, +neg}:
      tr(m, e, neg, okm(m, e, neg, h0))

# ---------------------------------------------------------------------
# The Big laws, one fact at a time
# ---------------------------------------------------------------------

def pfst(-A: Type, -B: Type, p: A & B) -> A:
  (x, y) = p
  x

def psnd(-A: Type, -B: Type, p: A & B) -> B:
  (x, y) = p
  y

def of_v(+n: Nat) -> {L.big_val(Big.of(n)) == n : Nat}:
  pfst({L.big_val(Big.of(n)) == n : Nat}, {L.big_ok(Big.of(n)) == True{} : Bool}, L.big_of(n))

def of_ok(+n: Nat) -> {L.big_ok(Big.of(n)) == True{} : Bool}:
  psnd({L.big_val(Big.of(n)) == n : Nat}, {L.big_ok(Big.of(n)) == True{} : Bool}, L.big_of(n))

def add_v(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool})
  -> {L.big_val(Big.add(a, b)) == Nat.add(L.big_val(a), L.big_val(b)) : Nat}:
  pfst({L.big_val(Big.add(a, b)) == Nat.add(L.big_val(a), L.big_val(b)) : Nat}, {L.big_ok(Big.add(a, b)) == True{} : Bool}, L.big_add(a, b, ha, hb))

def add_ok(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool})
  -> {L.big_ok(Big.add(a, b)) == True{} : Bool}:
  psnd({L.big_val(Big.add(a, b)) == Nat.add(L.big_val(a), L.big_val(b)) : Nat}, {L.big_ok(Big.add(a, b)) == True{} : Bool}, L.big_add(a, b, ha, hb))

def mul_v(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool})
  -> {L.big_val(Big.mul(a, b)) == Nat.mul(L.big_val(a), L.big_val(b)) : Nat}:
  pfst({L.big_val(Big.mul(a, b)) == Nat.mul(L.big_val(a), L.big_val(b)) : Nat}, {L.big_ok(Big.mul(a, b)) == True{} : Bool}, L.big_mul(a, b, ha, hb))

def mul_ok(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool})
  -> {L.big_ok(Big.mul(a, b)) == True{} : Bool}:
  psnd({L.big_val(Big.mul(a, b)) == Nat.mul(L.big_val(a), L.big_val(b)) : Nat}, {L.big_ok(Big.mul(a, b)) == True{} : Bool}, L.big_mul(a, b, ha, hb))

def DM2(+a: Big.Big, +b: Big.Big) -> Type:
  {Nat.is_lt(L.big_val(Big.mod(a, b)), L.big_val(b)) == True{} : Bool}
  & {L.big_ok(Big.div(a, b)) == True{} : Bool}
  & {L.big_ok(Big.mod(a, b)) == True{} : Bool}

def dm_eq(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool},
  +hz: {Nat.is_gt(L.big_val(b), 0n) == True{} : Bool})
  -> {Nat.add(Nat.mul(L.big_val(Big.div(a, b)), L.big_val(b)), L.big_val(Big.mod(a, b))) == L.big_val(a) : Nat}:
  pfst({Nat.add(Nat.mul(L.big_val(Big.div(a, b)), L.big_val(b)), L.big_val(Big.mod(a, b))) == L.big_val(a) : Nat}, DM2(a, b), L.big_divmod(a, b, ha, hb, hz))

def dm_rest(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool},
  +hz: {Nat.is_gt(L.big_val(b), 0n) == True{} : Bool}) -> DM2(a, b):
  psnd({Nat.add(Nat.mul(L.big_val(Big.div(a, b)), L.big_val(b)), L.big_val(Big.mod(a, b))) == L.big_val(a) : Nat}, DM2(a, b), L.big_divmod(a, b, ha, hb, hz))

def dm_lt(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool},
  +hz: {Nat.is_gt(L.big_val(b), 0n) == True{} : Bool}) -> {Nat.is_lt(L.big_val(Big.mod(a, b)), L.big_val(b)) == True{} : Bool}:
  pfst({Nat.is_lt(L.big_val(Big.mod(a, b)), L.big_val(b)) == True{} : Bool}, {L.big_ok(Big.div(a, b)) == True{} : Bool} & {L.big_ok(Big.mod(a, b)) == True{} : Bool},
    dm_rest(a, b, ha, hb, hz))

def div_ok(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool},
  +hz: {Nat.is_gt(L.big_val(b), 0n) == True{} : Bool}) -> {L.big_ok(Big.div(a, b)) == True{} : Bool}:
  pfst({L.big_ok(Big.div(a, b)) == True{} : Bool}, {L.big_ok(Big.mod(a, b)) == True{} : Bool},
    psnd({Nat.is_lt(L.big_val(Big.mod(a, b)), L.big_val(b)) == True{} : Bool}, {L.big_ok(Big.div(a, b)) == True{} : Bool} & {L.big_ok(Big.mod(a, b)) == True{} : Bool},
      dm_rest(a, b, ha, hb, hz)))

def mod_ok(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool},
  +hz: {Nat.is_gt(L.big_val(b), 0n) == True{} : Bool}) -> {L.big_ok(Big.mod(a, b)) == True{} : Bool}:
  psnd({L.big_ok(Big.div(a, b)) == True{} : Bool}, {L.big_ok(Big.mod(a, b)) == True{} : Bool},
    psnd({Nat.is_lt(L.big_val(Big.mod(a, b)), L.big_val(b)) == True{} : Bool}, {L.big_ok(Big.div(a, b)) == True{} : Bool} & {L.big_ok(Big.mod(a, b)) == True{} : Bool},
      dm_rest(a, b, ha, hb, hz)))

def pick_ok(c: Bool, +a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool})
  -> {L.big_ok(F64.pick(Big.Big, c, a, b)) == True{} : Bool}:
  match c:
    case True{}:
      ha
    case False{}:
      hb

# ---------------------------------------------------------------------
# Canonical Bigs: equal values, equal Bigs
# ---------------------------------------------------------------------

def add_cancel_l(c: Nat, -a: Nat, -b: Nat, e: {Nat.add(c, a) == Nat.add(c, b) : Nat}) -> {a == b : Nat}:
  match c:
    case 0n:
      e
    case 1n+p:
      add_cancel_l(p, a, b, PNat.succ_inj(Nat.add(p, a), Nat.add(p, b), e))

def gt0_ne(-v: Nat, +h: {Nat.is_gt(v, 0n) == True{} : Bool}, +e: {v == 0n : Nat}) -> Empty:
  PNat.false_ne_true({%e : {Nat.is_gt(_, 0n) == True{} : Bool}; h : {False{} == True{} : Bool}})

# x + 10000 vx == N with x < 10000: vx is N / 10000
def limb_q(+x: Nat, +vx: Nat, +n: Nat, +hx: {Nat.is_lt(x, 10000n) == True{} : Bool}, +e: {Nat.add(x, Nat.mul(10000n, vx)) == n : Nat})
  -> {vx == Nat.div(n, 10000n) : Nat}:
  +e1 = Equal.trans(Nat, Nat.add(Nat.mul(vx, 10000n), x), Nat.add(x, Nat.mul(10000n, vx)), n,
    Equal.trans(Nat, Nat.add(Nat.mul(vx, 10000n), x), Nat.add(x, Nat.mul(vx, 10000n)), Nat.add(x, Nat.mul(10000n, vx)),
      PNat.add_comm(Nat.mul(vx, 10000n), x), PBig.add_cong_r(x, Nat.mul(vx, 10000n), Nat.mul(10000n, vx), PNat.mul_comm(vx, 10000n))), e)
  eu(n, 10000n, vx, x, e1, hx)

def big_inj(la: List<&2, Nat>, lb: List<&2, Nat>, +oka: {L.limbs_ok(la) == True{} : Bool}, +okb: {L.limbs_ok(lb) == True{} : Bool},
  +lna: {L.last_nonzero(la) == True{} : Bool}, +lnb: {L.last_nonzero(lb) == True{} : Bool}, +e: {L.limbs_val(la) == L.limbs_val(lb) : Nat})
  -> {la == lb : List<&2, Nat>}:
  match la:
    case Nil{}:
      match lb:
        case Nil{}:
          {==}
        case Con{+y, +yt}:
          Empty.absurd({[] == Con{y, yt} : List<&2, Nat>},
            gt0_ne(L.limbs_val(Con{y, yt}), PBig.pos(Con{y, yt}, lnb, {==}), Equal.sym(Nat, 0n, L.limbs_val(Con{y, yt}), e)))
    case Con{+x, +xt}:
      match lb:
        case Nil{}:
          Empty.absurd({Con{x, xt} == [] : List<&2, Nat>}, gt0_ne(L.limbs_val(Con{x, xt}), PBig.pos(Con{x, xt}, lna, {==}), e))
        case Con{+y, +yt}:
          +vx = L.limbs_val(xt)
          +vy = L.limbs_val(yt)
          +n = Nat.add(x, Nat.mul(10000n, vx))
          +hx = PBig.and_l(Nat.is_lt(x, 10000n), L.limbs_ok(xt), oka)
          +hy = PBig.and_l(Nat.is_lt(y, 10000n), L.limbs_ok(yt), okb)
          +ev = Equal.trans(Nat, vx, Nat.div(n, 10000n), vy, limb_q(x, vx, n, hx, {==}),
            Equal.sym(Nat, vy, Nat.div(n, 10000n), limb_q(y, vy, n, hy, Equal.sym(Nat, n, Nat.add(y, Nat.mul(10000n, vy)), e))))
          +e2 = {%Equal.sym(Nat, vx, vy, ev) : {Nat.add(x, Nat.mul(10000n, vx)) == Nat.add(y, Nat.mul(10000n, _)) : Nat}; e : {Nat.add(x, Nat.mul(10000n, vx)) == Nat.add(y, Nat.mul(10000n, vx)) : Nat}}
          +eh = add_cancel_l(Nat.mul(10000n, vx), x, y,
            Equal.trans(Nat, Nat.add(Nat.mul(10000n, vx), x), Nat.add(x, Nat.mul(10000n, vx)), Nat.add(Nat.mul(10000n, vx), y),
              PNat.add_comm(Nat.mul(10000n, vx), x), Equal.trans(Nat, Nat.add(x, Nat.mul(10000n, vx)), Nat.add(y, Nat.mul(10000n, vx)), Nat.add(Nat.mul(10000n, vx), y),
                e2, PNat.add_comm(y, Nat.mul(10000n, vx)))))
          +et = big_inj(xt, yt, PBig.and_r(Nat.is_lt(x, 10000n), L.limbs_ok(xt), oka), PBig.and_r(Nat.is_lt(y, 10000n), L.limbs_ok(yt), okb),
            PBig.lnz_tail(x, xt, lna), PBig.lnz_tail(y, yt, lnb), ev)
          %eh : {Con{x, xt} == Con{_, yt} : List<&2, Nat>}
          %et : {Con{x, xt} == Con{x, _} : List<&2, Nat>}
          {==}

def big_eq(a: Big.Big, b: Big.Big, +oka: {L.big_ok(a) == True{} : Bool}, +okb: {L.big_ok(b) == True{} : Bool}, +e: {L.big_val(a) == L.big_val(b) : Nat})
  -> {a == b : Big.Big}:
  match a:
    case Big.Big{+la}:
      match b:
        case Big.Big{+lb}:
          %big_inj(la, lb, PBig.and_l(L.limbs_ok(la), L.last_nonzero(la), oka), PBig.and_l(L.limbs_ok(lb), L.last_nonzero(lb), okb),
              PBig.and_r(L.limbs_ok(la), L.last_nonzero(la), oka), PBig.and_r(L.limbs_ok(lb), L.last_nonzero(lb), okb), e)
            : {Big.Big{la} == Big.Big{_} : Big.Big}
          {==}

# ---------------------------------------------------------------------
# A double's num and den
# ---------------------------------------------------------------------

def num_ok(+m: Big.Big, +e: Nat, neg: Bool, +om: {L.big_ok(m) == True{} : Bool}) -> {L.big_ok(F64.num(F64.F64{m, e, neg})) == True{} : Bool}:
  match neg:
    case True{}:
      om
    case False{}:
      bshl_ok(e, m, om)

def den_ok(+m: Big.Big, +e: Nat, neg: Bool) -> {L.big_ok(F64.den(F64.F64{m, e, neg})) == True{} : Bool}:
  match neg:
    case True{}:
      bshl_ok(e, Big.of(1n), {==})
    case False{}:
      {==}

def one_pow2(+e: Nat) -> {Nat.pow(2n, e) == L.big_val(F64.bshl(e, Big.of(1n))) : Nat}:
  Equal.trans(Nat, Nat.pow(2n, e), Nat.mul(1n, Nat.pow(2n, e)), L.big_val(F64.bshl(e, Big.of(1n))), PNat.add_zero(Nat.pow(2n, e)),
    Equal.sym(Nat, L.big_val(F64.bshl(e, Big.of(1n))), Nat.mul(1n, Nat.pow(2n, e)), vfast(e, Big.of(1n))))

def den_pos(+m: Big.Big, +e: Nat, neg: Bool) -> {Nat.is_gt(L.big_val(F64.den(F64.F64{m, e, neg})), 0n) == True{} : Bool}:
  match neg:
    case True{}:
      gt_rw(Nat.pow(2n, e), L.big_val(F64.bshl(e, Big.of(1n))), one_pow2(e), pos_pow2(e))
    case False{}:
      {==}

# ---------------------------------------------------------------------
# 10^n as a Big
# ---------------------------------------------------------------------

def bp_ok(n: Nat) -> {L.big_ok(F64.bpow10(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      mul_ok(F64.bpow10(p), Big.of(10n), bp_ok(p), of_ok(10n))

def bp_v(n: Nat) -> {L.big_val(F64.bpow10(n)) == Nat.pow(10n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      +b = F64.bpow10(p)
      %Equal.sym(Nat, L.big_val(Big.mul(b, Big.of(10n))), Nat.mul(L.big_val(b), L.big_val(Big.of(10n))), mul_v(b, Big.of(10n), bp_ok(p), of_ok(10n)))
        : {_ == Nat.mul(10n, Nat.pow(10n, p)) : Nat}
      %Equal.sym(Nat, L.big_val(b), Nat.pow(10n, p), bp_v(p)) : {Nat.mul(_, L.big_val(Big.of(10n))) == Nat.mul(10n, Nat.pow(10n, p)) : Nat}
      PNat.mul_comm(Nat.pow(10n, p), 10n)

def bp_same(n: Nat) -> {F64.bpow10(n) == L.bpow10(n) : Big.Big}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %bp_same(p) : {Big.mul(F64.bpow10(p), Big.of(10n)) == Big.mul(_, Big.of(10n)) : Big.Big}
      {==}

def pos10.of(v: Nat, +h: {Nat.is_gt(v, 0n) == True{} : Bool}) -> {Nat.is_gt(Nat.mul(10n, v), 0n) == True{} : Bool}:
  match v:
    case 0n:
      Empty.absurd({Nat.is_gt(Nat.mul(10n, 0n), 0n) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n++p:
      {==}

def pos10(n: Nat) -> {Nat.is_gt(Nat.pow(10n, n), 0n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      pos10.of(Nat.pow(10n, p), pos10(p))

# ---------------------------------------------------------------------
# Texts without a dot
# ---------------------------------------------------------------------

def dotfree(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.not(U32.is_eq(L.code(c), 46)), dotfree(rest))

def notT(a: Bool, +h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PNat.false_ne_true(h))
    case False{}:
      {==}

def df_app(s: String, +t: String, +h: {dotfree(s) == True{} : Bool}) -> {L.drop_dot(String.append(s, t)) == String.append(s, L.drop_dot(t)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      +nc = U32.is_eq(L.code(c), 46)
      +ne = notT(nc, PBig.and_l(Bool.not(nc), dotfree(rest), h))
      +ih = df_app(rest, t, PBig.and_r(Bool.not(nc), dotfree(rest), h))
      %Equal.sym(Bool, nc, False{}, ne) : {L.pick(String, _, String.append(rest, t), SCon{c, L.drop_dot(String.append(rest, t))}) == SCon{c, String.append(rest, L.drop_dot(t))} : String}
      %Equal.sym(String, L.drop_dot(String.append(rest, t)), String.append(rest, L.drop_dot(t)), ih) : {SCon{c, _} == SCon{c, String.append(rest, L.drop_dot(t))} : String}
      {==}

def df_id(s: String, +h: {dotfree(s) == True{} : Bool}) -> {L.drop_dot(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      +nc = U32.is_eq(L.code(c), 46)
      +ne = notT(nc, PBig.and_l(Bool.not(nc), dotfree(rest), h))
      +ih = df_id(rest, PBig.and_r(Bool.not(nc), dotfree(rest), h))
      %Equal.sym(Bool, nc, False{}, ne) : {L.pick(String, _, rest, SCon{c, L.drop_dot(rest)}) == SCon{c, rest} : String}
      %Equal.sym(String, L.drop_dot(rest), rest, ih) : {SCon{c, _} == SCon{c, rest} : String}
      {==}

def df_dc(r: Nat) -> {Bool.not(U32.is_eq(L.code(Dec.digit_chr(r)), 46)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+c:
              match c:
                case 0n:
                  {==}
                case 1n+e:
                  match e:
                    case 0n:
                      {==}
                    case 1n+f:
                      match f:
                        case 0n:
                          {==}
                        case 1n+g:
                          match g:
                            case 0n:
                              {==}
                            case 1n+h:
                              match h:
                                case 0n:
                                  {==}
                                case 1n+i:
                                  match i:
                                    case 0n:
                                      {==}
                                    case 1n+j:
                                      {==}

def df_go(f: Nat, b: Bool, +n: Nat, +acc: String, +h: {dotfree(acc) == True{} : Bool}) -> {dotfree(Dec.show.go(f, b, n, acc)) == True{} : Bool}:
  match f:
    case 0n:
      h
    case 1n+g:
      match b:
        case True{}:
          h
        case False{}:
          +c = Dec.digit_chr(Nat.mod(n, 10n))
          df_go(g, Nat.is_lt(n, 10n), Nat.div(n, 10n), SCon{c, acc}, PBig.and_i(Bool.not(U32.is_eq(L.code(c), 46)), dotfree(acc), df_dc(Nat.mod(n, 10n)), h))

def df_show(+n: Nat) -> {dotfree(Dec.show(n)) == True{} : Bool}:
  df_go(1n+n, False{}, n, "", {==})

# ---------------------------------------------------------------------
# Digit values and lengths
# ---------------------------------------------------------------------

def dvg_cong(-s: String, -x: Nat, -y: Nat, e: {x == y : Nat}) -> {L.digits_value.go(s, x) == L.digits_value.go(s, y) : Nat}:
  %e : {L.digits_value.go(s, x) == L.digits_value.go(s, _) : Nat}
  {==}

def bd_ok(s: String, +acc: Big.Big, +ha: {L.big_ok(acc) == True{} : Bool}) -> {L.big_ok(L.bdigits.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      ha
    case SCon{+c, +rest}:
      +m = Big.mul(acc, L.B(10n))
      bd_ok(rest, Big.add(m, L.B(L.digit(c))), add_ok(m, L.B(L.digit(c)), mul_ok(acc, L.B(10n), ha, of_ok(10n)), of_ok(L.digit(c))))

def bd_v(s: String, +acc: Big.Big, +ha: {L.big_ok(acc) == True{} : Bool}) -> {L.big_val(L.bdigits.go(s, acc)) == L.digits_value.go(s, L.big_val(acc)) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      +m = Big.mul(acc, L.B(10n))
      +dc = L.digit(c)
      +om = mul_ok(acc, L.B(10n), ha, of_ok(10n))
      +a2 = Big.add(m, L.B(dc))
      +ok2 = add_ok(m, L.B(dc), om, of_ok(dc))
      +va = L.big_val(acc)
      +ev = {%Equal.sym(Nat, L.big_val(a2), Nat.add(L.big_val(m), L.big_val(L.B(dc))), add_v(m, L.B(dc), om, of_ok(dc))) : {_ == Nat.add(Nat.mul(va, 10n), dc) : Nat};
             %Equal.sym(Nat, L.big_val(m), Nat.mul(va, L.big_val(L.B(10n))), mul_v(acc, L.B(10n), ha, of_ok(10n))) : {Nat.add(_, L.big_val(L.B(dc))) == Nat.add(Nat.mul(va, 10n), dc) : Nat};
             %Equal.sym(Nat, L.big_val(L.B(dc)), dc, of_v(dc)) : {Nat.add(Nat.mul(va, L.big_val(L.B(10n))), _) == Nat.add(Nat.mul(va, 10n), dc) : Nat};
             {==} : {L.big_val(a2) == Nat.add(Nat.mul(va, 10n), dc) : Nat}}
      Equal.trans(Nat, L.big_val(L.bdigits.go(rest, a2)), L.digits_value.go(rest, L.big_val(a2)), L.digits_value.go(rest, Nat.add(Nat.mul(va, 10n), dc)),
        bd_v(rest, a2, ok2), dvg_cong(rest, L.big_val(a2), Nat.add(Nat.mul(va, 10n), dc), ev))

def dv_shift(t: String, +a: Nat) -> {L.digits_value.go(t, a) == Nat.add(Nat.mul(a, Nat.pow(10n, String.length(t))), L.digits_value.go(t, 0n)) : Nat}:
  match t:
    case SNil{}:
      %PBig.mul_one(a) : {_ == Nat.add(Nat.mul(a, 1n), 0n) : Nat}
      PNat.add_zero(Nat.mul(a, 1n))
    case SCon{+c, +r}:
      +dc = L.digit(c)
      +p = Nat.pow(10n, String.length(r))
      +x = L.digits_value.go(r, 0n)
      +a10 = Nat.mul(a, 10n)
      Equal.trans(Nat, L.digits_value.go(r, Nat.add(a10, dc)), Nat.add(Nat.mul(Nat.add(a10, dc), p), x), Nat.add(Nat.mul(a, Nat.mul(10n, p)), L.digits_value.go(r, dc)),
        dv_shift(r, Nat.add(a10, dc)),
        {%Equal.sym(Nat, L.digits_value.go(r, dc), Nat.add(Nat.mul(dc, p), x), dv_shift(r, dc)) : {Nat.add(Nat.mul(Nat.add(a10, dc), p), x) == Nat.add(Nat.mul(a, Nat.mul(10n, p)), _) : Nat};
         %PBig.mul_assoc(a, 10n, p) : {Nat.add(Nat.mul(Nat.add(a10, dc), p), x) == Nat.add(_, Nat.add(Nat.mul(dc, p), x)) : Nat};
         %Equal.sym(Nat, Nat.add(Nat.mul(a10, p), Nat.add(Nat.mul(dc, p), x)), Nat.add(Nat.add(Nat.mul(a10, p), Nat.mul(dc, p)), x), PNat.add_assoc(Nat.mul(a10, p), Nat.mul(dc, p), x))
           : {Nat.add(Nat.mul(Nat.add(a10, dc), p), x) == _ : Nat};
         %PNat.mul_dist(a10, dc, p) : {Nat.add(_, x) == Nat.add(Nat.add(Nat.mul(a10, p), Nat.mul(dc, p)), x) : Nat};
         {==} : {Nat.add(Nat.mul(Nat.add(a10, dc), p), x) == Nat.add(Nat.mul(a, Nat.mul(10n, p)), L.digits_value.go(r, dc)) : Nat}})

def dv_zeros(n: Nat) -> {L.digits_value.go(String.repeat("0", n), 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      dv_zeros(p)

def len_cat(s: String, +t: String) -> {String.length(String.append(s, t)) == Nat.add(String.length(s), String.length(t)) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      %Equal.sym(Nat, String.length(String.append(r, t)), Nat.add(String.length(r), String.length(t)), len_cat(r, t))
        : {1n+_ == 1n+Nat.add(String.length(r), String.length(t)) : Nat}
      {==}

def len_zeros(n: Nat) -> {String.length(String.repeat("0", n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, String.length(String.repeat("0", p)), p, len_zeros(p)) : {1n+_ == 1n+p : Nat}
      {==}

def sl_stop(g: Nat, +q: Nat, +acc: String) -> {Nat.is_le(String.length(Dec.show.go(g, True{}, q, acc)), String.length(acc)) == True{} : Bool}:
  match g:
    case 0n:
      PBig.le_refl(String.length(acc))
    case 1n+h:
      PBig.le_refl(String.length(acc))

# n < 10^(1+m): its text has at most 1+m digits
def sl(f: Nat, b: Bool, +n: Nat, m: Nat, +acc: String, +hn: {Nat.is_lt(n, Nat.pow(10n, 1n+m)) == True{} : Bool})
  -> {Nat.is_le(String.length(Dec.show.go(f, b, n, acc)), Nat.add(1n+m, String.length(acc))) == True{} : Bool}:
  match f:
    case 0n:
      PBig.le_add_l(String.length(acc), 1n+m)
    case 1n++g:
      match b:
        case True{}:
          PBig.le_add_l(String.length(acc), 1n+m)
        case False{}:
          match m:
            case 0n:
              +acc2 = {SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc} : String}
              %Equal.sym(Bool, Nat.is_lt(n, 10n), True{}, hn) : {Nat.is_le(String.length(Dec.show.go(g, _, Nat.div(n, 10n), acc2)), 1n+String.length(acc)) == True{} : Bool}
              sl_stop(g, Nat.div(n, 10n), acc2)
            case 1n++mp:
              +acc2 = {SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc} : String}
              +ih = sl(g, Nat.is_lt(n, 10n), Nat.div(n, 10n), mp, acc2, PBig.dbound(n, Nat.pow(10n, 1n+mp), hn))
              %Equal.sym(Nat, 1n+Nat.add(1n+mp, String.length(acc)), Nat.add(1n+mp, 1n+String.length(acc)), PNat.add_succ(1n+mp, String.length(acc)))
                : {Nat.is_le(String.length(Dec.show.go(g, Nat.is_lt(n, 10n), Nat.div(n, 10n), acc2)), _) == True{} : Bool}
              ih

def slen(+n: Nat, +m: Nat, +hn: {Nat.is_lt(n, Nat.pow(10n, 1n+m)) == True{} : Bool}) -> {Nat.is_le(String.length(Dec.show(n)), 1n+m) == True{} : Bool}:
  %PBig.add_zero_r(1n+m) : {Nat.is_le(String.length(Dec.show(n)), _) == True{} : Bool}
  sl(1n+n, False{}, n, m, "", hn)

# ---------------------------------------------------------------------
# Fixed notation: the text gives back its K
# ---------------------------------------------------------------------

def show_v(+b: Big.Big, +h: {L.big_ok(b) == True{} : Bool}) -> {Big.show(b) == Dec.show(L.big_val(b)) : String}:
  L.big_show(b, h)

def bd_show(+v: Nat) -> {L.big_val(L.bdigits(Dec.show(v))) == v : Nat}:
  Equal.trans(Nat, L.big_val(L.bdigits(Dec.show(v))), L.digits_value.go(Dec.show(v), 0n), v, bd_v(Dec.show(v), Big.of(0n), {==}), L.dec_show_value(v))

def zp_len(+w: Nat, +s: String, +h: {Nat.is_le(String.length(s), w) == True{} : Bool}) -> {String.length(F64.zpad(w, s)) == w : Nat}:
  +u = String.length(s)
  +k = Nat.sub(w, u)
  +z = String.repeat("0", k)
  Equal.trans(Nat, String.length(String.append(z, s)), Nat.add(String.length(z), u), w, len_cat(z, s),
    {%Equal.sym(Nat, String.length(z), k, len_zeros(k)) : {Nat.add(_, u) == w : Nat};
     %PNat.add_comm(u, k) : {_ == w : Nat};
     PBig.add_sub(u, w, h) : {Nat.add(String.length(z), u) == w : Nat}})

def zp_val(+w: Nat, +s: String) -> {L.digits_value.go(F64.zpad(w, s), 0n) == L.digits_value.go(s, 0n) : Nat}:
  +z = String.repeat("0", Nat.sub(w, String.length(s)))
  Equal.trans(Nat, L.digits_value.go(String.append(z, s), 0n), L.digits_value.go(s, L.digits_value.go(z, 0n)), L.digits_value.go(s, 0n),
    Equal.sym(Nat, L.digits_value.go(s, L.digits_value.go(z, 0n)), L.digits_value.go(String.append(z, s), 0n), PDec.val_app(z, s, 0n)),
    dvg_cong(s, L.digits_value.go(z, 0n), 0n, dv_zeros(Nat.sub(w, String.length(s)))))

def fk(d: Nat, +k: Big.Big, +hk: {L.big_ok(k) == True{} : Bool}) -> {L.fixed_k(F64.fixed_text(d, k)) == k : Big.Big}:
  match d:
    case 0n:
      +v = L.big_val(k)
      +s = Dec.show(v)
      %Equal.sym(String, Big.show(k), s, show_v(k, hk)) : {L.bdigits(L.drop_dot(_)) == k : Big.Big}
      %Equal.sym(String, L.drop_dot(s), s, df_id(s, df_show(v))) : {L.bdigits(_) == k : Big.Big}
      big_eq(L.bdigits(s), k, bd_ok(s, Big.of(0n), {==}), hk, bd_show(v))
    case 1n++p:
      +w = {1n+p : Nat}
      +P = F64.bpow10(w)
      +okP = bp_ok(w)
      +hzP = gt_rw(Nat.pow(10n, w), L.big_val(P), Equal.sym(Nat, L.big_val(P), Nat.pow(10n, w), bp_v(w)), pos10(w))
      +Q = Big.div(k, P)
      +R = Big.mod(k, P)
      +okQ = div_ok(k, P, hk, okP, hzP)
      +okR = mod_ok(k, P, hk, okP, hzP)
      +vQ = L.big_val(Q)
      +vR = L.big_val(R)
      +s1 = Big.show(Q)
      +sr = Big.show(R)
      +s2 = F64.zpad(w, sr)
      +e1 = show_v(Q, okQ)
      +er = show_v(R, okR)
      +hd1 = {%Equal.sym(String, s1, Dec.show(vQ), e1) : {dotfree(_) == True{} : Bool}; df_show(vQ) : {dotfree(s1) == True{} : Bool}}
      +hlt = {%bp_v(w) : {Nat.is_lt(vR, _) == True{} : Bool}; dm_lt(k, P, hk, okP, hzP) : {Nat.is_lt(vR, Nat.pow(10n, w)) == True{} : Bool}}
      +hl = {%Equal.sym(String, sr, Dec.show(vR), er) : {Nat.is_le(String.length(_), w) == True{} : Bool}; slen(vR, p, hlt) : {Nat.is_le(String.length(sr), w) == True{} : Bool}}
      +eQ = {%Equal.sym(String, s1, Dec.show(vQ), e1) : {L.digits_value.go(_, 0n) == vQ : Nat}; L.dec_show_value(vQ) : {L.digits_value.go(s1, 0n) == vQ : Nat}}
      +eR = {%Equal.sym(String, sr, Dec.show(vR), er) : {L.digits_value.go(_, 0n) == vR : Nat}; L.dec_show_value(vR) : {L.digits_value.go(sr, 0n) == vR : Nat}}
      +eR2 = Equal.trans(Nat, L.digits_value.go(s2, 0n), L.digits_value.go(sr, 0n), vR, zp_val(w, sr), eR)
      +s12 = String.append(s1, s2)
      +a4 = Nat.add(Nat.mul(vQ, Nat.pow(10n, String.length(s2))), L.digits_value.go(s2, 0n))
      +a5 = Nat.add(Nat.mul(vQ, L.big_val(P)), vR)
      +e45 = {%Equal.sym(Nat, String.length(s2), w, zp_len(w, sr, hl)) : {Nat.add(Nat.mul(vQ, Nat.pow(10n, _)), L.digits_value.go(s2, 0n)) == a5 : Nat};
              %bp_v(w) : {Nat.add(Nat.mul(vQ, _), L.digits_value.go(s2, 0n)) == a5 : Nat};
              %Equal.sym(Nat, L.digits_value.go(s2, 0n), vR, eR2) : {Nat.add(Nat.mul(vQ, L.big_val(P)), _) == a5 : Nat};
              {==} : {a4 == a5 : Nat}}
      +ev = Equal.trans(Nat, L.big_val(L.bdigits(s12)), L.digits_value.go(s12, 0n), L.big_val(k), bd_v(s12, Big.of(0n), {==}),
        Equal.trans(Nat, L.digits_value.go(s12, 0n), L.digits_value.go(s2, L.digits_value.go(s1, 0n)), L.big_val(k),
          Equal.sym(Nat, L.digits_value.go(s2, L.digits_value.go(s1, 0n)), L.digits_value.go(s12, 0n), PDec.val_app(s1, s2, 0n)),
          Equal.trans(Nat, L.digits_value.go(s2, L.digits_value.go(s1, 0n)), L.digits_value.go(s2, vQ), L.big_val(k), dvg_cong(s2, L.digits_value.go(s1, 0n), vQ, eQ),
            Equal.trans(Nat, L.digits_value.go(s2, vQ), a4, L.big_val(k), dv_shift(s2, vQ),
              Equal.trans(Nat, a4, a5, L.big_val(k), e45, dm_eq(k, P, hk, okP, hzP))))))
      %Equal.sym(String, L.drop_dot(String.append(s1, String.append(".", s2))), s12, df_app(s1, String.append(".", s2), hd1)) : {L.bdigits(_) == k : Big.Big}
      big_eq(L.bdigits(s12), k, bd_ok(s12, Big.of(0n), {==}), hk, ev)

def frac_same(p: Nat, +k: Big.Big) -> {F64.fixed_text(1n+p, k) == L.fixed_text(1n+p, k) : String}:
  %bp_same(1n+p) : {String.append(Big.show(Big.div(k, F64.bpow10(1n+p))), String.append(".", F64.zpad(1n+p, Big.show(Big.mod(k, F64.bpow10(1n+p))))))
    == String.append(Big.show(Big.div(k, _)), String.append(".", L.zpad(1n+p, Big.show(Big.mod(k, _))))) : String}
  {==}

def ft(d: Nat, +k: Big.Big, +hk: {L.big_ok(k) == True{} : Bool}) -> {F64.fixed_text(d, k) == L.fixed_text(d, L.fixed_k(F64.fixed_text(d, k))) : String}:
  match d:
    case 0n:
      %Equal.sym(Big.Big, L.fixed_k(F64.fixed_text(0n, k)), k, fk(0n, k, hk)) : {F64.fixed_text(0n, k) == L.fixed_text(0n, _) : String}
      {==}
    case 1n++p:
      %Equal.sym(Big.Big, L.fixed_k(F64.fixed_text(1n+p, k)), k, fk(1n+p, k, hk)) : {F64.fixed_text(1n+p, k) == L.fixed_text(1n+p, _) : String}
      frac_same(p, k)

def rint_ok(+p: Big.Big, +q: Big.Big, +hp: {L.big_ok(p) == True{} : Bool}, +hq: {L.big_ok(q) == True{} : Bool},
  +hz: {Nat.is_gt(L.big_val(q), 0n) == True{} : Bool}) -> {L.big_ok(F64.round_int(p, q)) == True{} : Bool}:
  +k = Big.div(p, q)
  +okk = div_ok(p, q, hp, hq, hz)
  +r = Big.mod(p, q)
  +c = Big.cmp(Big.add(r, r), q)
  pick_ok(Bool.or(Cmp.is_gt(c), Bool.and(Cmp.is_eq(c), F64.odd(k))), Big.add(k, F64.big1()), k, add_ok(k, F64.big1(), okk, {==}), okk)

def fixed_k_ok(+d: Nat, +m: Big.Big, +e: Nat, +neg: Bool, +om: {L.big_ok(m) == True{} : Bool})
  -> {L.big_ok(F64.round_int(Big.mul(F64.num(F64.F64{m, e, neg}), F64.bpow10(d)), F64.den(F64.F64{m, e, neg}))) == True{} : Bool}:
  +x = {F64.F64{m, e, neg} : F64.F64}
  rint_ok(Big.mul(F64.num(x), F64.bpow10(d)), F64.den(x), mul_ok(F64.num(x), F64.bpow10(d), num_ok(m, e, neg, om), bp_ok(d)), den_ok(m, e, neg), den_pos(m, e, neg))

def L.f64_fixed_text(d, x, h):
  match x:
    case F64.F64{+m, +e, +neg}:
      +xx = {F64.F64{m, e, neg} : F64.F64}
      ft(d, F64.round_int(Big.mul(F64.num(xx), F64.bpow10(d)), F64.den(xx)), fixed_k_ok(d, m, e, neg, okm(m, e, neg, h)))

# ---------------------------------------------------------------------
# Nearest integer, ties to even: the arithmetic
# ---------------------------------------------------------------------

# LAWS' fixed_nearest verdict on a distance comparison x
def fin(+x: Cmp, +eqk: Bool, +ev: Bool) -> Bool:
  Bool.or(Cmp.is_lt(x), Bool.and(Cmp.is_eq(x), Bool.or(eqk, ev)))

# LAWS' dist_cmp, over its six comparisons
def dcg(+x1: Cmp, +x2: Cmp, +x3: Cmp, +x4: Cmp, +x5: Cmp, +x6: Cmp) -> Cmp:
  L.pick(Cmp, Bool.not(Cmp.is_gt(x1)), L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x3, x4), L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x5, x6))

def dcg1T(x1: Cmp, +x2: Cmp, +x3: Cmp, +x4: Cmp, +x5: Cmp, +x6: Cmp, +h: {Cmp.is_gt(x1) == False{} : Bool})
  -> {dcg(x1, x2, x3, x4, x5, x6) == L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x3, x4) : Cmp}:
  match x1:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({dcg(GT{}, x2, x3, x4, x5, x6) == L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x3, x4) : Cmp}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))

def dcg1F(x1: Cmp, +x2: Cmp, +x3: Cmp, +x4: Cmp, +x5: Cmp, +x6: Cmp, +h: {Cmp.is_gt(x1) == True{} : Bool})
  -> {dcg(x1, x2, x3, x4, x5, x6) == L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x5, x6) : Cmp}:
  match x1:
    case LT{}:
      Empty.absurd({dcg(LT{}, x2, x3, x4, x5, x6) == L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x5, x6) : Cmp}, PNat.false_ne_true(h))
    case EQ{}:
      Empty.absurd({dcg(EQ{}, x2, x3, x4, x5, x6) == L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x5, x6) : Cmp}, PNat.false_ne_true(h))
    case GT{}:
      {==}

def pk_T(x2: Cmp, +a: Cmp, +b: Cmp, +h: {Cmp.is_gt(x2) == False{} : Bool}) -> {L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), a, b) == a : Cmp}:
  %Equal.sym(Bool, Cmp.is_gt(x2), False{}, h) : {L.pick(Cmp, Bool.not(_), a, b) == a : Cmp}
  {==}

def pk_F(x2: Cmp, +a: Cmp, +b: Cmp, +h: {Cmp.is_gt(x2) == True{} : Bool}) -> {L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), a, b) == b : Cmp}:
  %Equal.sym(Bool, Cmp.is_gt(x2), True{}, h) : {L.pick(Cmp, Bool.not(_), a, b) == b : Cmp}
  {==}

def fin_rw(-x: Cmp, -y: Cmp, -ek: Bool, -ev: Bool, e: {x == y : Cmp}, +h: {fin(y, ek, ev) == True{} : Bool}) -> {fin(x, ek, ev) == True{} : Bool}:
  %Equal.sym(Cmp, x, y, e) : {fin(_, ek, ev) == True{} : Bool}
  h

def or_tr(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def fin_ng(x: Cmp, +ek: Bool, +ev: Bool, +h: {Cmp.is_gt(x) == False{} : Bool}, +hev: {ev == True{} : Bool}) -> {fin(x, ek, ev) == True{} : Bool}:
  match x:
    case LT{}:
      {==}
    case EQ{}:
      %Equal.sym(Bool, ev, True{}, hev) : {Bool.or(ek, _) == True{} : Bool}
      or_tr(ek)
    case GT{}:
      Empty.absurd({fin(GT{}, ek, ev) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))

def finA(w: Nat, u: Nat, +ev: Bool, +h: {Nat.is_le(w, u) == True{} : Bool}) -> {fin(Nat.cmp(w, u), Cmp.is_eq(Nat.cmp(u, w)), ev) == True{} : Bool}:
  match w:
    case 0n:
      match u:
        case 0n:
          {==}
        case 1n+up:
          {==}
    case 1n+wp:
      match u:
        case 0n:
          Empty.absurd({fin(GT{}, False{}, ev) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n+up:
          finA(wp, up, ev, h)

def finB(u: Nat, w: Nat, +ev: Bool, +h: {Nat.is_le(u, w) == True{} : Bool}) -> {fin(Nat.cmp(u, w), Cmp.is_eq(Nat.cmp(u, w)), ev) == True{} : Bool}:
  match u:
    case 0n:
      match w:
        case 0n:
          {==}
        case 1n+wp:
          {==}
    case 1n+up:
      match w:
        case 0n:
          Empty.absurd({fin(GT{}, False{}, ev) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n+wp:
          finB(up, wp, ev, h)

def ngt_of_le(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Cmp.is_gt(Nat.cmp(a, b)) == False{} : Bool}:
  notT(Cmp.is_gt(Nat.cmp(a, b)), Equal.trans(Bool, Bool.not(Cmp.is_gt(Nat.cmp(a, b))), Cmp.is_le(Nat.cmp(a, b)), True{}, PBig.not_gt_le(Nat.cmp(a, b)), h))

def le_of_ngt(+a: Nat, +b: Nat, +h: {Cmp.is_gt(Nat.cmp(a, b)) == False{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_le(Nat.cmp(a, b)), Bool.not(Cmp.is_gt(Nat.cmp(a, b))), True{},
    Equal.sym(Bool, Bool.not(Cmp.is_gt(Nat.cmp(a, b))), Cmp.is_le(Nat.cmp(a, b)), PBig.not_gt_le(Nat.cmp(a, b))),
    {%Equal.sym(Bool, Cmp.is_gt(Nat.cmp(a, b)), False{}, h) : {Bool.not(_) == True{} : Bool}; {==} : {Bool.not(Cmp.is_gt(Nat.cmp(a, b))) == True{} : Bool}})

def gt_of_lt(a: Nat, b: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Cmp.is_gt(Nat.cmp(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Cmp.is_gt(Nat.cmp(0n, 0n)) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n+bp:
          Empty.absurd({Cmp.is_gt(Nat.cmp(0n, 1n+bp)) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          gt_of_lt(ap, bp, h)

def lt_of_gt(a: Nat, b: Nat, +h: {Cmp.is_gt(Nat.cmp(a, b)) == True{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n+bp:
          Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          lt_of_gt(ap, bp, h)

def cmp_lt_of(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == LT{} : Cmp}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(0n, 0n) == LT{} : Cmp}, PNat.false_ne_true(h))
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(1n+ap, 0n) == LT{} : Cmp}, PNat.false_ne_true(h))
        case 1n+bp:
          cmp_lt_of(ap, bp, h)

def lt_add_l(+s: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(s, a), Nat.add(s, b)) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(Nat.add(s, a), Nat.add(s, b)), Nat.cmp(a, b), PBig.cmp_cancel(s, a, b)) : {Cmp.is_lt(_) == True{} : Bool}
  h

def le_mul_r(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  %PNat.mul_comm(c, a) : {Nat.is_le(_, Nat.mul(b, c)) == True{} : Bool}
  %PNat.mul_comm(c, b) : {Nat.is_le(Nat.mul(c, a), _) == True{} : Bool}
  PBig.le_mul_mono(c, a, b, h)

def mono_cmp(u: Nat, w: Nat, +d: Nat) -> {Nat.cmp(Nat.mul(u, 1n+d), Nat.mul(w, 1n+d)) == Nat.cmp(u, w) : Cmp}:
  match u:
    case 0n:
      match w:
        case 0n:
          {==}
        case 1n+wp:
          {==}
    case 1n+up:
      match w:
        case 0n:
          {==}
        case 1n+wp:
          %Equal.sym(Cmp, Nat.cmp(Nat.add(1n+d, Nat.mul(up, 1n+d)), Nat.add(1n+d, Nat.mul(wp, 1n+d))), Nat.cmp(Nat.mul(up, 1n+d), Nat.mul(wp, 1n+d)),
            PBig.cmp_cancel(1n+d, Nat.mul(up, 1n+d), Nat.mul(wp, 1n+d))) : {_ == Nat.cmp(up, wp) : Cmp}
          mono_cmp(up, wp, d)

# (x + r) + (x + r) and x + (B + x), regrouped
def rg1(+x: Nat, +r: Nat) -> {Nat.add(Nat.add(x, r), Nat.add(x, r)) == Nat.add(Nat.add(x, x), Nat.add(r, r)) : Nat}:
  PBig.add4(x, r, x, r)

def rg2(+x: Nat, +b: Nat) -> {Nat.add(x, Nat.add(b, x)) == Nat.add(Nat.add(x, x), b) : Nat}:
  Equal.trans(Nat, Nat.add(x, Nat.add(b, x)), Nat.add(b, Nat.add(x, x)), Nat.add(Nat.add(x, x), b), PNat.add_swap(x, b, x), PNat.add_comm(b, Nat.add(x, x)))

def rg3(+x: Nat, +b: Nat) -> {Nat.add(Nat.add(b, x), x) == Nat.add(Nat.add(x, x), b) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(b, x), x), Nat.add(b, Nat.add(x, x)), Nat.add(Nat.add(x, x), b),
    Equal.sym(Nat, Nat.add(b, Nat.add(x, x)), Nat.add(Nat.add(b, x), x), PNat.add_assoc(b, x, x)), PNat.add_comm(b, Nat.add(x, x)))

# w B above q B + r (r < B): w above q
def w_gt.of(c: Bool, +q: Nat, +r: Nat, +b: Nat, +w: Nat, +hc: {Nat.is_le(w, q) == c : Bool},
  +h: {Nat.is_lt(Nat.add(Nat.mul(q, b), r), Nat.mul(w, b)) == True{} : Bool}) -> {Nat.is_le(1n+q, w) == True{} : Bool}:
  match c:
    case True{}:
      +le = PBig.le_trans(Nat.mul(w, b), Nat.mul(q, b), Nat.add(Nat.mul(q, b), r), le_mul_r(w, q, b, hc), PBig.le_add(Nat.mul(q, b), r))
      Empty.absurd({Nat.is_le(1n+q, w) == True{} : Bool}, PBig.lt_le_absurd(Nat.add(Nat.mul(q, b), r), Nat.mul(w, b), h, le))
    case False{}:
      PBig.lt_to_le(q, w, PBig.nle_lt(w, q, hc))

def w_gt(+q: Nat, +r: Nat, +b: Nat, +w: Nat, +h: {Nat.is_lt(Nat.add(Nat.mul(q, b), r), Nat.mul(w, b)) == True{} : Bool}) -> {Nat.is_le(1n+q, w) == True{} : Bool}:
  w_gt.of(Nat.is_le(w, q), q, r, b, w, {==}, h)

def lt_of_cmp_lt(-a: Nat, -b: Nat, h: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, b), LT{}, h) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

def le_of_cmp_eq(-a: Nat, -b: Nat, h: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {Nat.is_le(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, b), EQ{}, h) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def gt_of_cmp_gt(-a: Nat, -b: Nat, h: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Cmp.is_gt(Nat.cmp(a, b)) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, b), GT{}, h) : {Cmp.is_gt(_) == True{} : Bool}
  {==}

def ge_of_cmp_eq(+a: Nat, +b: Nat, +h: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {Nat.is_le(b, a) == True{} : Bool}:
  %Equal.sym(Nat, a, b, PBig.cmp_eq(a, b, h)) : {Nat.is_le(b, _) == True{} : Bool}
  PBig.le_refl(b)

# dist_cmp(u B, w B, vt) and the rest of fixed_nearest, over Nats
def NS(+u: Nat, +w: Nat, +vt: Nat, +b: Nat, +ev: Bool) -> Bool:
  +ua = Nat.mul(u, b)
  +wc = Nat.mul(w, b)
  fin(dcg(Nat.cmp(ua, vt), Nat.cmp(wc, vt), Nat.cmp(wc, ua), Nat.cmp(Nat.add(vt, vt), Nat.add(ua, wc)), Nat.cmp(Nat.add(ua, wc), Nat.add(vt, vt)), Nat.cmp(ua, wc)),
    Cmp.is_eq(Nat.cmp(u, w)), ev)

def dTT(+x1: Cmp, +x2: Cmp, +x3: Cmp, +x4: Cmp, +x5: Cmp, +x6: Cmp, +ek: Bool, +ev: Bool,
  +h1: {Cmp.is_gt(x1) == False{} : Bool}, +h2: {Cmp.is_gt(x2) == False{} : Bool}, +h: {fin(x3, ek, ev) == True{} : Bool})
  -> {fin(dcg(x1, x2, x3, x4, x5, x6), ek, ev) == True{} : Bool}:
  fin_rw(dcg(x1, x2, x3, x4, x5, x6), x3, ek, ev,
    Equal.trans(Cmp, dcg(x1, x2, x3, x4, x5, x6), L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x3, x4), x3, dcg1T(x1, x2, x3, x4, x5, x6, h1), pk_T(x2, x3, x4, h2)), h)

def dTF(+x1: Cmp, +x2: Cmp, +x3: Cmp, +x4: Cmp, +x5: Cmp, +x6: Cmp, +ek: Bool, +ev: Bool,
  +h1: {Cmp.is_gt(x1) == False{} : Bool}, +h2: {Cmp.is_gt(x2) == True{} : Bool}, +h: {fin(x4, ek, ev) == True{} : Bool})
  -> {fin(dcg(x1, x2, x3, x4, x5, x6), ek, ev) == True{} : Bool}:
  fin_rw(dcg(x1, x2, x3, x4, x5, x6), x4, ek, ev,
    Equal.trans(Cmp, dcg(x1, x2, x3, x4, x5, x6), L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x3, x4), x4, dcg1T(x1, x2, x3, x4, x5, x6, h1), pk_F(x2, x3, x4, h2)), h)

def dFT(+x1: Cmp, +x2: Cmp, +x3: Cmp, +x4: Cmp, +x5: Cmp, +x6: Cmp, +ek: Bool, +ev: Bool,
  +h1: {Cmp.is_gt(x1) == True{} : Bool}, +h2: {Cmp.is_gt(x2) == False{} : Bool}, +h: {fin(x5, ek, ev) == True{} : Bool})
  -> {fin(dcg(x1, x2, x3, x4, x5, x6), ek, ev) == True{} : Bool}:
  fin_rw(dcg(x1, x2, x3, x4, x5, x6), x5, ek, ev,
    Equal.trans(Cmp, dcg(x1, x2, x3, x4, x5, x6), L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x5, x6), x5, dcg1F(x1, x2, x3, x4, x5, x6, h1), pk_T(x2, x5, x6, h2)), h)

def dFF(+x1: Cmp, +x2: Cmp, +x3: Cmp, +x4: Cmp, +x5: Cmp, +x6: Cmp, +ek: Bool, +ev: Bool,
  +h1: {Cmp.is_gt(x1) == True{} : Bool}, +h2: {Cmp.is_gt(x2) == True{} : Bool}, +h: {fin(x6, ek, ev) == True{} : Bool})
  -> {fin(dcg(x1, x2, x3, x4, x5, x6), ek, ev) == True{} : Bool}:
  fin_rw(dcg(x1, x2, x3, x4, x5, x6), x6, ek, ev,
    Equal.trans(Cmp, dcg(x1, x2, x3, x4, x5, x6), L.pick(Cmp, Bool.not(Cmp.is_gt(x2)), x5, x6), x6, dcg1F(x1, x2, x3, x4, x5, x6, h1), pk_F(x2, x5, x6, h2)), h)

def finLT(+a: Nat, +c: Nat, +ek: Bool, +ev: Bool, +h: {Nat.is_lt(a, c) == True{} : Bool}) -> {fin(Nat.cmp(a, c), ek, ev) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(a, c), LT{}, cmp_lt_of(a, c, h)) : {fin(_, ek, ev) == True{} : Bool}
  {==}

def finLE(+a: Nat, +c: Nat, +ek: Bool, +ev: Bool, +h: {Nat.is_le(a, c) == True{} : Bool}, +hev: {ev == True{} : Bool}) -> {fin(Nat.cmp(a, c), ek, ev) == True{} : Bool}:
  fin_ng(Nat.cmp(a, c), ek, ev, ngt_of_le(a, c, h), hev)

def mono_cmpB(+u: Nat, +w: Nat, b: Nat, +hb: {Nat.is_gt(b, 0n) == True{} : Bool}) -> {Nat.cmp(Nat.mul(u, b), Nat.mul(w, b)) == Nat.cmp(u, w) : Cmp}:
  match b:
    case 0n:
      Empty.absurd({Nat.cmp(Nat.mul(u, 0n), Nat.mul(w, 0n)) == Nat.cmp(u, w) : Cmp}, PNat.false_ne_true(hb))
    case 1n++d:
      mono_cmp(u, w, d)

def TieA(t: Bool, +r: Nat, +b: Nat, +ev: Bool) -> Type:
  match t:
    case True{}:
      {Nat.add(r, r) == b : Nat} & {ev == True{} : Bool}
    case False{}:
      {Nat.is_lt(Nat.add(r, r), b) == True{} : Bool}

def TieB(t: Bool, +r: Nat, +b: Nat, +ev: Bool) -> Type:
  match t:
    case True{}:
      {Nat.add(r, r) == b : Nat} & {ev == True{} : Bool}
    case False{}:
      {Nat.is_lt(b, Nat.add(r, r)) == True{} : Bool}

def le_rw_r2(-a: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, +h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(a, y) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

def le_rw_l2(-x: Nat, -y: Nat, -b: Nat, e: {x == y : Nat}, +h: {Nat.is_le(x, b) == True{} : Bool}) -> {Nat.is_le(y, b) == True{} : Bool}:
  %e : {Nat.is_le(_, b) == True{} : Bool}
  h

def A4(t: Bool, +h2: Nat, +r: Nat, +b: Nat, +sS: Nat, +ek: Bool, +ev: Bool, ht: TieA(t, r, b, ev),
  +hS: {Nat.is_le(Nat.add(h2, b), sS) == True{} : Bool}) -> {fin(Nat.cmp(Nat.add(h2, Nat.add(r, r)), sS), ek, ev) == True{} : Bool}:
  match t:
    case True{}:
      (e, hev) = ht
      finLE(Nat.add(h2, Nat.add(r, r)), sS, ek, ev, le_rw_l2(Nat.add(h2, b), Nat.add(h2, Nat.add(r, r)), sS, PBig.add_cong_r(h2, b, Nat.add(r, r), Equal.sym(Nat, Nat.add(r, r), b, e)), hS), hev)
    case False{}:
      finLT(Nat.add(h2, Nat.add(r, r)), sS, ek, ev, PBig.lt_le_trans(Nat.add(h2, Nat.add(r, r)), Nat.add(h2, b), sS, lt_add_l(h2, Nat.add(r, r), b, ht), hS))

def B5(t: Bool, +h2: Nat, +r: Nat, +b: Nat, +sS: Nat, +ek: Bool, +ev: Bool, ht: TieB(t, r, b, ev),
  +hS: {Nat.is_le(sS, Nat.add(h2, b)) == True{} : Bool}) -> {fin(Nat.cmp(sS, Nat.add(h2, Nat.add(r, r))), ek, ev) == True{} : Bool}:
  match t:
    case True{}:
      (e, hev) = ht
      finLE(sS, Nat.add(h2, Nat.add(r, r)), ek, ev, le_rw_r2(sS, Nat.add(h2, b), Nat.add(h2, Nat.add(r, r)), PBig.add_cong_r(h2, b, Nat.add(r, r), Equal.sym(Nat, Nat.add(r, r), b, e)), hS), hev)
    case False{}:
      finLT(sS, Nat.add(h2, Nat.add(r, r)), ek, ev, PBig.le_lt_trans(sS, Nat.add(h2, b), Nat.add(h2, Nat.add(r, r)), hS, lt_add_l(h2, b, Nat.add(r, r), ht)))

def fin_cmp_rw(-a: Nat, -a2: Nat, -c: Nat, -ek: Bool, -ev: Bool, e: {a == a2 : Nat}, +h: {fin(Nat.cmp(a2, c), ek, ev) == True{} : Bool})
  -> {fin(Nat.cmp(a, c), ek, ev) == True{} : Bool}:
  %Equal.sym(Nat, a, a2, e) : {fin(Nat.cmp(_, c), ek, ev) == True{} : Bool}
  h

def fin_cmp_rw2(-a: Nat, -c: Nat, -c2: Nat, -ek: Bool, -ev: Bool, e: {c == c2 : Nat}, +h: {fin(Nat.cmp(a, c2), ek, ev) == True{} : Bool})
  -> {fin(Nat.cmp(a, c), ek, ev) == True{} : Bool}:
  %Equal.sym(Nat, c, c2, e) : {fin(Nat.cmp(a, _), ek, ev) == True{} : Bool}
  h

# q B + r < B + q B
def vt_lt(+q: Nat, +r: Nat, +b: Nat, +hr: {Nat.is_lt(r, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(Nat.mul(q, b), r), Nat.add(b, Nat.mul(q, b))) == True{} : Bool}:
  PBig.lt_rw_r(Nat.add(Nat.mul(q, b), r), Nat.add(Nat.mul(q, b), b), Nat.add(b, Nat.mul(q, b)), PNat.add_comm(Nat.mul(q, b), b), lt_add_l(Nat.mul(q, b), r, b, hr))

# the double's value rounded down (x = q): no w is nearer
def cA.of(c: Bool, t: Bool, +q: Nat, +w: Nat, +r: Nat, +b: Nat, +ev: Bool, +hc: {Nat.is_le(w, q) == c : Bool},
  +hr: {Nat.is_lt(r, b) == True{} : Bool}, +hb: {Nat.is_gt(b, 0n) == True{} : Bool}, ht: TieA(t, r, b, ev))
  -> {NS(q, w, Nat.add(Nat.mul(q, b), r), b, ev) == True{} : Bool}:
  match c:
    case True{}:
      +ua = Nat.mul(q, b)
      +wc = Nat.mul(w, b)
      +vt = Nat.add(ua, r)
      +ek = Cmp.is_eq(Nat.cmp(q, w))
      +h1 = ngt_of_le(ua, vt, PBig.le_add(ua, r))
      +h2 = ngt_of_le(wc, vt, PBig.le_trans(wc, ua, vt, le_mul_r(w, q, b, hc), PBig.le_add(ua, r)))
      dTT(Nat.cmp(ua, vt), Nat.cmp(wc, vt), Nat.cmp(wc, ua), Nat.cmp(Nat.add(vt, vt), Nat.add(ua, wc)), Nat.cmp(Nat.add(ua, wc), Nat.add(vt, vt)), Nat.cmp(ua, wc), ek, ev, h1, h2,
        {%Equal.sym(Cmp, Nat.cmp(wc, ua), Nat.cmp(w, q), mono_cmpB(w, q, b, hb)) : {fin(_, ek, ev) == True{} : Bool}; finA(w, q, ev, hc) : {fin(Nat.cmp(wc, ua), ek, ev) == True{} : Bool}})
    case False{}:
      +ua = Nat.mul(q, b)
      +wc = Nat.mul(w, b)
      +vt = Nat.add(ua, r)
      +ek = Cmp.is_eq(Nat.cmp(q, w))
      +h1 = ngt_of_le(ua, vt, PBig.le_add(ua, r))
      +hw = PBig.lt_to_le(q, w, PBig.nle_lt(w, q, hc))
      +wge = le_mul_r(1n+q, w, b, hw)
      +h2 = gt_of_lt(wc, vt, PBig.lt_le_trans(vt, Nat.add(b, ua), wc, vt_lt(q, r, b, hr), wge))
      +hS = le_rw_l2(Nat.add(ua, Nat.add(b, ua)), Nat.add(Nat.add(ua, ua), b), Nat.add(ua, wc), rg2(ua, b), PBig.le_add_mono(ua, Nat.add(b, ua), wc, wge))
      dTF(Nat.cmp(ua, vt), Nat.cmp(wc, vt), Nat.cmp(wc, ua), Nat.cmp(Nat.add(vt, vt), Nat.add(ua, wc)), Nat.cmp(Nat.add(ua, wc), Nat.add(vt, vt)), Nat.cmp(ua, wc), ek, ev, h1, h2,
        fin_cmp_rw(Nat.add(vt, vt), Nat.add(Nat.add(ua, ua), Nat.add(r, r)), Nat.add(ua, wc), ek, ev, rg1(ua, r),
          A4(t, Nat.add(ua, ua), r, b, Nat.add(ua, wc), ek, ev, ht, hS)))

def cA(t: Bool, +q: Nat, +w: Nat, +r: Nat, +b: Nat, +ev: Bool,
  +hr: {Nat.is_lt(r, b) == True{} : Bool}, +hb: {Nat.is_gt(b, 0n) == True{} : Bool}, ht: TieA(t, r, b, ev))
  -> {NS(q, w, Nat.add(Nat.mul(q, b), r), b, ev) == True{} : Bool}:
  cA.of(Nat.is_le(w, q), t, q, w, r, b, ev, {==}, hr, hb, ht)

# rounded up (x = q + 1): no w is nearer
def cB.of(c: Bool, t: Bool, +q: Nat, +w: Nat, +r: Nat, +b: Nat, +ev: Bool, +hc: {Nat.is_le(w, q) == c : Bool},
  +hr: {Nat.is_lt(r, b) == True{} : Bool}, +hb: {Nat.is_gt(b, 0n) == True{} : Bool}, ht: TieB(t, r, b, ev))
  -> {NS(1n+q, w, Nat.add(Nat.mul(q, b), r), b, ev) == True{} : Bool}:
  match c:
    case True{}:
      +qb = Nat.mul(q, b)
      +ua = Nat.add(b, qb)
      +wc = Nat.mul(w, b)
      +vt = Nat.add(qb, r)
      +ek = Cmp.is_eq(Nat.cmp(1n+q, w))
      +h1 = gt_of_lt(ua, vt, vt_lt(q, r, b, hr))
      +wle = le_mul_r(w, q, b, hc)
      +h2 = ngt_of_le(wc, vt, PBig.le_trans(wc, qb, vt, wle, PBig.le_add(qb, r)))
      +hS = le_rw_r2(Nat.add(ua, wc), Nat.add(ua, qb), Nat.add(Nat.add(qb, qb), b), rg3(qb, b), PBig.le_add_mono(ua, wc, qb, wle))
      dFT(Nat.cmp(ua, vt), Nat.cmp(wc, vt), Nat.cmp(wc, ua), Nat.cmp(Nat.add(vt, vt), Nat.add(ua, wc)), Nat.cmp(Nat.add(ua, wc), Nat.add(vt, vt)), Nat.cmp(ua, wc), ek, ev, h1, h2,
        fin_cmp_rw2(Nat.add(ua, wc), Nat.add(vt, vt), Nat.add(Nat.add(qb, qb), Nat.add(r, r)), ek, ev, rg1(qb, r),
          B5(t, Nat.add(qb, qb), r, b, Nat.add(ua, wc), ek, ev, ht, hS)))
    case False{}:
      +qb = Nat.mul(q, b)
      +ua = Nat.add(b, qb)
      +wc = Nat.mul(w, b)
      +vt = Nat.add(qb, r)
      +ek = Cmp.is_eq(Nat.cmp(1n+q, w))
      +h1 = gt_of_lt(ua, vt, vt_lt(q, r, b, hr))
      +hw = PBig.lt_to_le(q, w, PBig.nle_lt(w, q, hc))
      +wge = le_mul_r(1n+q, w, b, hw)
      +h2 = gt_of_lt(wc, vt, PBig.lt_le_trans(vt, ua, wc, vt_lt(q, r, b, hr), wge))
      dFF(Nat.cmp(ua, vt), Nat.cmp(wc, vt), Nat.cmp(wc, ua), Nat.cmp(Nat.add(vt, vt), Nat.add(ua, wc)), Nat.cmp(Nat.add(ua, wc), Nat.add(vt, vt)), Nat.cmp(ua, wc), ek, ev, h1, h2,
        {%Equal.sym(Cmp, Nat.cmp(ua, wc), Nat.cmp(1n+q, w), mono_cmpB(1n+q, w, b, hb)) : {fin(_, ek, ev) == True{} : Bool}; finB(1n+q, w, ev, hw) : {fin(Nat.cmp(ua, wc), ek, ev) == True{} : Bool}})

def cB(t: Bool, +q: Nat, +w: Nat, +r: Nat, +b: Nat, +ev: Bool,
  +hr: {Nat.is_lt(r, b) == True{} : Bool}, +hb: {Nat.is_gt(b, 0n) == True{} : Bool}, ht: TieB(t, r, b, ev))
  -> {NS(1n+q, w, Nat.add(Nat.mul(q, b), r), b, ev) == True{} : Bool}:
  cB.of(Nat.is_le(w, q), t, q, w, r, b, ev, {==}, hr, hb, ht)

# ---------------------------------------------------------------------
# From Bigs to the Nat core
# ---------------------------------------------------------------------

def cmpv(+x: Big.Big, +y: Big.Big, -xv: Nat, -yv: Nat, ex: {L.big_val(x) == xv : Nat}, ey: {L.big_val(y) == yv : Nat})
  -> {Big.cmp(x, y) == Nat.cmp(xv, yv) : Cmp}:
  %ex : {Big.cmp(x, y) == Nat.cmp(_, yv) : Cmp}
  %ey : {Big.cmp(x, y) == Nat.cmp(L.big_val(x), _) : Cmp}
  L.big_cmp(x, y)

def addv(+x: Big.Big, +y: Big.Big, +ox: {L.big_ok(x) == True{} : Bool}, +oy: {L.big_ok(y) == True{} : Bool}, -xv: Nat, -yv: Nat,
  ex: {L.big_val(x) == xv : Nat}, ey: {L.big_val(y) == yv : Nat}) -> {L.big_val(Big.add(x, y)) == Nat.add(xv, yv) : Nat}:
  %ex : {L.big_val(Big.add(x, y)) == Nat.add(_, yv) : Nat}
  %ey : {L.big_val(Big.add(x, y)) == Nat.add(L.big_val(x), _) : Nat}
  add_v(x, y, ox, oy)

def mulv(+x: Big.Big, +y: Big.Big, +ox: {L.big_ok(x) == True{} : Bool}, +oy: {L.big_ok(y) == True{} : Bool}, -xv: Nat, -yv: Nat,
  ex: {L.big_val(x) == xv : Nat}, ey: {L.big_val(y) == yv : Nat}) -> {L.big_val(Big.mul(x, y)) == Nat.mul(xv, yv) : Nat}:
  %ex : {L.big_val(Big.mul(x, y)) == Nat.mul(_, yv) : Nat}
  %ey : {L.big_val(Big.mul(x, y)) == Nat.mul(L.big_val(x), _) : Nat}
  mul_v(x, y, ox, oy)

def fdc(-x1: Cmp, -x2: Cmp, -x3: Cmp, -x4: Cmp, -x5: Cmp, -x6: Cmp, -y1: Cmp, -y2: Cmp, -y3: Cmp, -y4: Cmp, -y5: Cmp, -y6: Cmp, -k1: Bool, -k2: Bool, -ev: Bool,
  e1: {x1 == y1 : Cmp}, e2: {x2 == y2 : Cmp}, e3: {x3 == y3 : Cmp}, e4: {x4 == y4 : Cmp}, e5: {x5 == y5 : Cmp}, e6: {x6 == y6 : Cmp}, ek: {k1 == k2 : Bool},
  +h: {fin(dcg(y1, y2, y3, y4, y5, y6), k2, ev) == True{} : Bool}) -> {fin(dcg(x1, x2, x3, x4, x5, x6), k1, ev) == True{} : Bool}:
  %Equal.sym(Cmp, x1, y1, e1) : {fin(dcg(_, x2, x3, x4, x5, x6), k1, ev) == True{} : Bool}
  %Equal.sym(Cmp, x2, y2, e2) : {fin(dcg(y1, _, x3, x4, x5, x6), k1, ev) == True{} : Bool}
  %Equal.sym(Cmp, x3, y3, e3) : {fin(dcg(y1, y2, _, x4, x5, x6), k1, ev) == True{} : Bool}
  %Equal.sym(Cmp, x4, y4, e4) : {fin(dcg(y1, y2, y3, _, x5, x6), k1, ev) == True{} : Bool}
  %Equal.sym(Cmp, x5, y5, e5) : {fin(dcg(y1, y2, y3, y4, _, x6), k1, ev) == True{} : Bool}
  %Equal.sym(Cmp, x6, y6, e6) : {fin(dcg(y1, y2, y3, y4, y5, _), k1, ev) == True{} : Bool}
  %Equal.sym(Bool, k1, k2, ek) : {fin(dcg(y1, y2, y3, y4, y5, y6), _, ev) == True{} : Bool}
  h

def iseq_cong(-a: Cmp, -b: Cmp, e: {a == b : Cmp}) -> {Cmp.is_eq(a) == Cmp.is_eq(b) : Bool}:
  %e : {Cmp.is_eq(a) == Cmp.is_eq(_) : Bool}
  {==}

def asm(+A: Big.Big, +C: Big.Big, +T: Big.Big, +K: Big.Big, +k: Big.Big, +u: Nat, +w: Nat, +vt: Nat, +b: Nat, +ev: Bool,
  +okA: {L.big_ok(A) == True{} : Bool}, +okC: {L.big_ok(C) == True{} : Bool}, +okT: {L.big_ok(T) == True{} : Bool},
  +eA: {L.big_val(A) == Nat.mul(u, b) : Nat}, +eC: {L.big_val(C) == Nat.mul(w, b) : Nat}, +eT: {L.big_val(T) == vt : Nat},
  +eK: {L.big_val(K) == u : Nat}, +ek: {L.big_val(k) == w : Nat}, +hN: {NS(u, w, vt, b, ev) == True{} : Bool})
  -> {fin(dcg(Big.cmp(A, T), Big.cmp(C, T), Big.cmp(C, A), Big.cmp(Big.add(T, T), Big.add(A, C)), Big.cmp(Big.add(A, C), Big.add(T, T)), Big.cmp(A, C)),
       Cmp.is_eq(Big.cmp(K, k)), ev) == True{} : Bool}:
  +ua = Nat.mul(u, b)
  +wc = Nat.mul(w, b)
  +eTT = addv(T, T, okT, okT, vt, vt, eT, eT)
  +eAC = addv(A, C, okA, okC, ua, wc, eA, eC)
  fdc(Big.cmp(A, T), Big.cmp(C, T), Big.cmp(C, A), Big.cmp(Big.add(T, T), Big.add(A, C)), Big.cmp(Big.add(A, C), Big.add(T, T)), Big.cmp(A, C),
    Nat.cmp(ua, vt), Nat.cmp(wc, vt), Nat.cmp(wc, ua), Nat.cmp(Nat.add(vt, vt), Nat.add(ua, wc)), Nat.cmp(Nat.add(ua, wc), Nat.add(vt, vt)), Nat.cmp(ua, wc),
    Cmp.is_eq(Big.cmp(K, k)), Cmp.is_eq(Nat.cmp(u, w)), ev,
    cmpv(A, T, ua, vt, eA, eT), cmpv(C, T, wc, vt, eC, eT), cmpv(C, A, wc, ua, eC, eA),
    cmpv(Big.add(T, T), Big.add(A, C), Nat.add(vt, vt), Nat.add(ua, wc), eTT, eAC),
    cmpv(Big.add(A, C), Big.add(T, T), Nat.add(ua, wc), Nat.add(vt, vt), eAC, eTT),
    cmpv(A, C, ua, wc, eA, eC),
    iseq_cong(Big.cmp(K, k), Nat.cmp(u, w), cmpv(K, k, u, w, eK, ek)), hN)

# ---------------------------------------------------------------------
# The context of fixed(d, x)
# ---------------------------------------------------------------------

def lbp_ok(n: Nat) -> {L.big_ok(L.bpow10(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      mul_ok(L.bpow10(p), L.B(10n), lbp_ok(p), of_ok(10n))

def lnum_ok(+m: Big.Big, +e: Nat, neg: Bool, +om: {L.big_ok(m) == True{} : Bool}) -> {L.big_ok(L.f_num(F64.F64{m, e, neg})) == True{} : Bool}:
  match neg:
    case True{}:
      om
    case False{}:
      lbshl_ok(e, m, om)

def lden_ok(+m: Big.Big, +e: Nat, neg: Bool) -> {L.big_ok(L.f_den(F64.F64{m, e, neg})) == True{} : Bool}:
  match neg:
    case True{}:
      lbshl_ok(e, Big.of(1n), {==})
    case False{}:
      {==}

def lnum_v(+m: Big.Big, +e: Nat, neg: Bool) -> {L.big_val(L.f_num(F64.F64{m, e, neg})) == L.big_val(F64.num(F64.F64{m, e, neg})) : Nat}:
  match neg:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Nat, L.big_val(L.bshl(e, m)), Nat.mul(L.big_val(m), Nat.pow(2n, e)), L.big_val(F64.bshl(e, m)), vlaw(e, m),
        Equal.sym(Nat, L.big_val(F64.bshl(e, m)), Nat.mul(L.big_val(m), Nat.pow(2n, e)), vfast(e, m)))

def lden_v(+m: Big.Big, +e: Nat, neg: Bool) -> {L.big_val(L.f_den(F64.F64{m, e, neg})) == L.big_val(F64.den(F64.F64{m, e, neg})) : Nat}:
  match neg:
    case True{}:
      Equal.trans(Nat, L.big_val(L.bshl(e, Big.of(1n))), Nat.mul(1n, Nat.pow(2n, e)), L.big_val(F64.bshl(e, Big.of(1n))), vlaw(e, Big.of(1n)),
        Equal.sym(Nat, L.big_val(F64.bshl(e, Big.of(1n))), Nat.mul(1n, Nat.pow(2n, e)), vfast(e, Big.of(1n))))
    case False{}:
      {==}

def val_cong(-a: Big.Big, -b: Big.Big, e: {a == b : Big.Big}) -> {L.big_val(a) == L.big_val(b) : Nat}:
  %e : {L.big_val(a) == L.big_val(_) : Nat}
  {==}

def xf(+m: Big.Big, +e: Nat, +neg: Bool) -> F64.F64:
  F64.F64{m, e, neg}

def pP(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat) -> Big.Big:
  Big.mul(F64.num(xf(m, e, neg)), F64.bpow10(d))

def pD(+m: Big.Big, +e: Nat, +neg: Bool) -> Big.Big:
  F64.den(xf(m, e, neg))

def pT(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat) -> Big.Big:
  Big.mul(L.f_num(xf(m, e, neg)), L.bpow10(d))

def pK0(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat) -> Big.Big:
  Big.div(pP(m, e, neg, d), pD(m, e, neg))

def pR(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat) -> Big.Big:
  Big.mod(pP(m, e, neg, d), pD(m, e, neg))

def pP_ok(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +om: {L.big_ok(m) == True{} : Bool}) -> {L.big_ok(pP(m, e, neg, d)) == True{} : Bool}:
  mul_ok(F64.num(xf(m, e, neg)), F64.bpow10(d), num_ok(m, e, neg, om), bp_ok(d))

def pT_ok(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +om: {L.big_ok(m) == True{} : Bool}) -> {L.big_ok(pT(m, e, neg, d)) == True{} : Bool}:
  mul_ok(L.f_num(xf(m, e, neg)), L.bpow10(d), lnum_ok(m, e, neg, om), lbp_ok(d))

# the exact t = num 10^d, as q0 B + r
def pT_v(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +om: {L.big_ok(m) == True{} : Bool})
  -> {L.big_val(pT(m, e, neg, d)) == Nat.add(Nat.mul(L.big_val(pK0(m, e, neg, d)), L.big_val(pD(m, e, neg))), L.big_val(pR(m, e, neg, d))) : Nat}:
  +x = xf(m, e, neg)
  +p = pP(m, e, neg, d)
  +dd = pD(m, e, neg)
  +vp = Nat.mul(L.big_val(F64.num(x)), L.big_val(F64.bpow10(d)))
  Equal.trans(Nat, L.big_val(pT(m, e, neg, d)), vp, Nat.add(Nat.mul(L.big_val(pK0(m, e, neg, d)), L.big_val(dd)), L.big_val(pR(m, e, neg, d))),
    mulv(L.f_num(x), L.bpow10(d), lnum_ok(m, e, neg, om), lbp_ok(d), L.big_val(F64.num(x)), L.big_val(F64.bpow10(d)), lnum_v(m, e, neg),
      Equal.sym(Nat, L.big_val(F64.bpow10(d)), L.big_val(L.bpow10(d)), val_cong(F64.bpow10(d), L.bpow10(d), bp_same(d)))),
    Equal.trans(Nat, vp, L.big_val(p), Nat.add(Nat.mul(L.big_val(pK0(m, e, neg, d)), L.big_val(dd)), L.big_val(pR(m, e, neg, d))),
      Equal.sym(Nat, L.big_val(p), vp, mul_v(F64.num(x), F64.bpow10(d), num_ok(m, e, neg, om), bp_ok(d))),
      Equal.sym(Nat, Nat.add(Nat.mul(L.big_val(pK0(m, e, neg, d)), L.big_val(dd)), L.big_val(pR(m, e, neg, d))), L.big_val(p),
        dm_eq(p, dd, pP_ok(m, e, neg, d, om), den_ok(m, e, neg), den_pos(m, e, neg)))))

# ---------------------------------------------------------------------
# fixed_nearest
# ---------------------------------------------------------------------

def G(+kk: Big.Big, +k: Big.Big, +m: Big.Big, +e: Nat, +neg: Bool, +d: Nat) -> Bool:
  +dl = L.f_den(xf(m, e, neg))
  +a = Big.mul(kk, dl)
  +c = Big.mul(k, dl)
  +t = pT(m, e, neg, d)
  fin(dcg(Big.cmp(a, t), Big.cmp(c, t), Big.cmp(c, a), Big.cmp(Big.add(t, t), Big.add(a, c)), Big.cmp(Big.add(a, c), Big.add(t, t)), Big.cmp(a, c)),
    Cmp.is_eq(Big.cmp(kk, k)), L.b_zero(Big.mod(kk, L.B(2n))))

def k0_ok(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +om: {L.big_ok(m) == True{} : Bool}) -> {L.big_ok(pK0(m, e, neg, d)) == True{} : Bool}:
  div_ok(pP(m, e, neg, d), pD(m, e, neg), pP_ok(m, e, neg, d, om), den_ok(m, e, neg), den_pos(m, e, neg))

def r_ok(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +om: {L.big_ok(m) == True{} : Bool}) -> {L.big_ok(pR(m, e, neg, d)) == True{} : Bool}:
  mod_ok(pP(m, e, neg, d), pD(m, e, neg), pP_ok(m, e, neg, d, om), den_ok(m, e, neg), den_pos(m, e, neg))

def r_lt(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +om: {L.big_ok(m) == True{} : Bool})
  -> {Nat.is_lt(L.big_val(pR(m, e, neg, d)), L.big_val(pD(m, e, neg))) == True{} : Bool}:
  dm_lt(pP(m, e, neg, d), pD(m, e, neg), pP_ok(m, e, neg, d, om), den_ok(m, e, neg), den_pos(m, e, neg))

def fnA(t: Bool, +m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +k: Big.Big, +om: {L.big_ok(m) == True{} : Bool}, +hk: {L.big_ok(k) == True{} : Bool},
  ht: TieA(t, L.big_val(pR(m, e, neg, d)), L.big_val(pD(m, e, neg)), L.b_zero(Big.mod(pK0(m, e, neg, d), L.B(2n)))))
  -> {G(pK0(m, e, neg, d), k, m, e, neg, d) == True{} : Bool}:
  +kk = pK0(m, e, neg, d)
  +okK = k0_ok(m, e, neg, d, om)
  +dl = L.f_den(xf(m, e, neg))
  +okD = lden_ok(m, e, neg)
  +b = L.big_val(pD(m, e, neg))
  +q0 = L.big_val(kk)
  +w = L.big_val(k)
  +r = L.big_val(pR(m, e, neg, d))
  +ev = L.b_zero(Big.mod(kk, L.B(2n)))
  +eD = lden_v(m, e, neg)
  asm(Big.mul(kk, dl), Big.mul(k, dl), pT(m, e, neg, d), kk, k, q0, w, Nat.add(Nat.mul(q0, b), r), b, ev,
    mul_ok(kk, dl, okK, okD), mul_ok(k, dl, hk, okD), pT_ok(m, e, neg, d, om),
    mulv(kk, dl, okK, okD, q0, b, {==}, eD), mulv(k, dl, hk, okD, w, b, {==}, eD), pT_v(m, e, neg, d, om), {==}, {==},
    cA(t, q0, w, r, b, ev, r_lt(m, e, neg, d, om), den_pos(m, e, neg), ht))

def fnB(t: Bool, +m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +k: Big.Big, +om: {L.big_ok(m) == True{} : Bool}, +hk: {L.big_ok(k) == True{} : Bool},
  ht: TieB(t, L.big_val(pR(m, e, neg, d)), L.big_val(pD(m, e, neg)), L.b_zero(Big.mod(Big.add(pK0(m, e, neg, d), F64.big1()), L.B(2n)))))
  -> {G(Big.add(pK0(m, e, neg, d), F64.big1()), k, m, e, neg, d) == True{} : Bool}:
  +k0 = pK0(m, e, neg, d)
  +ok0 = k0_ok(m, e, neg, d, om)
  +kk = Big.add(k0, F64.big1())
  +okK = add_ok(k0, F64.big1(), ok0, {==})
  +dl = L.f_den(xf(m, e, neg))
  +okD = lden_ok(m, e, neg)
  +b = L.big_val(pD(m, e, neg))
  +q0 = L.big_val(k0)
  +w = L.big_val(k)
  +r = L.big_val(pR(m, e, neg, d))
  +ev = L.b_zero(Big.mod(kk, L.B(2n)))
  +eD = lden_v(m, e, neg)
  +eK = Equal.trans(Nat, L.big_val(kk), Nat.add(q0, 1n), 1n+q0, add_v(k0, F64.big1(), ok0, {==}), PNat.add_comm(q0, 1n))
  asm(Big.mul(kk, dl), Big.mul(k, dl), pT(m, e, neg, d), kk, k, 1n+q0, w, Nat.add(Nat.mul(q0, b), r), b, ev,
    mul_ok(kk, dl, okK, okD), mul_ok(k, dl, hk, okD), pT_ok(m, e, neg, d, om),
    mulv(kk, dl, okK, okD, 1n+q0, b, eK, eD), mulv(k, dl, hk, okD, w, b, {==}, eD), pT_v(m, e, neg, d, om), eK, {==},
    cB(t, q0, w, r, b, ev, r_lt(m, e, neg, d, om), den_pos(m, e, neg), ht))

def notF(a: Bool, +h: {Bool.not(a) == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))

def one_of(s: Nat, +h1: {Cmp.is_eq(Nat.cmp(s, 0n)) == False{} : Bool}, +h2: {Nat.is_lt(s, 2n) == True{} : Bool}) -> {s == 1n : Nat}:
  match s:
    case 0n:
      Empty.absurd({0n == 1n : Nat}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h1)))
    case 1n+z:
      match z:
        case 0n:
          {==}
        case 1n++y:
          Empty.absurd({2n+y == 1n : Nat}, PBig.lt_le_absurd(2n+y, 2n, h2, PBig.le_add(2n, y)))

def m11(+mm: Nat) -> {Nat.add(Nat.add(mm, 1n), 1n) == 2n+mm : Nat}:
  %Equal.sym(Nat, Nat.add(mm, 1n), 1n+mm, PNat.add_comm(mm, 1n)) : {Nat.add(_, 1n) == 2n+mm : Nat}
  %Equal.sym(Nat, Nat.add(mm, 1n), 1n+mm, PNat.add_comm(mm, 1n)) : {1n+_ == 2n+mm : Nat}
  {==}

# k0 odd: k0 + 1 even
def par(+k0: Big.Big, +ok0: {L.big_ok(k0) == True{} : Bool}, +h: {Cmp.is_eq(Big.cmp(Big.mod(k0, Big.of(2n)), Big.of(0n))) == False{} : Bool})
  -> {Cmp.is_eq(Big.cmp(Big.mod(Big.add(k0, F64.big1()), Big.of(2n)), Big.of(0n))) == True{} : Bool}:
  +two = Big.of(2n)
  +k1 = Big.add(k0, F64.big1())
  +ok1 = add_ok(k0, F64.big1(), ok0, {==})
  +a = L.big_val(Big.div(k0, two))
  +s = L.big_val(Big.mod(k0, two))
  +a1 = L.big_val(Big.div(k1, two))
  +s1 = L.big_val(Big.mod(k1, two))
  +v1 = L.big_val(k1)
  +mm = Nat.mul(a, 2n)
  +hs = one_of(s, Equal.trans(Bool, Cmp.is_eq(Nat.cmp(s, 0n)), Cmp.is_eq(Big.cmp(Big.mod(k0, two), Big.of(0n))), False{},
    iseq_cong(Nat.cmp(s, 0n), Big.cmp(Big.mod(k0, two), Big.of(0n)), Equal.sym(Cmp, Big.cmp(Big.mod(k0, two), Big.of(0n)), Nat.cmp(s, 0n), cmpv(Big.mod(k0, two), Big.of(0n), s, 0n, {==}, {==}))), h),
    dm_lt(k0, two, ok0, {==}, {==}))
  +e0 = dm_eq(k0, two, ok0, {==}, {==})
  +tg = Nat.add(Nat.mul(1n+a, 2n), 0n)
  +ev1 = {%Equal.sym(Nat, v1, Nat.add(L.big_val(k0), L.big_val(F64.big1())), add_v(k0, F64.big1(), ok0, {==})) : {_ == tg : Nat};
          %e0 : {Nat.add(_, 1n) == tg : Nat};
          %Equal.sym(Nat, s, 1n, hs) : {Nat.add(Nat.add(mm, _), 1n) == tg : Nat};
          %Equal.sym(Nat, Nat.add(Nat.add(mm, 1n), 1n), 2n+mm, m11(mm)) : {_ == tg : Nat};
          %PNat.add_zero(mm) : {2n+mm == 2n+_ : Nat};
          {==} : {v1 == tg : Nat}}
  +E = Equal.sym(Nat, v1, tg, ev1)
  +e1 = dm_eq(k1, two, ok1, {==}, {==})
  +qa = Equal.trans(Nat, a1, Nat.div(v1, 2n), 1n+a, eu(v1, 2n, a1, s1, e1, dm_lt(k1, two, ok1, {==}, {==})), Equal.sym(Nat, 1n+a, Nat.div(v1, 2n), eu(v1, 2n, 1n+a, 0n, E, {==})))
  +e2 = {%qa : {Nat.add(Nat.mul(_, 2n), s1) == tg : Nat};
         Equal.trans(Nat, Nat.add(Nat.mul(a1, 2n), s1), v1, tg, e1, ev1) : {Nat.add(Nat.mul(1n+a, 2n), s1) == tg : Nat}}
  +z = add_cancel_l(Nat.mul(1n+a, 2n), s1, 0n, e2)
  %Equal.sym(Cmp, Big.cmp(Big.mod(k1, two), Big.of(0n)), Nat.cmp(s1, 0n), cmpv(Big.mod(k1, two), Big.of(0n), s1, 0n, {==}, {==})) : {Cmp.is_eq(_) == True{} : Bool}
  %Equal.sym(Nat, s1, 0n, z) : {Cmp.is_eq(Nat.cmp(_, 0n)) == True{} : Bool}
  {==}

def hnc(+m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +om: {L.big_ok(m) == True{} : Bool})
  -> {Nat.cmp(Nat.add(L.big_val(pR(m, e, neg, d)), L.big_val(pR(m, e, neg, d))), L.big_val(pD(m, e, neg))) == Big.cmp(Big.add(pR(m, e, neg, d), pR(m, e, neg, d)), pD(m, e, neg)) : Cmp}:
  +rr = pR(m, e, neg, d)
  +ok = r_ok(m, e, neg, d, om)
  +r = L.big_val(rr)
  Equal.sym(Cmp, Big.cmp(Big.add(rr, rr), pD(m, e, neg)), Nat.cmp(Nat.add(r, r), L.big_val(pD(m, e, neg))),
    cmpv(Big.add(rr, rr), pD(m, e, neg), Nat.add(r, r), L.big_val(pD(m, e, neg)), addv(rr, rr, ok, ok, r, r, {==}, {==}), {==}))

def near.eq(od: Bool, +m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +k: Big.Big, +om: {L.big_ok(m) == True{} : Bool}, +hk: {L.big_ok(k) == True{} : Bool},
  +hn: {Nat.cmp(Nat.add(L.big_val(pR(m, e, neg, d)), L.big_val(pR(m, e, neg, d))), L.big_val(pD(m, e, neg))) == EQ{} : Cmp}, +hod: {F64.odd(pK0(m, e, neg, d)) == od : Bool})
  -> {G(F64.pick(Big.Big, od, Big.add(pK0(m, e, neg, d), F64.big1()), pK0(m, e, neg, d)), k, m, e, neg, d) == True{} : Bool}:
  match od:
    case True{}:
      +r = L.big_val(pR(m, e, neg, d))
      +k0 = pK0(m, e, neg, d)
      +z = Cmp.is_eq(Big.cmp(Big.mod(k0, Big.of(2n)), Big.of(0n)))
      fnB(True{}, m, e, neg, d, k, om, hk, (PBig.cmp_eq(Nat.add(r, r), L.big_val(pD(m, e, neg)), hn), par(k0, k0_ok(m, e, neg, d, om), notT(z, hod))))
    case False{}:
      +r = L.big_val(pR(m, e, neg, d))
      +k0 = pK0(m, e, neg, d)
      +z = Cmp.is_eq(Big.cmp(Big.mod(k0, Big.of(2n)), Big.of(0n)))
      fnA(True{}, m, e, neg, d, k, om, hk, (PBig.cmp_eq(Nat.add(r, r), L.big_val(pD(m, e, neg)), hn), notF(z, hod)))

def near.of(cc: Cmp, od: Bool, +m: Big.Big, +e: Nat, +neg: Bool, +d: Nat, +k: Big.Big, +om: {L.big_ok(m) == True{} : Bool}, +hk: {L.big_ok(k) == True{} : Bool},
  +hcc: {Big.cmp(Big.add(pR(m, e, neg, d), pR(m, e, neg, d)), pD(m, e, neg)) == cc : Cmp}, +hod: {F64.odd(pK0(m, e, neg, d)) == od : Bool})
  -> {G(F64.pick(Big.Big, Bool.or(Cmp.is_gt(cc), Bool.and(Cmp.is_eq(cc), od)), Big.add(pK0(m, e, neg, d), F64.big1()), pK0(m, e, neg, d)), k, m, e, neg, d) == True{} : Bool}:
  match cc:
    case LT{}:
      +r = L.big_val(pR(m, e, neg, d))
      +b = L.big_val(pD(m, e, neg))
      fnA(False{}, m, e, neg, d, k, om, hk, lt_of_cmp_lt(Nat.add(r, r), b, Equal.trans(Cmp, Nat.cmp(Nat.add(r, r), b), Big.cmp(Big.add(pR(m, e, neg, d), pR(m, e, neg, d)), pD(m, e, neg)), LT{}, hnc(m, e, neg, d, om), hcc)))
    case GT{}:
      +r = L.big_val(pR(m, e, neg, d))
      +b = L.big_val(pD(m, e, neg))
      fnB(False{}, m, e, neg, d, k, om, hk, lt_of_gt(Nat.add(r, r), b, gt_of_cmp_gt(Nat.add(r, r), b, Equal.trans(Cmp, Nat.cmp(Nat.add(r, r), b), Big.cmp(Big.add(pR(m, e, neg, d), pR(m, e, neg, d)), pD(m, e, neg)), GT{}, hnc(m, e, neg, d, om), hcc))))
    case EQ{}:
      near.eq(od, m, e, neg, d, k, om, hk, Equal.trans(Cmp, Nat.cmp(Nat.add(L.big_val(pR(m, e, neg, d)), L.big_val(pR(m, e, neg, d))), L.big_val(pD(m, e, neg))),
        Big.cmp(Big.add(pR(m, e, neg, d), pR(m, e, neg, d)), pD(m, e, neg)), EQ{}, hnc(m, e, neg, d, om), hcc), hod)

def L.f64_fixed_nearest(d, x, k, h0, h1):
  match x:
    case F64.F64{+m, +e, +neg}:
      +om = okm(m, e, neg, h0)
      +kk = F64.round_int(pP(m, e, neg, d), pD(m, e, neg))
      %Equal.sym(Big.Big, L.fixed_k(F64.fixed_text(d, kk)), kk, fk(d, kk, fixed_k_ok(d, m, e, neg, om))) : {L.fixed_nearest(d, F64.F64{m, e, neg}, _, k) == True{} : Bool}
      near.of(Big.cmp(Big.add(pR(m, e, neg, d), pR(m, e, neg, d)), pD(m, e, neg)), F64.odd(pK0(m, e, neg, d)), m, e, neg, d, k, om, h1, {==}, {==})

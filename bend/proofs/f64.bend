# Proofs of the double laws (f64_*).
import Base
import ../LAWS.bend as L
import ../lib/big.bend as Big
import ../lib/f64.bend as F64
import ./nat.bend as PNat
import ./big.bend as PBig

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

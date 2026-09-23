# Proofs of the metrics, table and report laws (met_*, tab_render, report_*).
import Base
import ../LAWS.bend as L
import ../lib/big.bend as Big
import ../lib/f64.bend as F64
import ../lib/civil.bend as Civil
import ../lib/hit.bend as Hit
import ../lib/json.bend as Json
import ../lib/dec.bend as Dec
import ../lib/report.bend as Rep
import ../lib/metrics.bend as Met
import ../lib/tab.bend as Tab
import ./nat.bend as PNat
import ./big.bend as PBig
import ./codec.bend as PCodec

def L.met_empty(bs):
  {==}

# =====================================================================
# The accumulator, field by field
# =====================================================================

def a_bs(+a: Met.Acc) -> List<&2, Nat>:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  bs

def a_n(+a: Met.Acc) -> Nat:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  n

def a_ok(+a: Met.Acc) -> Nat:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  ok

def a_cs(+a: Met.Acc) -> List<&2, Sigma<&2, &2, Nat, _ => Nat>>:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  cs

def a_es(+a: Met.Acc) -> List<&2, String>:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  es

def a_lat(+a: Met.Acc) -> Big.Big:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  l

def a_bin(+a: Met.Acc) -> Big.Big:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  i

def a_bout(+a: Met.Acc) -> Big.Big:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  o

def a_x(+a: Met.Acc) -> Met.Ext:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  x

def a_t(+a: Met.Acc) -> Met.Lats:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  t

def is_ext(x: Met.Ext) -> Bool:
  match x:
    case Met.NoExt{}:
      False{}
    case Met.Ext{a, b, c, d, e, f, g, h}:
      True{}

def no_ft(e: {False{} == True{} : Bool}) -> Empty:
  PNat.false_ne_true(e)

def pick_ml(-A: Data, c: Bool, -a: A, -b: A) -> {Met.pick(A, c, a, b) == L.pick(A, c, a, b) : A}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# ---------------------------------------------------------------------
# merge and of_hit on each field (lemmas read {new == old}: a rewrite
# replaces the old form in the goal by the new)
# ---------------------------------------------------------------------

def m_bs(a: Met.Acc, b: Met.Acc) -> {a_bs(a) == a_bs(Met.merge(a, b)) : List<&2, Nat>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_n(a: Met.Acc, b: Met.Acc) -> {Nat.add(a_n(a), a_n(b)) == a_n(Met.merge(a, b)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_ok(a: Met.Acc, b: Met.Acc) -> {Nat.add(a_ok(a), a_ok(b)) == a_ok(Met.merge(a, b)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_cs(a: Met.Acc, b: Met.Acc) -> {Met.codes_merge(a_cs(a), a_cs(b)) == a_cs(Met.merge(a, b)) : List<&2, Sigma<&2, &2, Nat, _ => Nat>>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_es(a: Met.Acc, b: Met.Acc) -> {Met.strs_merge(a_es(a), a_es(b)) == a_es(Met.merge(a, b)) : List<&2, String>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_lat(a: Met.Acc, b: Met.Acc) -> {Big.add(a_lat(a), a_lat(b)) == a_lat(Met.merge(a, b)) : Big.Big}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_bin(a: Met.Acc, b: Met.Acc) -> {Big.add(a_bin(a), a_bin(b)) == a_bin(Met.merge(a, b)) : Big.Big}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_bout(a: Met.Acc, b: Met.Acc) -> {Big.add(a_bout(a), a_bout(b)) == a_bout(Met.merge(a, b)) : Big.Big}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_x(a: Met.Acc, b: Met.Acc) -> {Met.ext_merge(a_x(a), a_x(b)) == a_x(Met.merge(a, b)) : Met.Ext}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def m_t(a: Met.Acc, b: Met.Acc) -> {Met.lcat(a_t(a), a_t(b)) == a_t(Met.merge(a, b)) : Met.Lats}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def oh_n(h: Hit.Hit) -> {1n == a_n(Met.of_hit(h)) : Nat}:
  match h:
    case Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          {==}

def oh_ok(h: Hit.Hit) -> {L.pick(Nat, L.is_ok(L.h_code(h)), 1n, 0n) == a_ok(Met.of_hit(h)) : Nat}:
  match h:
    case Hit.Hit{a, q, +c, t, l, bo, bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          Equal.sym(Nat, Met.pick(Nat, L.is_ok(c), 1n, 0n), L.pick(Nat, L.is_ok(c), 1n, 0n), pick_ml(Nat, L.is_ok(c), 1n, 0n))

def oh_x(h: Hit.Hit) -> {is_ext(a_x(Met.of_hit(h))) == True{} : Bool}:
  match h:
    case Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          {==}

# merging keeps the extremes present
def x_merge_l(a: Met.Ext, b: Met.Ext, h: {is_ext(a) == True{} : Bool}) -> {is_ext(Met.ext_merge(a, b)) == True{} : Bool}:
  match a:
    case Met.NoExt{}:
      Empty.absurd({is_ext(Met.ext_merge(Met.NoExt{}, b)) == True{} : Bool}, no_ft(h))
    case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
      match b:
        case Met.NoExt{}:
          {==}
        case Met.Ext{a2, b2, es2, en2, ls2, ln2, xs2, xn2}:
          {==}

def x_merge_r(a: Met.Ext, b: Met.Ext, h: {is_ext(b) == True{} : Bool}) -> {is_ext(Met.ext_merge(a, b)) == True{} : Bool}:
  match a:
    case Met.NoExt{}:
      h
    case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
      match b:
        case Met.NoExt{}:
          {==}
        case Met.Ext{a2, b2, es2, en2, ls2, ln2, xs2, xn2}:
          {==}

def add_x(+a: Met.Acc, +h: Hit.Hit) -> {is_ext(a_x(Met.add(a, h))) == True{} : Bool}:
  %m_x(a, Met.of_hit(h)) : {is_ext(_) == True{} : Bool}
  x_merge_r(a_x(a), a_x(Met.of_hit(h)), oh_x(h))

# ---------------------------------------------------------------------
# Folds: acc_all adds the results one by one
# ---------------------------------------------------------------------

def f_bs(hs: List<&2, Hit.Hit>, +a: Met.Acc) -> {a_bs(a) == a_bs(L.acc_all(hs, a)) : List<&2, Nat>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %f_bs(rest, Met.add(a, h)) : {a_bs(a) == _ : List<&2, Nat>}
      m_bs(a, Met.of_hit(h))

def f_n(hs: List<&2, Hit.Hit>, +a: Met.Acc) -> {Nat.add(a_n(a), List.length(&2, Hit.Hit, hs)) == a_n(L.acc_all(hs, a)) : Nat}:
  match hs:
    case Nil{}:
      Equal.sym(Nat, a_n(a), Nat.add(a_n(a), 0n), PNat.add_zero(a_n(a)))
    case Con{+h, +rest}:
      +len = List.length(&2, Hit.Hit, rest)
      %f_n(rest, Met.add(a, h)) : {Nat.add(a_n(a), 1n+len) == _ : Nat}
      %m_n(a, Met.of_hit(h)) : {Nat.add(a_n(a), 1n+len) == Nat.add(_, len) : Nat}
      %oh_n(h) : {Nat.add(a_n(a), 1n+len) == Nat.add(Nat.add(a_n(a), _), len) : Nat}
      PNat.add_assoc(a_n(a), 1n, len)

def f_ok(hs: List<&2, Hit.Hit>, +a: Met.Acc) -> {Nat.add(a_ok(a), L.n_ok(hs)) == a_ok(L.acc_all(hs, a)) : Nat}:
  match hs:
    case Nil{}:
      Equal.sym(Nat, a_ok(a), Nat.add(a_ok(a), 0n), PNat.add_zero(a_ok(a)))
    case Con{+h, +rest}:
      +p = L.pick(Nat, L.is_ok(L.h_code(h)), 1n, 0n)
      %f_ok(rest, Met.add(a, h)) : {Nat.add(a_ok(a), Nat.add(p, L.n_ok(rest))) == _ : Nat}
      %m_ok(a, Met.of_hit(h)) : {Nat.add(a_ok(a), Nat.add(p, L.n_ok(rest))) == Nat.add(_, L.n_ok(rest)) : Nat}
      %oh_ok(h) : {Nat.add(a_ok(a), Nat.add(p, L.n_ok(rest))) == Nat.add(Nat.add(a_ok(a), _), L.n_ok(rest)) : Nat}
      PNat.add_assoc(a_ok(a), p, L.n_ok(rest))

def f_x(hs: List<&2, Hit.Hit>, +a: Met.Acc, +hx: {is_ext(a_x(a)) == True{} : Bool}) -> {is_ext(a_x(L.acc_all(hs, a))) == True{} : Bool}:
  match hs:
    case Nil{}:
      hx
    case Con{+h, +rest}:
      f_x(rest, Met.add(a, h), add_x(a, h))

# the results of a non-empty list leave extremes
def sum_x(+bs: List<&2, Nat>, +h: Hit.Hit, +hs: List<&2, Hit.Hit>) -> {is_ext(a_x(L.acc_all(Con{h, hs}, Met.empty(bs)))) == True{} : Bool}:
  f_x(hs, Met.add(Met.empty(bs), h), add_x(Met.empty(bs), h))

# ---------------------------------------------------------------------
# Closing an accumulator with extremes
# ---------------------------------------------------------------------

def c_req(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {a_n(a) == L.s_requests(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({n == 0n : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def c_ok(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {a_ok(a) == L.s_success(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({ok == 0n : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

# =====================================================================
# Nat order
# =====================================================================

def cmp_lt_gt(c: Cmp, h1: {Cmp.is_lt(c) == True{} : Bool}, h2: {Cmp.is_gt(c) == True{} : Bool}) -> Empty:
  match c:
    case LT{}:
      no_ft(h2)
    case EQ{}:
      no_ft(h1)
    case GT{}:
      no_ft(h1)

def n_lt_gt(a: Nat, b: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_gt(a, b) == True{} : Bool}) -> Empty:
  cmp_lt_gt(Nat.cmp(a, b), h1, h2)

def succ_eq(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def n_eq_of(a: Nat, b: Nat, h1: {Nat.is_lt(a, b) == False{} : Bool}, h2: {Nat.is_gt(a, b) == False{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          Empty.absurd({0n == 1n+bp : Nat}, no_ft(Equal.sym(Bool, True{}, False{}, h1)))
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({1n+ap == 0n : Nat}, no_ft(Equal.sym(Bool, True{}, False{}, h2)))
        case 1n+bp:
          succ_eq(ap, bp, n_eq_of(ap, bp, h1, h2))

def n_eq_is(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          Empty.absurd({0n == 1n+bp : Nat}, no_ft(h))
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({1n+ap == 0n : Nat}, no_ft(h))
        case 1n+bp:
          succ_eq(ap, bp, n_eq_is(ap, bp, h))

# a < b: b is not a
def n_lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, no_ft(h))
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          n_lt_ne(ap, bp, h)

def n_le_lt(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a:
    case 0n:
      match c:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PNat.lt_zero(b, h2))
        case 1n+cp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool}, no_ft(h1))
        case 1n+bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, no_ft(h2))
            case 1n+cp:
              n_le_lt(ap, bp, cp, h1, h2)

def n_lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          n_lt_le(ap, bp, h)

def and_l(p: Bool, -q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {p == True{} : Bool}:
  match p:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case True{}:
      {==}

def and_r(p: Bool, -q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case False{}:
      Empty.absurd({q == True{} : Bool}, no_ft(h))
    case True{}:
      h

def and_i(-p: Bool, -q: Bool, hp: {p == True{} : Bool}, hq: {q == True{} : Bool}) -> {Bool.and(p, q) == True{} : Bool}:
  %Equal.sym(Bool, p, True{}, hp) : {Bool.and(_, q) == True{} : Bool}
  hq

def gt_lt(a: Nat, b: Nat, h: {Nat.is_gt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, no_ft(h))
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          gt_lt(ap, bp, h)

def lt_gt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_gt(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_gt(0n, 0n) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_gt(0n, 1n+ap) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          lt_gt(ap, bp, h)

def gt_add(a: Nat, -b: Nat, h: {Nat.is_gt(a, 0n) == True{} : Bool}) -> {Nat.is_gt(Nat.add(a, b), 0n) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_gt(b, 0n) == True{} : Bool}, no_ft(h))
    case 1n+ap:
      {==}

# =====================================================================
# Status codes: an ascending code -> count list
# =====================================================================

def CP() -> Data:
  Sigma<&2, &2, Nat, _ => Nat>

# a list with all codes above k is ascending
def after_asc(cs: List<&2, CP()>, +k: Nat, +h: {L.codes_after(cs, k) == True{} : Bool}) -> {L.codes_ascending(cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{p, +rest}:
      match p:
        case (+j, +v):
          +a = Bool.and(Nat.is_lt(k, j), Nat.is_gt(v, 0n))
          and_i(Nat.is_gt(v, 0n), L.codes_after(rest, j),
            and_r(Nat.is_lt(k, j), Nat.is_gt(v, 0n), and_l(a, L.codes_after(rest, j), h)),
            and_r(a, L.codes_after(rest, j), h))

# codes all above k hold nothing for c <= k
def lk_zero(ys: List<&2, CP()>, +k: Nat, +c: Nat, +ha: {L.codes_after(ys, k) == True{} : Bool}, hc: {Nat.is_le(c, k) == True{} : Bool})
  -> {0n == L.lookup_code(c, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{p, +rest}:
      match p:
        case (+j, +v):
          +a = Bool.and(Nat.is_lt(k, j), Nat.is_gt(v, 0n))
          +cj = n_le_lt(c, k, j, hc, and_l(Nat.is_lt(k, j), Nat.is_gt(v, 0n), and_l(a, L.codes_after(rest, j), ha)))
          %Equal.sym(Bool, Nat.is_eq(j, c), False{}, n_lt_ne(c, j, cj)) : {0n == L.pick(Nat, _, v, L.lookup_code(c, rest)) : Nat}
          lk_zero(rest, j, c, and_r(a, L.codes_after(rest, j), ha), n_lt_le(c, j, cj))

# c below the first code of an ascending list: nothing
def lk_below(+c: Nat, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +hlt: {Nat.is_lt(c, k2) == True{} : Bool},
  ha: {L.codes_after(yr, k2) == True{} : Bool}) -> {0n == L.lookup_code(c, Con{{(k2, v2) : CP()}, yr}) : Nat}:
  %Equal.sym(Bool, Nat.is_eq(k2, c), False{}, n_lt_ne(c, k2, hlt)) : {0n == L.pick(Nat, _, v2, L.lookup_code(c, yr)) : Nat}
  lk_zero(yr, k2, c, ha, n_lt_le(c, k2, hlt))

# fuel bookkeeping for the merges: |xr| + |yr| + 2 + k consumed one step
def fuel_gt(+xr: Nat, +yr: Nat, +k: Nat, -g: Nat, +hg: {Nat.add(Nat.add(xr, 1n+yr), k) == g : Nat})
  -> {Nat.add(Nat.add(1n+xr, yr), k) == g : Nat}:
  %Equal.sym(Nat, 1n+Nat.add(xr, yr), Nat.add(xr, 1n+yr), PNat.add_succ(xr, yr)) : {Nat.add(_, k) == g : Nat}
  hg

def fuel_eq(+xr: Nat, +yr: Nat, +k: Nat, -g: Nat, +hg: {Nat.add(Nat.add(xr, 1n+yr), k) == g : Nat})
  -> {Nat.add(Nat.add(xr, yr), 1n+k) == g : Nat}:
  %PNat.add_succ(Nat.add(xr, yr), k) : {_ == g : Nat}
  fuel_gt(xr, yr, k, g, hg)

def asc_tail(+k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool})
  -> {L.codes_after(xr, k1) == True{} : Bool}:
  and_r(Nat.is_gt(v1, 0n), L.codes_after(xr, k1), ax)

def asc_pos(+k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool})
  -> {Nat.is_gt(v1, 0n) == True{} : Bool}:
  and_l(Nat.is_gt(v1, 0n), L.codes_after(xr, k1), ax)

def asc_rest(+k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool})
  -> {L.codes_ascending(xr) == True{} : Bool}:
  after_asc(xr, k1, asc_tail(k1, v1, xr, ax))

# an ascending list headed by k2 is all above k1 < k2
def asc_above(+k1: Nat, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +hlt: {Nat.is_lt(k1, k2) == True{} : Bool},
  +ay: {L.codes_ascending(Con{{(k2, v2) : CP()}, yr}) == True{} : Bool})
  -> {L.codes_after(Con{{(k2, v2) : CP()}, yr}, k1) == True{} : Bool}:
  and_i(Bool.and(Nat.is_lt(k1, k2), Nat.is_gt(v2, 0n)), L.codes_after(yr, k2),
    and_i(Nat.is_lt(k1, k2), Nat.is_gt(v2, 0n), hlt, asc_pos(k2, v2, yr, ay)),
    asc_tail(k2, v2, yr, ay))

# ---------------------------------------------------------------------
# lookup of a merge: the counts add
# ---------------------------------------------------------------------

def lk_lt(e: Bool, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +g: Nat, +c: Nat, +k: Nat,
  +ee: {Nat.is_eq(k1, c) == e : Bool}, +elt: {Nat.is_lt(k1, k2) == True{} : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k) == g : Nat},
  +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool},
  +ay: {L.codes_ascending(Con{{(k2, v2) : CP()}, yr}) == True{} : Bool},
  ih: @xs2: List<&2, CP()> -> @ys2: List<&2, CP()> -> @k3: Nat
    -> {Nat.add(Nat.add(List.length(&2, CP(), xs2), List.length(&2, CP(), ys2)), k3) == g : Nat}
    -> {L.codes_ascending(xs2) == True{} : Bool} -> {L.codes_ascending(ys2) == True{} : Bool}
    -> {Nat.add(L.lookup_code(c, xs2), L.lookup_code(c, ys2)) == L.lookup_code(c, Met.codes_merge.go(g, xs2, ys2)) : Nat})
  -> {Nat.add(L.pick(Nat, e, v1, L.lookup_code(c, xr)), L.lookup_code(c, Con{{(k2, v2) : CP()}, yr}))
      == L.pick(Nat, e, v1, L.lookup_code(c, Met.codes_merge.go(g, xr, Con{{(k2, v2) : CP()}, yr}))) : Nat}:
  match e:
    case True{}:
      +kc = n_eq_is(k1, c, ee)
      +hc = {%kc : {Nat.is_lt(_, k2) == True{} : Bool}; elt : {Nat.is_lt(c, k2) == True{} : Bool}}
      %lk_below(c, k2, v2, yr, hc, asc_tail(k2, v2, yr, ay)) : {Nat.add(v1, _) == v1 : Nat}
      Equal.sym(Nat, v1, Nat.add(v1, 0n), PNat.add_zero(v1))
    case False{}:
      ih(xr, Con{{(k2, v2) : CP()}, yr}, k, hg, asc_rest(k1, v1, xr, ax), ay)

def lk_gt(e: Bool, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +g: Nat, +c: Nat, +k: Nat,
  +ee: {Nat.is_eq(k2, c) == e : Bool}, +egt: {Nat.is_gt(k1, k2) == True{} : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k) == g : Nat},
  +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool},
  +ay: {L.codes_ascending(Con{{(k2, v2) : CP()}, yr}) == True{} : Bool},
  ih: @xs2: List<&2, CP()> -> @ys2: List<&2, CP()> -> @k3: Nat
    -> {Nat.add(Nat.add(List.length(&2, CP(), xs2), List.length(&2, CP(), ys2)), k3) == g : Nat}
    -> {L.codes_ascending(xs2) == True{} : Bool} -> {L.codes_ascending(ys2) == True{} : Bool}
    -> {Nat.add(L.lookup_code(c, xs2), L.lookup_code(c, ys2)) == L.lookup_code(c, Met.codes_merge.go(g, xs2, ys2)) : Nat})
  -> {Nat.add(L.lookup_code(c, Con{{(k1, v1) : CP()}, xr}), L.pick(Nat, e, v2, L.lookup_code(c, yr)))
      == L.pick(Nat, e, v2, L.lookup_code(c, Met.codes_merge.go(g, Con{{(k1, v1) : CP()}, xr}, yr))) : Nat}:
  match e:
    case True{}:
      +kc = n_eq_is(k2, c, ee)
      +hc = {%kc : {Nat.is_lt(_, k1) == True{} : Bool}; gt_lt(k1, k2, egt) : {Nat.is_lt(c, k1) == True{} : Bool}}
      %lk_below(c, k1, v1, xr, hc, asc_tail(k1, v1, xr, ax)) : {Nat.add(_, v2) == v2 : Nat}
      {==}
    case False{}:
      ih(Con{{(k1, v1) : CP()}, xr}, yr, k,
        fuel_gt(List.length(&2, CP(), xr), List.length(&2, CP(), yr), k, g, hg), ax, asc_rest(k2, v2, yr, ay))

def lk_eq(e: Bool, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +g: Nat, +c: Nat, +k: Nat,
  +hg: {Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k) == g : Nat},
  +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool},
  +ay: {L.codes_ascending(Con{{(k2, v2) : CP()}, yr}) == True{} : Bool},
  ih: @xs2: List<&2, CP()> -> @ys2: List<&2, CP()> -> @k3: Nat
    -> {Nat.add(Nat.add(List.length(&2, CP(), xs2), List.length(&2, CP(), ys2)), k3) == g : Nat}
    -> {L.codes_ascending(xs2) == True{} : Bool} -> {L.codes_ascending(ys2) == True{} : Bool}
    -> {Nat.add(L.lookup_code(c, xs2), L.lookup_code(c, ys2)) == L.lookup_code(c, Met.codes_merge.go(g, xs2, ys2)) : Nat})
  -> {Nat.add(L.pick(Nat, e, v1, L.lookup_code(c, xr)), L.pick(Nat, e, v2, L.lookup_code(c, yr)))
      == L.pick(Nat, e, Nat.add(v1, v2), L.lookup_code(c, Met.codes_merge.go(g, xr, yr))) : Nat}:
  match e:
    case True{}:
      {==}
    case False{}:
      ih(xr, yr, 1n+k, fuel_eq(List.length(&2, CP(), xr), List.length(&2, CP(), yr), k, g, hg),
        asc_rest(k1, v1, xr, ax), asc_rest(k2, v2, yr, ay))

def lk_step(lt: Bool, gt: Bool, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +g: Nat, +c: Nat, +k: Nat,
  +elt: {Nat.is_lt(k1, k2) == lt : Bool}, +egt: {Nat.is_gt(k1, k2) == gt : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k) == g : Nat},
  +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool},
  +ay: {L.codes_ascending(Con{{(k2, v2) : CP()}, yr}) == True{} : Bool},
  ih: @xs2: List<&2, CP()> -> @ys2: List<&2, CP()> -> @k3: Nat
    -> {Nat.add(Nat.add(List.length(&2, CP(), xs2), List.length(&2, CP(), ys2)), k3) == g : Nat}
    -> {L.codes_ascending(xs2) == True{} : Bool} -> {L.codes_ascending(ys2) == True{} : Bool}
    -> {Nat.add(L.lookup_code(c, xs2), L.lookup_code(c, ys2)) == L.lookup_code(c, Met.codes_merge.go(g, xs2, ys2)) : Nat})
  -> {Nat.add(L.lookup_code(c, Con{{(k1, v1) : CP()}, xr}), L.lookup_code(c, Con{{(k2, v2) : CP()}, yr}))
      == L.lookup_code(c, Con{Met.pick(CP(), lt, {(k1, v1) : CP()}, Met.pick(CP(), gt, {(k2, v2) : CP()}, Met.code_sum({(k1, v1) : CP()}, {(k2, v2) : CP()}))),
           Met.codes_merge.go(g, Met.pick(List<&2, CP()>, gt, Con{{(k1, v1) : CP()}, xr}, xr), Met.pick(List<&2, CP()>, lt, Con{{(k2, v2) : CP()}, yr}, yr))}) : Nat}:
  match lt:
    case True{}:
      match gt:
        case True{}:
          Empty.absurd({Nat.add(L.lookup_code(c, Con{{(k1, v1) : CP()}, xr}), L.lookup_code(c, Con{{(k2, v2) : CP()}, yr}))
            == L.lookup_code(c, Con{{(k1, v1) : CP()}, Met.codes_merge.go(g, Con{{(k1, v1) : CP()}, xr}, Con{{(k2, v2) : CP()}, yr})}) : Nat},
            n_lt_gt(k1, k2, elt, egt))
        case False{}:
          lk_lt(Nat.is_eq(k1, c), k1, v1, xr, k2, v2, yr, g, c, k, {==}, elt, hg, ax, ay, ih)
    case False{}:
      match gt:
        case True{}:
          lk_gt(Nat.is_eq(k2, c), k1, v1, xr, k2, v2, yr, g, c, k, {==}, egt, hg, ax, ay, ih)
        case False{}:
          +keq = n_eq_of(k1, k2, elt, egt)
          %keq : {Nat.add(L.pick(Nat, Nat.is_eq(k1, c), v1, L.lookup_code(c, xr)), L.pick(Nat, Nat.is_eq(_, c), v2, L.lookup_code(c, yr)))
                  == L.pick(Nat, Nat.is_eq(k1, c), Nat.add(v1, v2), L.lookup_code(c, Met.codes_merge.go(g, xr, yr))) : Nat}
          lk_eq(Nat.is_eq(k1, c), k1, v1, xr, k2, v2, yr, g, c, k, hg, ax, ay, ih)

def lk_go(f: Nat, xs: List<&2, CP()>, ys: List<&2, CP()>, +c: Nat, +k: Nat,
  +hf: {Nat.add(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)), k) == f : Nat},
  +ax: {L.codes_ascending(xs) == True{} : Bool}, +ay: {L.codes_ascending(ys) == True{} : Bool})
  -> {Nat.add(L.lookup_code(c, xs), L.lookup_code(c, ys)) == L.lookup_code(c, Met.codes_merge.go(f, xs, ys)) : Nat}:
  match f:
    case 0n:
      match xs:
        case Nil{}:
          match ys:
            case Nil{}:
              {==}
            case Con{q, yr}:
              Empty.absurd({L.lookup_code(c, Con{q, yr}) == L.lookup_code(c, Con{q, yr}) : Nat},
                PNat.no_zero(Nat.add(List.length(&2, CP(), yr), k), hf))
        case Con{p, xr}:
          Empty.absurd({Nat.add(L.lookup_code(c, Con{p, xr}), L.lookup_code(c, ys)) == L.lookup_code(c, List.append(&2, CP(), Con{p, xr}, ys)) : Nat},
            PNat.no_zero(Nat.add(Nat.add(List.length(&2, CP(), xr), List.length(&2, CP(), ys)), k), hf))
    case 1n+(+g):
      match xs:
        case Nil{}:
          {==}
        case Con{p, +xr}:
          match p:
            case (+k1, +v1):
              match ys:
                case Nil{}:
                  Equal.sym(Nat, L.lookup_code(c, Con{{(k1, v1) : CP()}, xr}), Nat.add(L.lookup_code(c, Con{{(k1, v1) : CP()}, xr}), 0n),
                    PNat.add_zero(L.lookup_code(c, Con{{(k1, v1) : CP()}, xr})))
                case Con{q, +yr}:
                  match q:
                    case (+k2, +v2):
                      lk_step(Nat.is_lt(k1, k2), Nat.is_gt(k1, k2), k1, v1, xr, k2, v2, yr, g, c, k, {==}, {==},
                        PNat.succ_inj(Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k), g, hf), ax, ay,
                        xs2 => ys2 => k3 => h1 => h2 => h3 => lk_go(g, xs2, ys2, c, k3, h1, h2, h3))

def lk_merge(+xs: List<&2, CP()>, +ys: List<&2, CP()>, +c: Nat,
  +ax: {L.codes_ascending(xs) == True{} : Bool}, +ay: {L.codes_ascending(ys) == True{} : Bool})
  -> {Nat.add(L.lookup_code(c, xs), L.lookup_code(c, ys)) == L.lookup_code(c, Met.codes_merge(xs, ys)) : Nat}:
  lk_go(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)), xs, ys, c, 0n,
    Equal.sym(Nat, Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)),
      Nat.add(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)), 0n),
      PNat.add_zero(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)))), ax, ay)

# ---------------------------------------------------------------------
# a merge of lists all above k is all above k
# ---------------------------------------------------------------------

def aft_head(+k: Nat, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +ax: {L.codes_after(Con{{(k1, v1) : CP()}, xr}, k) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(k, k1), Nat.is_gt(v1, 0n)) == True{} : Bool}:
  and_l(Bool.and(Nat.is_lt(k, k1), Nat.is_gt(v1, 0n)), L.codes_after(xr, k1), ax)

def aft_tail(+k: Nat, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +ax: {L.codes_after(Con{{(k1, v1) : CP()}, xr}, k) == True{} : Bool})
  -> {L.codes_after(xr, k1) == True{} : Bool}:
  and_r(Bool.and(Nat.is_lt(k, k1), Nat.is_gt(v1, 0n)), L.codes_after(xr, k1), ax)

def aft_pos(+k: Nat, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +ax: {L.codes_after(Con{{(k1, v1) : CP()}, xr}, k) == True{} : Bool})
  -> {Nat.is_gt(v1, 0n) == True{} : Bool}:
  and_r(Nat.is_lt(k, k1), Nat.is_gt(v1, 0n), aft_head(k, k1, v1, xr, ax))

def aft_lt(+k: Nat, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +ax: {L.codes_after(Con{{(k1, v1) : CP()}, xr}, k) == True{} : Bool})
  -> {Nat.is_lt(k, k1) == True{} : Bool}:
  and_l(Nat.is_lt(k, k1), Nat.is_gt(v1, 0n), aft_head(k, k1, v1, xr, ax))

# a list all above k2 whose head is above k1 < k2... rebuilt with bound k1
def aft_mk(+k1: Nat, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +hlt: {Nat.is_lt(k1, k2) == True{} : Bool},
  +hv: {Nat.is_gt(v2, 0n) == True{} : Bool}, +hr: {L.codes_after(yr, k2) == True{} : Bool})
  -> {L.codes_after(Con{{(k2, v2) : CP()}, yr}, k1) == True{} : Bool}:
  and_i(Bool.and(Nat.is_lt(k1, k2), Nat.is_gt(v2, 0n)), L.codes_after(yr, k2), and_i(Nat.is_lt(k1, k2), Nat.is_gt(v2, 0n), hlt, hv), hr)

def af_step(lt: Bool, gt: Bool, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +g: Nat, +k: Nat, +b: Nat,
  +elt: {Nat.is_lt(k1, k2) == lt : Bool}, +egt: {Nat.is_gt(k1, k2) == gt : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k) == g : Nat},
  +ax: {L.codes_after(Con{{(k1, v1) : CP()}, xr}, b) == True{} : Bool},
  +ay: {L.codes_after(Con{{(k2, v2) : CP()}, yr}, b) == True{} : Bool},
  ih: @xs2: List<&2, CP()> -> @ys2: List<&2, CP()> -> @k3: Nat -> @b2: Nat
    -> {Nat.add(Nat.add(List.length(&2, CP(), xs2), List.length(&2, CP(), ys2)), k3) == g : Nat}
    -> {L.codes_after(xs2, b2) == True{} : Bool} -> {L.codes_after(ys2, b2) == True{} : Bool}
    -> {L.codes_after(Met.codes_merge.go(g, xs2, ys2), b2) == True{} : Bool})
  -> {L.codes_after(Con{Met.pick(CP(), lt, {(k1, v1) : CP()}, Met.pick(CP(), gt, {(k2, v2) : CP()}, Met.code_sum({(k1, v1) : CP()}, {(k2, v2) : CP()}))),
           Met.codes_merge.go(g, Met.pick(List<&2, CP()>, gt, Con{{(k1, v1) : CP()}, xr}, xr), Met.pick(List<&2, CP()>, lt, Con{{(k2, v2) : CP()}, yr}, yr))}, b) == True{} : Bool}:
  match lt:
    case True{}:
      match gt:
        case True{}:
          Empty.absurd({L.codes_after(Con{{(k1, v1) : CP()}, Met.codes_merge.go(g, Con{{(k1, v1) : CP()}, xr}, Con{{(k2, v2) : CP()}, yr})}, b) == True{} : Bool},
            n_lt_gt(k1, k2, elt, egt))
        case False{}:
          and_i(Bool.and(Nat.is_lt(b, k1), Nat.is_gt(v1, 0n)), L.codes_after(Met.codes_merge.go(g, xr, Con{{(k2, v2) : CP()}, yr}), k1),
            aft_head(b, k1, v1, xr, ax),
            ih(xr, Con{{(k2, v2) : CP()}, yr}, k, k1, hg, aft_tail(b, k1, v1, xr, ax),
              aft_mk(k1, k2, v2, yr, elt, aft_pos(b, k2, v2, yr, ay), aft_tail(b, k2, v2, yr, ay))))
    case False{}:
      match gt:
        case True{}:
          and_i(Bool.and(Nat.is_lt(b, k2), Nat.is_gt(v2, 0n)), L.codes_after(Met.codes_merge.go(g, Con{{(k1, v1) : CP()}, xr}, yr), k2),
            aft_head(b, k2, v2, yr, ay),
            ih(Con{{(k1, v1) : CP()}, xr}, yr, k, k2, fuel_gt(List.length(&2, CP(), xr), List.length(&2, CP(), yr), k, g, hg),
              aft_mk(k2, k1, v1, xr, gt_lt(k1, k2, egt), aft_pos(b, k1, v1, xr, ax), aft_tail(b, k1, v1, xr, ax)),
              aft_tail(b, k2, v2, yr, ay)))
        case False{}:
          +keq = n_eq_of(k1, k2, elt, egt)
          +hyr = {%Equal.sym(Nat, k1, k2, keq) : {L.codes_after(yr, _) == True{} : Bool}; aft_tail(b, k2, v2, yr, ay) : {L.codes_after(yr, k1) == True{} : Bool}}
          and_i(Bool.and(Nat.is_lt(b, k1), Nat.is_gt(Nat.add(v1, v2), 0n)), L.codes_after(Met.codes_merge.go(g, xr, yr), k1),
            and_i(Nat.is_lt(b, k1), Nat.is_gt(Nat.add(v1, v2), 0n), aft_lt(b, k1, v1, xr, ax), gt_add(v1, v2, aft_pos(b, k1, v1, xr, ax))),
            ih(xr, yr, 1n+k, k1, fuel_eq(List.length(&2, CP(), xr), List.length(&2, CP(), yr), k, g, hg), aft_tail(b, k1, v1, xr, ax), hyr))

def af_go(f: Nat, xs: List<&2, CP()>, ys: List<&2, CP()>, +k: Nat, +b: Nat,
  +hf: {Nat.add(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)), k) == f : Nat},
  +ax: {L.codes_after(xs, b) == True{} : Bool}, +ay: {L.codes_after(ys, b) == True{} : Bool})
  -> {L.codes_after(Met.codes_merge.go(f, xs, ys), b) == True{} : Bool}:
  match f:
    case 0n:
      match xs:
        case Nil{}:
          match ys:
            case Nil{}:
              {==}
            case Con{q, yr}:
              Empty.absurd({L.codes_after(Con{q, yr}, b) == True{} : Bool}, PNat.no_zero(Nat.add(List.length(&2, CP(), yr), k), hf))
        case Con{p, xr}:
          Empty.absurd({L.codes_after(List.append(&2, CP(), Con{p, xr}, ys), b) == True{} : Bool},
            PNat.no_zero(Nat.add(Nat.add(List.length(&2, CP(), xr), List.length(&2, CP(), ys)), k), hf))
    case 1n+(+g):
      match xs:
        case Nil{}:
          ay
        case Con{p, +xr}:
          match p:
            case (+k1, +v1):
              match ys:
                case Nil{}:
                  ax
                case Con{q, +yr}:
                  match q:
                    case (+k2, +v2):
                      af_step(Nat.is_lt(k1, k2), Nat.is_gt(k1, k2), k1, v1, xr, k2, v2, yr, g, k, b, {==}, {==},
                        PNat.succ_inj(Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k), g, hf), ax, ay,
                        xs2 => ys2 => k3 => b2 => h1 => h2 => h3 => af_go(g, xs2, ys2, k3, b2, h1, h2, h3))

def asc_step(lt: Bool, gt: Bool, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +g: Nat, +k: Nat,
  +elt: {Nat.is_lt(k1, k2) == lt : Bool}, +egt: {Nat.is_gt(k1, k2) == gt : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k) == g : Nat},
  +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool},
  +ay: {L.codes_ascending(Con{{(k2, v2) : CP()}, yr}) == True{} : Bool})
  -> {L.codes_ascending(Con{Met.pick(CP(), lt, {(k1, v1) : CP()}, Met.pick(CP(), gt, {(k2, v2) : CP()}, Met.code_sum({(k1, v1) : CP()}, {(k2, v2) : CP()}))),
           Met.codes_merge.go(g, Met.pick(List<&2, CP()>, gt, Con{{(k1, v1) : CP()}, xr}, xr), Met.pick(List<&2, CP()>, lt, Con{{(k2, v2) : CP()}, yr}, yr))}) == True{} : Bool}:
  match lt:
    case True{}:
      match gt:
        case True{}:
          Empty.absurd({L.codes_ascending(Con{{(k1, v1) : CP()}, Met.codes_merge.go(g, Con{{(k1, v1) : CP()}, xr}, Con{{(k2, v2) : CP()}, yr})}) == True{} : Bool},
            n_lt_gt(k1, k2, elt, egt))
        case False{}:
          and_i(Nat.is_gt(v1, 0n), L.codes_after(Met.codes_merge.go(g, xr, Con{{(k2, v2) : CP()}, yr}), k1),
            asc_pos(k1, v1, xr, ax),
            af_go(g, xr, Con{{(k2, v2) : CP()}, yr}, k, k1, hg, asc_tail(k1, v1, xr, ax), asc_above(k1, k2, v2, yr, elt, ay)))
    case False{}:
      match gt:
        case True{}:
          and_i(Nat.is_gt(v2, 0n), L.codes_after(Met.codes_merge.go(g, Con{{(k1, v1) : CP()}, xr}, yr), k2),
            asc_pos(k2, v2, yr, ay),
            af_go(g, Con{{(k1, v1) : CP()}, xr}, yr, k, k2, fuel_gt(List.length(&2, CP(), xr), List.length(&2, CP(), yr), k, g, hg),
              asc_above(k2, k1, v1, xr, gt_lt(k1, k2, egt), ax), asc_tail(k2, v2, yr, ay)))
        case False{}:
          +keq = n_eq_of(k1, k2, elt, egt)
          +hyr = {%Equal.sym(Nat, k1, k2, keq) : {L.codes_after(yr, _) == True{} : Bool}; asc_tail(k2, v2, yr, ay) : {L.codes_after(yr, k1) == True{} : Bool}}
          and_i(Nat.is_gt(Nat.add(v1, v2), 0n), L.codes_after(Met.codes_merge.go(g, xr, yr), k1),
            gt_add(v1, v2, asc_pos(k1, v1, xr, ax)),
            af_go(g, xr, yr, 1n+k, k1, fuel_eq(List.length(&2, CP(), xr), List.length(&2, CP(), yr), k, g, hg), asc_tail(k1, v1, xr, ax), hyr))

def asc_go(f: Nat, xs: List<&2, CP()>, ys: List<&2, CP()>, +k: Nat,
  +hf: {Nat.add(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)), k) == f : Nat},
  +ax: {L.codes_ascending(xs) == True{} : Bool}, +ay: {L.codes_ascending(ys) == True{} : Bool})
  -> {L.codes_ascending(Met.codes_merge.go(f, xs, ys)) == True{} : Bool}:
  match f:
    case 0n:
      match xs:
        case Nil{}:
          match ys:
            case Nil{}:
              {==}
            case Con{q, yr}:
              Empty.absurd({L.codes_ascending(Con{q, yr}) == True{} : Bool}, PNat.no_zero(Nat.add(List.length(&2, CP(), yr), k), hf))
        case Con{p, xr}:
          Empty.absurd({L.codes_ascending(List.append(&2, CP(), Con{p, xr}, ys)) == True{} : Bool},
            PNat.no_zero(Nat.add(Nat.add(List.length(&2, CP(), xr), List.length(&2, CP(), ys)), k), hf))
    case 1n+(+g):
      match xs:
        case Nil{}:
          ay
        case Con{p, +xr}:
          match p:
            case (+k1, +v1):
              match ys:
                case Nil{}:
                  ax
                case Con{q, +yr}:
                  match q:
                    case (+k2, +v2):
                      asc_step(Nat.is_lt(k1, k2), Nat.is_gt(k1, k2), k1, v1, xr, k2, v2, yr, g, k, {==}, {==},
                        PNat.succ_inj(Nat.add(Nat.add(List.length(&2, CP(), xr), 1n+List.length(&2, CP(), yr)), k), g, hf), ax, ay)

def asc_merge(+xs: List<&2, CP()>, +ys: List<&2, CP()>,
  +ax: {L.codes_ascending(xs) == True{} : Bool}, +ay: {L.codes_ascending(ys) == True{} : Bool})
  -> {L.codes_ascending(Met.codes_merge(xs, ys)) == True{} : Bool}:
  asc_go(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)), xs, ys, 0n,
    Equal.sym(Nat, Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)),
      Nat.add(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)), 0n),
      PNat.add_zero(Nat.add(List.length(&2, CP(), xs), List.length(&2, CP(), ys)))), ax, ay)

# ---------------------------------------------------------------------
# the codes of the accumulator
# ---------------------------------------------------------------------

def oh_asc(h: Hit.Hit) -> {L.codes_ascending(a_cs(Met.of_hit(h))) == True{} : Bool}:
  match h:
    case Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          {==}

def oh_lk(h: Hit.Hit, +c: Nat) -> {L.pick(Nat, Nat.is_eq(L.h_code(h), c), 1n, 0n) == L.lookup_code(c, a_cs(Met.of_hit(h))) : Nat}:
  match h:
    case Hit.Hit{a, q, code, t, l, bo, bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          {==}

def add_asc(+a: Met.Acc, +h: Hit.Hit, +ha: {L.codes_ascending(a_cs(a)) == True{} : Bool})
  -> {L.codes_ascending(a_cs(Met.add(a, h))) == True{} : Bool}:
  %m_cs(a, Met.of_hit(h)) : {L.codes_ascending(_) == True{} : Bool}
  asc_merge(a_cs(a), a_cs(Met.of_hit(h)), ha, oh_asc(h))

def f_asc(hs: List<&2, Hit.Hit>, +a: Met.Acc, +ha: {L.codes_ascending(a_cs(a)) == True{} : Bool})
  -> {L.codes_ascending(a_cs(L.acc_all(hs, a))) == True{} : Bool}:
  match hs:
    case Nil{}:
      ha
    case Con{+h, +rest}:
      f_asc(rest, Met.add(a, h), add_asc(a, h, ha))

def f_lk(hs: List<&2, Hit.Hit>, +a: Met.Acc, +c: Nat, +ha: {L.codes_ascending(a_cs(a)) == True{} : Bool})
  -> {Nat.add(L.lookup_code(c, a_cs(a)), L.n_code(c, hs)) == L.lookup_code(c, a_cs(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      Equal.sym(Nat, L.lookup_code(c, a_cs(a)), Nat.add(L.lookup_code(c, a_cs(a)), 0n), PNat.add_zero(L.lookup_code(c, a_cs(a))))
    case Con{+h, +rest}:
      +x = L.lookup_code(c, a_cs(a))
      +p = L.pick(Nat, Nat.is_eq(L.h_code(h), c), 1n, 0n)
      +r = L.n_code(c, rest)
      %f_lk(rest, Met.add(a, h), c, add_asc(a, h, ha)) : {Nat.add(x, Nat.add(p, r)) == _ : Nat}
      %m_cs(a, Met.of_hit(h)) : {Nat.add(x, Nat.add(p, r)) == Nat.add(L.lookup_code(c, _), r) : Nat}
      %lk_merge(a_cs(a), a_cs(Met.of_hit(h)), c, ha, oh_asc(h)) : {Nat.add(x, Nat.add(p, r)) == Nat.add(_, r) : Nat}
      %oh_lk(h, c) : {Nat.add(x, Nat.add(p, r)) == Nat.add(Nat.add(x, _), r) : Nat}
      PNat.add_assoc(x, p, r)

def c_cs(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {a_cs(a) == L.s_codes(Met.close(a)) : List<&2, CP()>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({cs == [] : List<&2, CP()>}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def L.met_counts(bs, hs, c):
  match hs:
    case Nil{}:
      ({==}, ({==}, ({==}, {==})))
    case Con{+h, +rest}:
      +A = L.acc_all(Con{h, rest}, Met.empty(bs))
      +hx = sum_x(bs, h, rest)
      +e1 = {%c_req(A, hx) : {_ == 1n+List.length(&2, Hit.Hit, rest) : Nat};
             Equal.sym(Nat, 1n+List.length(&2, Hit.Hit, rest), a_n(A), f_n(Con{h, rest}, Met.empty(bs)))
             : {L.s_requests(L.summary(bs, Con{h, rest})) == List.length(&2, Hit.Hit, Con{h, rest}) : Nat}}
      +e2 = {%c_ok(A, hx) : {_ == L.n_ok(Con{h, rest}) : Nat};
             Equal.sym(Nat, L.n_ok(Con{h, rest}), a_ok(A), f_ok(Con{h, rest}, Met.empty(bs)))
             : {L.s_success(L.summary(bs, Con{h, rest})) == L.n_ok(Con{h, rest}) : Nat}}
      +e3 = {%c_cs(A, hx) : {L.lookup_code(c, _) == L.n_code(c, Con{h, rest}) : Nat};
             Equal.sym(Nat, L.n_code(c, Con{h, rest}), L.lookup_code(c, a_cs(A)), f_lk(Con{h, rest}, Met.empty(bs), c, {==}))
             : {L.lookup_code(c, L.s_codes(L.summary(bs, Con{h, rest}))) == L.n_code(c, Con{h, rest}) : Nat}}
      +e4 = {%c_cs(A, hx) : {L.codes_ascending(_) == True{} : Bool};
             f_asc(Con{h, rest}, Met.empty(bs), {==})
             : {L.codes_ascending(L.s_codes(L.summary(bs, Con{h, rest}))) == True{} : Bool}}
      (e1, (e2, (e3, e4)))


# =====================================================================
# Latency lists: counting survives the merge sort
# =====================================================================

type Pr is Data:
  PLt{p: Nat}
  PLe{p: Nat}
  PBk{bs: List<&2, Nat>, i: Nat}
  PAll{}

def ev(p: Pr, +x: Nat) -> Bool:
  match p:
    case PLt{q}:
      Nat.is_lt(x, q)
    case PLe{q}:
      Nat.is_le(x, q)
    case PBk{bs, i}:
      Nat.is_eq(L.bucket_of(bs, x), i)
    case PAll{}:
      True{}

def cnt(+p: Pr, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, +rest}:
      Nat.add(L.pick(Nat, ev(p, x), 1n, 0n), cnt(p, rest))

def cnt_app(+p: Pr, xs: List<&2, Nat>, +ys: List<&2, Nat>)
  -> {Nat.add(cnt(p, xs), cnt(p, ys)) == cnt(p, List.append(&2, Nat, xs, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      +e = L.pick(Nat, ev(p, x), 1n, 0n)
      %cnt_app(p, rest, ys) : {Nat.add(Nat.add(e, cnt(p, rest)), cnt(p, ys)) == Nat.add(e, _) : Nat}
      Equal.sym(Nat, Nat.add(e, Nat.add(cnt(p, rest), cnt(p, ys))), Nat.add(Nat.add(e, cnt(p, rest)), cnt(p, ys)), PNat.add_assoc(e, cnt(p, rest), cnt(p, ys)))

def cm_step(le: Bool, +p: Pr, +x: Nat, +xr: List<&2, Nat>, +y: Nat, +yr: List<&2, Nat>, +g: Nat,
  ih: @xs2: List<&2, Nat> -> @ys2: List<&2, Nat> -> {Nat.add(cnt(p, xs2), cnt(p, ys2)) == cnt(p, Met.nmerge(g, xs2, ys2)) : Nat})
  -> {Nat.add(cnt(p, Con{x, xr}), cnt(p, Con{y, yr}))
      == cnt(p, Con{Met.pick(Nat, le, x, y), Met.nmerge(g, Met.pick(List<&2, Nat>, le, xr, Con{x, xr}), Met.pick(List<&2, Nat>, le, Con{y, yr}, yr))}) : Nat}:
  match le:
    case True{}:
      +ex = L.pick(Nat, ev(p, x), 1n, 0n)
      +ey = L.pick(Nat, ev(p, y), 1n, 0n)
      %ih(xr, Con{y, yr}) : {Nat.add(Nat.add(ex, cnt(p, xr)), Nat.add(ey, cnt(p, yr))) == Nat.add(ex, _) : Nat}
      Equal.sym(Nat, Nat.add(ex, Nat.add(cnt(p, xr), Nat.add(ey, cnt(p, yr)))), Nat.add(Nat.add(ex, cnt(p, xr)), Nat.add(ey, cnt(p, yr))),
        PNat.add_assoc(ex, cnt(p, xr), Nat.add(ey, cnt(p, yr))))
    case False{}:
      +ex = L.pick(Nat, ev(p, x), 1n, 0n)
      +ey = L.pick(Nat, ev(p, y), 1n, 0n)
      %ih(Con{x, xr}, yr) : {Nat.add(Nat.add(ex, cnt(p, xr)), Nat.add(ey, cnt(p, yr))) == Nat.add(ey, _) : Nat}
      PNat.add_swap(Nat.add(ex, cnt(p, xr)), ey, cnt(p, yr))

def cnt_merge(f: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>, +p: Pr)
  -> {Nat.add(cnt(p, xs), cnt(p, ys)) == cnt(p, Met.nmerge(f, xs, ys)) : Nat}:
  match f:
    case 0n:
      cnt_app(p, xs, ys)
    case 1n+(+g):
      match xs:
        case Nil{}:
          {==}
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              Equal.sym(Nat, cnt(p, Con{x, xr}), Nat.add(cnt(p, Con{x, xr}), 0n), PNat.add_zero(cnt(p, Con{x, xr})))
            case Con{+y, +yr}:
              cm_step(Nat.is_le(x, y), p, x, xr, y, yr, g, xs2 => ys2 => cnt_merge(g, xs2, ys2, p))

def cnt_split(xs: List<&2, Nat>, h: Nat, +p: Pr)
  -> {Nat.add(cnt(p, List.take(&2, Nat, xs, h)), cnt(p, List.drop(&2, Nat, xs, h))) == cnt(p, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      match h:
        case 0n:
          {==}
        case 1n+(+hp):
          +e = L.pick(Nat, ev(p, x), 1n, 0n)
          +a = cnt(p, List.take(&2, Nat, rest, hp))
          +b = cnt(p, List.drop(&2, Nat, rest, hp))
          %cnt_split(rest, hp, p) : {Nat.add(Nat.add(e, a), b) == Nat.add(e, _) : Nat}
          Equal.sym(Nat, Nat.add(e, Nat.add(a, b)), Nat.add(Nat.add(e, a), b), PNat.add_assoc(e, a, b))

def cnt_msort(f: Nat, s: Bool, +xs: List<&2, Nat>, +n: Nat, +p: Pr) -> {cnt(p, xs) == cnt(p, Met.msort(f, s, xs, n)) : Nat}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      match s:
        case True{}:
          {==}
        case False{}:
          +h = Nat.div(n, 2n)
          +m = Nat.sub(n, h)
          +a = Met.msort(g, Nat.is_le(h, 1n), List.take(&2, Nat, xs, h), h)
          +b = Met.msort(g, Nat.is_le(m, 1n), List.drop(&2, Nat, xs, h), m)
          %cnt_merge(n, a, b, p) : {cnt(p, xs) == _ : Nat}
          %cnt_msort(g, Nat.is_le(h, 1n), List.take(&2, Nat, xs, h), h, p) : {cnt(p, xs) == Nat.add(_, cnt(p, b)) : Nat}
          %cnt_msort(g, Nat.is_le(m, 1n), List.drop(&2, Nat, xs, h), m, p) : {cnt(p, xs) == Nat.add(cnt(p, List.take(&2, Nat, xs, h)), _) : Nat}
          Equal.sym(Nat, Nat.add(cnt(p, List.take(&2, Nat, xs, h)), cnt(p, List.drop(&2, Nat, xs, h))), cnt(p, xs), cnt_split(xs, h, p))

def cnt_sort(+xs: List<&2, Nat>, +p: Pr) -> {cnt(p, xs) == cnt(p, Met.sort(xs)) : Nat}:
  cnt_msort(List.length(&2, Nat, xs), Nat.is_le(List.length(&2, Nat, xs), 1n), xs, List.length(&2, Nat, xs), p)

def cnt_all(xs: List<&2, Nat>) -> {cnt(PAll{}, xs) == List.length(&2, Nat, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %cnt_all(rest) : {1n+cnt(PAll{}, rest) == 1n+_ : Nat}
      {==}

def len_sort(+xs: List<&2, Nat>) -> {List.length(&2, Nat, xs) == List.length(&2, Nat, Met.sort(xs)) : Nat}:
  %cnt_all(Met.sort(xs)) : {List.length(&2, Nat, xs) == _ : Nat}
  %cnt_all(xs) : {_ == cnt(PAll{}, Met.sort(xs)) : Nat}
  cnt_sort(xs, PAll{})

def n_less_cnt(+q: Nat, xs: List<&2, Nat>) -> {L.n_less(q, xs) == cnt(PLt{q}, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %n_less_cnt(q, rest) : {Nat.add(L.pick(Nat, Nat.is_lt(x, q), 1n, 0n), L.n_less(q, rest)) == Nat.add(L.pick(Nat, Nat.is_lt(x, q), 1n, 0n), _) : Nat}
      {==}

def n_upto_cnt(+q: Nat, xs: List<&2, Nat>) -> {L.n_upto(q, xs) == cnt(PLe{q}, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %n_upto_cnt(q, rest) : {Nat.add(L.pick(Nat, Nat.is_le(x, q), 1n, 0n), L.n_upto(q, rest)) == Nat.add(L.pick(Nat, Nat.is_le(x, q), 1n, 0n), _) : Nat}
      {==}

def nib_cnt(+bs: List<&2, Nat>, +i: Nat, xs: List<&2, Nat>) -> {L.n_in_bucket(bs, i, xs) == cnt(PBk{bs, i}, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %nib_cnt(bs, i, rest) : {Nat.add(L.pick(Nat, Nat.is_eq(L.bucket_of(bs, x), i), 1n, 0n), L.n_in_bucket(bs, i, rest))
        == Nat.add(L.pick(Nat, Nat.is_eq(L.bucket_of(bs, x), i), 1n, 0n), _) : Nat}
      {==}

# ---------------------------------------------------------------------
# The rope flattens to the latencies in order
# ---------------------------------------------------------------------

def fl_lcat(x: Met.Lats, y: Met.Lats, +acc: List<&2, Nat>)
  -> {Met.flatten(x, Met.flatten(y, acc)) == Met.flatten(Met.lcat(x, y), acc) : List<&2, Nat>}:
  match x:
    case Met.LNone{}:
      {==}
    case Met.LOne{v}:
      match y:
        case Met.LNone{}:
          {==}
        case Met.LOne{w}:
          {==}
        case Met.LCat{l, r}:
          {==}
    case Met.LCat{l1, r1}:
      match y:
        case Met.LNone{}:
          {==}
        case Met.LOne{w}:
          {==}
        case Met.LCat{l, r}:
          {==}

def oh_fl(h: Hit.Hit, +acc: List<&2, Nat>) -> {Con{L.h_lat(h), acc} == Met.flatten(a_t(Met.of_hit(h)), acc) : List<&2, Nat>}:
  match h:
    case Hit.Hit{a, q, c, t, l, bo, bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          {==}

def fl_all(hs: List<&2, Hit.Hit>, +a: Met.Acc, +acc: List<&2, Nat>)
  -> {Met.flatten(a_t(a), List.append(&2, Nat, L.lats(hs), acc)) == Met.flatten(a_t(L.acc_all(hs, a)), acc) : List<&2, Nat>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      +r = List.append(&2, Nat, L.lats(rest), acc)
      %fl_all(rest, Met.add(a, h), acc) : {Met.flatten(a_t(a), Con{L.h_lat(h), r}) == _ : List<&2, Nat>}
      %m_t(a, Met.of_hit(h)) : {Met.flatten(a_t(a), Con{L.h_lat(h), r}) == Met.flatten(_, r) : List<&2, Nat>}
      %fl_lcat(a_t(a), a_t(Met.of_hit(h)), r) : {Met.flatten(a_t(a), Con{L.h_lat(h), r}) == _ : List<&2, Nat>}
      %oh_fl(h, r) : {Met.flatten(a_t(a), Con{L.h_lat(h), r}) == Met.flatten(a_t(a), _) : List<&2, Nat>}
      {==}

def app_nil(xs: List<&2, Nat>) -> {xs == List.append(&2, Nat, xs, []) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %app_nil(rest) : {Con{x, rest} == Con{x, _} : List<&2, Nat>}
      {==}

# the latencies of a summary's accumulator, in arrival order
def lats_all(+bs: List<&2, Nat>, +hs: List<&2, Hit.Hit>) -> {L.lats(hs) == Met.flatten(a_t(L.acc_all(hs, Met.empty(bs))), []) : List<&2, Nat>}:
  %fl_all(hs, Met.empty(bs), []) : {L.lats(hs) == _ : List<&2, Nat>}
  app_nil(L.lats(hs))

# ---------------------------------------------------------------------
# Buckets: lib's list walk is LAWS' index walk
# ---------------------------------------------------------------------

def nil_con_t(xs: List<&2, Nat>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, r}:
      Empty

def nil_ne_con(-b: Nat, -r: List<&2, Nat>, e: {[] == Con{b, r} : List<&2, Nat>}) -> Empty:
  %e : nil_con_t(_)
  Unit{}

def sub_zero(n: Nat) -> {n == Nat.sub(n, 0n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def drop0(bs: List<&2, Nat>) -> {bs == List.drop(&2, Nat, bs, 0n) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

def drop_get(bs: List<&2, Nat>, i: Nat, -b: Nat, -r: List<&2, Nat>, hd: {List.drop(&2, Nat, bs, i) == Con{b, r} : List<&2, Nat>})
  -> {L.nth_or0(i, bs) == b : Nat}:
  match bs:
    case Nil{}:
      Empty.absurd({L.nth_or0(i, []) == b : Nat}, nil_ne_con(b, r, hd))
    case Con{+x, +xs}:
      match i:
        case 0n:
          Equal.cong(List<&2, Nat>, Nat, ys => L.head_or(0n, ys), Con{x, xs}, Con{b, r}, hd)
        case 1n+j:
          drop_get(xs, j, b, r, hd)

def drop_succ(bs: List<&2, Nat>, i: Nat, -b: Nat, -r: List<&2, Nat>, hd: {List.drop(&2, Nat, bs, i) == Con{b, r} : List<&2, Nat>})
  -> {List.drop(&2, Nat, bs, 1n+i) == r : List<&2, Nat>}:
  match bs:
    case Nil{}:
      Empty.absurd({[] == r : List<&2, Nat>}, nil_ne_con(b, r, hd))
    case Con{+x, +xs}:
      match i:
        case 0n:
          %drop0(xs) : {_ == r : List<&2, Nat>}
          Equal.cong(List<&2, Nat>, List<&2, Nat>, ys => List.tail(&2, Nat, ys), Con{x, xs}, Con{b, r}, hd)
        case 1n+j:
          drop_succ(xs, j, b, r, hd)

def bk_step(stop: Bool, +b: Nat, +c: Nat, +more: List<&2, Nat>, +bs: List<&2, Nat>, +lat: Nat, +i: Nat,
  ih: {L.bucket_of.go(List.length(&2, Nat, more), bs, lat, 1n+i) == Met.bucket_of.go(Con{c, more}, Met.in_first(Con{c, more}, lat), lat, 1n+i) : Nat})
  -> {L.pick(Nat, stop, i, L.bucket_of.go(List.length(&2, Nat, more), bs, lat, 1n+i)) == Met.bucket_of.go(Con{b, Con{c, more}}, stop, lat, i) : Nat}:
  match stop:
    case True{}:
      {==}
    case False{}:
      ih

def bk_go(ds: List<&2, Nat>, +bs: List<&2, Nat>, +lat: Nat, +i: Nat, +hd: {List.drop(&2, Nat, bs, i) == ds : List<&2, Nat>})
  -> {L.bucket_of.go(Nat.sub(List.length(&2, Nat, ds), 1n), bs, lat, i) == Met.bucket_of.go(ds, Met.in_first(ds, lat), lat, i) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      match r:
        case Nil{}:
          {==}
        case Con{+c, +more}:
          +hb = drop_get(bs, i, b, Con{c, more}, hd)
          +hr = drop_succ(bs, i, b, Con{c, more}, hd)
          +hc = drop_get(bs, 1n+i, c, more, hr)
          %Equal.sym(Nat, L.nth_or0(i, bs), b, hb)
            : {L.pick(Nat, Bool.and(Nat.is_le(_, lat), Nat.is_lt(lat, L.nth_or0(1n+i, bs))), i, L.bucket_of.go(List.length(&2, Nat, more), bs, lat, 1n+i))
               == Met.bucket_of.go(Con{b, Con{c, more}}, Met.in_first(Con{b, Con{c, more}}, lat), lat, i) : Nat}
          %Equal.sym(Nat, L.nth_or0(1n+i, bs), c, hc)
            : {L.pick(Nat, Bool.and(Nat.is_le(b, lat), Nat.is_lt(lat, _)), i, L.bucket_of.go(List.length(&2, Nat, more), bs, lat, 1n+i))
               == Met.bucket_of.go(Con{b, Con{c, more}}, Met.in_first(Con{b, Con{c, more}}, lat), lat, i) : Nat}
          +ih = {%Equal.sym(Nat, List.length(&2, Nat, more), Nat.sub(List.length(&2, Nat, more), 0n), sub_zero(List.length(&2, Nat, more))) : {L.bucket_of.go(_, bs, lat, 1n+i) == Met.bucket_of.go(Con{c, more}, Met.in_first(Con{c, more}, lat), lat, 1n+i) : Nat};
                 bk_go(Con{c, more}, bs, lat, 1n+i, hr)
                 : {L.bucket_of.go(List.length(&2, Nat, more), bs, lat, 1n+i) == Met.bucket_of.go(Con{c, more}, Met.in_first(Con{c, more}, lat), lat, 1n+i) : Nat}}
          bk_step(Bool.and(Nat.is_le(b, lat), Nat.is_lt(lat, c)), b, c, more, bs, lat, i, ih)

def bucket_same(+bs: List<&2, Nat>, +lat: Nat) -> {L.bucket_of(bs, lat) == Met.bucket_of(bs, lat) : Nat}:
  bk_go(bs, bs, lat, 0n, Equal.sym(List<&2, Nat>, bs, List.drop(&2, Nat, bs, 0n), drop0(bs)))

# ---------------------------------------------------------------------
# The histogram counts
# ---------------------------------------------------------------------

def len_inc(cs: List<&2, Nat>, j: Nat) -> {List.length(&2, Nat, cs) == List.length(&2, Nat, Met.inc_at(cs, j)) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match j:
        case 0n:
          {==}
        case 1n+jp:
          %len_inc(rest, jp) : {1n+List.length(&2, Nat, rest) == 1n+_ : Nat}
          {==}

def inc_nth(cs: List<&2, Nat>, j: Nat, i: Nat, +hi: {Nat.is_lt(i, List.length(&2, Nat, cs)) == True{} : Bool})
  -> {Nat.add(L.pick(Nat, Nat.is_eq(j, i), 1n, 0n), L.nth_or0(i, cs)) == L.nth_or0(i, Met.inc_at(cs, j)) : Nat}:
  match cs:
    case Nil{}:
      Empty.absurd({Nat.add(L.pick(Nat, Nat.is_eq(j, i), 1n, 0n), 0n) == 0n : Nat}, PNat.lt_zero(i, hi))
    case Con{+c, +rest}:
      match j:
        case 0n:
          match i:
            case 0n:
              {==}
            case 1n+ip:
              {==}
        case 1n+jp:
          match i:
            case 0n:
              {==}
            case 1n+ip:
              inc_nth(rest, jp, ip, hi)

def len_hist(xs: List<&2, Nat>, +bs: List<&2, Nat>, +cs: List<&2, Nat>)
  -> {List.length(&2, Nat, cs) == List.length(&2, Nat, Met.hist_of(xs, bs, cs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %len_hist(rest, bs, Met.inc_at(cs, Met.bucket_of(bs, x))) : {List.length(&2, Nat, cs) == _ : Nat}
      len_inc(cs, Met.bucket_of(bs, x))

def hist_nth(xs: List<&2, Nat>, +bs: List<&2, Nat>, +cs: List<&2, Nat>, +i: Nat, +hi: {Nat.is_lt(i, List.length(&2, Nat, cs)) == True{} : Bool})
  -> {Nat.add(L.nth_or0(i, cs), cnt(PBk{bs, i}, xs)) == L.nth_or0(i, Met.hist_of(xs, bs, cs)) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, L.nth_or0(i, cs), Nat.add(L.nth_or0(i, cs), 0n), PNat.add_zero(L.nth_or0(i, cs)))
    case Con{+x, +rest}:
      +j = Met.bucket_of(bs, x)
      +cs2 = Met.inc_at(cs, j)
      +n = L.nth_or0(i, cs)
      +e = L.pick(Nat, Nat.is_eq(L.bucket_of(bs, x), i), 1n, 0n)
      +r = cnt(PBk{bs, i}, rest)
      +hi2 = {%len_inc(cs, j) : {Nat.is_lt(i, _) == True{} : Bool}; hi : {Nat.is_lt(i, List.length(&2, Nat, cs2)) == True{} : Bool}}
      %hist_nth(rest, bs, cs2, i, hi2) : {Nat.add(n, Nat.add(e, r)) == _ : Nat}
      %inc_nth(cs, j, i, hi) : {Nat.add(n, Nat.add(e, r)) == Nat.add(_, r) : Nat}
      %bucket_same(bs, x) : {Nat.add(n, Nat.add(e, r)) == Nat.add(Nat.add(L.pick(Nat, Nat.is_eq(_, i), 1n, 0n), n), r) : Nat}
      %PNat.add_swap(e, n, r) : {_ == Nat.add(Nat.add(e, n), r) : Nat}
      PNat.add_assoc(e, n, r)

def len_rep(n: Nat) -> {List.length(&2, Nat, List.replicate(Nat, n, 0n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %len_rep(p) : {1n+List.length(&2, Nat, List.replicate(Nat, p, 0n)) == 1n+_ : Nat}
      {==}

def nth_rep(n: Nat, i: Nat) -> {L.nth_or0(i, List.replicate(Nat, n, 0n)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match i:
        case 0n:
          {==}
        case 1n+ip:
          nth_rep(p, ip)

def c_bs(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {a_bs(a) == L.s_buckets(Met.close(a)) : List<&2, Nat>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          {==}
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def c_hist(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {Met.hist_of(Met.sort(Met.flatten(a_t(a), [])), a_bs(a), List.replicate(Nat, List.length(&2, Nat, a_bs(a)), 0n)) == L.s_hist(Met.close(a)) : List<&2, Nat>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Met.hist_of(Met.sort(Met.flatten(t, [])), bs, List.replicate(Nat, List.length(&2, Nat, bs), 0n))
            == List.replicate(Nat, List.length(&2, Nat, bs), 0n) : List<&2, Nat>}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

# the histogram of a summary of some results
def sum_hist(+bs: List<&2, Nat>, +h: Hit.Hit, +rest: List<&2, Hit.Hit>)
  -> {Met.hist_of(Met.sort(L.lats(Con{h, rest})), bs, List.replicate(Nat, List.length(&2, Nat, bs), 0n)) == L.s_hist(L.summary(bs, Con{h, rest})) : List<&2, Nat>}:
  +A = L.acc_all(Con{h, rest}, Met.empty(bs))
  %c_hist(A, sum_x(bs, h, rest)) : {Met.hist_of(Met.sort(L.lats(Con{h, rest})), bs, List.replicate(Nat, List.length(&2, Nat, bs), 0n)) == _ : List<&2, Nat>}
  %f_bs(Con{h, rest}, Met.empty(bs))
    : {Met.hist_of(Met.sort(L.lats(Con{h, rest})), bs, List.replicate(Nat, List.length(&2, Nat, bs), 0n))
       == Met.hist_of(Met.sort(Met.flatten(a_t(A), [])), _, List.replicate(Nat, List.length(&2, Nat, _), 0n)) : List<&2, Nat>}
  %lats_all(bs, Con{h, rest})
    : {Met.hist_of(Met.sort(L.lats(Con{h, rest})), bs, List.replicate(Nat, List.length(&2, Nat, bs), 0n))
       == Met.hist_of(Met.sort(_), bs, List.replicate(Nat, List.length(&2, Nat, bs), 0n)) : List<&2, Nat>}
  {==}

def L.met_hist(bs, hs, i, h):
  match hs:
    case Nil{}:
      ({==}, (len_rep(List.length(&2, Nat, bs)), nth_rep(List.length(&2, Nat, bs), i)))
    case Con{+x, +rest}:
      +A = L.acc_all(Con{x, rest}, Met.empty(bs))
      +hx = sum_x(bs, x, rest)
      +rep = List.replicate(Nat, List.length(&2, Nat, bs), 0n)
      +sl = Met.sort(L.lats(Con{x, rest}))
      +e1 = {%c_bs(A, hx) : {_ == bs : List<&2, Nat>};
             Equal.sym(List<&2, Nat>, bs, a_bs(A), f_bs(Con{x, rest}, Met.empty(bs)))
             : {L.s_buckets(L.summary(bs, Con{x, rest})) == bs : List<&2, Nat>}}
      +e2 = {%sum_hist(bs, x, rest) : {List.length(&2, Nat, _) == List.length(&2, Nat, bs) : Nat};
             %len_hist(sl, bs, rep) : {_ == List.length(&2, Nat, bs) : Nat};
             len_rep(List.length(&2, Nat, bs))
             : {List.length(&2, Nat, L.s_hist(L.summary(bs, Con{x, rest}))) == List.length(&2, Nat, bs) : Nat}}
      +hi = {%Equal.sym(Nat, List.length(&2, Nat, rep), List.length(&2, Nat, bs), len_rep(List.length(&2, Nat, bs))) : {Nat.is_lt(i, _) == True{} : Bool}; h : {Nat.is_lt(i, List.length(&2, Nat, rep)) == True{} : Bool}}
      +e3 = {%sum_hist(bs, x, rest) : {L.nth_or0(i, _) == L.n_in_bucket(bs, i, L.lats(Con{x, rest})) : Nat};
             %hist_nth(sl, bs, rep, i, hi) : {_ == L.n_in_bucket(bs, i, L.lats(Con{x, rest})) : Nat};
             %Equal.sym(Nat, L.nth_or0(i, rep), 0n, nth_rep(List.length(&2, Nat, bs), i)) : {Nat.add(_, cnt(PBk{bs, i}, sl)) == L.n_in_bucket(bs, i, L.lats(Con{x, rest})) : Nat};
             %Equal.sym(Nat, L.n_in_bucket(bs, i, L.lats(Con{x, rest})), cnt(PBk{bs, i}, L.lats(Con{x, rest})), nib_cnt(bs, i, L.lats(Con{x, rest}))) : {cnt(PBk{bs, i}, sl) == _ : Nat};
             Equal.sym(Nat, cnt(PBk{bs, i}, L.lats(Con{x, rest})), cnt(PBk{bs, i}, sl), cnt_sort(L.lats(Con{x, rest}), PBk{bs, i}))
             : {L.nth_or0(i, L.s_hist(L.summary(bs, Con{x, rest}))) == L.n_in_bucket(bs, i, L.lats(Con{x, rest})) : Nat}}
      (e1, (e2, e3))

# =====================================================================
# Latencies: the extremes
# =====================================================================

def x_lmin(x: Met.Ext) -> Nat:
  match x:
    case Met.NoExt{}:
      0n
    case Met.Ext{a, b, c, d, e, f, g, h}:
      a

def x_lmax(x: Met.Ext) -> Nat:
  match x:
    case Met.NoExt{}:
      0n
    case Met.Ext{a, b, c, d, e, f, g, h}:
      b

def pick_succ(c: Bool, -a: Nat, -b: Nat) -> {1n+Met.pick(Nat, c, a, b) == Met.pick(Nat, c, 1n+a, 1n+b) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def nmin_min(a: Nat, b: Nat) -> {Nat.min(a, b) == Met.nmin(a, b) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          {==}
    case 1n+(+ap):
      match b:
        case 0n:
          {==}
        case 1n+(+bp):
          %Equal.sym(Nat, Nat.min(ap, bp), Met.nmin(ap, bp), nmin_min(ap, bp)) : {1n+_ == Met.pick(Nat, Nat.is_le(ap, bp), 1n+ap, 1n+bp) : Nat}
          pick_succ(Nat.is_le(ap, bp), ap, bp)

def nmax_max(a: Nat, b: Nat) -> {Nat.max(a, b) == Met.nmax(a, b) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          {==}
    case 1n+(+ap):
      match b:
        case 0n:
          {==}
        case 1n+(+bp):
          %Equal.sym(Nat, Nat.max(ap, bp), Met.nmax(ap, bp), nmax_max(ap, bp)) : {1n+_ == Met.pick(Nat, Nat.is_le(ap, bp), 1n+bp, 1n+ap) : Nat}
          pick_succ(Nat.is_le(ap, bp), bp, ap)

def add_lmin(a: Met.Acc, h: Hit.Hit, +hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {Nat.min(x_lmin(a_x(a)), L.h_lat(h)) == x_lmin(a_x(Met.add(a, h))) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Nat.min(0n, L.h_lat(h)) == x_lmin(a_x(Met.add(Met.Acc{bs, n, ok, cs, es, l, i, o, Met.NoExt{}, t}, h))) : Nat}, no_ft(hx))
        case Met.Ext{+a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          match h:
            case Hit.Hit{ha, q, c, tt, +lat, bo, bi, e, b, m, u, hs}:
              match tt:
                case Civil.Time{s0, ns0, off}:
                  nmin_min(a1, lat)

def add_lmax(a: Met.Acc, h: Hit.Hit, +hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {Nat.max(x_lmax(a_x(a)), L.h_lat(h)) == x_lmax(a_x(Met.add(a, h))) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Nat.max(0n, L.h_lat(h)) == x_lmax(a_x(Met.add(Met.Acc{bs, n, ok, cs, es, l, i, o, Met.NoExt{}, t}, h))) : Nat}, no_ft(hx))
        case Met.Ext{a1, +b1, es1, en1, ls1, ln1, xs1, xn1}:
          match h:
            case Hit.Hit{ha, q, c, tt, +lat, bo, bi, e, b, m, u, hs}:
              match tt:
                case Civil.Time{s0, ns0, off}:
                  nmax_max(b1, lat)

def f_lmin(hs: List<&2, Hit.Hit>, +a: Met.Acc, +hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {L.min_of.go(L.lats(hs), x_lmin(a_x(a))) == x_lmin(a_x(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %f_lmin(rest, Met.add(a, h), add_x(a, h)) : {L.min_of.go(L.lats(Con{h, rest}), x_lmin(a_x(a))) == _ : Nat}
      %add_lmin(a, h, hx) : {L.min_of.go(L.lats(rest), Nat.min(x_lmin(a_x(a)), L.h_lat(h))) == L.min_of.go(L.lats(rest), _) : Nat}
      {==}

def f_lmax(hs: List<&2, Hit.Hit>, +a: Met.Acc, +hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {L.max_of.go(L.lats(hs), x_lmax(a_x(a))) == x_lmax(a_x(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %f_lmax(rest, Met.add(a, h), add_x(a, h)) : {L.max_of.go(L.lats(Con{h, rest}), x_lmax(a_x(a))) == _ : Nat}
      %add_lmax(a, h, hx) : {L.max_of.go(L.lats(rest), Nat.max(x_lmax(a_x(a)), L.h_lat(h))) == L.max_of.go(L.lats(rest), _) : Nat}
      {==}

def first_lmin(+bs: List<&2, Nat>, h: Hit.Hit) -> {L.h_lat(h) == x_lmin(a_x(Met.add(Met.empty(bs), h))) : Nat}:
  match h:
    case Hit.Hit{ha, q, c, tt, lat, bo, bi, e, b, m, u, hs}:
      match tt:
        case Civil.Time{s0, ns0, off}:
          {==}

def first_lmax(+bs: List<&2, Nat>, h: Hit.Hit) -> {L.h_lat(h) == x_lmax(a_x(Met.add(Met.empty(bs), h))) : Nat}:
  match h:
    case Hit.Hit{ha, q, c, tt, lat, bo, bi, e, b, m, u, hs}:
      match tt:
        case Civil.Time{s0, ns0, off}:
          {==}

def c_lmin(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {x_lmin(a_x(a)) == L.s_lat_min(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          {==}
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def c_lmax(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {x_lmax(a_x(a)) == L.s_lat_max(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          {==}
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def sum_lmin(+bs: List<&2, Nat>, +h: Hit.Hit, +rest: List<&2, Hit.Hit>)
  -> {L.s_lat_min(L.summary(bs, Con{h, rest})) == L.min_of(L.h_lat(h), L.lats(rest)) : Nat}:
  +A = L.acc_all(Con{h, rest}, Met.empty(bs))
  %c_lmin(A, sum_x(bs, h, rest)) : {_ == L.min_of(L.h_lat(h), L.lats(rest)) : Nat}
  %f_lmin(rest, Met.add(Met.empty(bs), h), add_x(Met.empty(bs), h)) : {_ == L.min_of(L.h_lat(h), L.lats(rest)) : Nat}
  %first_lmin(bs, h) : {L.min_of.go(L.lats(rest), _) == L.min_of(L.h_lat(h), L.lats(rest)) : Nat}
  {==}

def sum_lmax(+bs: List<&2, Nat>, +h: Hit.Hit, +rest: List<&2, Hit.Hit>)
  -> {L.s_lat_max(L.summary(bs, Con{h, rest})) == L.max_of(L.h_lat(h), L.lats(rest)) : Nat}:
  +A = L.acc_all(Con{h, rest}, Met.empty(bs))
  %c_lmax(A, sum_x(bs, h, rest)) : {_ == L.max_of(L.h_lat(h), L.lats(rest)) : Nat}
  %f_lmax(rest, Met.add(Met.empty(bs), h), add_x(Met.empty(bs), h)) : {_ == L.max_of(L.h_lat(h), L.lats(rest)) : Nat}
  %first_lmax(bs, h) : {L.max_of.go(L.lats(rest), _) == L.max_of(L.h_lat(h), L.lats(rest)) : Nat}
  {==}

# =====================================================================
# More Nat order
# =====================================================================

def le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def lt_irr(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_irr(p)

def le_trans(a: Nat, b: Nat, c: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      le_zero(c)
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, no_ft(h1))
        case 1n+bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, no_ft(h2))
            case 1n+cp:
              le_trans(ap, bp, cp, h1, h2)

# not a <= b: b < a, so b <= a
def nle_le(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_le(b, 0n) == True{} : Bool}, no_ft(Equal.trans(Bool, False{}, Nat.is_le(0n, b), True{}, Equal.sym(Bool, Nat.is_le(0n, b), False{}, h), le_zero(b))))
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          nle_le(ap, bp, h)

# not a <= b: b < a
def nle_lt(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_lt(b, 0n) == True{} : Bool}, no_ft(Equal.trans(Bool, False{}, Nat.is_le(0n, b), True{}, Equal.sym(Bool, Nat.is_le(0n, b), False{}, h), le_zero(b))))
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          nle_lt(ap, bp, h)

def le_nlt(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 1n+ap) == False{} : Bool}, no_ft(h))
        case 1n+bp:
          le_nlt(ap, bp, h)

def le_succ(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          le_succ(ap, bp, h)

# a <= b: a < 1 + b
def le_lt_succ(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, 1n) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          le_lt_succ(ap, bp, h)

# a < b: 1 + a <= b
def lt_le_succ(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          le_zero(bp)
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(2n+ap, 0n) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          lt_le_succ(ap, bp, h)

def le_add(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      le_zero(b)
    case 1n+ap:
      le_add(ap, b)

def le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(b, a)) == True{} : Bool}:
  %PNat.add_comm(a, b) : {Nat.is_le(a, _) == True{} : Bool}
  le_add(a, b)

def le_add_mono(c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+cp:
      le_add_mono(cp, a, b, h)

def lt_add_mono(c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+cp:
      lt_add_mono(cp, a, b, h)

def le_add_mono_r(a: Nat, b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  match a:
    case 0n:
      le_add_l(c, b)
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.add(1n+ap, c), c) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          le_add_mono_r(ap, bp, c, h)

def mul_le_mono(a: Nat, b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  match a:
    case 0n:
      le_zero(Nat.mul(b, c))
    case 1n+(+ap):
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.mul(1n+ap, c), 0n) == True{} : Bool}, no_ft(h))
        case 1n+(+bp):
          le_add_mono(c, Nat.mul(ap, c), Nat.mul(bp, c), mul_le_mono(ap, bp, c, h))

def le_rw(-a: Nat, -b: Nat, -c: Nat, e: {b == c : Nat}, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

# ---------------------------------------------------------------------
# Nearest rank: rank(q, n) < n for q <= 100 and n > 0
# ---------------------------------------------------------------------

def div_bound.of(c: Bool, +x: Nat, +b: Nat, +bn: Nat, +ec: {Nat.is_le(Nat.div(x, 1n+b), bn) == c : Bool},
  +hx: {Nat.is_lt(x, Nat.mul(1n+bn, 1n+b)) == True{} : Bool}) -> {Nat.is_le(Nat.div(x, 1n+b), bn) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      +d = Nat.div(x, 1n+b)
      +r = Nat.mod(x, 1n+b)
      +h1 = mul_le_mono(1n+bn, d, 1n+b, lt_le_succ(bn, d, nle_lt(d, bn, ec)))
      +h2 = le_trans(Nat.mul(1n+bn, 1n+b), Nat.mul(d, 1n+b), Nat.add(Nat.mul(d, 1n+b), r), h1, le_add(Nat.mul(d, 1n+b), r))
      +h3 = le_rw(Nat.mul(1n+bn, 1n+b), Nat.add(Nat.mul(d, 1n+b), r), x, Equal.sym(Nat, x, Nat.add(Nat.mul(d, 1n+b), r), PNat.div_mod_eq(x, b)), h2)
      Empty.absurd({Nat.is_le(Nat.div(x, 1n+b), bn) == True{} : Bool}, no_ft(Equal.trans(Bool, False{}, Nat.is_lt(x, Nat.mul(1n+bn, 1n+b)), True{},
        Equal.sym(Bool, Nat.is_lt(x, Nat.mul(1n+bn, 1n+b)), False{}, le_nlt(Nat.mul(1n+bn, 1n+b), x, h3)), hx)))

def div_bound(+x: Nat, +b: Nat, +bn: Nat, +hx: {Nat.is_lt(x, Nat.mul(1n+bn, 1n+b)) == True{} : Bool})
  -> {Nat.is_le(Nat.div(x, 1n+b), bn) == True{} : Bool}:
  div_bound.of(Nat.is_le(Nat.div(x, 1n+b), bn), x, b, bn, {==}, hx)

def sub1_lt(d: Nat, +n: Nat, +h: {Nat.is_le(d, 1n+n) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(d, 1n), 1n+n) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+(+dp):
      %sub_zero(dp) : {Nat.is_lt(_, 1n+n) == True{} : Bool}
      le_lt_succ(dp, n, h)

def rank_lt(+q: Nat, +n: Nat, +hq: {Nat.is_le(q, 100n) == True{} : Bool}) -> {Nat.is_lt(L.rank(q, 1n+n), 1n+n) == True{} : Bool}:
  +bn = {1n+n : Nat}
  +x = Nat.add(Nat.mul(q, bn), 99n)
  +h1 = le_add_mono_r(Nat.mul(q, bn), Nat.mul(100n, bn), 99n, mul_le_mono(q, 100n, bn, hq))
  +h2 = lt_add_mono(Nat.mul(100n, bn), 99n, 100n, {==})
  +h3 = n_le_lt(x, Nat.add(Nat.mul(100n, bn), 99n), Nat.add(Nat.mul(100n, bn), 100n), h1, h2)
  +h4 = {%PNat.add_comm(Nat.mul(bn, 100n), 100n) : {Nat.is_lt(x, _) == True{} : Bool};
         %PNat.mul_comm(100n, bn) : {Nat.is_lt(x, Nat.add(_, 100n)) == True{} : Bool};
         h3 : {Nat.is_lt(x, Nat.mul(1n+bn, 100n)) == True{} : Bool}}
  sub1_lt(Nat.div(x, 100n), n, div_bound(x, 99n, bn, h4))

# =====================================================================
# The merge sort sorts
# =====================================================================

# xs ascending, all at least b
def sb(xs: List<&2, Nat>, +b: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(Nat.is_le(b, x), sb(rest, x))

def sb_head(+b: Nat, +x: Nat, +r: List<&2, Nat>, +h: {sb(Con{x, r}, b) == True{} : Bool}) -> {Nat.is_le(b, x) == True{} : Bool}:
  and_l(Nat.is_le(b, x), sb(r, x), h)

def sb_tail(+b: Nat, +x: Nat, +r: List<&2, Nat>, +h: {sb(Con{x, r}, b) == True{} : Bool}) -> {sb(r, x) == True{} : Bool}:
  and_r(Nat.is_le(b, x), sb(r, x), h)

def sm_step(le: Bool, +x: Nat, +xr: List<&2, Nat>, +y: Nat, +yr: List<&2, Nat>, +g: Nat, +k: Nat, +b: Nat,
  +ele: {Nat.is_le(x, y) == le : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, Nat, xr), 1n+List.length(&2, Nat, yr)), k) == g : Nat},
  +hx: {sb(Con{x, xr}, b) == True{} : Bool}, +hy: {sb(Con{y, yr}, b) == True{} : Bool},
  ih: @xs2: List<&2, Nat> -> @ys2: List<&2, Nat> -> @k3: Nat -> @b2: Nat
    -> {Nat.add(Nat.add(List.length(&2, Nat, xs2), List.length(&2, Nat, ys2)), k3) == g : Nat}
    -> {sb(xs2, b2) == True{} : Bool} -> {sb(ys2, b2) == True{} : Bool}
    -> {sb(Met.nmerge(g, xs2, ys2), b2) == True{} : Bool})
  -> {sb(Con{Met.pick(Nat, le, x, y), Met.nmerge(g, Met.pick(List<&2, Nat>, le, xr, Con{x, xr}), Met.pick(List<&2, Nat>, le, Con{y, yr}, yr))}, b) == True{} : Bool}:
  match le:
    case True{}:
      and_i(Nat.is_le(b, x), sb(Met.nmerge(g, xr, Con{y, yr}), x), sb_head(b, x, xr, hx),
        ih(xr, Con{y, yr}, k, x, hg, sb_tail(b, x, xr, hx), and_i(Nat.is_le(x, y), sb(yr, y), ele, sb_tail(b, y, yr, hy))))
    case False{}:
      and_i(Nat.is_le(b, y), sb(Met.nmerge(g, Con{x, xr}, yr), y), sb_head(b, y, yr, hy),
        ih(Con{x, xr}, yr, k, y, fuel_gt(List.length(&2, Nat, xr), List.length(&2, Nat, yr), k, g, hg),
          and_i(Nat.is_le(y, x), sb(xr, x), nle_le(x, y, ele), sb_tail(b, x, xr, hx)), sb_tail(b, y, yr, hy)))

def sm_go(f: Nat, xs: List<&2, Nat>, ys: List<&2, Nat>, +k: Nat, +b: Nat,
  +hf: {Nat.add(Nat.add(List.length(&2, Nat, xs), List.length(&2, Nat, ys)), k) == f : Nat},
  +hx: {sb(xs, b) == True{} : Bool}, +hy: {sb(ys, b) == True{} : Bool})
  -> {sb(Met.nmerge(f, xs, ys), b) == True{} : Bool}:
  match f:
    case 0n:
      match xs:
        case Nil{}:
          match ys:
            case Nil{}:
              {==}
            case Con{y, yr}:
              Empty.absurd({sb(Con{y, yr}, b) == True{} : Bool}, PNat.no_zero(Nat.add(List.length(&2, Nat, yr), k), hf))
        case Con{x, xr}:
          Empty.absurd({sb(List.append(&2, Nat, Con{x, xr}, ys), b) == True{} : Bool},
            PNat.no_zero(Nat.add(Nat.add(List.length(&2, Nat, xr), List.length(&2, Nat, ys)), k), hf))
    case 1n+(+g):
      match xs:
        case Nil{}:
          hy
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              hx
            case Con{+y, +yr}:
              sm_step(Nat.is_le(x, y), x, xr, y, yr, g, k, b, {==},
                PNat.succ_inj(Nat.add(Nat.add(List.length(&2, Nat, xr), 1n+List.length(&2, Nat, yr)), k), g, hf), hx, hy,
                xs2 => ys2 => k3 => b2 => h1 => h2 => h3 => sm_go(g, xs2, ys2, k3, b2, h1, h2, h3))

# ---------------------------------------------------------------------
# lengths and halves
# ---------------------------------------------------------------------

def sub_add(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.add(1n+ap, 0n) == 0n : Nat}, no_ft(h))
        case 1n+bp:
          succ_eq(Nat.add(ap, Nat.sub(bp, ap)), bp, sub_add(ap, bp, h))

def len_take(xs: List<&2, Nat>, h: Nat, +hh: {Nat.is_le(h, List.length(&2, Nat, xs)) == True{} : Bool})
  -> {List.length(&2, Nat, List.take(&2, Nat, xs, h)) == h : Nat}:
  match xs:
    case Nil{}:
      match h:
        case 0n:
          {==}
        case 1n+hp:
          Empty.absurd({0n == 1n+hp : Nat}, no_ft(hh))
    case Con{x, rest}:
      match h:
        case 0n:
          {==}
        case 1n+hp:
          succ_eq(List.length(&2, Nat, List.take(&2, Nat, rest, hp)), hp, len_take(rest, hp, hh))

def len_drop(xs: List<&2, Nat>, h: Nat) -> {List.length(&2, Nat, List.drop(&2, Nat, xs, h)) == Nat.sub(List.length(&2, Nat, xs), h) : Nat}:
  match xs:
    case Nil{}:
      match h:
        case 0n:
          {==}
        case 1n+hp:
          {==}
    case Con{x, rest}:
      match h:
        case 0n:
          {==}
        case 1n+hp:
          len_drop(rest, hp)

def len_ms(+f: Nat, +s: Bool, +xs: List<&2, Nat>, +n: Nat) -> {List.length(&2, Nat, xs) == List.length(&2, Nat, Met.msort(f, s, xs, n)) : Nat}:
  %cnt_all(Met.msort(f, s, xs, n)) : {List.length(&2, Nat, xs) == _ : Nat}
  %cnt_all(xs) : {_ == cnt(PAll{}, Met.msort(f, s, xs, n)) : Nat}
  cnt_msort(f, s, xs, n, PAll{})

def div_pos.of(d: Nat, +x: Nat, +b: Nat, +ed: {Nat.div(x, 1n+b) == d : Nat}, +hx: {Nat.is_le(1n+b, x) == True{} : Bool})
  -> {Nat.is_le(1n, Nat.div(x, 1n+b)) == True{} : Bool}:
  match d:
    case 0n:
      +e = {%ed : {x == Nat.add(Nat.mul(_, 1n+b), Nat.mod(x, 1n+b)) : Nat}; PNat.div_mod_eq(x, b) : {x == Nat.mod(x, 1n+b) : Nat}}
      +hl = {%Equal.sym(Nat, x, Nat.mod(x, 1n+b), e) : {Nat.is_lt(_, 1n+b) == True{} : Bool}; PNat.mod_lt(x, b) : {Nat.is_lt(x, 1n+b) == True{} : Bool}}
      Empty.absurd({Nat.is_le(1n, Nat.div(x, 1n+b)) == True{} : Bool}, no_ft(Equal.trans(Bool, False{}, Nat.is_lt(x, 1n+b), True{},
        Equal.sym(Bool, Nat.is_lt(x, 1n+b), False{}, le_nlt(1n+b, x, hx)), hl)))
    case 1n+(+dp):
      %Equal.sym(Nat, Nat.div(x, 1n+b), 1n+dp, ed) : {Nat.is_le(1n, _) == True{} : Bool}
      le_zero(dp)

# n >= 2: its half h has 1 <= h, h <= n and 1 + h <= n
def half_pos(+n: Nat, +hn: {Nat.is_le(2n, n) == True{} : Bool}) -> {Nat.is_le(1n, Nat.div(n, 2n)) == True{} : Bool}:
  div_pos.of(Nat.div(n, 2n), n, 1n, {==}, hn)

def twice_le(+n: Nat) -> {Nat.is_le(Nat.mul(Nat.div(n, 2n), 2n), n) == True{} : Bool}:
  +h = Nat.div(n, 2n)
  le_rw(Nat.mul(h, 2n), Nat.add(Nat.mul(h, 2n), Nat.mod(n, 2n)), n,
    Equal.sym(Nat, n, Nat.add(Nat.mul(h, 2n), Nat.mod(n, 2n)), PNat.div_mod_eq(n, 1n)), le_add(Nat.mul(h, 2n), Nat.mod(n, 2n)))

def two_h(+h: Nat) -> {Nat.add(h, h) == Nat.mul(h, 2n) : Nat}:
  %PNat.mul_comm(2n, h) : {Nat.add(h, h) == _ : Nat}
  %PNat.add_zero(h) : {Nat.add(h, h) == Nat.add(h, _) : Nat}
  {==}

def half_le(+n: Nat) -> {Nat.is_le(Nat.div(n, 2n), n) == True{} : Bool}:
  +h = Nat.div(n, 2n)
  le_trans(h, Nat.mul(h, 2n), n, le_rw(h, Nat.add(h, h), Nat.mul(h, 2n), two_h(h), le_add(h, h)), twice_le(n))

def half_lt(+n: Nat, +hn: {Nat.is_le(2n, n) == True{} : Bool}) -> {Nat.is_le(1n+Nat.div(n, 2n), n) == True{} : Bool}:
  +h = Nat.div(n, 2n)
  +a = {%PNat.add_comm(h, 1n) : {Nat.is_le(_, Nat.add(h, h)) == True{} : Bool};
        le_add_mono(h, 1n, h, half_pos(n, hn)) : {Nat.is_le(1n+h, Nat.add(h, h)) == True{} : Bool}}
  le_trans(1n+h, Nat.mul(h, 2n), n, le_rw(1n+h, Nat.add(h, h), Nat.mul(h, 2n), two_h(h), a), twice_le(n))

def rest_lt(+n: Nat, +hn: {Nat.is_le(2n, n) == True{} : Bool}) -> {Nat.is_le(1n+Nat.sub(n, Nat.div(n, 2n)), n) == True{} : Bool}:
  +h = Nat.div(n, 2n)
  +m = Nat.sub(n, h)
  +a = le_add_mono_r(1n, h, m, half_pos(n, hn))
  le_rw(1n+m, Nat.add(h, m), n, sub_add(h, n, half_le(n)), a)

def le0(n: Nat, +h: {Nat.is_le(n, 0n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, no_ft(h))

def ms(f: Nat, s: Bool, +xs: List<&2, Nat>, +n: Nat, +es: {Nat.is_le(n, 1n) == s : Bool},
  +hl: {List.length(&2, Nat, xs) == n : Nat}, +hf: {Nat.is_le(n, f) == True{} : Bool})
  -> {sb(Met.msort(f, s, xs, n), 0n) == True{} : Bool}:
  match f:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{x, r}:
          Empty.absurd({sb(Con{x, r}, 0n) == True{} : Bool},
            PNat.no_zero(List.length(&2, Nat, r), Equal.trans(Nat, 1n+List.length(&2, Nat, r), n, 0n, hl, le0(n, hf))))
    case 1n+(+g):
      match s:
        case True{}:
          match xs:
            case Nil{}:
              {==}
            case Con{+x, +r}:
              match r:
                case Nil{}:
                  and_i(Nat.is_le(0n, x), True{}, le_zero(x), {==})
                case Con{y, r2}:
                  Empty.absurd({sb(Con{x, Con{y, r2}}, 0n) == True{} : Bool},
                    no_ft(Equal.trans(Bool, Nat.is_le(2n+List.length(&2, Nat, r2), 1n), Nat.is_le(n, 1n), True{},
                      Equal.cong(Nat, Bool, v => Nat.is_le(v, 1n), 2n+List.length(&2, Nat, r2), n, hl), es)))
        case False{}:
          +hn = lt_le_succ(1n, n, nle_lt(n, 1n, es))
          +h = Nat.div(n, 2n)
          +m = Nat.sub(n, h)
          +ta = List.take(&2, Nat, xs, h)
          +dr = List.drop(&2, Nat, xs, h)
          +a = Met.msort(g, Nat.is_le(h, 1n), ta, h)
          +b = Met.msort(g, Nat.is_le(m, 1n), dr, m)
          +lta = len_take(xs, h, le_rw(h, n, List.length(&2, Nat, xs), Equal.sym(Nat, List.length(&2, Nat, xs), n, hl), half_le(n)))
          +ldr = {%hl : {List.length(&2, Nat, dr) == Nat.sub(_, h) : Nat}; len_drop(xs, h) : {List.length(&2, Nat, dr) == m : Nat}}
          +ha = ms(g, Nat.is_le(h, 1n), ta, h, {==}, lta, le_trans(1n+h, n, 1n+g, half_lt(n, hn), hf))
          +hb = ms(g, Nat.is_le(m, 1n), dr, m, {==}, ldr, le_trans(1n+m, n, 1n+g, rest_lt(n, hn), hf))
          +ea = Equal.trans(Nat, h, List.length(&2, Nat, ta), List.length(&2, Nat, a), Equal.sym(Nat, List.length(&2, Nat, ta), h, lta), len_ms(g, Nat.is_le(h, 1n), ta, h))
          +eb = Equal.trans(Nat, m, List.length(&2, Nat, dr), List.length(&2, Nat, b), Equal.sym(Nat, List.length(&2, Nat, dr), m, ldr), len_ms(g, Nat.is_le(m, 1n), dr, m))
          +fu = {%ea : {Nat.add(Nat.add(_, List.length(&2, Nat, b)), 0n) == n : Nat};
                 %eb : {Nat.add(Nat.add(h, _), 0n) == n : Nat};
                 %PNat.add_zero(Nat.add(h, m)) : {_ == n : Nat};
                 sub_add(h, n, half_le(n)) : {Nat.add(Nat.add(List.length(&2, Nat, a), List.length(&2, Nat, b)), 0n) == n : Nat}}
          sm_go(n, a, b, 0n, 0n, fu, ha, hb)

def sort_sorted(+xs: List<&2, Nat>) -> {sb(Met.sort(xs), 0n) == True{} : Bool}:
  ms(List.length(&2, Nat, xs), Nat.is_le(List.length(&2, Nat, xs), 1n), xs, List.length(&2, Nat, xs), {==}, {==}, le_refl(List.length(&2, Nat, xs)))

# ---------------------------------------------------------------------
# In a sorted list, the k-th is the rank-k element
# ---------------------------------------------------------------------

def sb_weak(r: List<&2, Nat>, +b: Nat, +y: Nat, +h1: {Nat.is_le(b, y) == True{} : Bool}, +h2: {sb(r, y) == True{} : Bool})
  -> {sb(r, b) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+z, +rest}:
      and_i(Nat.is_le(b, z), sb(rest, z), le_trans(b, y, z, h1, sb_head(y, z, rest, h2)), sb_tail(y, z, rest, h2))

def sb_le_nth(ys: List<&2, Nat>, k: Nat, +b: Nat, +hs: {sb(ys, b) == True{} : Bool}, +hk: {Nat.is_lt(k, List.length(&2, Nat, ys)) == True{} : Bool})
  -> {Nat.is_le(b, L.nth_or0(k, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Nat.is_le(b, L.nth_or0(k, [])) == True{} : Bool}, PNat.lt_zero(k, hk))
    case Con{+y, +r}:
      match k:
        case 0n:
          sb_head(b, y, r, hs)
        case 1n+(+kp):
          le_trans(b, y, L.nth_or0(kp, r), sb_head(b, y, r, hs), sb_le_nth(r, kp, y, sb_tail(b, y, r, hs), hk))

def sb_less0(ys: List<&2, Nat>, +b: Nat, +hs: {sb(ys, b) == True{} : Bool}) -> {0n == L.n_less(b, ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      %Equal.sym(Bool, Nat.is_lt(y, b), False{}, le_nlt(b, y, sb_head(b, y, r, hs))) : {0n == Nat.add(L.pick(Nat, _, 1n, 0n), L.n_less(b, r)) : Nat}
      sb_less0(r, b, sb_weak(r, b, y, sb_head(b, y, r, hs), sb_tail(b, y, r, hs)))

def pick_le(c: Bool, +x: Nat, +k: Nat, +h: {Nat.is_le(x, k) == True{} : Bool}) -> {Nat.is_le(Nat.add(L.pick(Nat, c, 1n, 0n), x), 1n+k) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      le_succ(x, k, h)

def rk_less(ys: List<&2, Nat>, k: Nat, +b: Nat, +hs: {sb(ys, b) == True{} : Bool}, +hk: {Nat.is_lt(k, List.length(&2, Nat, ys)) == True{} : Bool})
  -> {Nat.is_le(L.n_less(L.nth_or0(k, ys), ys), k) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Nat.is_le(L.n_less(L.nth_or0(k, []), []), k) == True{} : Bool}, PNat.lt_zero(k, hk))
    case Con{+y, +r}:
      match k:
        case 0n:
          %Equal.sym(Bool, Nat.is_lt(y, y), False{}, lt_irr(y)) : {Nat.is_le(Nat.add(L.pick(Nat, _, 1n, 0n), L.n_less(y, r)), 0n) == True{} : Bool}
          %sb_less0(r, y, sb_tail(b, y, r, hs)) : {Nat.is_le(_, 0n) == True{} : Bool}
          {==}
        case 1n+(+kp):
          pick_le(Nat.is_lt(y, L.nth_or0(kp, r)), L.n_less(L.nth_or0(kp, r), r), kp, rk_less(r, kp, y, sb_tail(b, y, r, hs), hk))

def rk_upto(ys: List<&2, Nat>, k: Nat, +b: Nat, +hs: {sb(ys, b) == True{} : Bool}, +hk: {Nat.is_lt(k, List.length(&2, Nat, ys)) == True{} : Bool})
  -> {Nat.is_lt(k, L.n_upto(L.nth_or0(k, ys), ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({Nat.is_lt(k, L.n_upto(L.nth_or0(k, []), [])) == True{} : Bool}, PNat.lt_zero(k, hk))
    case Con{+y, +r}:
      match k:
        case 0n:
          %Equal.sym(Bool, Nat.is_le(y, y), True{}, le_refl(y)) : {Nat.is_lt(0n, Nat.add(L.pick(Nat, _, 1n, 0n), L.n_upto(y, r))) == True{} : Bool}
          {==}
        case 1n+(+kp):
          +p = L.nth_or0(kp, r)
          %Equal.sym(Bool, Nat.is_le(y, p), True{}, sb_le_nth(r, kp, y, sb_tail(b, y, r, hs), hk))
            : {Nat.is_lt(1n+kp, Nat.add(L.pick(Nat, _, 1n, 0n), L.n_upto(p, r))) == True{} : Bool}
          rk_upto(r, kp, y, sb_tail(b, y, r, hs), hk)

def len_lats(hs: List<&2, Hit.Hit>) -> {List.length(&2, Nat, L.lats(hs)) == List.length(&2, Hit.Hit, hs) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      succ_eq(List.length(&2, Nat, L.lats(rest)), List.length(&2, Hit.Hit, rest), len_lats(rest))

# the rank-k element of the sorted latencies is a rank-k latency
def rank_ok(+q: Nat, +xs: List<&2, Nat>, +n: Nat, +hlen: {List.length(&2, Nat, xs) == 1n+n : Nat}, +hq: {Nat.is_le(q, 100n) == True{} : Bool})
  -> {L.is_rank(L.nth_or0(L.rank(q, 1n+n), Met.sort(xs)), L.rank(q, 1n+n), xs) == True{} : Bool}:
  +ys = Met.sort(xs)
  +k = L.rank(q, 1n+n)
  +p = L.nth_or0(k, ys)
  +el = Equal.trans(Nat, L.n_less(p, ys), cnt(PLt{p}, ys), L.n_less(p, xs), n_less_cnt(p, ys),
          Equal.trans(Nat, cnt(PLt{p}, ys), cnt(PLt{p}, xs), L.n_less(p, xs),
            Equal.sym(Nat, cnt(PLt{p}, xs), cnt(PLt{p}, ys), cnt_sort(xs, PLt{p})), Equal.sym(Nat, L.n_less(p, xs), cnt(PLt{p}, xs), n_less_cnt(p, xs))))
  +eu = Equal.trans(Nat, L.n_upto(p, ys), cnt(PLe{p}, ys), L.n_upto(p, xs), n_upto_cnt(p, ys),
          Equal.trans(Nat, cnt(PLe{p}, ys), cnt(PLe{p}, xs), L.n_upto(p, xs),
            Equal.sym(Nat, cnt(PLe{p}, xs), cnt(PLe{p}, ys), cnt_sort(xs, PLe{p})), Equal.sym(Nat, L.n_upto(p, xs), cnt(PLe{p}, xs), n_upto_cnt(p, xs))))
  +hk = {%len_sort(xs) : {Nat.is_lt(k, _) == True{} : Bool};
         %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+n, hlen) : {Nat.is_lt(k, _) == True{} : Bool};
         rank_lt(q, n, hq) : {Nat.is_lt(k, List.length(&2, Nat, ys)) == True{} : Bool}}
  %el : {Bool.and(Nat.is_le(_, k), Nat.is_lt(k, L.n_upto(p, xs))) == True{} : Bool}
  %eu : {Bool.and(Nat.is_le(L.n_less(p, ys), k), Nat.is_lt(k, _)) == True{} : Bool}
  and_i(Nat.is_le(L.n_less(p, ys), k), Nat.is_lt(k, L.n_upto(p, ys)), rk_less(ys, k, 0n, sort_sorted(xs), hk), rk_upto(ys, k, 0n, sort_sorted(xs), hk))

def c_p50(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {L.nth_or0(L.rank(50n, a_n(a)), Met.sort(Met.flatten(a_t(a), []))) == L.s_p50(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({L.nth_or0(L.rank(50n, n), Met.sort(Met.flatten(t, []))) == 0n : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def sum_p50(+bs: List<&2, Nat>, +h: Hit.Hit, +rest: List<&2, Hit.Hit>)
  -> {L.is_rank(L.s_p50(L.summary(bs, Con{h, rest})), L.rank(50n, 1n+List.length(&2, Hit.Hit, rest)), L.lats(Con{h, rest})) == True{} : Bool}:
  +A = L.acc_all(Con{h, rest}, Met.empty(bs))
  +k = L.rank(50n, 1n+List.length(&2, Hit.Hit, rest))
  %c_p50(A, sum_x(bs, h, rest)) : {L.is_rank(_, k, L.lats(Con{h, rest})) == True{} : Bool}
  %f_n(Con{h, rest}, Met.empty(bs)) : {L.is_rank(L.nth_or0(L.rank(50n, _), Met.sort(Met.flatten(a_t(A), []))), k, L.lats(Con{h, rest})) == True{} : Bool}
  %lats_all(bs, Con{h, rest}) : {L.is_rank(L.nth_or0(k, Met.sort(_)), k, L.lats(Con{h, rest})) == True{} : Bool}
  rank_ok(50n, L.lats(Con{h, rest}), List.length(&2, Hit.Hit, rest), succ_eq(List.length(&2, Nat, L.lats(rest)), List.length(&2, Hit.Hit, rest), len_lats(rest)), {==})

def c_p90(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {L.nth_or0(L.rank(90n, a_n(a)), Met.sort(Met.flatten(a_t(a), []))) == L.s_p90(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({L.nth_or0(L.rank(90n, n), Met.sort(Met.flatten(t, []))) == 0n : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def sum_p90(+bs: List<&2, Nat>, +h: Hit.Hit, +rest: List<&2, Hit.Hit>)
  -> {L.is_rank(L.s_p90(L.summary(bs, Con{h, rest})), L.rank(90n, 1n+List.length(&2, Hit.Hit, rest)), L.lats(Con{h, rest})) == True{} : Bool}:
  +A = L.acc_all(Con{h, rest}, Met.empty(bs))
  +k = L.rank(90n, 1n+List.length(&2, Hit.Hit, rest))
  %c_p90(A, sum_x(bs, h, rest)) : {L.is_rank(_, k, L.lats(Con{h, rest})) == True{} : Bool}
  %f_n(Con{h, rest}, Met.empty(bs)) : {L.is_rank(L.nth_or0(L.rank(90n, _), Met.sort(Met.flatten(a_t(A), []))), k, L.lats(Con{h, rest})) == True{} : Bool}
  %lats_all(bs, Con{h, rest}) : {L.is_rank(L.nth_or0(k, Met.sort(_)), k, L.lats(Con{h, rest})) == True{} : Bool}
  rank_ok(90n, L.lats(Con{h, rest}), List.length(&2, Hit.Hit, rest), succ_eq(List.length(&2, Nat, L.lats(rest)), List.length(&2, Hit.Hit, rest), len_lats(rest)), {==})

def c_p95(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {L.nth_or0(L.rank(95n, a_n(a)), Met.sort(Met.flatten(a_t(a), []))) == L.s_p95(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({L.nth_or0(L.rank(95n, n), Met.sort(Met.flatten(t, []))) == 0n : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def sum_p95(+bs: List<&2, Nat>, +h: Hit.Hit, +rest: List<&2, Hit.Hit>)
  -> {L.is_rank(L.s_p95(L.summary(bs, Con{h, rest})), L.rank(95n, 1n+List.length(&2, Hit.Hit, rest)), L.lats(Con{h, rest})) == True{} : Bool}:
  +A = L.acc_all(Con{h, rest}, Met.empty(bs))
  +k = L.rank(95n, 1n+List.length(&2, Hit.Hit, rest))
  %c_p95(A, sum_x(bs, h, rest)) : {L.is_rank(_, k, L.lats(Con{h, rest})) == True{} : Bool}
  %f_n(Con{h, rest}, Met.empty(bs)) : {L.is_rank(L.nth_or0(L.rank(95n, _), Met.sort(Met.flatten(a_t(A), []))), k, L.lats(Con{h, rest})) == True{} : Bool}
  %lats_all(bs, Con{h, rest}) : {L.is_rank(L.nth_or0(k, Met.sort(_)), k, L.lats(Con{h, rest})) == True{} : Bool}
  rank_ok(95n, L.lats(Con{h, rest}), List.length(&2, Hit.Hit, rest), succ_eq(List.length(&2, Nat, L.lats(rest)), List.length(&2, Hit.Hit, rest), len_lats(rest)), {==})

def c_p99(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {L.nth_or0(L.rank(99n, a_n(a)), Met.sort(Met.flatten(a_t(a), []))) == L.s_p99(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({L.nth_or0(L.rank(99n, n), Met.sort(Met.flatten(t, []))) == 0n : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def sum_p99(+bs: List<&2, Nat>, +h: Hit.Hit, +rest: List<&2, Hit.Hit>)
  -> {L.is_rank(L.s_p99(L.summary(bs, Con{h, rest})), L.rank(99n, 1n+List.length(&2, Hit.Hit, rest)), L.lats(Con{h, rest})) == True{} : Bool}:
  +A = L.acc_all(Con{h, rest}, Met.empty(bs))
  +k = L.rank(99n, 1n+List.length(&2, Hit.Hit, rest))
  %c_p99(A, sum_x(bs, h, rest)) : {L.is_rank(_, k, L.lats(Con{h, rest})) == True{} : Bool}
  %f_n(Con{h, rest}, Met.empty(bs)) : {L.is_rank(L.nth_or0(L.rank(99n, _), Met.sort(Met.flatten(a_t(A), []))), k, L.lats(Con{h, rest})) == True{} : Bool}
  %lats_all(bs, Con{h, rest}) : {L.is_rank(L.nth_or0(k, Met.sort(_)), k, L.lats(Con{h, rest})) == True{} : Bool}
  rank_ok(99n, L.lats(Con{h, rest}), List.length(&2, Hit.Hit, rest), succ_eq(List.length(&2, Nat, L.lats(rest)), List.length(&2, Hit.Hit, rest), len_lats(rest)), {==})

def L.met_latencies(bs, h, hs):
  (sum_lmin(bs, h, hs), (sum_lmax(bs, h, hs), (sum_p50(bs, h, hs), (sum_p90(bs, h, hs), (sum_p95(bs, h, hs), sum_p99(bs, h, hs))))))

# =====================================================================
# Totals: exact sums as Bigs (Big's own laws big_of and big_add)
# =====================================================================

def pfst(-A: Type, -B: Type, p: A & B) -> A:
  (x, y) = p
  x

def psnd(-A: Type, -B: Type, p: A & B) -> B:
  (x, y) = p
  y

def big_of_val(+n: Nat) -> {n == L.big_val(Big.of(n)) : Nat}:
  Equal.sym(Nat, L.big_val(Big.of(n)), n,
    pfst({L.big_val(Big.of(n)) == n : Nat}, {L.big_ok(Big.of(n)) == True{} : Bool}, L.big_of(n)))

def big_of_ok(+n: Nat) -> {L.big_ok(Big.of(n)) == True{} : Bool}:
  psnd({L.big_val(Big.of(n)) == n : Nat}, {L.big_ok(Big.of(n)) == True{} : Bool}, L.big_of(n))

def big_add_val(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool})
  -> {Nat.add(L.big_val(a), L.big_val(b)) == L.big_val(Big.add(a, b)) : Nat}:
  Equal.sym(Nat, L.big_val(Big.add(a, b)), Nat.add(L.big_val(a), L.big_val(b)),
    pfst({L.big_val(Big.add(a, b)) == Nat.add(L.big_val(a), L.big_val(b)) : Nat}, {L.big_ok(Big.add(a, b)) == True{} : Bool}, L.big_add(a, b, ha, hb)))

def big_add_ok(+a: Big.Big, +b: Big.Big, +ha: {L.big_ok(a) == True{} : Bool}, +hb: {L.big_ok(b) == True{} : Bool})
  -> {L.big_ok(Big.add(a, b)) == True{} : Bool}:
  psnd({L.big_val(Big.add(a, b)) == Nat.add(L.big_val(a), L.big_val(b)) : Nat}, {L.big_ok(Big.add(a, b)) == True{} : Bool}, L.big_add(a, b, ha, hb))

def oh_lat_ok(h: Hit.Hit) -> {L.big_ok(a_lat(Met.of_hit(h))) == True{} : Bool}:
  match h:
    case Hit.Hit{a, q, c, t, +l, +bo, +bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          big_of_ok(l)

def oh_lat_val(h: Hit.Hit) -> {L.h_lat(h) == L.big_val(a_lat(Met.of_hit(h))) : Nat}:
  match h:
    case Hit.Hit{a, q, c, t, +l, +bo, +bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          big_of_val(l)

def add_lat_ok(+a: Met.Acc, +h: Hit.Hit, +ha: {L.big_ok(a_lat(a)) == True{} : Bool}) -> {L.big_ok(a_lat(Met.add(a, h))) == True{} : Bool}:
  %m_lat(a, Met.of_hit(h)) : {L.big_ok(_) == True{} : Bool}
  big_add_ok(a_lat(a), a_lat(Met.of_hit(h)), ha, oh_lat_ok(h))

def fo_lat(hs: List<&2, Hit.Hit>, +a: Met.Acc, +ha: {L.big_ok(a_lat(a)) == True{} : Bool}) -> {L.big_ok(a_lat(L.acc_all(hs, a))) == True{} : Bool}:
  match hs:
    case Nil{}:
      ha
    case Con{+h, +rest}:
      fo_lat(rest, Met.add(a, h), add_lat_ok(a, h, ha))

def fv_lat(hs: List<&2, Hit.Hit>, +a: Met.Acc, +ha: {L.big_ok(a_lat(a)) == True{} : Bool})
  -> {Nat.add(L.big_val(a_lat(a)), L.sum_lat(hs)) == L.big_val(a_lat(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      Equal.sym(Nat, L.big_val(a_lat(a)), Nat.add(L.big_val(a_lat(a)), 0n), PNat.add_zero(L.big_val(a_lat(a))))
    case Con{+h, +rest}:
      +x = L.big_val(a_lat(a))
      +p = L.h_lat(h)
      +r = L.sum_lat(rest)
      %fv_lat(rest, Met.add(a, h), add_lat_ok(a, h, ha)) : {Nat.add(x, Nat.add(p, r)) == _ : Nat}
      %m_lat(a, Met.of_hit(h)) : {Nat.add(x, Nat.add(p, r)) == Nat.add(L.big_val(_), r) : Nat}
      %big_add_val(a_lat(a), a_lat(Met.of_hit(h)), ha, oh_lat_ok(h)) : {Nat.add(x, Nat.add(p, r)) == Nat.add(_, r) : Nat}
      %oh_lat_val(h) : {Nat.add(x, Nat.add(p, r)) == Nat.add(Nat.add(x, _), r) : Nat}
      PNat.add_assoc(x, p, r)

def c_lat(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {a_lat(a) == L.s_lat_total(Met.close(a)) : Big.Big}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({l == Big.of(0n) : Big.Big}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def oh_bin_ok(h: Hit.Hit) -> {L.big_ok(a_bin(Met.of_hit(h))) == True{} : Bool}:
  match h:
    case Hit.Hit{a, q, c, t, +l, +bo, +bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          big_of_ok(bi)

def oh_bin_val(h: Hit.Hit) -> {L.h_in(h) == L.big_val(a_bin(Met.of_hit(h))) : Nat}:
  match h:
    case Hit.Hit{a, q, c, t, +l, +bo, +bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          big_of_val(bi)

def add_bin_ok(+a: Met.Acc, +h: Hit.Hit, +ha: {L.big_ok(a_bin(a)) == True{} : Bool}) -> {L.big_ok(a_bin(Met.add(a, h))) == True{} : Bool}:
  %m_bin(a, Met.of_hit(h)) : {L.big_ok(_) == True{} : Bool}
  big_add_ok(a_bin(a), a_bin(Met.of_hit(h)), ha, oh_bin_ok(h))

def fo_bin(hs: List<&2, Hit.Hit>, +a: Met.Acc, +ha: {L.big_ok(a_bin(a)) == True{} : Bool}) -> {L.big_ok(a_bin(L.acc_all(hs, a))) == True{} : Bool}:
  match hs:
    case Nil{}:
      ha
    case Con{+h, +rest}:
      fo_bin(rest, Met.add(a, h), add_bin_ok(a, h, ha))

def fv_bin(hs: List<&2, Hit.Hit>, +a: Met.Acc, +ha: {L.big_ok(a_bin(a)) == True{} : Bool})
  -> {Nat.add(L.big_val(a_bin(a)), L.sum_in(hs)) == L.big_val(a_bin(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      Equal.sym(Nat, L.big_val(a_bin(a)), Nat.add(L.big_val(a_bin(a)), 0n), PNat.add_zero(L.big_val(a_bin(a))))
    case Con{+h, +rest}:
      +x = L.big_val(a_bin(a))
      +p = L.h_in(h)
      +r = L.sum_in(rest)
      %fv_bin(rest, Met.add(a, h), add_bin_ok(a, h, ha)) : {Nat.add(x, Nat.add(p, r)) == _ : Nat}
      %m_bin(a, Met.of_hit(h)) : {Nat.add(x, Nat.add(p, r)) == Nat.add(L.big_val(_), r) : Nat}
      %big_add_val(a_bin(a), a_bin(Met.of_hit(h)), ha, oh_bin_ok(h)) : {Nat.add(x, Nat.add(p, r)) == Nat.add(_, r) : Nat}
      %oh_bin_val(h) : {Nat.add(x, Nat.add(p, r)) == Nat.add(Nat.add(x, _), r) : Nat}
      PNat.add_assoc(x, p, r)

def c_bin(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {a_bin(a) == L.s_bytes_in(Met.close(a)) : Big.Big}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({i == Big.of(0n) : Big.Big}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def oh_bout_ok(h: Hit.Hit) -> {L.big_ok(a_bout(Met.of_hit(h))) == True{} : Bool}:
  match h:
    case Hit.Hit{a, q, c, t, +l, +bo, +bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          big_of_ok(bo)

def oh_bout_val(h: Hit.Hit) -> {L.h_out(h) == L.big_val(a_bout(Met.of_hit(h))) : Nat}:
  match h:
    case Hit.Hit{a, q, c, t, +l, +bo, +bi, e, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          big_of_val(bo)

def add_bout_ok(+a: Met.Acc, +h: Hit.Hit, +ha: {L.big_ok(a_bout(a)) == True{} : Bool}) -> {L.big_ok(a_bout(Met.add(a, h))) == True{} : Bool}:
  %m_bout(a, Met.of_hit(h)) : {L.big_ok(_) == True{} : Bool}
  big_add_ok(a_bout(a), a_bout(Met.of_hit(h)), ha, oh_bout_ok(h))

def fo_bout(hs: List<&2, Hit.Hit>, +a: Met.Acc, +ha: {L.big_ok(a_bout(a)) == True{} : Bool}) -> {L.big_ok(a_bout(L.acc_all(hs, a))) == True{} : Bool}:
  match hs:
    case Nil{}:
      ha
    case Con{+h, +rest}:
      fo_bout(rest, Met.add(a, h), add_bout_ok(a, h, ha))

def fv_bout(hs: List<&2, Hit.Hit>, +a: Met.Acc, +ha: {L.big_ok(a_bout(a)) == True{} : Bool})
  -> {Nat.add(L.big_val(a_bout(a)), L.sum_out(hs)) == L.big_val(a_bout(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      Equal.sym(Nat, L.big_val(a_bout(a)), Nat.add(L.big_val(a_bout(a)), 0n), PNat.add_zero(L.big_val(a_bout(a))))
    case Con{+h, +rest}:
      +x = L.big_val(a_bout(a))
      +p = L.h_out(h)
      +r = L.sum_out(rest)
      %fv_bout(rest, Met.add(a, h), add_bout_ok(a, h, ha)) : {Nat.add(x, Nat.add(p, r)) == _ : Nat}
      %m_bout(a, Met.of_hit(h)) : {Nat.add(x, Nat.add(p, r)) == Nat.add(L.big_val(_), r) : Nat}
      %big_add_val(a_bout(a), a_bout(Met.of_hit(h)), ha, oh_bout_ok(h)) : {Nat.add(x, Nat.add(p, r)) == Nat.add(_, r) : Nat}
      %oh_bout_val(h) : {Nat.add(x, Nat.add(p, r)) == Nat.add(Nat.add(x, _), r) : Nat}
      PNat.add_assoc(x, p, r)

def c_bout(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {a_bout(a) == L.s_bytes_out(Met.close(a)) : Big.Big}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({o == Big.of(0n) : Big.Big}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def L.met_totals(bs, hs):
  match hs:
    case Nil{}:
      ({==}, ({==}, ({==}, {==})))
    case Con{+h, +rest}:
      +A = L.acc_all(Con{h, rest}, Met.empty(bs))
      +hx = sum_x(bs, h, rest)
      +e1 = {%c_lat(A, hx) : {L.big_val(_) == L.sum_lat(Con{h, rest}) : Nat};
             Equal.sym(Nat, L.sum_lat(Con{h, rest}), L.big_val(a_lat(A)), fv_lat(Con{h, rest}, Met.empty(bs), {==}))
             : {L.big_val(L.s_lat_total(L.summary(bs, Con{h, rest}))) == L.sum_lat(Con{h, rest}) : Nat}}
      +e2 = {%c_bin(A, hx) : {L.big_val(_) == L.sum_in(Con{h, rest}) : Nat};
             Equal.sym(Nat, L.sum_in(Con{h, rest}), L.big_val(a_bin(A)), fv_bin(Con{h, rest}, Met.empty(bs), {==}))
             : {L.big_val(L.s_bytes_in(L.summary(bs, Con{h, rest}))) == L.sum_in(Con{h, rest}) : Nat}}
      +e3 = {%c_bout(A, hx) : {L.big_val(_) == L.sum_out(Con{h, rest}) : Nat};
             Equal.sym(Nat, L.sum_out(Con{h, rest}), L.big_val(a_bout(A)), fv_bout(Con{h, rest}, Met.empty(bs), {==}))
             : {L.big_val(L.s_bytes_out(L.summary(bs, Con{h, rest}))) == L.sum_out(Con{h, rest}) : Nat}}
      +e4 = {%c_lat(A, hx) : {Bool.and(L.big_ok(_), Bool.and(L.big_ok(L.s_bytes_in(Met.close(A))), L.big_ok(L.s_bytes_out(Met.close(A))))) == True{} : Bool};
             %c_bin(A, hx) : {Bool.and(L.big_ok(a_lat(A)), Bool.and(L.big_ok(_), L.big_ok(L.s_bytes_out(Met.close(A))))) == True{} : Bool};
             %c_bout(A, hx) : {Bool.and(L.big_ok(a_lat(A)), Bool.and(L.big_ok(a_bin(A)), L.big_ok(_))) == True{} : Bool};
             and_i(L.big_ok(a_lat(A)), Bool.and(L.big_ok(a_bin(A)), L.big_ok(a_bout(A))),
               fo_lat(Con{h, rest}, Met.empty(bs), {==}),
               and_i(L.big_ok(a_bin(A)), L.big_ok(a_bout(A)), fo_bin(Con{h, rest}, Met.empty(bs), {==}), fo_bout(Con{h, rest}, Met.empty(bs), {==})))
             : {Bool.and(L.big_ok(L.s_lat_total(L.summary(bs, Con{h, rest}))), Bool.and(L.big_ok(L.s_bytes_in(L.summary(bs, Con{h, rest}))),
                 L.big_ok(L.s_bytes_out(L.summary(bs, Con{h, rest}))))) == True{} : Bool}}
      (e1, (e2, (e3, e4)))

# =====================================================================
# The span: times as (seconds, nanoseconds below a second)
# =====================================================================

def lt_le_trans(a: Nat, b: Nat, c: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, no_ft(h1))
        case 1n+bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, no_ft(h2))
            case 1n+cp:
              {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool}, no_ft(h1))
        case 1n+bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, no_ft(h2))
            case 1n+cp:
              lt_le_trans(ap, bp, cp, h1, h2)

def add_cancel(c: Nat, -a: Nat, -b: Nat, e: {Nat.add(c, a) == Nat.add(c, b) : Nat}) -> {a == b : Nat}:
  match c:
    case 0n:
      e
    case 1n+cp:
      add_cancel(cp, a, b, PNat.succ_inj(Nat.add(cp, a), Nat.add(cp, b), e))

def le_cancel(c: Nat, +a: Nat, +b: Nat) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == Nat.is_le(a, b) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+cp:
      le_cancel(cp, a, b)

def sub_cancel(c: Nat, +a: Nat, +b: Nat) -> {Nat.sub(Nat.add(c, a), Nat.add(c, b)) == Nat.sub(a, b) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+cp:
      sub_cancel(cp, a, b)

def lt_ne_t(+a: Nat, -b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}, e: {a == b : Nat}) -> Empty:
  +h2 = {%Equal.sym(Nat, a, b, e) : {Nat.is_lt(a, _) == True{} : Bool}; h : {Nat.is_lt(a, a) == True{} : Bool}}
  no_ft(Equal.trans(Bool, False{}, Nat.is_lt(a, a), True{}, Equal.sym(Bool, Nat.is_lt(a, a), False{}, lt_irr(a)), h2))

# q B + r with r < B: B = 1 + b
def tq(+q: Nat, +r: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.mul(q, 1n+b), r)

# q1 < q2 and r1 < B: q1 B + r1 < q2 B + r2
def lt_tot(+q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, +b: Nat, +hq: {Nat.is_lt(q1, q2) == True{} : Bool}, +hr: {Nat.is_lt(r1, 1n+b) == True{} : Bool})
  -> {Nat.is_lt(tq(q1, r1, b), tq(q2, r2, b)) == True{} : Bool}:
  +m1 = Nat.mul(q1, 1n+b)
  +h1 = {%PNat.add_comm(m1, 1n+b) : {Nat.is_lt(tq(q1, r1, b), _) == True{} : Bool};
         lt_add_mono(m1, r1, 1n+b, hr) : {Nat.is_lt(tq(q1, r1, b), Nat.mul(1n+q1, 1n+b)) == True{} : Bool}}
  +h2 = le_trans(Nat.mul(1n+q1, 1n+b), Nat.mul(q2, 1n+b), tq(q2, r2, b), mul_le_mono(1n+q1, q2, 1n+b, lt_le_succ(q1, q2, hq)), le_add(Nat.mul(q2, 1n+b), r2))
  lt_le_trans(tq(q1, r1, b), Nat.mul(1n+q1, 1n+b), tq(q2, r2, b), h1, h2)

def div_uq.of(c1: Bool, c2: Bool, +q: Nat, +r: Nat, +b: Nat, +e1: {Nat.is_lt(q, Nat.div(tq(q, r, b), 1n+b)) == c1 : Bool},
  +e2: {Nat.is_gt(q, Nat.div(tq(q, r, b), 1n+b)) == c2 : Bool}, +hr: {Nat.is_lt(r, 1n+b) == True{} : Bool})
  -> {q == Nat.div(tq(q, r, b), 1n+b) : Nat}:
  match c1:
    case True{}:
      +x = tq(q, r, b)
      +d = Nat.div(x, 1n+b)
      +m = Nat.mod(x, 1n+b)
      +ex = PNat.div_mod_eq(x, b)
      Empty.absurd({q == d : Nat}, lt_ne_t(x, tq(d, m, b), lt_tot(q, r, d, m, b, e1, hr), ex))
    case False{}:
      match c2:
        case True{}:
          +x = tq(q, r, b)
          +d = Nat.div(x, 1n+b)
          +m = Nat.mod(x, 1n+b)
          +ex = PNat.div_mod_eq(x, b)
          Empty.absurd({q == d : Nat}, lt_ne_t(tq(d, m, b), x, lt_tot(d, m, q, r, b, gt_lt(q, d, e2), PNat.mod_lt(x, b)), Equal.sym(Nat, x, tq(d, m, b), ex)))
        case False{}:
          n_eq_of(q, Nat.div(tq(q, r, b), 1n+b), e1, e2)

def div_uq(+q: Nat, +r: Nat, +b: Nat, +hr: {Nat.is_lt(r, 1n+b) == True{} : Bool}) -> {q == Nat.div(tq(q, r, b), 1n+b) : Nat}:
  div_uq.of(Nat.is_lt(q, Nat.div(tq(q, r, b), 1n+b)), Nat.is_gt(q, Nat.div(tq(q, r, b), 1n+b)), q, r, b, {==}, {==}, hr)

def mod_uq(+q: Nat, +r: Nat, +b: Nat, +hr: {Nat.is_lt(r, 1n+b) == True{} : Bool}) -> {r == Nat.mod(tq(q, r, b), 1n+b) : Nat}:
  +x = tq(q, r, b)
  +e = {%Equal.sym(Nat, q, Nat.div(x, 1n+b), div_uq(q, r, b, hr)) : {x == Nat.add(Nat.mul(_, 1n+b), Nat.mod(x, 1n+b)) : Nat}; PNat.div_mod_eq(x, b)
        : {Nat.add(Nat.mul(q, 1n+b), r) == Nat.add(Nat.mul(q, 1n+b), Nat.mod(x, 1n+b)) : Nat}}
  add_cancel(Nat.mul(q, 1n+b), r, Nat.mod(x, 1n+b), e)

def cmp_eq(a: Nat, b: Nat, +e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          Empty.absurd({0n == 1n+bp : Nat}, no_ft(Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e)))
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({1n+ap == 0n : Nat}, no_ft(Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e)))
        case 1n+bp:
          succ_eq(ap, bp, cmp_eq(ap, bp, e))

def cmp_gt(a: Nat, b: Nat, +e: {Nat.cmp(a, b) == GT{} : Cmp}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, no_ft(Equal.cong(Cmp, Bool, c => Cmp.is_gt(c), EQ{}, GT{}, e)))
        case 1n+bp:
          Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, no_ft(Equal.cong(Cmp, Bool, c => Cmp.is_gt(c), LT{}, GT{}, e)))
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          cmp_gt(ap, bp, e)

def lt_nle(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, no_ft(h))
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(0n, 1n+ap) == False{} : Bool}, no_ft(h))
        case 1n+bp:
          lt_nle(ap, bp, h)

# (s1, n1) no later than (s2, n2), for nanoseconds below B, is s1 B + n1 <= s2 B + n2
def nl_same(c: Cmp, +s1: Nat, +n1: Nat, +s2: Nat, +n2: Nat, +b: Nat, +ec: {Nat.cmp(s1, s2) == c : Cmp},
  +h1: {Nat.is_lt(n1, 1n+b) == True{} : Bool}, +h2: {Nat.is_lt(n2, 1n+b) == True{} : Bool})
  -> {Nat.is_le(tq(s1, n1, b), tq(s2, n2, b)) == Met.no_later(s1, n1, s2, n2) : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, Nat.cmp(s1, s2), LT{}, ec)
        : {Nat.is_le(tq(s1, n1, b), tq(s2, n2, b)) == Bool.or(Cmp.is_lt(_), Bool.and(Cmp.is_eq(_), Nat.is_le(n1, n2))) : Bool}
      n_lt_le(tq(s1, n1, b), tq(s2, n2, b), lt_tot(s1, n1, s2, n2, b, Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), Nat.cmp(s1, s2), LT{}, ec), h1))
    case EQ{}:
      %Equal.sym(Cmp, Nat.cmp(s1, s2), EQ{}, ec)
        : {Nat.is_le(tq(s1, n1, b), tq(s2, n2, b)) == Bool.or(Cmp.is_lt(_), Bool.and(Cmp.is_eq(_), Nat.is_le(n1, n2))) : Bool}
      %cmp_eq(s1, s2, ec) : {Nat.is_le(tq(s1, n1, b), tq(_, n2, b)) == Nat.is_le(n1, n2) : Bool}
      le_cancel(Nat.mul(s1, 1n+b), n1, n2)
    case GT{}:
      %Equal.sym(Cmp, Nat.cmp(s1, s2), GT{}, ec)
        : {Nat.is_le(tq(s1, n1, b), tq(s2, n2, b)) == Bool.or(Cmp.is_lt(_), Bool.and(Cmp.is_eq(_), Nat.is_le(n1, n2))) : Bool}
      lt_nle(tq(s2, n2, b), tq(s1, n1, b), lt_tot(s2, n2, s1, n1, b, cmp_gt(s1, s2, ec), h2))

def pk(c: Bool, -s1: Nat, -n1: Nat, -s2: Nat, -n2: Nat, -b: Nat)
  -> {Met.pick(Nat, c, tq(s1, n1, b), tq(s2, n2, b)) == tq(Met.pick(Nat, c, s1, s2), Met.pick(Nat, c, n1, n2), b) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def pick_lt(c: Bool, -a: Nat, -b: Nat, -m: Nat, +ha: {Nat.is_lt(a, m) == True{} : Bool}, +hb: {Nat.is_lt(b, m) == True{} : Bool})
  -> {Nat.is_lt(Met.pick(Nat, c, a, b), m) == True{} : Bool}:
  match c:
    case True{}:
      ha
    case False{}:
      hb

def add4(+x: Nat, +y: Nat, +a: Nat, +b: Nat) -> {Nat.add(Nat.add(x, y), Nat.add(a, b)) == Nat.add(Nat.add(x, a), Nat.add(y, b)) : Nat}:
  %PNat.add_assoc(x, y, Nat.add(a, b)) : {_ == Nat.add(Nat.add(x, a), Nat.add(y, b)) : Nat}
  %PNat.add_assoc(x, a, Nat.add(y, b)) : {Nat.add(x, Nat.add(y, Nat.add(a, b))) == _ : Nat}
  %PNat.add_swap(y, a, b) : {Nat.add(x, Nat.add(y, Nat.add(a, b))) == Nat.add(x, _) : Nat}
  {==}

def B9() -> Nat:
  999999999n

# a start carried into (s, ns < 1s)
def norm_start(+s0: Nat, +ns0: Nat)
  -> {Nat.add(Nat.mul(s0, L.sec()), ns0) == tq(Nat.add(s0, Nat.div(ns0, L.sec())), Nat.mod(ns0, L.sec()), B9()) : Nat}:
  +d = Nat.div(ns0, L.sec())
  +r = Nat.mod(ns0, L.sec())
  %PNat.mul_dist(s0, d, L.sec()) : {Nat.add(Nat.mul(s0, L.sec()), ns0) == Nat.add(_, r) : Nat}
  %PNat.add_assoc(Nat.mul(s0, L.sec()), Nat.mul(d, L.sec()), r) : {Nat.add(Nat.mul(s0, L.sec()), ns0) == _ : Nat}
  %PNat.div_mod_eq(ns0, B9()) : {Nat.add(Nat.mul(s0, L.sec()), ns0) == Nat.add(Nat.mul(s0, L.sec()), _) : Nat}
  {==}

# a start plus a latency carried the same way
def norm_end(+s0: Nat, +ns0: Nat, +lat: Nat)
  -> {Nat.add(Nat.add(Nat.mul(s0, L.sec()), ns0), lat)
      == tq(Nat.add(Nat.add(Nat.add(s0, Nat.div(ns0, L.sec())), Nat.div(lat, L.sec())), Nat.div(Nat.add(Nat.mod(ns0, L.sec()), Nat.mod(lat, L.sec())), L.sec())),
            Nat.mod(Nat.add(Nat.mod(ns0, L.sec()), Nat.mod(lat, L.sec())), L.sec()), B9()) : Nat}:
  +bb = L.sec()
  +s = Nat.add(s0, Nat.div(ns0, bb))
  +ns = Nat.mod(ns0, bb)
  +ld = Nat.div(lat, bb)
  +lr = Nat.mod(lat, bb)
  +en = Nat.add(ns, lr)
  +ed = Nat.div(en, bb)
  +er = Nat.mod(en, bb)
  +t = Nat.add(Nat.add(Nat.mul(s0, bb), ns0), lat)
  %PNat.mul_dist(Nat.add(s, ld), ed, bb) : {t == Nat.add(_, er) : Nat}
  %PNat.add_assoc(Nat.mul(Nat.add(s, ld), bb), Nat.mul(ed, bb), er) : {t == _ : Nat}
  %PNat.div_mod_eq(en, B9()) : {t == Nat.add(Nat.mul(Nat.add(s, ld), bb), _) : Nat}
  %PNat.mul_dist(s, ld, bb) : {t == Nat.add(_, en) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(s0, bb), ns0), tq(s, ns, B9()), norm_start(s0, ns0))
    : {Nat.add(_, lat) == Nat.add(Nat.add(Nat.mul(s, bb), Nat.mul(ld, bb)), en) : Nat}
  %Equal.sym(Nat, lat, Nat.add(Nat.mul(ld, bb), lr), PNat.div_mod_eq(lat, B9()))
    : {Nat.add(tq(s, ns, B9()), _) == Nat.add(Nat.add(Nat.mul(s, bb), Nat.mul(ld, bb)), en) : Nat}
  add4(Nat.mul(s, bb), ns, Nat.mul(ld, bb), lr)


# the span between two times, the first no later
def sp.of(c: Bool, +s1: Nat, +n1: Nat, +s2: Nat, +n2: Nat, +ec: {Nat.is_le(s1, s2) == c : Bool},
  +hle: {Nat.is_le(tq(s1, n1, B9()), tq(s2, n2, B9())) == True{} : Bool},
  +h1: {Nat.is_lt(n1, L.sec()) == True{} : Bool}, +h2: {Nat.is_lt(n2, L.sec()) == True{} : Bool})
  -> {Nat.sub(tq(s2, n2, B9()), tq(s1, n1, B9())) == Met.span_ns(s1, n1, s2, n2) : Nat}:
  match c:
    case False{}:
      Empty.absurd({Nat.sub(tq(s2, n2, B9()), tq(s1, n1, B9())) == Met.span_ns(s1, n1, s2, n2) : Nat},
        no_ft(Equal.trans(Bool, False{}, Nat.is_le(tq(s1, n1, B9()), tq(s2, n2, B9())), True{},
          Equal.sym(Bool, Nat.is_le(tq(s1, n1, B9()), tq(s2, n2, B9())), False{}, lt_nle(tq(s2, n2, B9()), tq(s1, n1, B9()),
            lt_tot(s2, n2, s1, n1, B9(), nle_lt(s1, s2, ec), h2))), hle)))
    case True{}:
      +bb = L.sec()
      +d = Nat.sub(s2, s1)
      +r = Nat.sub(Nat.add(Nat.mul(d, bb), n2), n1)
      %sub_add(s1, s2, ec) : {Nat.sub(Nat.add(Nat.mul(_, bb), n2), tq(s1, n1, B9())) == r : Nat}
      %PNat.mul_dist(s1, d, bb) : {Nat.sub(Nat.add(_, n2), tq(s1, n1, B9())) == r : Nat}
      %PNat.add_assoc(Nat.mul(s1, bb), Nat.mul(d, bb), n2) : {Nat.sub(_, tq(s1, n1, B9())) == r : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(Nat.mul(s1, bb), Nat.add(Nat.mul(d, bb), n2)), Nat.add(Nat.mul(s1, bb), n1)),
          Nat.sub(Nat.add(Nat.mul(d, bb), n2), n1), sub_cancel(Nat.mul(s1, bb), Nat.add(Nat.mul(d, bb), n2), n1))
        : {_ == r : Nat}
      {==}

def sp(+s1: Nat, +n1: Nat, +s2: Nat, +n2: Nat,
  +hle: {Nat.is_le(tq(s1, n1, B9()), tq(s2, n2, B9())) == True{} : Bool},
  +h1: {Nat.is_lt(n1, L.sec()) == True{} : Bool}, +h2: {Nat.is_lt(n2, L.sec()) == True{} : Bool})
  -> {Nat.sub(tq(s2, n2, B9()), tq(s1, n1, B9())) == Met.span_ns(s1, n1, s2, n2) : Nat}:
  sp.of(Nat.is_le(s1, s2), s1, n1, s2, n2, {==}, hle, h1, h2)

# ---------------------------------------------------------------------
# min and max over lists
# ---------------------------------------------------------------------

def min_le(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          min_le(ap, bp)

def le_max(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      le_zero(b)
    case 1n+ap:
      match b:
        case 0n:
          le_refl(ap)
        case 1n+bp:
          le_max(ap, bp)

def le_max_r(a: Nat, b: Nat) -> {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      le_refl(b)
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          le_max_r(ap, bp)

def max_le(a: Nat, b: Nat, c: Nat, +h1: {Nat.is_le(a, c) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(Nat.max(a, b), c) == True{} : Bool}:
  match a:
    case 0n:
      h2
    case 1n+ap:
      match b:
        case 0n:
          h1
        case 1n+bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+Nat.max(ap, bp), 0n) == True{} : Bool}, no_ft(h1))
            case 1n+cp:
              max_le(ap, bp, cp, h1, h2)

def min_go_le(xs: List<&2, Nat>, +d: Nat) -> {Nat.is_le(L.min_of.go(xs, d), d) == True{} : Bool}:
  match xs:
    case Nil{}:
      le_refl(d)
    case Con{+x, +r}:
      le_trans(L.min_of.go(r, Nat.min(d, x)), Nat.min(d, x), d, min_go_le(r, Nat.min(d, x)), min_le(d, x))

def le_max_go(xs: List<&2, Nat>, +d: Nat) -> {Nat.is_le(d, L.max_of.go(xs, d)) == True{} : Bool}:
  match xs:
    case Nil{}:
      le_refl(d)
    case Con{+x, +r}:
      le_trans(d, Nat.max(d, x), L.max_of.go(r, Nat.max(d, x)), le_max(d, x), le_max_go(r, Nat.max(d, x)))

# the last start is no later than the last end
def mx_mono(hs: List<&2, Hit.Hit>, +d: Nat, +e: Nat, +h: {Nat.is_le(d, e) == True{} : Bool})
  -> {Nat.is_le(L.max_of.go(L.starts(hs), d), L.max_of.go(L.ends(hs), e)) == True{} : Bool}:
  match hs:
    case Nil{}:
      h
    case Con{+x, +r}:
      +t = L.total_ns(L.h_ts(x))
      +u = Nat.add(t, L.h_lat(x))
      +m = Nat.max(e, u)
      mx_mono(r, Nat.max(d, t), m,
        max_le(d, t, m, le_trans(d, e, m, h, le_max(e, u)), le_trans(t, u, m, le_add(t, L.h_lat(x)), le_max_r(e, u))))

# ---------------------------------------------------------------------
# The accumulator's times
# ---------------------------------------------------------------------

def x_es(x: Met.Ext) -> Nat:
  match x:
    case Met.NoExt{}:
      0n
    case Met.Ext{a, b, es, en, ls, ln, xs, xn}:
      es

def x_en(x: Met.Ext) -> Nat:
  match x:
    case Met.NoExt{}:
      0n
    case Met.Ext{a, b, es, en, ls, ln, xs, xn}:
      en

def x_ls(x: Met.Ext) -> Nat:
  match x:
    case Met.NoExt{}:
      0n
    case Met.Ext{a, b, es, en, ls, ln, xs, xn}:
      ls

def x_ln(x: Met.Ext) -> Nat:
  match x:
    case Met.NoExt{}:
      0n
    case Met.Ext{a, b, es, en, ls, ln, xs, xn}:
      ln

def x_xs(x: Met.Ext) -> Nat:
  match x:
    case Met.NoExt{}:
      0n
    case Met.Ext{a, b, es, en, ls, ln, xs, xn}:
      xs

def x_xn(x: Met.Ext) -> Nat:
  match x:
    case Met.NoExt{}:
      0n
    case Met.Ext{a, b, es, en, ls, ln, xs, xn}:
      xn

def tE(+x: Met.Ext) -> Nat:
  tq(x_es(x), x_en(x), B9())

def tL(+x: Met.Ext) -> Nat:
  tq(x_ls(x), x_ln(x), B9())

def tN(+x: Met.Ext) -> Nat:
  tq(x_xs(x), x_xn(x), B9())

# the nanoseconds are below a second
def okx(x: Met.Ext) -> Bool:
  match x:
    case Met.NoExt{}:
      True{}
    case Met.Ext{a, b, es, en, ls, ln, xs, xn}:
      Bool.and(Nat.is_lt(en, L.sec()), Bool.and(Nat.is_lt(ln, L.sec()), Nat.is_lt(xn, L.sec())))

def ok1(+a: Bool, -b: Bool, -c: Bool, +h: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {a == True{} : Bool}:
  and_l(a, Bool.and(b, c), h)

def ok2(+a: Bool, +b: Bool, -c: Bool, +h: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {b == True{} : Bool}:
  and_l(b, c, and_r(a, Bool.and(b, c), h))

def ok3(+a: Bool, +b: Bool, +c: Bool, +h: {Bool.and(a, Bool.and(b, c)) == True{} : Bool}) -> {c == True{} : Bool}:
  and_r(b, c, and_r(a, Bool.and(b, c), h))

def ok_mk(-a: Bool, -b: Bool, -c: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}, +hc: {c == True{} : Bool})
  -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, Bool.and(b, c)) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, Bool.and(_, c)) == True{} : Bool}
  hc

def st_e(a: Met.Acc, h: Hit.Hit, +hx: {is_ext(a_x(a)) == True{} : Bool}, +hok: {okx(a_x(a)) == True{} : Bool})
  -> {Nat.min(tE(a_x(a)), L.total_ns(L.h_ts(h))) == tE(a_x(Met.add(a, h))) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Nat.min(0n, L.total_ns(L.h_ts(h))) == tE(a_x(Met.add(Met.Acc{bs, n, ok, cs, es, l, i, o, Met.NoExt{}, t}, h))) : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, +es1, +en1, ls1, +ln1, xs1, +xn1}:
          match h:
            case Hit.Hit{ha, q, c, tt, lat, bo, bi, e, b, m, u, hs}:
              match tt:
                case Civil.Time{+s0, +ns0, off}:
                  +s = Nat.add(s0, Nat.div(ns0, L.sec()))
                  +ns = Nat.mod(ns0, L.sec())
                  +te = tq(es1, en1, B9())
                  +ts = tq(s, ns, B9())
                  +t0 = Nat.add(Nat.mul(s0, L.sec()), ns0)
                  +nl = Met.no_later(es1, en1, s, ns)
                  +hen = ok1(Nat.is_lt(en1, L.sec()), Nat.is_lt(ln1, L.sec()), Nat.is_lt(xn1, L.sec()), hok)
                  %pk(nl, es1, en1, s, ns, B9()) : {Nat.min(te, t0) == _ : Nat}
                  %nl_same(Nat.cmp(es1, s), es1, en1, s, ns, B9(), {==}, hen, PNat.mod_lt(ns0, B9())) : {Nat.min(te, t0) == Met.pick(Nat, _, te, ts) : Nat}
                  %norm_start(s0, ns0) : {Nat.min(te, t0) == Met.nmin(te, _) : Nat}
                  nmin_min(te, t0)

def st_l(a: Met.Acc, h: Hit.Hit, +hx: {is_ext(a_x(a)) == True{} : Bool}, +hok: {okx(a_x(a)) == True{} : Bool})
  -> {Nat.max(tL(a_x(a)), L.total_ns(L.h_ts(h))) == tL(a_x(Met.add(a, h))) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Nat.max(0n, L.total_ns(L.h_ts(h))) == tL(a_x(Met.add(Met.Acc{bs, n, ok, cs, es, l, i, o, Met.NoExt{}, t}, h))) : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, +en1, +ls1, +ln1, xs1, +xn1}:
          match h:
            case Hit.Hit{ha, q, c, tt, lat, bo, bi, e, b, m, u, hs}:
              match tt:
                case Civil.Time{+s0, +ns0, off}:
                  +s = Nat.add(s0, Nat.div(ns0, L.sec()))
                  +ns = Nat.mod(ns0, L.sec())
                  +tl = tq(ls1, ln1, B9())
                  +ts = tq(s, ns, B9())
                  +t0 = Nat.add(Nat.mul(s0, L.sec()), ns0)
                  +nl = Met.no_later(ls1, ln1, s, ns)
                  +hln = ok2(Nat.is_lt(en1, L.sec()), Nat.is_lt(ln1, L.sec()), Nat.is_lt(xn1, L.sec()), hok)
                  %pk(nl, s, ns, ls1, ln1, B9()) : {Nat.max(tl, t0) == _ : Nat}
                  %nl_same(Nat.cmp(ls1, s), ls1, ln1, s, ns, B9(), {==}, hln, PNat.mod_lt(ns0, B9())) : {Nat.max(tl, t0) == Met.pick(Nat, _, ts, tl) : Nat}
                  %norm_start(s0, ns0) : {Nat.max(tl, t0) == Met.nmax(tl, _) : Nat}
                  nmax_max(tl, t0)

def st_n(a: Met.Acc, h: Hit.Hit, +hx: {is_ext(a_x(a)) == True{} : Bool}, +hok: {okx(a_x(a)) == True{} : Bool})
  -> {Nat.max(tN(a_x(a)), Nat.add(L.total_ns(L.h_ts(h)), L.h_lat(h))) == tN(a_x(Met.add(a, h))) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Nat.max(0n, Nat.add(L.total_ns(L.h_ts(h)), L.h_lat(h))) == tN(a_x(Met.add(Met.Acc{bs, n, ok, cs, es, l, i, o, Met.NoExt{}, t}, h))) : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, +en1, ls1, +ln1, +xs1, +xn1}:
          match h:
            case Hit.Hit{ha, q, c, tt, +lat, bo, bi, e, b, m, u, hs}:
              match tt:
                case Civil.Time{+s0, +ns0, off}:
                  +s = Nat.add(s0, Nat.div(ns0, L.sec()))
                  +ns = Nat.mod(ns0, L.sec())
                  +en2 = Nat.add(ns, Nat.mod(lat, L.sec()))
                  +es2 = Nat.add(Nat.add(s, Nat.div(lat, L.sec())), Nat.div(en2, L.sec()))
                  +xn2 = Nat.mod(en2, L.sec())
                  +tx = tq(xs1, xn1, B9())
                  +t2 = tq(es2, xn2, B9())
                  +t0 = Nat.add(Nat.add(Nat.mul(s0, L.sec()), ns0), lat)
                  +nl = Met.no_later(xs1, xn1, es2, xn2)
                  +hxn = ok3(Nat.is_lt(en1, L.sec()), Nat.is_lt(ln1, L.sec()), Nat.is_lt(xn1, L.sec()), hok)
                  %pk(nl, es2, xn2, xs1, xn1, B9()) : {Nat.max(tx, t0) == _ : Nat}
                  %nl_same(Nat.cmp(xs1, es2), xs1, xn1, es2, xn2, B9(), {==}, hxn, PNat.mod_lt(en2, B9())) : {Nat.max(tx, t0) == Met.pick(Nat, _, t2, tx) : Nat}
                  %norm_end(s0, ns0, lat) : {Nat.max(tx, t0) == Met.nmax(tx, _) : Nat}
                  nmax_max(tx, t0)

def st_ok(a: Met.Acc, h: Hit.Hit, +hx: {is_ext(a_x(a)) == True{} : Bool}, +hok: {okx(a_x(a)) == True{} : Bool})
  -> {okx(a_x(Met.add(a, h))) == True{} : Bool}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({okx(a_x(Met.add(Met.Acc{bs, n, ok, cs, es, l, i, o, Met.NoExt{}, t}, h))) == True{} : Bool}, no_ft(hx))
        case Met.Ext{a1, b1, +es1, +en1, +ls1, +ln1, +xs1, +xn1}:
          match h:
            case Hit.Hit{ha, q, c, tt, +lat, bo, bi, e, b, m, u, hs}:
              match tt:
                case Civil.Time{+s0, +ns0, off}:
                  +s = Nat.add(s0, Nat.div(ns0, L.sec()))
                  +ns = Nat.mod(ns0, L.sec())
                  +en2 = Nat.add(ns, Nat.mod(lat, L.sec()))
                  +es2 = Nat.add(Nat.add(s, Nat.div(lat, L.sec())), Nat.div(en2, L.sec()))
                  +xn2 = Nat.mod(en2, L.sec())
                  +a1 = Nat.is_lt(en1, L.sec())
                  +a2 = Nat.is_lt(ln1, L.sec())
                  +a3 = Nat.is_lt(xn1, L.sec())
                  ok_mk(Nat.is_lt(Met.pick(Nat, Met.no_later(es1, en1, s, ns), en1, ns), L.sec()),
                    Nat.is_lt(Met.pick(Nat, Met.no_later(ls1, ln1, s, ns), ns, ln1), L.sec()),
                    Nat.is_lt(Met.pick(Nat, Met.no_later(xs1, xn1, es2, xn2), xn2, xn1), L.sec()),
                    pick_lt(Met.no_later(es1, en1, s, ns), en1, ns, L.sec(), ok1(a1, a2, a3, hok), PNat.mod_lt(ns0, B9())),
                    pick_lt(Met.no_later(ls1, ln1, s, ns), ns, ln1, L.sec(), PNat.mod_lt(ns0, B9()), ok2(a1, a2, a3, hok)),
                    pick_lt(Met.no_later(xs1, xn1, es2, xn2), xn2, xn1, L.sec(), PNat.mod_lt(en2, B9()), ok3(a1, a2, a3, hok)))

def first_ok(+bs: List<&2, Nat>, h: Hit.Hit) -> {okx(a_x(Met.add(Met.empty(bs), h))) == True{} : Bool}:
  match h:
    case Hit.Hit{ha, q, c, tt, +lat, bo, bi, e, b, m, u, hs}:
      match tt:
        case Civil.Time{+s0, +ns0, off}:
          +ns = Nat.mod(ns0, L.sec())
          +en2 = Nat.add(ns, Nat.mod(lat, L.sec()))
          ok_mk(Nat.is_lt(ns, L.sec()), Nat.is_lt(ns, L.sec()), Nat.is_lt(Nat.mod(en2, L.sec()), L.sec()),
            PNat.mod_lt(ns0, B9()), PNat.mod_lt(ns0, B9()), PNat.mod_lt(en2, B9()))

def first_e(+bs: List<&2, Nat>, h: Hit.Hit) -> {L.total_ns(L.h_ts(h)) == tE(a_x(Met.add(Met.empty(bs), h))) : Nat}:
  match h:
    case Hit.Hit{ha, q, c, tt, lat, bo, bi, e, b, m, u, hs}:
      match tt:
        case Civil.Time{+s0, +ns0, off}:
          norm_start(s0, ns0)

def first_l(+bs: List<&2, Nat>, h: Hit.Hit) -> {L.total_ns(L.h_ts(h)) == tL(a_x(Met.add(Met.empty(bs), h))) : Nat}:
  match h:
    case Hit.Hit{ha, q, c, tt, lat, bo, bi, e, b, m, u, hs}:
      match tt:
        case Civil.Time{+s0, +ns0, off}:
          norm_start(s0, ns0)

def first_n(+bs: List<&2, Nat>, h: Hit.Hit) -> {Nat.add(L.total_ns(L.h_ts(h)), L.h_lat(h)) == tN(a_x(Met.add(Met.empty(bs), h))) : Nat}:
  match h:
    case Hit.Hit{ha, q, c, tt, +lat, bo, bi, e, b, m, u, hs}:
      match tt:
        case Civil.Time{+s0, +ns0, off}:
          norm_end(s0, ns0, lat)

def f_okx(hs: List<&2, Hit.Hit>, +a: Met.Acc, +hx: {is_ext(a_x(a)) == True{} : Bool}, +hok: {okx(a_x(a)) == True{} : Bool})
  -> {okx(a_x(L.acc_all(hs, a))) == True{} : Bool}:
  match hs:
    case Nil{}:
      hok
    case Con{+h, +rest}:
      f_okx(rest, Met.add(a, h), add_x(a, h), st_ok(a, h, hx, hok))

def f_e(hs: List<&2, Hit.Hit>, +a: Met.Acc, +hx: {is_ext(a_x(a)) == True{} : Bool}, +hok: {okx(a_x(a)) == True{} : Bool})
  -> {L.min_of.go(L.starts(hs), tE(a_x(a))) == tE(a_x(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %f_e(rest, Met.add(a, h), add_x(a, h), st_ok(a, h, hx, hok)) : {L.min_of.go(L.starts(Con{h, rest}), tE(a_x(a))) == _ : Nat}
      %st_e(a, h, hx, hok) : {L.min_of.go(L.starts(rest), Nat.min(tE(a_x(a)), L.total_ns(L.h_ts(h)))) == L.min_of.go(L.starts(rest), _) : Nat}
      {==}

def f_l(hs: List<&2, Hit.Hit>, +a: Met.Acc, +hx: {is_ext(a_x(a)) == True{} : Bool}, +hok: {okx(a_x(a)) == True{} : Bool})
  -> {L.max_of.go(L.starts(hs), tL(a_x(a))) == tL(a_x(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %f_l(rest, Met.add(a, h), add_x(a, h), st_ok(a, h, hx, hok)) : {L.max_of.go(L.starts(Con{h, rest}), tL(a_x(a))) == _ : Nat}
      %st_l(a, h, hx, hok) : {L.max_of.go(L.starts(rest), Nat.max(tL(a_x(a)), L.total_ns(L.h_ts(h)))) == L.max_of.go(L.starts(rest), _) : Nat}
      {==}

def f_nd(hs: List<&2, Hit.Hit>, +a: Met.Acc, +hx: {is_ext(a_x(a)) == True{} : Bool}, +hok: {okx(a_x(a)) == True{} : Bool})
  -> {L.max_of.go(L.ends(hs), tN(a_x(a))) == tN(a_x(L.acc_all(hs, a))) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %f_nd(rest, Met.add(a, h), add_x(a, h), st_ok(a, h, hx, hok)) : {L.max_of.go(L.ends(Con{h, rest}), tN(a_x(a))) == _ : Nat}
      %st_n(a, h, hx, hok) : {L.max_of.go(L.ends(rest), Nat.max(tN(a_x(a)), Nat.add(L.total_ns(L.h_ts(h)), L.h_lat(h)))) == L.max_of.go(L.ends(rest), _) : Nat}
      {==}

def okE(x: Met.Ext, +h: {okx(x) == True{} : Bool}) -> {Nat.is_lt(x_en(x), L.sec()) == True{} : Bool}:
  match x:
    case Met.NoExt{}:
      {==}
    case Met.Ext{a, b, es, +en, ls, +ln, xs, +xn}:
      ok1(Nat.is_lt(en, L.sec()), Nat.is_lt(ln, L.sec()), Nat.is_lt(xn, L.sec()), h)

def okL(x: Met.Ext, +h: {okx(x) == True{} : Bool}) -> {Nat.is_lt(x_ln(x), L.sec()) == True{} : Bool}:
  match x:
    case Met.NoExt{}:
      {==}
    case Met.Ext{a, b, es, +en, ls, +ln, xs, +xn}:
      ok2(Nat.is_lt(en, L.sec()), Nat.is_lt(ln, L.sec()), Nat.is_lt(xn, L.sec()), h)

def okN(x: Met.Ext, +h: {okx(x) == True{} : Bool}) -> {Nat.is_lt(x_xn(x), L.sec()) == True{} : Bool}:
  match x:
    case Met.NoExt{}:
      {==}
    case Met.Ext{a, b, es, +en, ls, +ln, xs, +xn}:
      ok3(Nat.is_lt(en, L.sec()), Nat.is_lt(ln, L.sec()), Nat.is_lt(xn, L.sec()), h)

def c_ear(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {Met.utc(x_es(a_x(a)), x_en(a_x(a))) == L.s_earliest(Met.close(a)) : Maybe<&2, Civil.Time>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Met.utc(0n, 0n) == None{} : Maybe<&2, Civil.Time>}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def c_lat2(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {Met.utc(x_ls(a_x(a)), x_ln(a_x(a))) == L.s_latest(Met.close(a)) : Maybe<&2, Civil.Time>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Met.utc(0n, 0n) == None{} : Maybe<&2, Civil.Time>}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def c_end(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {Met.utc(x_xs(a_x(a)), x_xn(a_x(a))) == L.s_end(Met.close(a)) : Maybe<&2, Civil.Time>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Met.utc(0n, 0n) == None{} : Maybe<&2, Civil.Time>}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def c_dur(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {Met.span_ns(x_es(a_x(a)), x_en(a_x(a)), x_ls(a_x(a)), x_ln(a_x(a))) == L.s_duration(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Met.span_ns(0n, 0n, 0n, 0n) == 0n : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def c_wait(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool})
  -> {Met.span_ns(x_ls(a_x(a)), x_ln(a_x(a)), x_xs(a_x(a)), x_xn(a_x(a))) == L.s_wait(Met.close(a)) : Nat}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({Met.span_ns(0n, 0n, 0n, 0n) == 0n : Nat}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

# a time (s, ns < 1s) in UTC is the UTC time of s B + ns
def utc_tq(+s: Nat, +n: Nat, +hn: {Nat.is_lt(n, L.sec()) == True{} : Bool})
  -> {Met.utc(s, n) == Some{L.utc_at(tq(s, n, B9()))} : Maybe<&2, Civil.Time>}:
  %div_uq(s, n, B9(), hn) : {Met.utc(s, n) == Some{Civil.Time{_, Nat.mod(tq(s, n, B9()), L.sec()), 86400n}} : Maybe<&2, Civil.Time>}
  %mod_uq(s, n, B9(), hn) : {Met.utc(s, n) == Some{Civil.Time{s, _, 86400n}} : Maybe<&2, Civil.Time>}
  {==}

def L.met_span(bs, h, hs, ok, fits):
  +a1 = Met.add(Met.empty(bs), h)
  +A = L.acc_all(Con{h, hs}, Met.empty(bs))
  +X = a_x(A)
  +hx = sum_x(bs, h, hs)
  +hx1 = add_x(Met.empty(bs), h)
  +hok = f_okx(hs, a1, hx1, first_ok(bs, h))
  +t0 = L.total_ns(L.h_ts(h))
  +t1 = Nat.add(t0, L.h_lat(h))
  +mn = L.min_of(t0, L.starts(hs))
  +mx = L.max_of(t0, L.starts(hs))
  +me = L.max_of(t1, L.ends(hs))
  +eE = {%Equal.sym(Nat, t0, tE(a_x(a1)), first_e(bs, h)) : {L.min_of.go(L.starts(hs), _) == tE(X) : Nat};
         f_e(hs, a1, hx1, first_ok(bs, h)) : {mn == tE(X) : Nat}}
  +eL = {%Equal.sym(Nat, t0, tL(a_x(a1)), first_l(bs, h)) : {L.max_of.go(L.starts(hs), _) == tL(X) : Nat};
         f_l(hs, a1, hx1, first_ok(bs, h)) : {mx == tL(X) : Nat}}
  +eN = {%Equal.sym(Nat, t1, tN(a_x(a1)), first_n(bs, h)) : {L.max_of.go(L.ends(hs), _) == tN(X) : Nat};
         f_nd(hs, a1, hx1, first_ok(bs, h)) : {me == tN(X) : Nat}}
  +p1 = {%c_ear(A, hx) : {_ == Some{L.utc_at(mn)} : Maybe<&2, Civil.Time>};
         %Equal.sym(Nat, mn, tE(X), eE) : {Met.utc(x_es(X), x_en(X)) == Some{L.utc_at(_)} : Maybe<&2, Civil.Time>};
         utc_tq(x_es(X), x_en(X), okE(X, hok))
         : {L.s_earliest(L.summary(bs, Con{h, hs})) == Some{L.utc_at(mn)} : Maybe<&2, Civil.Time>}}
  +p2 = {%c_lat2(A, hx) : {_ == Some{L.utc_at(mx)} : Maybe<&2, Civil.Time>};
         %Equal.sym(Nat, mx, tL(X), eL) : {Met.utc(x_ls(X), x_ln(X)) == Some{L.utc_at(_)} : Maybe<&2, Civil.Time>};
         utc_tq(x_ls(X), x_ln(X), okL(X, hok))
         : {L.s_latest(L.summary(bs, Con{h, hs})) == Some{L.utc_at(mx)} : Maybe<&2, Civil.Time>}}
  +p3 = {%c_end(A, hx) : {_ == Some{L.utc_at(me)} : Maybe<&2, Civil.Time>};
         %Equal.sym(Nat, me, tN(X), eN) : {Met.utc(x_xs(X), x_xn(X)) == Some{L.utc_at(_)} : Maybe<&2, Civil.Time>};
         utc_tq(x_xs(X), x_xn(X), okN(X, hok))
         : {L.s_end(L.summary(bs, Con{h, hs})) == Some{L.utc_at(me)} : Maybe<&2, Civil.Time>}}
  +hle = {%eE : {Nat.is_le(_, tL(X)) == True{} : Bool};
          %eL : {Nat.is_le(mn, _) == True{} : Bool};
          le_trans(mn, t0, mx, min_go_le(L.starts(hs), t0), le_max_go(L.starts(hs), t0)) : {Nat.is_le(tE(X), tL(X)) == True{} : Bool}}
  +hle2 = {%eL : {Nat.is_le(_, tN(X)) == True{} : Bool};
           %eN : {Nat.is_le(mx, _) == True{} : Bool};
           mx_mono(hs, t0, t1, le_add(t0, L.h_lat(h))) : {Nat.is_le(tL(X), tN(X)) == True{} : Bool}}
  +p4 = {%c_dur(A, hx) : {_ == Nat.sub(mx, mn) : Nat};
         %Equal.sym(Nat, mx, tL(X), eL) : {Met.span_ns(x_es(X), x_en(X), x_ls(X), x_ln(X)) == Nat.sub(_, mn) : Nat};
         %Equal.sym(Nat, mn, tE(X), eE) : {Met.span_ns(x_es(X), x_en(X), x_ls(X), x_ln(X)) == Nat.sub(tL(X), _) : Nat};
         Equal.sym(Nat, Nat.sub(tL(X), tE(X)), Met.span_ns(x_es(X), x_en(X), x_ls(X), x_ln(X)),
           sp(x_es(X), x_en(X), x_ls(X), x_ln(X), hle, okE(X, hok), okL(X, hok)))
         : {L.s_duration(L.summary(bs, Con{h, hs})) == Nat.sub(mx, mn) : Nat}}
  +p5 = {%c_wait(A, hx) : {_ == Nat.sub(me, mx) : Nat};
         %Equal.sym(Nat, me, tN(X), eN) : {Met.span_ns(x_ls(X), x_ln(X), x_xs(X), x_xn(X)) == Nat.sub(_, mx) : Nat};
         %Equal.sym(Nat, mx, tL(X), eL) : {Met.span_ns(x_ls(X), x_ln(X), x_xs(X), x_xn(X)) == Nat.sub(tN(X), _) : Nat};
         Equal.sym(Nat, Nat.sub(tN(X), tL(X)), Met.span_ns(x_ls(X), x_ln(X), x_xs(X), x_xn(X)),
           sp(x_ls(X), x_ln(X), x_xs(X), x_xn(X), hle2, okL(X, hok), okN(X, hok)))
         : {L.s_wait(L.summary(bs, Con{h, hs})) == Nat.sub(me, mx) : Nat}}
  (p1, (p2, (p3, (p4, p5))))

# =====================================================================
# Reports: lib/report.bend and LAWS' text_src, json_src, hist_rows
# =====================================================================

def split_step(b: Bool, +c: Char, +r: List<&2, String>)
  -> {Tab.pick(List<&2, String>, b, Con{"", r}, Tab.split_cons(c, r)) == L.pick(List<&2, String>, b, Con{"", r}, L.split_cons(c, r)) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match r:
        case Nil{}:
          {==}
        case Con{p, rest}:
          {==}

def split_same(+k: U32, s: String) -> {Tab.split_on(k, s) == L.split_on(k, s) : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+j}:
          %split_same(k, rest)
            : {Tab.pick(List<&2, String>, U32.is_eq(j, k), Con{"", Tab.split_on(k, rest)}, Tab.split_cons(Chr{j}, Tab.split_on(k, rest)))
               == L.pick(List<&2, String>, U32.is_eq(j, k), Con{"", _}, L.split_cons(Chr{j}, _)) : List<&2, String>}
          split_step(U32.is_eq(j, k), Chr{j}, Tab.split_on(k, rest))

def pp2(-A: Data, c: Bool, -a: A, -b: A, -x: A, -y: A, ea: {a == x : A}, eb: {b == y : A})
  -> {Rep.pick(A, c, a, b) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def code_of_same(p: Sigma<&2, &2, Nat, _ => Nat>) -> {Rep.code_of(p) == L.code_of(p) : Nat}:
  match p:
    case (k, v):
      {==}

def insert_same(+p: Sigma<&2, &2, Nat, _ => Nat>, cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>)
  -> {Rep.insert_code(p, cs) == L.insert_code(p, cs) : List<&2, Sigma<&2, &2, Nat, _ => Nat>>}:
  match cs:
    case Nil{}:
      {==}
    case Con{+q, +rest}:
      %code_of_same(p)
        : {Rep.insert_code(p, Con{q, rest}) == L.pick(List<&2, Sigma<&2, &2, Nat, _ => Nat>>, String.is_lt(Dec.show(_), Dec.show(L.code_of(q))),
            Con{p, Con{q, rest}}, Con{q, L.insert_code(p, rest)}) : List<&2, Sigma<&2, &2, Nat, _ => Nat>>}
      %code_of_same(q)
        : {Rep.insert_code(p, Con{q, rest}) == L.pick(List<&2, Sigma<&2, &2, Nat, _ => Nat>>, String.is_lt(Dec.show(Rep.code_of(p)), Dec.show(_)),
            Con{p, Con{q, rest}}, Con{q, L.insert_code(p, rest)}) : List<&2, Sigma<&2, &2, Nat, _ => Nat>>}
      pp2(List<&2, Sigma<&2, &2, Nat, _ => Nat>>, String.is_lt(Dec.show(Rep.code_of(p)), Dec.show(Rep.code_of(q))),
        Con{p, Con{q, rest}}, Con{q, Rep.insert_code(p, rest)}, Con{p, Con{q, rest}}, Con{q, L.insert_code(p, rest)},
        {==}, Equal.cong(List<&2, Sigma<&2, &2, Nat, _ => Nat>>, List<&2, Sigma<&2, &2, Nat, _ => Nat>>, t => Con{q, t},
          Rep.insert_code(p, rest), L.insert_code(p, rest), insert_same(p, rest)))

def by_text_same(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>)
  -> {Rep.codes_by_text(cs) == L.codes_by_text(cs) : List<&2, Sigma<&2, &2, Nat, _ => Nat>>}:
  match cs:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      %by_text_same(rest) : {Rep.codes_by_text(Con{p, rest}) == L.insert_code(p, _) : List<&2, Sigma<&2, &2, Nat, _ => Nat>>}
      insert_same(p, Rep.codes_by_text(rest))


def esc_same(+s: String) -> {Json.esc(s) == L.jesc(s) : String}:
  PCodec.esc_go_j(String.length(s), s)

def has_char_same(s: String, +k: U32) -> {Rep.has_char(s, k) == L.has_char(s, k) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+j}:
          %has_char_same(rest, k) : {Rep.has_char(SCon{Chr{j}, rest}, k) == Bool.or(U32.is_eq(j, k), _) : Bool}
          {==}

def rjesc_ff_same(ps: List<&2, String>) -> {Rep.rjesc_ff(ps) == L.rjesc_ff(ps) : String}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      match rest:
        case Nil{}:
          esc_same(p)
        case Con{+q, +more}:
          %rjesc_ff_same(Con{q, more}) : {Rep.rjesc_ff(Con{p, Con{q, more}}) == L.jesc(p) ++ "\\f" ++ _ : String}
          %esc_same(p) : {Rep.rjesc_ff(Con{p, Con{q, more}}) == _ ++ "\\f" ++ Rep.rjesc_ff(Con{q, more}) : String}
          {==}

def ff_split_same(+p: String) -> {Rep.rjesc_ff(Tab.split_on(12, p)) == L.rjesc_ff(L.split_on(12, p)) : String}:
  %split_same(12, p) : {Rep.rjesc_ff(Tab.split_on(12, p)) == L.rjesc_ff(_) : String}
  rjesc_ff_same(Tab.split_on(12, p))

def rjesc_parts_same(ps: List<&2, String>) -> {Rep.rjesc_parts(ps) == L.rjesc_parts(ps) : String}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      match rest:
        case Nil{}:
          ff_split_same(p)
        case Con{+q, +more}:
          %rjesc_parts_same(Con{q, more}) : {Rep.rjesc_parts(Con{p, Con{q, more}}) == L.rjesc_ff(L.split_on(12, p)) ++ "\\b" ++ _ : String}
          %ff_split_same(p) : {Rep.rjesc_parts(Con{p, Con{q, more}}) == _ ++ "\\b" ++ Rep.rjesc_parts(Con{q, more}) : String}
          {==}

def rjesc_of_same(b: Bool, +s: String)
  -> {Rep.rjesc_of(b, s) == L.pick(String, b, L.rjesc_parts(L.split_on(8, s)), L.jesc(s)) : String}:
  match b:
    case True{}:
      %split_same(8, s) : {Rep.rjesc_of(True{}, s) == L.rjesc_parts(_) : String}
      rjesc_parts_same(Tab.split_on(8, s))
    case False{}:
      esc_same(s)

def rjesc_str_same(+s: String) -> {Rep.rjesc_str(s) == L.rjesc_str(s) : String}:
  %has_char_same(s, 8) : {Rep.rjesc_str(s) == L.pick(String, Bool.or(_, L.has_char(s, 12)), L.rjesc_parts(L.split_on(8, s)), L.jesc(s)) : String}
  %has_char_same(s, 12) : {Rep.rjesc_str(s) == L.pick(String, Bool.or(Rep.has_char(s, 8), _), L.rjesc_parts(L.split_on(8, s)), L.jesc(s)) : String}
  rjesc_of_same(Bool.or(Rep.has_char(s, 8), Rep.has_char(s, 12)), s)

def rjson_strs_same(vs: List<&2, String>) -> {Rep.rjson_strs(vs) == L.rjson_strs(vs) : List<&2, String>}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      %rjson_strs_same(rest) : {Rep.rjson_strs(Con{v, rest}) == Con{"\"" ++ L.rjesc_str(v) ++ "\"", _} : List<&2, String>}
      %rjesc_str_same(v) : {Rep.rjson_strs(Con{v, rest}) == Con{"\"" ++ _ ++ "\"", Rep.rjson_strs(rest)} : List<&2, String>}
      {==}

def join_same(+sep: String, xs: List<&2, String>) -> {Rep.join_str(sep, xs) == L.join_str(sep, xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      match rest:
        case Nil{}:
          {==}
        case Con{+y, +more}:
          %join_same(sep, Con{y, more}) : {Rep.join_str(sep, Con{x, Con{y, more}}) == x ++ sep ++ _ : String}
          {==}

def json_codes_same(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> {Rep.json_codes(cs) == L.json_codes(cs) : List<&2, String>}:
  match cs:
    case Nil{}:
      {==}
    case Con{p, +rest}:
      match p:
        case (k, v):
          %json_codes_same(rest) : {Rep.json_codes(Con{(k, v), rest}) == Con{"\"" ++ Dec.show(k) ++ "\":" ++ Dec.show(v), _} : List<&2, String>}
          {==}

def json_buckets_same(bs: List<&2, Nat>, +cs: List<&2, Nat>) -> {Rep.json_buckets(bs, cs) == L.json_buckets(bs, cs) : List<&2, String>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      %json_buckets_same(rest, List.drop(&2, Nat, cs, 1n))
        : {Rep.json_buckets(Con{b, rest}, cs) == Con{"\"" ++ Dec.show(b) ++ "\":" ++ Dec.show(L.head_or(0n, cs)), _} : List<&2, String>}
      {==}

def json_hist_same(+bs: List<&2, Nat>, +h: List<&2, Nat>)
  -> {Rep.json_hist(bs, h) == L.pick(String, List.is_empty(&2, Nat, bs), "", ",\"buckets\":{" ++ L.join_str(",", L.json_buckets(bs, h)) ++ "}") : String}:
  %json_buckets_same(bs, h)
    : {Rep.json_hist(bs, h) == L.pick(String, List.is_empty(&2, Nat, bs), "", ",\"buckets\":{" ++ L.join_str(",", _) ++ "}") : String}
  %join_same(",", Rep.json_buckets(bs, h))
    : {Rep.json_hist(bs, h) == L.pick(String, List.is_empty(&2, Nat, bs), "", ",\"buckets\":{" ++ _ ++ "}") : String}
  pp2(String, List.is_empty(&2, Nat, bs), "", ",\"buckets\":{" ++ Rep.join_str(",", Rep.json_buckets(bs, h)) ++ "}",
    "", ",\"buckets\":{" ++ Rep.join_str(",", Rep.json_buckets(bs, h)) ++ "}", {==}, {==})

def json_time_same(m: Maybe<&2, Civil.Time>, +off: Nat) -> {Rep.json_time(m, off) == L.json_time(m, off) : String}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      match t:
        case Civil.Time{s, ns, o}:
          {==}

def jtpl(+s: Met.Summary, hist: String, te: String, tl: String, tn: String, codes: String, errs: String) -> String:
  "{\"latencies\":{\"total\":" ++ Big.show(L.s_lat_total(s)) ++ ",\"mean\":" ++ Dec.show(L.s_lat_mean(s))
  ++ ",\"50th\":" ++ Dec.show(L.s_p50(s)) ++ ",\"90th\":" ++ Dec.show(L.s_p90(s)) ++ ",\"95th\":" ++ Dec.show(L.s_p95(s))
  ++ ",\"99th\":" ++ Dec.show(L.s_p99(s)) ++ ",\"max\":" ++ Dec.show(L.s_lat_max(s)) ++ ",\"min\":" ++ Dec.show(L.s_lat_min(s)) ++ "}"
  ++ hist
  ++ ",\"bytes_in\":{\"total\":" ++ Big.show(L.s_bytes_in(s)) ++ ",\"mean\":" ++ F64.json(L.s_in_mean(s)) ++ "}"
  ++ ",\"bytes_out\":{\"total\":" ++ Big.show(L.s_bytes_out(s)) ++ ",\"mean\":" ++ F64.json(L.s_out_mean(s)) ++ "}"
  ++ ",\"earliest\":" ++ te ++ ",\"latest\":" ++ tl
  ++ ",\"end\":" ++ tn
  ++ ",\"duration\":" ++ Dec.show(L.s_duration(s)) ++ ",\"wait\":" ++ Dec.show(L.s_wait(s))
  ++ ",\"requests\":" ++ Dec.show(L.s_requests(s)) ++ ",\"rate\":" ++ F64.json(L.s_rate(s))
  ++ ",\"throughput\":" ++ F64.json(L.s_throughput(s)) ++ ",\"success\":" ++ F64.json(L.s_ratio(s))
  ++ ",\"status_codes\":{" ++ codes ++ "}"
  ++ ",\"errors\":[" ++ errs ++ "]}\n"

def json_codes_by(+cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>)
  -> {Rep.join_str(",", Rep.json_codes(Rep.codes_by_text(cs))) == L.join_str(",", L.json_codes(L.codes_by_text(cs))) : String}:
  %by_text_same(cs) : {Rep.join_str(",", Rep.json_codes(Rep.codes_by_text(cs))) == L.join_str(",", L.json_codes(_)) : String}
  %json_codes_same(Rep.codes_by_text(cs)) : {Rep.join_str(",", Rep.json_codes(Rep.codes_by_text(cs))) == L.join_str(",", _) : String}
  join_same(",", Rep.json_codes(Rep.codes_by_text(cs)))

def json_errs(+es: List<&2, String>) -> {Rep.join_str(",", Rep.rjson_strs(es)) == L.join_str(",", L.rjson_strs(es)) : String}:
  %rjson_strs_same(es) : {Rep.join_str(",", Rep.rjson_strs(es)) == L.join_str(",", _) : String}
  join_same(",", Rep.rjson_strs(es))

def L.report_json(s, z):
  match s:
    case Met.Summary{+req, +ok, +cs, +es, +lt, +lm, +lmin, +lmax, +p50, +p90, +p95, +p99, +bi, +bo, +im, +om, +rate, +thr, +ratio, +e, +l, +n, +du, +w, +b, +h}:
      match z:
        case Rep.Zones{+ze, +zl, +zn}:
          +S = {Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} : Met.Summary}
          +Z = {Rep.Zones{ze, zl, zn} : Rep.Zones}
          %json_hist_same(b, h)
            : {Rep.json(S, Z) == jtpl(S, _, L.json_time(e, ze), L.json_time(l, zl), L.json_time(n, zn),
                L.join_str(",", L.json_codes(L.codes_by_text(cs))), L.join_str(",", L.rjson_strs(es))) : String}
          %json_time_same(e, ze)
            : {Rep.json(S, Z) == jtpl(S, Rep.json_hist(b, h), _, L.json_time(l, zl), L.json_time(n, zn),
                L.join_str(",", L.json_codes(L.codes_by_text(cs))), L.join_str(",", L.rjson_strs(es))) : String}
          %json_time_same(l, zl)
            : {Rep.json(S, Z) == jtpl(S, Rep.json_hist(b, h), Rep.json_time(e, ze), _, L.json_time(n, zn),
                L.join_str(",", L.json_codes(L.codes_by_text(cs))), L.join_str(",", L.rjson_strs(es))) : String}
          %json_time_same(n, zn)
            : {Rep.json(S, Z) == jtpl(S, Rep.json_hist(b, h), Rep.json_time(e, ze), Rep.json_time(l, zl), _,
                L.join_str(",", L.json_codes(L.codes_by_text(cs))), L.join_str(",", L.rjson_strs(es))) : String}
          %json_codes_by(cs)
            : {Rep.json(S, Z) == jtpl(S, Rep.json_hist(b, h), Rep.json_time(e, ze), Rep.json_time(l, zl), Rep.json_time(n, zn),
                _, L.join_str(",", L.rjson_strs(es))) : String}
          %json_errs(es)
            : {Rep.json(S, Z) == jtpl(S, Rep.json_hist(b, h), Rep.json_time(e, ze), Rep.json_time(l, zl), Rep.json_time(n, zn),
                Rep.join_str(",", Rep.json_codes(Rep.codes_by_text(cs))), _) : String}
          {==}

# =====================================================================
# The byte order of strings
# =====================================================================

def flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def fin_flip(t: Cmp, ah: Bool, bh: Bool) -> {Word.cmp.fin(bh, ah, flip(t)) == flip(Word.cmp.fin(ah, bh, t)) : Cmp}:
  match t:
    case LT{}:
      {==}
    case EQ{}:
      match ah bh:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case GT{}:
      {==}

# Word.cmp decides equality (as proofs/codec.bend shows)
def fin_eq_t(t: Cmp, -ah: Bool, -bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, no_ft(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, no_ft(h))

def fin_eq_h(t: Cmp, ah: Bool, bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {ah == bh : Bool}:
  match t:
    case LT{}:
      Empty.absurd({ah == bh : Bool}, no_ft(h))
    case GT{}:
      Empty.absurd({ah == bh : Bool}, no_ft(h))
    case EQ{}:
      match ah bh:
        case False{} False{}:
          {==}
        case True{} True{}:
          {==}
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, no_ft(h))
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, no_ft(h))

def weq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          %weq(p, at, bt, Equal.cong(Cmp, Bool, Cmp.is_eq, Word.cmp(p, at, bt), EQ{}, fin_eq_t(Word.cmp(p, at, bt), ah, bh, h)))
            : {WCon{ah, at} == WCon{bh, _} : Word(1n+p)}
          %fin_eq_h(Word.cmp(p, at, bt), ah, bh, h) : {WCon{ah, at} == WCon{_, at} : Word(1n+p)}
          {==}

def w_anti(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, b, a) == flip(Word.cmp(n, a, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, bt, at), flip(Word.cmp(p, at, bt)), w_anti(p, at, bt)) : {Word.cmp.fin(bh, ah, _) == flip(Word.cmp.fin(ah, bh, Word.cmp(p, at, bt))) : Cmp}
          fin_flip(Word.cmp(p, at, bt), ah, bh)

def w_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{} : Cmp}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+(+p):
      match a:
        case WCon{ah, +at}:
          match ah:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, w_refl(p, at)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, w_refl(p, at)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}

def lt_ne_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  no_ft(Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def gt_ne_lt(e: {GT{} == LT{} : Cmp}) -> Empty:
  no_ft(Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), GT{}, LT{}, e))

def eq_ne_lt(e: {EQ{} == LT{} : Cmp}) -> Empty:
  no_ft(Equal.cong(Cmp, Bool, c => Cmp.is_lt(c), EQ{}, LT{}, e))

# the head bits decide when the tails tie
def bool_trans(a: Bool, b: Bool, c: Bool, +h1: {Bool.cmp(a, b) == LT{} : Cmp}, +h2: {Bool.cmp(b, c) == LT{} : Cmp}) -> Empty:
  match a b:
    case False{} False{}:
      eq_ne_lt(h1)
    case False{} True{}:
      match c:
        case False{}:
          gt_ne_lt(h2)
        case True{}:
          eq_ne_lt(h2)
    case True{} False{}:
      gt_ne_lt(h1)
    case True{} True{}:
      eq_ne_lt(h1)

def w_trans.of(t1: Cmp, t2: Cmp, +p: Nat, +ah: Bool, +at: Word(p), +bh: Bool, +bt: Word(p), +ch: Bool, +ct: Word(p),
  +e1: {Word.cmp(p, at, bt) == t1 : Cmp}, +e2: {Word.cmp(p, bt, ct) == t2 : Cmp},
  +h1: {Word.cmp.fin(ah, bh, t1) == LT{} : Cmp}, +h2: {Word.cmp.fin(bh, ch, t2) == LT{} : Cmp},
  ih: {Word.cmp(p, at, bt) == LT{} : Cmp} -> {Word.cmp(p, bt, ct) == LT{} : Cmp} -> {Word.cmp(p, at, ct) == LT{} : Cmp})
  -> {Word.cmp.fin(ah, ch, Word.cmp(p, at, ct)) == LT{} : Cmp}:
  match t1:
    case LT{}:
      match t2:
        case LT{}:
          %Equal.sym(Cmp, Word.cmp(p, at, ct), LT{}, ih(e1, e2)) : {Word.cmp.fin(ah, ch, _) == LT{} : Cmp}
          {==}
        case EQ{}:
          +ebc = weq(p, bt, ct, Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, bt, ct), EQ{}, e2))
          %ebc : {Word.cmp.fin(ah, ch, Word.cmp(p, at, _)) == LT{} : Cmp}
          %Equal.sym(Cmp, Word.cmp(p, at, bt), LT{}, e1) : {Word.cmp.fin(ah, ch, _) == LT{} : Cmp}
          {==}
        case GT{}:
          Empty.absurd({Word.cmp.fin(ah, ch, Word.cmp(p, at, ct)) == LT{} : Cmp}, gt_ne_lt(h2))
    case EQ{}:
      match t2:
        case LT{}:
          +eab = weq(p, at, bt, Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, e1))
          %Equal.sym(Word(p), at, bt, eab) : {Word.cmp.fin(ah, ch, Word.cmp(p, _, ct)) == LT{} : Cmp}
          %Equal.sym(Cmp, Word.cmp(p, bt, ct), LT{}, e2) : {Word.cmp.fin(ah, ch, _) == LT{} : Cmp}
          {==}
        case EQ{}:
          Empty.absurd({Word.cmp.fin(ah, ch, Word.cmp(p, at, ct)) == LT{} : Cmp}, bool_trans(ah, bh, ch, h1, h2))
        case GT{}:
          Empty.absurd({Word.cmp.fin(ah, ch, Word.cmp(p, at, ct)) == LT{} : Cmp}, gt_ne_lt(h2))
    case GT{}:
      Empty.absurd({Word.cmp.fin(ah, ch, Word.cmp(p, at, ct)) == LT{} : Cmp}, gt_ne_lt(h1))

def w_trans(n: Nat, a: Word(n), b: Word(n), c: Word(n), +h1: {Word.cmp(n, a, b) == LT{} : Cmp}, +h2: {Word.cmp(n, b, c) == LT{} : Cmp})
  -> {Word.cmp(n, a, c) == LT{} : Cmp}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          Empty.absurd({EQ{} == LT{} : Cmp}, eq_ne_lt(h1))
    case 1n+(+p):
      match a b c:
        case WCon{+ah, +at} WCon{+bh, +bt} WCon{+ch, +ct}:
          w_trans.of(Word.cmp(p, at, bt), Word.cmp(p, bt, ct), p, ah, at, bh, bt, ch, ct, {==}, {==}, h1, h2,
            x => y => w_trans(p, at, bt, ct, x, y))

def ccmp(a: Char, b: Char) -> Cmp:
  match a b:
    case Chr{x} Chr{y}:
      U32.cmp(x, y)

def c_anti(a: Char, b: Char) -> {ccmp(b, a) == flip(ccmp(a, b)) : Cmp}:
  match a:
    case Chr{u}:
      match u:
        case U32{x}:
          match b:
            case Chr{v}:
              match v:
                case U32{y}:
                  w_anti(32n, x, y)

def c_refl(a: Char) -> {ccmp(a, a) == EQ{} : Cmp}:
  match a:
    case Chr{u}:
      match u:
        case U32{x}:
          w_refl(32n, x)

def c_eqv(a: Char, b: Char, +h: {ccmp(a, b) == EQ{} : Cmp}) -> {a == b : Char}:
  match a:
    case Chr{u}:
      match u:
        case U32{+x}:
          match b:
            case Chr{v}:
              match v:
                case U32{+y}:
                  %weq(32n, x, y, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Word.cmp(32n, x, y), EQ{}, h)) : {Chr{U32{x}} == Chr{U32{_}} : Char}
                  {==}

def c_trans(a: Char, b: Char, c: Char, +h1: {ccmp(a, b) == LT{} : Cmp}, +h2: {ccmp(b, c) == LT{} : Cmp}) -> {ccmp(a, c) == LT{} : Cmp}:
  match a:
    case Chr{u}:
      match u:
        case U32{x}:
          match b:
            case Chr{v}:
              match v:
                case U32{y}:
                  match c:
                    case Chr{w}:
                      match w:
                        case U32{z}:
                          w_trans(32n, x, y, z, h1, h2)

# a string order that reads like its definition
def cpick(c: Cmp, r: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      r
    case GT{}:
      GT{}

def sord(a: String, b: String) -> Cmp:
  match a b:
    case SNil{} SNil{}:
      EQ{}
    case SNil{} SCon{c, t}:
      LT{}
    case SCon{c, t} SNil{}:
      GT{}
    case SCon{c1, t1} SCon{c2, t2}:
      cpick(ccmp(c1, c2), sord(t1, t2))

def rec_fin(-h1: Char, -h2: Char, r: (String & String) & Cmp) -> {String.order.fin(String.cmp.rec(h1, h2, r)) == String.order.fin(r) : Cmp}:
  match r:
    case (xy, c):
      match xy:
        case (x, y):
          {==}

def so_step(c: Cmp, -h1: Char, -h2: Char, +t1: String, +t2: String, ih: {sord(t1, t2) == String.order(t1, t2) : Cmp})
  -> {cpick(c, sord(t1, t2)) == String.order.fin(String.cmp.fin(t1, t2, ((h1, h2), c))) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      %Equal.sym(Cmp, String.order.fin(String.cmp.rec(h1, h2, String.cmp(t1, t2))), String.order.fin(String.cmp(t1, t2)), rec_fin(h1, h2, String.cmp(t1, t2))) : {sord(t1, t2) == _ : Cmp}
      ih
    case GT{}:
      {==}

def so_order(a: String, b: String) -> {sord(a, b) == String.order(a, b) : Cmp}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{c, t}:
          {==}
    case SCon{c1, +t1}:
      match c1:
        case Chr{u1}:
          match u1:
            case U32{+x}:
              match b:
                case SNil{}:
                  {==}
                case SCon{c2, +t2}:
                  match c2:
                    case Chr{u2}:
                      match u2:
                        case U32{+y}:
                          so_step(Word.cmp(32n, x, y), Chr{U32{x}}, Chr{U32{y}}, t1, t2, so_order(t1, t2))

def cpick_flip(c: Cmp, r: Cmp) -> {cpick(flip(c), flip(r)) == flip(cpick(c, r)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def so_anti(a: String, b: String) -> {sord(b, a) == flip(sord(a, b)) : Cmp}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{c, t}:
      {==}
    case SCon{c, t} SNil{}:
      {==}
    case SCon{+c1, +t1} SCon{+c2, +t2}:
      %Equal.sym(Cmp, ccmp(c2, c1), flip(ccmp(c1, c2)), c_anti(c1, c2)) : {cpick(_, sord(t2, t1)) == flip(cpick(ccmp(c1, c2), sord(t1, t2))) : Cmp}
      %Equal.sym(Cmp, sord(t2, t1), flip(sord(t1, t2)), so_anti(t1, t2)) : {cpick(flip(ccmp(c1, c2)), _) == flip(cpick(ccmp(c1, c2), sord(t1, t2))) : Cmp}
      cpick_flip(ccmp(c1, c2), sord(t1, t2))

def so_refl(a: String) -> {sord(a, a) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Cmp, ccmp(c, c), EQ{}, c_refl(c)) : {cpick(_, sord(t, t)) == EQ{} : Cmp}
      so_refl(t)

def so_eqv.of(k: Cmp, +c1: Char, +t1: String, +c2: Char, +t2: String, +ek: {ccmp(c1, c2) == k : Cmp},
  +h: {cpick(k, sord(t1, t2)) == EQ{} : Cmp}, ih: {sord(t1, t2) == EQ{} : Cmp} -> {t1 == t2 : String})
  -> {SCon{c1, t1} == SCon{c2, t2} : String}:
  match k:
    case LT{}:
      Empty.absurd({SCon{c1, t1} == SCon{c2, t2} : String}, lt_ne_eq(h))
    case EQ{}:
      %c_eqv(c1, c2, ek) : {SCon{c1, t1} == SCon{_, t2} : String}
      %ih(h) : {SCon{c1, t1} == SCon{c1, _} : String}
      {==}
    case GT{}:
      Empty.absurd({SCon{c1, t1} == SCon{c2, t2} : String}, no_ft(Equal.cong(Cmp, Bool, x => Cmp.is_gt(x), EQ{}, GT{}, Equal.sym(Cmp, GT{}, EQ{}, h))))

def so_eqv(a: String, b: String, +h: {sord(a, b) == EQ{} : Cmp}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{c, t}:
      Empty.absurd({SNil{} == SCon{c, t} : String}, lt_ne_eq(h))
    case SCon{c, t} SNil{}:
      Empty.absurd({SCon{c, t} == SNil{} : String}, no_ft(Equal.cong(Cmp, Bool, x => Cmp.is_gt(x), EQ{}, GT{}, Equal.sym(Cmp, GT{}, EQ{}, h))))
    case SCon{+c1, +t1} SCon{+c2, +t2}:
      so_eqv.of(ccmp(c1, c2), c1, t1, c2, t2, {==}, h, e => so_eqv(t1, t2, e))

def eq_fin(r: (String & String) & Cmp) -> {Cmp.is_eq(String.order.fin(r)) == String.eq.fin(r) : Bool}:
  match r:
    case (xy, c):
      match xy:
        case (x, y):
          {==}

# String.is_lt and String.eq read the order
def s_lt(+a: String, +b: String) -> {Cmp.is_lt(sord(a, b)) == String.is_lt(a, b) : Bool}:
  %Equal.sym(Cmp, sord(a, b), String.order(a, b), so_order(a, b)) : {Cmp.is_lt(_) == String.is_lt(a, b) : Bool}
  {==}

def s_eq(+a: String, +b: String) -> {Cmp.is_eq(sord(a, b)) == String.eq(a, b) : Bool}:
  %Equal.sym(Cmp, sord(a, b), String.order(a, b), so_order(a, b)) : {Cmp.is_eq(_) == String.eq(a, b) : Bool}
  eq_fin(String.cmp(a, b))

def cmp_lt(c: Cmp, +h: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, no_ft(h))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, no_ft(h))

def s_lt_ord(+x: String, +y: String, +h: {String.is_lt(x, y) == True{} : Bool}) -> {sord(x, y) == LT{} : Cmp}:
  cmp_lt(sord(x, y), Equal.trans(Bool, Cmp.is_lt(sord(x, y)), String.is_lt(x, y), True{}, s_lt(x, y), h))

def s_asym(+x: String, +y: String, +h1: {String.is_lt(x, y) == True{} : Bool}, +h2: {String.is_lt(y, x) == True{} : Bool}) -> Empty:
  +e1 = s_lt_ord(x, y, h1)
  +e2 = {%so_anti(x, y) : {_ == LT{} : Cmp}; s_lt_ord(y, x, h2) : {flip(sord(x, y)) == LT{} : Cmp}}
  +e3 = {%e1 : {flip(_) == LT{} : Cmp}; e2 : {GT{} == LT{} : Cmp}}
  gt_ne_lt(e3)

def s_tri.of(k: Cmp, +x: String, +y: String, +ek: {sord(x, y) == k : Cmp},
  +h1: {String.is_lt(x, y) == False{} : Bool}, +h2: {String.is_lt(y, x) == False{} : Bool}) -> {x == y : String}:
  match k:
    case LT{}:
      Empty.absurd({x == y : String}, no_ft(Equal.trans(Bool, False{}, String.is_lt(x, y), True{}, Equal.sym(Bool, String.is_lt(x, y), False{}, h1),
        {%s_lt(x, y) : {_ == True{} : Bool};
         %Equal.sym(Cmp, sord(x, y), LT{}, ek) : {Cmp.is_lt(_) == True{} : Bool}; {==} : {String.is_lt(x, y) == True{} : Bool}})))
    case EQ{}:
      so_eqv(x, y, ek)
    case GT{}:
      +e = {%Equal.sym(Cmp, sord(y, x), flip(sord(x, y)), so_anti(x, y)) : {_ == LT{} : Cmp}; %Equal.sym(Cmp, sord(x, y), GT{}, ek) : {flip(_) == LT{} : Cmp}; {==} : {sord(y, x) == LT{} : Cmp}}
      Empty.absurd({x == y : String}, no_ft(Equal.trans(Bool, False{}, String.is_lt(y, x), True{}, Equal.sym(Bool, String.is_lt(y, x), False{}, h2),
        {%s_lt(y, x) : {_ == True{} : Bool};
         %Equal.sym(Cmp, sord(y, x), LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}; {==} : {String.is_lt(y, x) == True{} : Bool}})))

def s_tri(+x: String, +y: String, +h1: {String.is_lt(x, y) == False{} : Bool}, +h2: {String.is_lt(y, x) == False{} : Bool}) -> {x == y : String}:
  s_tri.of(sord(x, y), x, y, {==}, h1, h2)

def eqflip(c: Cmp) -> {Cmp.is_eq(c) == Cmp.is_eq(flip(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# String.eq is symmetric
def s_eq_sym(+a: String, +b: String) -> {String.eq(a, b) == String.eq(b, a) : Bool}:
  %s_eq(a, b) : {_ == String.eq(b, a) : Bool}
  %s_eq(b, a) : {Cmp.is_eq(sord(a, b)) == _ : Bool}
  %Equal.sym(Cmp, sord(b, a), flip(sord(a, b)), so_anti(a, b)) : {Cmp.is_eq(sord(a, b)) == Cmp.is_eq(_) : Bool}
  eqflip(sord(a, b))

# ---------------------------------------------------------------------
# Booleans
# ---------------------------------------------------------------------

def or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or_swap(a: Bool, b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def or_dup(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(Bool.or(a, b), Bool.or(a, c)) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# =====================================================================
# The error set: a merge of ascending, distinct lists
# =====================================================================

def hs_step(lt: Bool, gt: Bool, +x: String, +xr: List<&2, String>, +y: String, +yr: List<&2, String>, +g: Nat, +e: String, +k: Nat,
  +elt: {String.is_lt(x, y) == lt : Bool}, +egt: {String.is_lt(y, x) == gt : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, String, xr), 1n+List.length(&2, String, yr)), k) == g : Nat},
  ih: @xs2: List<&2, String> -> @ys2: List<&2, String> -> @k3: Nat
    -> {Nat.add(Nat.add(List.length(&2, String, xs2), List.length(&2, String, ys2)), k3) == g : Nat}
    -> {Bool.or(L.has_str(e, xs2), L.has_str(e, ys2)) == L.has_str(e, Met.strs_merge.go(g, xs2, ys2)) : Bool})
  -> {Bool.or(L.has_str(e, Con{x, xr}), L.has_str(e, Con{y, yr}))
      == L.has_str(e, Con{Met.pick(String, gt, y, x), Met.strs_merge.go(g, Met.pick(List<&2, String>, gt, Con{x, xr}, xr), Met.pick(List<&2, String>, lt, Con{y, yr}, yr))}) : Bool}:
  match lt:
    case True{}:
      match gt:
        case True{}:
          Empty.absurd({Bool.or(L.has_str(e, Con{x, xr}), L.has_str(e, Con{y, yr}))
            == L.has_str(e, Con{y, Met.strs_merge.go(g, Con{x, xr}, Con{y, yr})}) : Bool}, s_asym(x, y, elt, egt))
        case False{}:
          %ih(xr, Con{y, yr}, k, hg) : {Bool.or(L.has_str(e, Con{x, xr}), L.has_str(e, Con{y, yr})) == Bool.or(String.eq(e, x), _) : Bool}
          or_assoc(String.eq(e, x), L.has_str(e, xr), L.has_str(e, Con{y, yr}))
    case False{}:
      match gt:
        case True{}:
          %ih(Con{x, xr}, yr, k, fuel_gt(List.length(&2, String, xr), List.length(&2, String, yr), k, g, hg))
            : {Bool.or(L.has_str(e, Con{x, xr}), L.has_str(e, Con{y, yr})) == Bool.or(String.eq(e, y), _) : Bool}
          or_swap(L.has_str(e, Con{x, xr}), String.eq(e, y), L.has_str(e, yr))
        case False{}:
          %ih(xr, yr, 1n+k, fuel_eq(List.length(&2, String, xr), List.length(&2, String, yr), k, g, hg))
            : {Bool.or(L.has_str(e, Con{x, xr}), L.has_str(e, Con{y, yr})) == Bool.or(String.eq(e, x), _) : Bool}
          %s_tri(x, y, elt, egt)
            : {Bool.or(Bool.or(String.eq(e, x), L.has_str(e, xr)), Bool.or(String.eq(e, _), L.has_str(e, yr))) == Bool.or(String.eq(e, x), Bool.or(L.has_str(e, xr), L.has_str(e, yr))) : Bool}
          or_dup(String.eq(e, x), L.has_str(e, xr), L.has_str(e, yr))

def hs_go(f: Nat, xs: List<&2, String>, ys: List<&2, String>, +e: String, +k: Nat,
  +hf: {Nat.add(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), k) == f : Nat})
  -> {Bool.or(L.has_str(e, xs), L.has_str(e, ys)) == L.has_str(e, Met.strs_merge.go(f, xs, ys)) : Bool}:
  match f:
    case 0n:
      match xs:
        case Nil{}:
          match ys:
            case Nil{}:
              {==}
            case Con{y, yr}:
              Empty.absurd({L.has_str(e, Con{y, yr}) == L.has_str(e, Con{y, yr}) : Bool}, PNat.no_zero(Nat.add(List.length(&2, String, yr), k), hf))
        case Con{x, xr}:
          Empty.absurd({Bool.or(L.has_str(e, Con{x, xr}), L.has_str(e, ys)) == L.has_str(e, List.append(&2, String, Con{x, xr}, ys)) : Bool},
            PNat.no_zero(Nat.add(Nat.add(List.length(&2, String, xr), List.length(&2, String, ys)), k), hf))
    case 1n+(+g):
      match xs:
        case Nil{}:
          {==}
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              or_false(L.has_str(e, Con{x, xr}))
            case Con{+y, +yr}:
              hs_step(String.is_lt(x, y), String.is_lt(y, x), x, xr, y, yr, g, e, k, {==}, {==},
                PNat.succ_inj(Nat.add(Nat.add(List.length(&2, String, xr), 1n+List.length(&2, String, yr)), k), g, hf),
                xs2 => ys2 => k3 => h1 => hs_go(g, xs2, ys2, e, k3, h1))

def hs_merge(+xs: List<&2, String>, +ys: List<&2, String>, +e: String)
  -> {Bool.or(L.has_str(e, xs), L.has_str(e, ys)) == L.has_str(e, Met.strs_merge(xs, ys)) : Bool}:
  hs_go(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), xs, ys, e, 0n,
    Equal.sym(Nat, Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)),
      Nat.add(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), 0n),
      PNat.add_zero(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)))))

# strictly ascending, all above k
def sa(xs: List<&2, String>, +k: String) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(String.is_lt(k, x), sa(rest, x))

def sa_asc(r: List<&2, String>, +x: String) -> {sa(r, x) == L.strs_ascending(Con{x, r}) : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+y, +m}:
      %sa_asc(m, y) : {Bool.and(String.is_lt(x, y), sa(m, y)) == Bool.and(String.is_lt(x, y), _) : Bool}
      {==}

def sa_of(+x: String, +r: List<&2, String>, +h: {L.strs_ascending(Con{x, r}) == True{} : Bool}) -> {sa(r, x) == True{} : Bool}:
  %Equal.sym(Bool, sa(r, x), L.strs_ascending(Con{x, r}), sa_asc(r, x)) : {_ == True{} : Bool}
  h

def sa_mk(+x: String, +r: List<&2, String>, +h: {sa(r, x) == True{} : Bool}) -> {L.strs_ascending(Con{x, r}) == True{} : Bool}:
  %sa_asc(r, x) : {_ == True{} : Bool}
  h

def sa_head(+b: String, +x: String, +r: List<&2, String>, +h: {sa(Con{x, r}, b) == True{} : Bool}) -> {String.is_lt(b, x) == True{} : Bool}:
  and_l(String.is_lt(b, x), sa(r, x), h)

def sa_tail(+b: String, +x: String, +r: List<&2, String>, +h: {sa(Con{x, r}, b) == True{} : Bool}) -> {sa(r, x) == True{} : Bool}:
  and_r(String.is_lt(b, x), sa(r, x), h)

def sa_step(lt: Bool, gt: Bool, +x: String, +xr: List<&2, String>, +y: String, +yr: List<&2, String>, +g: Nat, +k: Nat, +b: String,
  +elt: {String.is_lt(x, y) == lt : Bool}, +egt: {String.is_lt(y, x) == gt : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, String, xr), 1n+List.length(&2, String, yr)), k) == g : Nat},
  +hx: {sa(Con{x, xr}, b) == True{} : Bool}, +hy: {sa(Con{y, yr}, b) == True{} : Bool},
  ih: @xs2: List<&2, String> -> @ys2: List<&2, String> -> @k3: Nat -> @b2: String
    -> {Nat.add(Nat.add(List.length(&2, String, xs2), List.length(&2, String, ys2)), k3) == g : Nat}
    -> {sa(xs2, b2) == True{} : Bool} -> {sa(ys2, b2) == True{} : Bool}
    -> {sa(Met.strs_merge.go(g, xs2, ys2), b2) == True{} : Bool})
  -> {sa(Con{Met.pick(String, gt, y, x), Met.strs_merge.go(g, Met.pick(List<&2, String>, gt, Con{x, xr}, xr), Met.pick(List<&2, String>, lt, Con{y, yr}, yr))}, b) == True{} : Bool}:
  match lt:
    case True{}:
      match gt:
        case True{}:
          Empty.absurd({sa(Con{y, Met.strs_merge.go(g, Con{x, xr}, Con{y, yr})}, b) == True{} : Bool}, s_asym(x, y, elt, egt))
        case False{}:
          and_i(String.is_lt(b, x), sa(Met.strs_merge.go(g, xr, Con{y, yr}), x), sa_head(b, x, xr, hx),
            ih(xr, Con{y, yr}, k, x, hg, sa_tail(b, x, xr, hx), and_i(String.is_lt(x, y), sa(yr, y), elt, sa_tail(b, y, yr, hy))))
    case False{}:
      match gt:
        case True{}:
          and_i(String.is_lt(b, y), sa(Met.strs_merge.go(g, Con{x, xr}, yr), y), sa_head(b, y, yr, hy),
            ih(Con{x, xr}, yr, k, y, fuel_gt(List.length(&2, String, xr), List.length(&2, String, yr), k, g, hg),
              and_i(String.is_lt(y, x), sa(xr, x), egt, sa_tail(b, x, xr, hx)), sa_tail(b, y, yr, hy)))
        case False{}:
          +exy = s_tri(x, y, elt, egt)
          +hyr = {%Equal.sym(String, x, y, exy) : {sa(yr, _) == True{} : Bool}; sa_tail(b, y, yr, hy) : {sa(yr, x) == True{} : Bool}}
          and_i(String.is_lt(b, x), sa(Met.strs_merge.go(g, xr, yr), x), sa_head(b, x, xr, hx),
            ih(xr, yr, 1n+k, x, fuel_eq(List.length(&2, String, xr), List.length(&2, String, yr), k, g, hg), sa_tail(b, x, xr, hx), hyr))

def sa_go(f: Nat, xs: List<&2, String>, ys: List<&2, String>, +k: Nat, +b: String,
  +hf: {Nat.add(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), k) == f : Nat},
  +hx: {sa(xs, b) == True{} : Bool}, +hy: {sa(ys, b) == True{} : Bool})
  -> {sa(Met.strs_merge.go(f, xs, ys), b) == True{} : Bool}:
  match f:
    case 0n:
      match xs:
        case Nil{}:
          match ys:
            case Nil{}:
              {==}
            case Con{y, yr}:
              Empty.absurd({sa(Con{y, yr}, b) == True{} : Bool}, PNat.no_zero(Nat.add(List.length(&2, String, yr), k), hf))
        case Con{x, xr}:
          Empty.absurd({sa(List.append(&2, String, Con{x, xr}, ys), b) == True{} : Bool},
            PNat.no_zero(Nat.add(Nat.add(List.length(&2, String, xr), List.length(&2, String, ys)), k), hf))
    case 1n+(+g):
      match xs:
        case Nil{}:
          hy
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              hx
            case Con{+y, +yr}:
              sa_step(String.is_lt(x, y), String.is_lt(y, x), x, xr, y, yr, g, k, b, {==}, {==},
                PNat.succ_inj(Nat.add(Nat.add(List.length(&2, String, xr), 1n+List.length(&2, String, yr)), k), g, hf), hx, hy,
                xs2 => ys2 => k3 => b2 => h1 => h2 => h3 => sa_go(g, xs2, ys2, k3, b2, h1, h2, h3))

def as_step(lt: Bool, gt: Bool, +x: String, +xr: List<&2, String>, +y: String, +yr: List<&2, String>, +g: Nat, +k: Nat,
  +elt: {String.is_lt(x, y) == lt : Bool}, +egt: {String.is_lt(y, x) == gt : Bool},
  +hg: {Nat.add(Nat.add(List.length(&2, String, xr), 1n+List.length(&2, String, yr)), k) == g : Nat},
  +hx: {L.strs_ascending(Con{x, xr}) == True{} : Bool}, +hy: {L.strs_ascending(Con{y, yr}) == True{} : Bool})
  -> {L.strs_ascending(Con{Met.pick(String, gt, y, x), Met.strs_merge.go(g, Met.pick(List<&2, String>, gt, Con{x, xr}, xr), Met.pick(List<&2, String>, lt, Con{y, yr}, yr))}) == True{} : Bool}:
  match lt:
    case True{}:
      match gt:
        case True{}:
          Empty.absurd({L.strs_ascending(Con{y, Met.strs_merge.go(g, Con{x, xr}, Con{y, yr})}) == True{} : Bool}, s_asym(x, y, elt, egt))
        case False{}:
          sa_mk(x, Met.strs_merge.go(g, xr, Con{y, yr}),
            sa_go(g, xr, Con{y, yr}, k, x, hg, sa_of(x, xr, hx), and_i(String.is_lt(x, y), sa(yr, y), elt, sa_of(y, yr, hy))))
    case False{}:
      match gt:
        case True{}:
          sa_mk(y, Met.strs_merge.go(g, Con{x, xr}, yr),
            sa_go(g, Con{x, xr}, yr, k, y, fuel_gt(List.length(&2, String, xr), List.length(&2, String, yr), k, g, hg),
              and_i(String.is_lt(y, x), sa(xr, x), egt, sa_of(x, xr, hx)), sa_of(y, yr, hy)))
        case False{}:
          +exy = s_tri(x, y, elt, egt)
          +hyr = {%Equal.sym(String, x, y, exy) : {sa(yr, _) == True{} : Bool}; sa_of(y, yr, hy) : {sa(yr, x) == True{} : Bool}}
          sa_mk(x, Met.strs_merge.go(g, xr, yr),
            sa_go(g, xr, yr, 1n+k, x, fuel_eq(List.length(&2, String, xr), List.length(&2, String, yr), k, g, hg), sa_of(x, xr, hx), hyr))

def as_go(f: Nat, xs: List<&2, String>, ys: List<&2, String>, +k: Nat,
  +hf: {Nat.add(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), k) == f : Nat},
  +hx: {L.strs_ascending(xs) == True{} : Bool}, +hy: {L.strs_ascending(ys) == True{} : Bool})
  -> {L.strs_ascending(Met.strs_merge.go(f, xs, ys)) == True{} : Bool}:
  match f:
    case 0n:
      match xs:
        case Nil{}:
          match ys:
            case Nil{}:
              {==}
            case Con{y, yr}:
              Empty.absurd({L.strs_ascending(Con{y, yr}) == True{} : Bool}, PNat.no_zero(Nat.add(List.length(&2, String, yr), k), hf))
        case Con{x, xr}:
          Empty.absurd({L.strs_ascending(List.append(&2, String, Con{x, xr}, ys)) == True{} : Bool},
            PNat.no_zero(Nat.add(Nat.add(List.length(&2, String, xr), List.length(&2, String, ys)), k), hf))
    case 1n+(+g):
      match xs:
        case Nil{}:
          hy
        case Con{+x, +xr}:
          match ys:
            case Nil{}:
              hx
            case Con{+y, +yr}:
              as_step(String.is_lt(x, y), String.is_lt(y, x), x, xr, y, yr, g, k, {==}, {==},
                PNat.succ_inj(Nat.add(Nat.add(List.length(&2, String, xr), 1n+List.length(&2, String, yr)), k), g, hf), hx, hy)

def as_merge(+xs: List<&2, String>, +ys: List<&2, String>,
  +hx: {L.strs_ascending(xs) == True{} : Bool}, +hy: {L.strs_ascending(ys) == True{} : Bool})
  -> {L.strs_ascending(Met.strs_merge(xs, ys)) == True{} : Bool}:
  as_go(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), xs, ys, 0n,
    Equal.sym(Nat, Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)),
      Nat.add(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)), 0n),
      PNat.add_zero(Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)))), hx, hy)

# ---------------------------------------------------------------------
# the accumulator's errors
# ---------------------------------------------------------------------

def and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pk_asc(c: Bool, -err: String) -> {L.strs_ascending(Met.pick(List<&2, String>, c, [], [err])) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def oh_es_asc(h: Hit.Hit) -> {L.strs_ascending(a_es(Met.of_hit(h))) == True{} : Bool}:
  match h:
    case Hit.Hit{a, q, c, t, l, bo, bi, +err, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          pk_asc(String.is_empty(err), err)

# a result's error is in the set when not empty
def oh_hs(h: Hit.Hit, +e: String)
  -> {Bool.and(Bool.not(String.is_empty(e)), String.eq(L.h_err(h), e)) == L.has_str(e, a_es(Met.of_hit(h))) : Bool}:
  match h:
    case Hit.Hit{a, q, c, t, l, bo, bi, err, b, m, u, hs}:
      match t:
        case Civil.Time{s0, ns0, off}:
          match err:
            case SNil{}:
              match e:
                case SNil{}:
                  {==}
                case SCon{d, r}:
                  {==}
            case SCon{+c1, +r1}:
              match e:
                case SNil{}:
                  {==}
                case SCon{+d, +r}:
                  %s_eq_sym(SCon{d, r}, SCon{c1, r1}) : {_ == Bool.or(String.eq(SCon{d, r}, SCon{c1, r1}), False{}) : Bool}
                  Equal.sym(Bool, Bool.or(String.eq(SCon{d, r}, SCon{c1, r1}), False{}), String.eq(SCon{d, r}, SCon{c1, r1}), or_false(String.eq(SCon{d, r}, SCon{c1, r1})))

def add_es_asc(+a: Met.Acc, +h: Hit.Hit, +ha: {L.strs_ascending(a_es(a)) == True{} : Bool}) -> {L.strs_ascending(a_es(Met.add(a, h))) == True{} : Bool}:
  %m_es(a, Met.of_hit(h)) : {L.strs_ascending(_) == True{} : Bool}
  as_merge(a_es(a), a_es(Met.of_hit(h)), ha, oh_es_asc(h))

def f_es_asc(hs: List<&2, Hit.Hit>, +a: Met.Acc, +ha: {L.strs_ascending(a_es(a)) == True{} : Bool})
  -> {L.strs_ascending(a_es(L.acc_all(hs, a))) == True{} : Bool}:
  match hs:
    case Nil{}:
      ha
    case Con{+h, +rest}:
      f_es_asc(rest, Met.add(a, h), add_es_asc(a, h, ha))

def bl(ne: Bool, x: Bool, -q: Bool, -r: Bool) -> {Bool.or(x, Bool.and(ne, Bool.or(q, r))) == Bool.or(Bool.or(x, Bool.and(ne, q)), Bool.and(ne, r)) : Bool}:
  match ne:
    case True{}:
      Equal.sym(Bool, Bool.or(Bool.or(x, q), r), Bool.or(x, Bool.or(q, r)), or_assoc(x, q, r))
    case False{}:
      match x:
        case True{}:
          {==}
        case False{}:
          {==}

def f_hs(hs: List<&2, Hit.Hit>, +a: Met.Acc, +e: String)
  -> {Bool.or(L.has_str(e, a_es(a)), Bool.and(Bool.not(String.is_empty(e)), L.has_err(e, hs))) == L.has_str(e, a_es(L.acc_all(hs, a))) : Bool}:
  match hs:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(Bool.not(String.is_empty(e)), False{}), False{}, and_false(Bool.not(String.is_empty(e)))) : {Bool.or(L.has_str(e, a_es(a)), _) == L.has_str(e, a_es(a)) : Bool}
      or_false(L.has_str(e, a_es(a)))
    case Con{+h, +rest}:
      +ne = Bool.not(String.is_empty(e))
      +x = L.has_str(e, a_es(a))
      +q = String.eq(L.h_err(h), e)
      +r = L.has_err(e, rest)
      +lhs = Bool.or(x, Bool.and(ne, Bool.or(q, r)))
      %f_hs(rest, Met.add(a, h), e) : {lhs == _ : Bool}
      %m_es(a, Met.of_hit(h)) : {lhs == Bool.or(L.has_str(e, _), Bool.and(ne, r)) : Bool}
      %hs_merge(a_es(a), a_es(Met.of_hit(h)), e) : {lhs == Bool.or(_, Bool.and(ne, r)) : Bool}
      %oh_hs(h, e) : {lhs == Bool.or(Bool.or(x, _), Bool.and(ne, r)) : Bool}
      bl(ne, x, q, r)

def c_es(a: Met.Acc, hx: {is_ext(a_x(a)) == True{} : Bool}) -> {a_es(a) == L.s_errors(Met.close(a)) : List<&2, String>}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd({es == [] : List<&2, String>}, no_ft(hx))
        case Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
          {==}

def L.met_errors(bs, hs, e):
  match hs:
    case Nil{}:
      ({==}, Equal.sym(Bool, Bool.and(Bool.not(String.is_empty(e)), False{}), False{}, and_false(Bool.not(String.is_empty(e)))))
    case Con{+h, +rest}:
      +A = L.acc_all(Con{h, rest}, Met.empty(bs))
      +hx = sum_x(bs, h, rest)
      +ne = Bool.not(String.is_empty(e))
      +p1 = {%c_es(A, hx) : {L.strs_ascending(_) == True{} : Bool};
             f_es_asc(Con{h, rest}, Met.empty(bs), {==})
             : {L.strs_ascending(L.s_errors(L.summary(bs, Con{h, rest}))) == True{} : Bool}}
      +p2 = {%c_es(A, hx) : {L.has_str(e, _) == Bool.and(ne, L.has_err(e, Con{h, rest})) : Bool};
             Equal.sym(Bool, Bool.and(ne, L.has_err(e, Con{h, rest})), L.has_str(e, a_es(A)), f_hs(Con{h, rest}, Met.empty(bs), e))
             : {L.has_str(e, L.s_errors(L.summary(bs, Con{h, rest}))) == Bool.and(ne, L.has_err(e, Con{h, rest})) : Bool}}
      (p1, p2)

# =====================================================================
# Tables: lib/tab.bend's two passes are LAWS' up_w and down_w
# =====================================================================

def rg(f: Nat, s: String, +acc: Nat) -> {Nat.add(acc, L.runes.go(f, s)) == Tab.runes.go(f, String.is_empty(s), s, acc) : Nat}:
  match f:
    case 0n:
      Equal.sym(Nat, acc, Nat.add(acc, 0n), PNat.add_zero(acc))
    case 1n+(+g):
      match s:
        case SNil{}:
          Equal.sym(Nat, acc, Nat.add(acc, 0n), PNat.add_zero(acc))
        case SCon{+c, +r}:
          +x = L.runes.go(g, String.drop(SCon{c, r}, Nat.max(1n, L.utf8_len(SCon{c, r}))))
          +t = String.drop(SCon{c, r}, Json.esc_len(SCon{c, r}))
          %PNat.add_succ(acc, x) : {_ == Tab.runes.go(g, String.is_empty(t), t, 1n+acc) : Nat}
          %PCodec.utf8_len_j(SCon{c, r}) : {1n+Nat.add(acc, L.runes.go(g, String.drop(SCon{c, r}, Nat.max(1n, _)))) == Tab.runes.go(g, String.is_empty(t), t, 1n+acc) : Nat}
          rg(g, t, 1n+acc)

def runes_same(+s: String) -> {L.runes(s) == Tab.runes(s) : Nat}:
  rg(String.length(s), s, 0n)

def cells_same(+l: String) -> {L.tab_cells(l) == Tab.cells(l) : List<&2, String>}:
  %split_same(9, l) : {List.take(&2, String, _, Nat.sub(List.length(&2, String, _), 1n)) == Tab.cells(l) : List<&2, String>}
  {==}

def trailing_same(+l: String) -> {L.trailing(l) == Tab.trailing(l) : String}:
  %split_same(9, l) : {Maybe.default(&2, String, List.last(&2, String, _), "") == Tab.trailing(l) : String}
  {==}

def tpick_succ(c: Bool, -a: Nat, -b: Nat) -> {1n+Tab.pick(Nat, c, a, b) == Tab.pick(Nat, c, 1n+a, 1n+b) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tmax(a: Nat, b: Nat) -> {Nat.max(a, b) == Tab.nmax(a, b) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          {==}
    case 1n+(+ap):
      match b:
        case 0n:
          {==}
        case 1n+(+bp):
          %Equal.sym(Nat, Nat.max(ap, bp), Tab.nmax(ap, bp), tmax(ap, bp)) : {1n+_ == Tab.pick(Nat, Nat.is_le(ap, bp), 1n+bp, 1n+ap) : Nat}
          tpick_succ(Nat.is_le(ap, bp), bp, ap)

def tjoin_same(xs: List<&2, String>) -> {Tab.join_lines(xs) == L.join_str("\n", xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      match rest:
        case Nil{}:
          {==}
        case Con{+y, +more}:
          %tjoin_same(Con{y, more}) : {Tab.join_lines(Con{x, Con{y, more}}) == x ++ "\n" ++ _ : String}
          {==}

def snil_con_t(xs: List<&2, String>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, r}:
      Empty

def snil_ne_con(-b: String, -r: List<&2, String>, e: {[] == Con{b, r} : List<&2, String>}) -> Empty:
  %e : snil_con_t(_)
  Unit{}

# ---------------------------------------------------------------------
# indexing
# ---------------------------------------------------------------------

def hd_drop(xs: List<&2, Nat>, j: Nat) -> {Tab.head0(List.drop(&2, Nat, xs, j)) == L.nth_or0(j, xs) : Nat}:
  match xs:
    case Nil{}:
      match j:
        case 0n:
          {==}
        case 1n+jp:
          {==}
    case Con{x, rest}:
      match j:
        case 0n:
          {==}
        case 1n+jp:
          hd_drop(rest, jp)

def tl_drop(xs: List<&2, Nat>, j: Nat) -> {List.tail(&2, Nat, List.drop(&2, Nat, xs, j)) == List.drop(&2, Nat, xs, 1n+j) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      match j:
        case 0n:
          {==}
        case 1n+jp:
          {==}
    case Con{x, +rest}:
      match j:
        case 0n:
          drop0(rest)
        case 1n+jp:
          tl_drop(rest, jp)

def nth_tail(p: List<&2, Nat>, j: Nat) -> {L.nth_or0(j, List.tail(&2, Nat, p)) == L.nth_or0(1n+j, p) : Nat}:
  match p:
    case Nil{}:
      match j:
        case 0n:
          {==}
        case 1n+jp:
          {==}
    case Con{x, r}:
      {==}

def gt0(j: Nat) -> {Nat.is_gt(0n, j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+jp:
      {==}

def get0(p: List<&2, Nat>) -> {Tab.head0(p) == L.nth_or0(0n, p) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# one line's run widths: the widest so far in each column it has
def zm(ws: List<&2, Nat>, +p: List<&2, Nat>, j: Nat)
  -> {L.nth_or0(j, Tab.zmax(ws, p)) == L.pick(Nat, Nat.is_gt(List.length(&2, Nat, ws), j), Nat.max(L.nth_or0(j, ws), L.nth_or0(j, p)), 0n) : Nat}:
  match ws:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_gt(0n, j), False{}, gt0(j)) : {0n == L.pick(Nat, _, Nat.max(L.nth_or0(j, []), L.nth_or0(j, p)), 0n) : Nat}
      {==}
    case Con{+w, +rest}:
      match j:
        case 0n:
          %get0(p) : {Tab.nmax(w, Tab.head0(p)) == Nat.max(w, _) : Nat}
          Equal.sym(Nat, Nat.max(w, Tab.head0(p)), Tab.nmax(w, Tab.head0(p)), tmax(w, Tab.head0(p)))
        case 1n+(+jp):
          %Equal.sym(Nat, L.nth_or0(jp, Tab.zmax(rest, List.tail(&2, Nat, p))),
              L.pick(Nat, Nat.is_gt(List.length(&2, Nat, rest), jp), Nat.max(L.nth_or0(jp, rest), L.nth_or0(jp, List.tail(&2, Nat, p))), 0n),
              zm(rest, List.tail(&2, Nat, p), jp))
            : {_ == L.pick(Nat, Nat.is_gt(List.length(&2, Nat, rest), jp), Nat.max(L.nth_or0(jp, rest), L.nth_or0(1n+jp, p)), 0n) : Nat}
          %nth_tail(p, jp)
            : {L.pick(Nat, Nat.is_gt(List.length(&2, Nat, rest), jp), Nat.max(L.nth_or0(jp, rest), L.nth_or0(jp, List.tail(&2, Nat, p))), 0n)
               == L.pick(Nat, Nat.is_gt(List.length(&2, Nat, rest), jp), Nat.max(L.nth_or0(jp, rest), _), 0n) : Nat}
          {==}

def len_widths(cs: List<&2, String>) -> {List.length(&2, Nat, Tab.widths(cs)) == List.length(&2, String, cs) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      PNat.succ_inj(1n+List.length(&2, Nat, Tab.widths(rest)), 1n+List.length(&2, String, rest),
        Equal.cong(Nat, Nat, v => 2n+v, List.length(&2, Nat, Tab.widths(rest)), List.length(&2, String, rest), len_widths(rest)))

def nth_widths(cs: List<&2, String>, j: Nat) -> {L.nth_or0(j, Tab.widths(cs)) == L.runes(Maybe.default(&2, String, List.get(&2, String, cs, j), "")) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      match j:
        case 0n:
          Equal.sym(Nat, L.runes(c), Tab.runes(c), runes_same(c))
        case 1n+jp:
          nth_widths(rest, jp)

def get_line(ls: List<&2, String>, i: Nat, -l: String, -r: List<&2, String>, hd: {List.drop(&2, String, ls, i) == Con{l, r} : List<&2, String>})
  -> {L.line_at(ls, i) == l : String}:
  match ls:
    case Nil{}:
      Empty.absurd({"" == l : String}, snil_ne_con(l, r, hd))
    case Con{+x, +xs}:
      match i:
        case 0n:
          Equal.cong(List<&2, String>, String, ys => Maybe.default(&2, String, List.head(&2, String, ys), ""), Con{x, xs}, Con{l, r}, hd)
        case 1n+ip:
          get_line(xs, ip, l, r, hd)

def sdrop0(bs: List<&2, String>) -> {bs == List.drop(&2, String, bs, 0n) : List<&2, String>}:
  match bs:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

def sdrop_succ(bs: List<&2, String>, i: Nat, -b: String, -r: List<&2, String>, hd: {List.drop(&2, String, bs, i) == Con{b, r} : List<&2, String>})
  -> {List.drop(&2, String, bs, 1n+i) == r : List<&2, String>}:
  match bs:
    case Nil{}:
      Empty.absurd({[] == r : List<&2, String>}, snil_ne_con(b, r, hd))
    case Con{+x, +xs}:
      match i:
        case 0n:
          %sdrop0(xs) : {_ == r : List<&2, String>}
          Equal.cong(List<&2, String>, List<&2, String>, ys => List.tail(&2, String, ys), Con{x, xs}, Con{b, r}, hd)
        case 1n+j:
          sdrop_succ(xs, j, b, r, hd)

def get_nil(ls: List<&2, String>, i: Nat, hd: {List.drop(&2, String, ls, i) == [] : List<&2, String>}) -> {L.line_at(ls, i) == "" : String}:
  match ls:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      match i:
        case 0n:
          Empty.absurd({x == "" : String}, snil_ne_con(x, xs, Equal.sym(List<&2, String>, Con{x, xs}, [], hd)))
        case 1n+ip:
          get_nil(xs, ip, hd)

# one line's widths joined with the neighbour's run: up_w one step
def up_line(+ls: List<&2, String>, +l: String, +i: Nat, +p: List<&2, Nat>, +f: Nat, +hl: {L.line_at(ls, i) == l : String},
  hp: @j: Nat -> {L.nth_or0(j, p) == L.pick(Nat, Nat.is_eq(i, 0n), 0n, L.up_w(f, ls, Nat.sub(i, 1n), j)) : Nat}, +j: Nat)
  -> {L.nth_or0(j, Tab.zmax(Tab.widths(Tab.cells(l)), p)) == L.up_w(1n+f, ls, i, j) : Nat}:
  +cs = Tab.cells(l)
  +prev = L.pick(Nat, Nat.is_eq(i, 0n), 0n, L.up_w(f, ls, Nat.sub(i, 1n), j))
  +rw = L.runes(Maybe.default(&2, String, List.get(&2, String, cs, j), ""))
  Equal.trans(Nat, L.nth_or0(j, Tab.zmax(Tab.widths(cs), p)),
    L.pick(Nat, Nat.is_gt(List.length(&2, Nat, Tab.widths(cs)), j), Nat.max(L.nth_or0(j, Tab.widths(cs)), L.nth_or0(j, p)), 0n),
    L.up_w(1n+f, ls, i, j), zm(Tab.widths(cs), p, j),
    {%Equal.sym(Nat, List.length(&2, Nat, Tab.widths(cs)), List.length(&2, String, cs), len_widths(cs))
       : {L.pick(Nat, Nat.is_gt(_, j), Nat.max(L.nth_or0(j, Tab.widths(cs)), L.nth_or0(j, p)), 0n) == L.up_w(1n+f, ls, i, j) : Nat};
     %Equal.sym(Nat, L.nth_or0(j, Tab.widths(cs)), rw, nth_widths(cs, j))
       : {L.pick(Nat, Nat.is_gt(List.length(&2, String, cs), j), Nat.max(_, L.nth_or0(j, p)), 0n) == L.up_w(1n+f, ls, i, j) : Nat};
     %Equal.sym(Nat, L.nth_or0(j, p), prev, hp(j))
       : {L.pick(Nat, Nat.is_gt(List.length(&2, String, cs), j), Nat.max(rw, _), 0n) == L.up_w(1n+f, ls, i, j) : Nat};
     %Equal.sym(String, L.line_at(ls, i), l, hl)
       : {L.pick(Nat, Nat.is_gt(List.length(&2, String, cs), j), Nat.max(rw, prev), 0n)
          == L.pick(Nat, Nat.is_gt(List.length(&2, String, L.tab_cells(_)), j), Nat.max(L.runes(Maybe.default(&2, String, List.get(&2, String, L.tab_cells(_), j), "")), prev), 0n) : Nat};
     %Equal.sym(List<&2, String>, L.tab_cells(l), cs, cells_same(l))
       : {L.pick(Nat, Nat.is_gt(List.length(&2, String, cs), j), Nat.max(rw, prev), 0n)
          == L.pick(Nat, Nat.is_gt(List.length(&2, String, _), j), Nat.max(L.runes(Maybe.default(&2, String, List.get(&2, String, _, j), "")), prev), 0n) : Nat};
     {==}
     : {L.pick(Nat, Nat.is_gt(List.length(&2, Nat, Tab.widths(cs)), j), Nat.max(L.nth_or0(j, Tab.widths(cs)), L.nth_or0(j, p)), 0n) == L.up_w(1n+f, ls, i, j) : Nat}})

def down_line(+ls: List<&2, String>, +l: String, +i: Nat, +p: List<&2, Nat>, +f: Nat, +hl: {L.line_at(ls, i) == l : String},
  hp: @j: Nat -> {L.nth_or0(j, p) == L.down_w(f, ls, 1n+i, j) : Nat}, +j: Nat)
  -> {L.nth_or0(j, Tab.zmax(Tab.widths(Tab.cells(l)), p)) == L.down_w(1n+f, ls, i, j) : Nat}:
  +cs = Tab.cells(l)
  +prev = L.down_w(f, ls, 1n+i, j)
  +rw = L.runes(Maybe.default(&2, String, List.get(&2, String, cs, j), ""))
  Equal.trans(Nat, L.nth_or0(j, Tab.zmax(Tab.widths(cs), p)),
    L.pick(Nat, Nat.is_gt(List.length(&2, Nat, Tab.widths(cs)), j), Nat.max(L.nth_or0(j, Tab.widths(cs)), L.nth_or0(j, p)), 0n),
    L.down_w(1n+f, ls, i, j), zm(Tab.widths(cs), p, j),
    {%Equal.sym(Nat, List.length(&2, Nat, Tab.widths(cs)), List.length(&2, String, cs), len_widths(cs))
       : {L.pick(Nat, Nat.is_gt(_, j), Nat.max(L.nth_or0(j, Tab.widths(cs)), L.nth_or0(j, p)), 0n) == L.down_w(1n+f, ls, i, j) : Nat};
     %Equal.sym(Nat, L.nth_or0(j, Tab.widths(cs)), rw, nth_widths(cs, j))
       : {L.pick(Nat, Nat.is_gt(List.length(&2, String, cs), j), Nat.max(_, L.nth_or0(j, p)), 0n) == L.down_w(1n+f, ls, i, j) : Nat};
     %Equal.sym(Nat, L.nth_or0(j, p), prev, hp(j))
       : {L.pick(Nat, Nat.is_gt(List.length(&2, String, cs), j), Nat.max(rw, _), 0n) == L.down_w(1n+f, ls, i, j) : Nat};
     %Equal.sym(String, L.line_at(ls, i), l, hl)
       : {L.pick(Nat, Nat.is_gt(List.length(&2, String, cs), j), Nat.max(rw, prev), 0n)
          == L.pick(Nat, Nat.is_gt(List.length(&2, String, L.tab_cells(_)), j), Nat.max(L.runes(Maybe.default(&2, String, List.get(&2, String, L.tab_cells(_), j), "")), prev), 0n) : Nat};
     %Equal.sym(List<&2, String>, L.tab_cells(l), cs, cells_same(l))
       : {L.pick(Nat, Nat.is_gt(List.length(&2, String, cs), j), Nat.max(rw, prev), 0n)
          == L.pick(Nat, Nat.is_gt(List.length(&2, String, _), j), Nat.max(L.runes(Maybe.default(&2, String, List.get(&2, String, _, j), "")), prev), 0n) : Nat};
     {==}
     : {L.pick(Nat, Nat.is_gt(List.length(&2, Nat, Tab.widths(cs)), j), Nat.max(L.nth_or0(j, Tab.widths(cs)), L.nth_or0(j, p)), 0n) == L.down_w(1n+f, ls, i, j) : Nat}})

def up_fuel(+ls: List<&2, String>, i: Nat, +k: Nat, +j: Nat) -> {L.up_w(Nat.add(1n+i, k), ls, i, j) == L.up_w(1n+i, ls, i, j) : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+(+ip):
      %sub_zero(ip)
        : {L.pick(Nat, Nat.is_gt(L.n_cells(L.line_at(ls, 1n+ip)), j), Nat.max(L.cell_w(ls, 1n+ip, j), L.up_w(Nat.add(1n+ip, k), ls, _, j)), 0n)
           == L.pick(Nat, Nat.is_gt(L.n_cells(L.line_at(ls, 1n+ip)), j), Nat.max(L.cell_w(ls, 1n+ip, j), L.up_w(1n+ip, ls, _, j)), 0n) : Nat}
      %up_fuel(ls, ip, k, j)
        : {L.pick(Nat, Nat.is_gt(L.n_cells(L.line_at(ls, 1n+ip)), j), Nat.max(L.cell_w(ls, 1n+ip, j), L.up_w(Nat.add(1n+ip, k), ls, ip, j)), 0n)
           == L.pick(Nat, Nat.is_gt(L.n_cells(L.line_at(ls, 1n+ip)), j), Nat.max(L.cell_w(ls, 1n+ip, j), _), 0n) : Nat}
      {==}

def down_nil(k: Nat, +ls: List<&2, String>, +i: Nat, +j: Nat, +hd: {List.drop(&2, String, ls, i) == [] : List<&2, String>})
  -> {L.down_w(k, ls, i, j) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      %Equal.sym(String, L.line_at(ls, i), "", get_nil(ls, i, hd))
        : {L.pick(Nat, Nat.is_gt(L.n_cells(_), j), Nat.max(L.cell_w(ls, i, j), L.down_w(kp, ls, 1n+i, j)), 0n) == 0n : Nat}
      %Equal.sym(Bool, Nat.is_gt(0n, j), False{}, gt0(j))
        : {L.pick(Nat, _, Nat.max(L.cell_w(ls, i, j), L.down_w(kp, ls, 1n+i, j)), 0n) == 0n : Nat}
      {==}

def dn_fuel(sfx: List<&2, String>, +ls: List<&2, String>, +i: Nat, +k: Nat, +j: Nat, +hd: {List.drop(&2, String, ls, i) == sfx : List<&2, String>})
  -> {L.down_w(Nat.add(k, List.length(&2, String, sfx)), ls, i, j) == L.down_w(List.length(&2, String, sfx), ls, i, j) : Nat}:
  match sfx:
    case Nil{}:
      %PNat.add_zero(k) : {L.down_w(_, ls, i, j) == 0n : Nat}
      down_nil(k, ls, i, j, hd)
    case Con{+l, +r}:
      +rr = List.length(&2, String, r)
      %PNat.add_succ(k, rr) : {L.down_w(_, ls, i, j) == L.down_w(1n+rr, ls, i, j) : Nat}
      %dn_fuel(r, ls, 1n+i, k, j, sdrop_succ(ls, i, l, r, hd))
        : {L.pick(Nat, Nat.is_gt(L.n_cells(L.line_at(ls, i)), j), Nat.max(L.cell_w(ls, i, j), L.down_w(Nat.add(k, rr), ls, 1n+i, j)), 0n)
           == L.pick(Nat, Nat.is_gt(L.n_cells(L.line_at(ls, i)), j), Nat.max(L.cell_w(ls, i, j), _), 0n) : Nat}
      {==}

# ---------------------------------------------------------------------
# the backward pass: runs over the reversed lines, reversed back
# ---------------------------------------------------------------------

def hd_or(xs: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  Maybe.default(&2, List<&2, Nat>, List.head(&2, List<&2, Nat>, xs), [])

def br(ws: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match ws:
    case Nil{}:
      []
    case Con{+w, +rest}:
      Con{Tab.zmax(w, hd_or(br(rest))), br(rest)}

def lr(xs: List<&2, List<&2, Nat>>, +p: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      p
    case Con{+a, +r}:
      lr(r, Tab.zmax(a, p))

def last_or(xs: List<&2, List<&2, Nat>>, +d: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      d
    case Con{+x, +r}:
      last_or(r, x)

def rev_app(xs: List<&2, List<&2, Nat>>, ys: List<&2, List<&2, Nat>>, +acc: List<&2, List<&2, Nat>>)
  -> {List.reverse.go(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, xs, ys), acc)
      == List.reverse.go(&2, List<&2, Nat>, ys, List.reverse.go(&2, List<&2, Nat>, xs, acc)) : List<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      rev_app(r, ys, Con{x, acc})

def app_assoc(xs: List<&2, List<&2, Nat>>, +ys: List<&2, List<&2, Nat>>, +zs: List<&2, List<&2, Nat>>)
  -> {List.append(&2, List<&2, Nat>, xs, List.append(&2, List<&2, Nat>, ys, zs)) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, xs, ys), zs) : List<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %app_assoc(r, ys, zs) : {Con{x, List.append(&2, List<&2, Nat>, r, List.append(&2, List<&2, Nat>, ys, zs))} == Con{x, _} : List<&2, List<&2, Nat>>}
      {==}

def rev_acc(xs: List<&2, List<&2, Nat>>, +acc: List<&2, List<&2, Nat>>)
  -> {List.reverse.go(&2, List<&2, Nat>, xs, acc) == List.append(&2, List<&2, Nat>, List.reverse.go(&2, List<&2, Nat>, xs, []), acc) : List<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +rv = List.reverse.go(&2, List<&2, Nat>, r, [])
      Equal.trans(List<&2, List<&2, Nat>>, List.reverse.go(&2, List<&2, Nat>, r, Con{x, acc}), List.append(&2, List<&2, Nat>, rv, Con{x, acc}),
        List.append(&2, List<&2, Nat>, List.reverse.go(&2, List<&2, Nat>, r, [x]), acc), rev_acc(r, Con{x, acc}),
        {%Equal.sym(List<&2, List<&2, Nat>>, List.reverse.go(&2, List<&2, Nat>, r, [x]), List.append(&2, List<&2, Nat>, rv, [x]), rev_acc(r, [x]))
           : {List.append(&2, List<&2, Nat>, rv, Con{x, acc}) == List.append(&2, List<&2, Nat>, _, acc) : List<&2, List<&2, Nat>>};
         app_assoc(rv, [x], acc)
         : {List.append(&2, List<&2, Nat>, rv, Con{x, acc}) == List.append(&2, List<&2, Nat>, List.reverse.go(&2, List<&2, Nat>, r, [x]), acc) : List<&2, List<&2, Nat>>}})

def runs_app(a: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +p: List<&2, Nat>)
  -> {Tab.runs(List.append(&2, List<&2, Nat>, a, [w]), p) == List.append(&2, List<&2, Nat>, Tab.runs(a, p), [Tab.zmax(w, lr(a, p))]) : List<&2, List<&2, Nat>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %runs_app(r, w, Tab.zmax(x, p)) : {Con{Tab.zmax(x, p), Tab.runs(List.append(&2, List<&2, Nat>, r, [w]), Tab.zmax(x, p))} == Con{Tab.zmax(x, p), _} : List<&2, List<&2, Nat>>}
      {==}

def hd_rev(xs: List<&2, List<&2, Nat>>, +acc: List<&2, List<&2, Nat>>)
  -> {hd_or(List.reverse.go(&2, List<&2, Nat>, xs, acc)) == last_or(xs, hd_or(acc)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      hd_rev(r, Con{x, acc})

def last_runs(a: List<&2, List<&2, Nat>>, +p: List<&2, Nat>) -> {last_or(Tab.runs(a, p), p) == lr(a, p) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      last_runs(r, Tab.zmax(x, p))

def brl(ws: List<&2, List<&2, Nat>>) -> {br(ws) == List.reverse(&2, List<&2, Nat>, Tab.runs(List.reverse(&2, List<&2, Nat>, ws), [])) : List<&2, List<&2, Nat>>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +a = List.reverse(&2, List<&2, Nat>, rest)
      +rs = Tab.runs(a, [])
      +z = Tab.zmax(w, lr(a, []))
      %Equal.sym(List<&2, List<&2, Nat>>, List.reverse.go(&2, List<&2, Nat>, rest, [w]), List.append(&2, List<&2, Nat>, a, [w]), rev_acc(rest, [w]))
        : {br(Con{w, rest}) == List.reverse(&2, List<&2, Nat>, Tab.runs(_, [])) : List<&2, List<&2, Nat>>}
      %Equal.sym(List<&2, List<&2, Nat>>, Tab.runs(List.append(&2, List<&2, Nat>, a, [w]), []), List.append(&2, List<&2, Nat>, rs, [z]), runs_app(a, w, []))
        : {br(Con{w, rest}) == List.reverse(&2, List<&2, Nat>, _) : List<&2, List<&2, Nat>>}
      %Equal.sym(List<&2, List<&2, Nat>>, List.reverse.go(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, rs, [z]), []),
          List.reverse.go(&2, List<&2, Nat>, [z], List.reverse.go(&2, List<&2, Nat>, rs, [])), rev_app(rs, [z], []))
        : {br(Con{w, rest}) == _ : List<&2, List<&2, Nat>>}
      %Equal.sym(List<&2, List<&2, Nat>>, br(rest), List.reverse(&2, List<&2, Nat>, rs), brl(rest))
        : {Con{Tab.zmax(w, hd_or(_)), _} == Con{z, List.reverse(&2, List<&2, Nat>, rs)} : List<&2, List<&2, Nat>>}
      %Equal.sym(List<&2, Nat>, hd_or(List.reverse(&2, List<&2, Nat>, rs)), last_or(rs, []), hd_rev(rs, []))
        : {Con{Tab.zmax(w, _), List.reverse(&2, List<&2, Nat>, rs)} == Con{z, List.reverse(&2, List<&2, Nat>, rs)} : List<&2, List<&2, Nat>>}
      %Equal.sym(List<&2, Nat>, last_or(rs, []), lr(a, []), last_runs(a, []))
        : {Con{Tab.zmax(w, _), List.reverse(&2, List<&2, Nat>, rs)} == Con{z, List.reverse(&2, List<&2, Nat>, rs)} : List<&2, List<&2, Nat>>}
      {==}

def dn(sfx: List<&2, String>, +ls: List<&2, String>, +i: Nat, +hd: {List.drop(&2, String, ls, i) == sfx : List<&2, String>}, +j: Nat)
  -> {L.nth_or0(j, hd_or(br(Tab.all_widths(sfx)))) == L.down_w(List.length(&2, String, sfx), ls, i, j) : Nat}:
  match sfx:
    case Nil{}:
      {==}
    case Con{+l, +r}:
      down_line(ls, l, i, hd_or(br(Tab.all_widths(r))), List.length(&2, String, r), get_line(ls, i, l, r, hd),
        jj => dn(r, ls, 1n+i, sdrop_succ(ls, i, l, r, hd), jj), j)

# the forward pass, line by line: the run widths of line i
def urun(i: Nat, +ls: List<&2, String>) -> List<&2, Nat>:
  match i:
    case 0n:
      Tab.zmax(Tab.widths(Tab.cells(L.line_at(ls, 0n))), [])
    case 1n+(+ip):
      Tab.zmax(Tab.widths(Tab.cells(L.line_at(ls, 1n+ip))), urun(ip, ls))

def prev(i: Nat, +ls: List<&2, String>) -> List<&2, Nat>:
  match i:
    case 0n:
      []
    case 1n+ip:
      urun(ip, ls)

def urun_eq(i: Nat, +ls: List<&2, String>) -> {Tab.zmax(Tab.widths(Tab.cells(L.line_at(ls, i))), prev(i, ls)) == urun(i, ls) : List<&2, Nat>}:
  match i:
    case 0n:
      {==}
    case 1n+ip:
      {==}

def uf(i: Nat, +ls: List<&2, String>, +jj: Nat) -> {L.nth_or0(jj, urun(i, ls)) == L.up_w(1n+i, ls, i, jj) : Nat}:
  match i:
    case 0n:
      up_line(ls, L.line_at(ls, 0n), 0n, [], 0n, {==}, j2 => {==}, jj)
    case 1n+(+ip):
      up_line(ls, L.line_at(ls, 1n+ip), 1n+ip, urun(ip, ls), 1n+ip, {==},
        j2 => {%sub_zero(ip) : {L.nth_or0(j2, urun(ip, ls)) == L.up_w(1n+ip, ls, _, j2) : Nat};
               uf(ip, ls, j2)
               : {L.nth_or0(j2, urun(ip, ls)) == L.pick(Nat, Nat.is_eq(1n+ip, 0n), 0n, L.up_w(1n+ip, ls, Nat.sub(1n+ip, 1n), j2)) : Nat}}, jj)

# the widths facts at line i (i + 1 + rn lines), for any column
def fu(+ls: List<&2, String>, +i: Nat, +rn: Nat, +hn1: {Nat.add(1n+i, rn) == List.length(&2, String, ls) : Nat}, +jj: Nat)
  -> {L.nth_or0(jj, urun(i, ls)) == L.up_w(List.length(&2, String, ls), ls, i, jj) : Nat}:
  %hn1 : {L.nth_or0(jj, urun(i, ls)) == L.up_w(_, ls, i, jj) : Nat}
  %Equal.sym(Nat, L.up_w(Nat.add(1n+i, rn), ls, i, jj), L.up_w(1n+i, ls, i, jj), up_fuel(ls, i, rn, jj)) : {L.nth_or0(jj, urun(i, ls)) == _ : Nat}
  uf(i, ls, jj)

def fd(+sfx: List<&2, String>, +ls: List<&2, String>, +i: Nat, +hd: {List.drop(&2, String, ls, i) == sfx : List<&2, String>},
  +hn: {Nat.add(i, List.length(&2, String, sfx)) == List.length(&2, String, ls) : Nat}, +jj: Nat)
  -> {L.nth_or0(jj, hd_or(br(Tab.all_widths(sfx)))) == L.down_w(List.length(&2, String, ls), ls, i, jj) : Nat}:
  %hn : {L.nth_or0(jj, hd_or(br(Tab.all_widths(sfx)))) == L.down_w(_, ls, i, jj) : Nat}
  %Equal.sym(Nat, L.down_w(Nat.add(i, List.length(&2, String, sfx)), ls, i, jj), L.down_w(List.length(&2, String, sfx), ls, i, jj), dn_fuel(sfx, ls, i, i, jj, hd))
    : {L.nth_or0(jj, hd_or(br(Tab.all_widths(sfx)))) == _ : Nat}
  dn(sfx, ls, i, hd, jj)

# a line's cells padded by the two passes' widths are LAWS' pad_cells
def pc(cs: List<&2, String>, +ls: List<&2, String>, +i: Nat, +rn: Nat, +hn1: {Nat.add(1n+i, rn) == List.length(&2, String, ls) : Nat},
  +sfx: List<&2, String>, +hd: {List.drop(&2, String, ls, i) == sfx : List<&2, String>},
  +hn: {Nat.add(i, List.length(&2, String, sfx)) == List.length(&2, String, ls) : Nat}, +j: Nat)
  -> {Tab.pad_cells(cs, List.drop(&2, Nat, urun(i, ls), j), List.drop(&2, Nat, hd_or(br(Tab.all_widths(sfx))), j)) == L.pad_cells(cs, ls, i, j) : String}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      +u = urun(i, ls)
      +d = hd_or(br(Tab.all_widths(sfx)))
      +n = List.length(&2, String, ls)
      +du = List.drop(&2, Nat, u, j)
      +dd = List.drop(&2, Nat, d, j)
      +tabside = c ++ String.repeat(" ", Nat.sub(Nat.add(Tab.nmax(Tab.head0(du), Tab.head0(dd)), 2n), Tab.runes(c))) ++ Tab.pad_cells(rest, List.tail(&2, Nat, du), List.tail(&2, Nat, dd))
      %pc(rest, ls, i, rn, hn1, sfx, hd, hn, 1n+j)
        : {tabside == c ++ String.repeat(" ", Nat.sub(Nat.add(Nat.max(L.up_w(n, ls, i, j), L.down_w(n, ls, i, j)), 2n), L.runes(c))) ++ _ : String}
      %tl_drop(u, j)
        : {tabside == c ++ String.repeat(" ", Nat.sub(Nat.add(Nat.max(L.up_w(n, ls, i, j), L.down_w(n, ls, i, j)), 2n), L.runes(c)))
             ++ Tab.pad_cells(rest, _, List.drop(&2, Nat, d, 1n+j)) : String}
      %tl_drop(d, j)
        : {tabside == c ++ String.repeat(" ", Nat.sub(Nat.add(Nat.max(L.up_w(n, ls, i, j), L.down_w(n, ls, i, j)), 2n), L.runes(c)))
             ++ Tab.pad_cells(rest, List.tail(&2, Nat, du), _) : String}
      %Equal.sym(Nat, L.runes(c), Tab.runes(c), runes_same(c))
        : {tabside == c ++ String.repeat(" ", Nat.sub(Nat.add(Nat.max(L.up_w(n, ls, i, j), L.down_w(n, ls, i, j)), 2n), _))
             ++ Tab.pad_cells(rest, List.tail(&2, Nat, du), List.tail(&2, Nat, dd)) : String}
      %Equal.trans(Nat, Tab.head0(du), L.nth_or0(j, u), L.up_w(n, ls, i, j), hd_drop(u, j), fu(ls, i, rn, hn1, j))
        : {tabside == c ++ String.repeat(" ", Nat.sub(Nat.add(Nat.max(_, L.down_w(n, ls, i, j)), 2n), Tab.runes(c)))
             ++ Tab.pad_cells(rest, List.tail(&2, Nat, du), List.tail(&2, Nat, dd)) : String}
      %Equal.trans(Nat, Tab.head0(dd), L.nth_or0(j, d), L.down_w(n, ls, i, j), hd_drop(d, j), fd(sfx, ls, i, hd, hn, j))
        : {tabside == c ++ String.repeat(" ", Nat.sub(Nat.add(Nat.max(Tab.head0(du), _), 2n), Tab.runes(c)))
             ++ Tab.pad_cells(rest, List.tail(&2, Nat, du), List.tail(&2, Nat, dd)) : String}
      %Equal.sym(Nat, Nat.max(Tab.head0(du), Tab.head0(dd)), Tab.nmax(Tab.head0(du), Tab.head0(dd)), tmax(Tab.head0(du), Tab.head0(dd)))
        : {tabside == c ++ String.repeat(" ", Nat.sub(Nat.add(_, 2n), Tab.runes(c)))
             ++ Tab.pad_cells(rest, List.tail(&2, Nat, du), List.tail(&2, Nat, dd)) : String}
      {==}

def lay(sfx: List<&2, String>, +ls: List<&2, String>, +i: Nat, +p: List<&2, Nat>, +hd: {List.drop(&2, String, ls, i) == sfx : List<&2, String>},
  +hp: {p == prev(i, ls) : List<&2, Nat>},
  +hn: {Nat.add(i, List.length(&2, String, sfx)) == List.length(&2, String, ls) : Nat})
  -> {Tab.lay(sfx, Tab.runs(Tab.all_widths(sfx), p), br(Tab.all_widths(sfx))) == L.tab_lines(List.length(&2, String, sfx), ls, i) : List<&2, String>}:
  match sfx:
    case Nil{}:
      {==}
    case Con{+l, +r}:
      +n = List.length(&2, String, ls)
      +rn = List.length(&2, String, r)
      +wl = Tab.widths(Tab.cells(l))
      +u = Tab.zmax(wl, p)
      +pd = hd_or(br(Tab.all_widths(r)))
      +d = Tab.zmax(wl, pd)
      +hl = get_line(ls, i, l, r, hd)
      +hr = sdrop_succ(ls, i, l, r, hd)
      +hu = {%Equal.sym(List<&2, Nat>, p, prev(i, ls), hp) : {Tab.zmax(wl, _) == urun(i, ls) : List<&2, Nat>};
             %hl : {Tab.zmax(Tab.widths(Tab.cells(_)), prev(i, ls)) == urun(i, ls) : List<&2, Nat>};
             urun_eq(i, ls) : {u == urun(i, ls) : List<&2, Nat>}}
      +hn1 = {%Equal.sym(Nat, 1n+Nat.add(i, rn), Nat.add(i, 1n+rn), PNat.add_succ(i, rn)) : {_ == n : Nat};
              hn : {Nat.add(1n+i, rn) == n : Nat}}
      +tabhead = Tab.pad_cells(Tab.cells(l), u, d) ++ Tab.trailing(l)
      +tabrest = Tab.lay(r, Tab.runs(Tab.all_widths(r), u), br(Tab.all_widths(r)))
      %lay(r, ls, 1n+i, u, hr, hu, hn1)
        : {Con{tabhead, tabrest} == Con{L.pad_cells(L.tab_cells(L.line_at(ls, i)), ls, i, 0n) ++ L.trailing(L.line_at(ls, i)), _} : List<&2, String>}
      %Equal.sym(String, L.line_at(ls, i), l, hl)
        : {Con{tabhead, tabrest} == Con{L.pad_cells(L.tab_cells(_), ls, i, 0n) ++ L.trailing(_), tabrest} : List<&2, String>}
      %Equal.sym(String, L.trailing(l), Tab.trailing(l), trailing_same(l))
        : {Con{tabhead, tabrest} == Con{L.pad_cells(L.tab_cells(l), ls, i, 0n) ++ _, tabrest} : List<&2, String>}
      %Equal.sym(List<&2, String>, L.tab_cells(l), Tab.cells(l), cells_same(l))
        : {Con{tabhead, tabrest} == Con{L.pad_cells(_, ls, i, 0n) ++ Tab.trailing(l), tabrest} : List<&2, String>}
      %pc(Tab.cells(l), ls, i, rn, hn1, Con{l, r}, hd, hn, 0n)
        : {Con{tabhead, tabrest} == Con{_ ++ Tab.trailing(l), tabrest} : List<&2, String>}
      %drop0(urun(i, ls))
        : {Con{tabhead, tabrest} == Con{Tab.pad_cells(Tab.cells(l), _, List.drop(&2, Nat, d, 0n)) ++ Tab.trailing(l), tabrest} : List<&2, String>}
      %drop0(d)
        : {Con{tabhead, tabrest} == Con{Tab.pad_cells(Tab.cells(l), urun(i, ls), _) ++ Tab.trailing(l), tabrest} : List<&2, String>}
      %hu
        : {Con{tabhead, tabrest} == Con{Tab.pad_cells(Tab.cells(l), _, d) ++ Tab.trailing(l), tabrest} : List<&2, String>}
      {==}

def L.tab_render(s, h):
  +ls = Tab.split_on(10, s)
  +w = Tab.all_widths(ls)
  +x = Tab.lay(ls, Tab.runs(w, []), List.reverse(&2, List<&2, Nat>, Tab.runs(List.reverse(&2, List<&2, Nat>, w), [])))
  %split_same(10, s) : {Tab.render(s) == L.join_str("\n", L.tab_lines(List.length(&2, String, _), _, 0n)) : String}
  %lay(ls, ls, 0n, [], Equal.sym(List<&2, String>, ls, List.drop(&2, String, ls, 0n), sdrop0(ls)), {==}, {==})
    : {Tab.render(s) == L.join_str("\n", _) : String}
  %Equal.sym(List<&2, List<&2, Nat>>, br(w), List.reverse(&2, List<&2, Nat>, Tab.runs(List.reverse(&2, List<&2, Nat>, w), [])), brl(w))
    : {Tab.render(s) == L.join_str("\n", Tab.lay(ls, Tab.runs(w, []), _)) : String}
  tjoin_same(x)

# =====================================================================
# met_build: merge is a monoid on the report's view of an accumulator
# =====================================================================
#
# Two ascending code lists with the same counts on every code they hold
# are equal; so are two ascending error lists holding the same strings.
# That makes the merges associative; Bigs are canonical, and the extremes
# are mins and maxes.

def eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def keys(cs: List<&2, CP()>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      []
    case Con{p, rest}:
      Con{Met.code_k(p), keys(rest)}

def mem(+k: Nat, ks: List<&2, Nat>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{+x, +rest}:
      Bool.or(Nat.is_eq(k, x), mem(k, rest))

def subk(cs: List<&2, CP()>, +ks: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{p, rest}:
      Bool.and(mem(Met.code_k(p), ks), subk(rest, ks))

# the counts agree on every code of ks
def eqon(ks: List<&2, Nat>, +xs: List<&2, CP()>, +ys: List<&2, CP()>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+k, +rest}:
      Bool.and(Nat.is_eq(L.lookup_code(k, xs), L.lookup_code(k, ys)), eqon(rest, xs, ys))

def or_l(a: Bool, -b: Bool, +h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def eqon_at.of(c: Bool, +k: Nat, +x: Nat, +rest: List<&2, Nat>, +xs: List<&2, CP()>, +ys: List<&2, CP()>, +ec: {Nat.is_eq(k, x) == c : Bool},
  +h: {eqon(Con{x, rest}, xs, ys) == True{} : Bool}, +hm: {Bool.or(c, mem(k, rest)) == True{} : Bool},
  ih: {eqon(rest, xs, ys) == True{} : Bool} -> {mem(k, rest) == True{} : Bool} -> {L.lookup_code(k, xs) == L.lookup_code(k, ys) : Nat})
  -> {L.lookup_code(k, xs) == L.lookup_code(k, ys) : Nat}:
  match c:
    case True{}:
      +hh = and_l(Nat.is_eq(L.lookup_code(x, xs), L.lookup_code(x, ys)), eqon(rest, xs, ys), h)
      %Equal.sym(Nat, k, x, n_eq_is(k, x, ec)) : {L.lookup_code(_, xs) == L.lookup_code(_, ys) : Nat}
      n_eq_is(L.lookup_code(x, xs), L.lookup_code(x, ys), hh)
    case False{}:
      ih(and_r(Nat.is_eq(L.lookup_code(x, xs), L.lookup_code(x, ys)), eqon(rest, xs, ys), h), hm)

def eqon_at(ks: List<&2, Nat>, +k: Nat, +xs: List<&2, CP()>, +ys: List<&2, CP()>, +h: {eqon(ks, xs, ys) == True{} : Bool}, +hm: {mem(k, ks) == True{} : Bool})
  -> {L.lookup_code(k, xs) == L.lookup_code(k, ys) : Nat}:
  match ks:
    case Nil{}:
      Empty.absurd({L.lookup_code(k, xs) == L.lookup_code(k, ys) : Nat}, no_ft(hm))
    case Con{+x, +rest}:
      eqon_at.of(Nat.is_eq(k, x), k, x, rest, xs, ys, {==}, h, hm, h1 => h2 => eqon_at(rest, k, xs, ys, h1, h2))

def et.of(c: Bool, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +v2: Nat, +yr: List<&2, CP()>, +k: Nat, +ec: {Nat.is_eq(k1, k) == c : Bool},
  +h: {Nat.is_eq(L.pick(Nat, c, v1, L.lookup_code(k, xr)), L.pick(Nat, c, v2, L.lookup_code(k, yr))) == True{} : Bool},
  +ax: {L.codes_after(xr, k1) == True{} : Bool}, +ay: {L.codes_after(yr, k1) == True{} : Bool})
  -> {Nat.is_eq(L.lookup_code(k, xr), L.lookup_code(k, yr)) == True{} : Bool}:
  match c:
    case True{}:
      +le = {%Equal.sym(Nat, k1, k, n_eq_is(k1, k, ec)) : {Nat.is_le(k, _) == True{} : Bool}; le_refl(k) : {Nat.is_le(k, k1) == True{} : Bool}}
      %lk_zero(xr, k1, k, ax, le) : {Nat.is_eq(_, L.lookup_code(k, yr)) == True{} : Bool}
      %lk_zero(yr, k1, k, ay, le) : {Nat.is_eq(0n, _) == True{} : Bool}
      {==}
    case False{}:
      h

def eqon_tail(ks: List<&2, Nat>, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +v2: Nat, +yr: List<&2, CP()>,
  +h: {eqon(ks, Con{{(k1, v1) : CP()}, xr}, Con{{(k1, v2) : CP()}, yr}) == True{} : Bool},
  +ax: {L.codes_after(xr, k1) == True{} : Bool}, +ay: {L.codes_after(yr, k1) == True{} : Bool})
  -> {eqon(ks, xr, yr) == True{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +rest}:
      +xs = {Con{{(k1, v1) : CP()}, xr} : List<&2, CP()>}
      +ys = {Con{{(k1, v2) : CP()}, yr} : List<&2, CP()>}
      +a = Nat.is_eq(L.lookup_code(k, xs), L.lookup_code(k, ys))
      and_i(Nat.is_eq(L.lookup_code(k, xr), L.lookup_code(k, yr)), eqon(rest, xr, yr),
        et.of(Nat.is_eq(k1, k), k1, v1, xr, v2, yr, k, {==}, and_l(a, eqon(rest, xs, ys), h), ax, ay),
        eqon_tail(rest, k1, v1, xr, v2, yr, and_r(a, eqon(rest, xs, ys), h), ax, ay))

def gt0_ne(-v: Nat, +h: {Nat.is_gt(v, 0n) == True{} : Bool}, +e: {v == 0n : Nat}) -> Empty:
  no_ft({%e : {Nat.is_gt(_, 0n) == True{} : Bool}; h : {Nat.is_gt(0n, 0n) == True{} : Bool}})

# the value at the head of an ascending list
def lk_head(+k: Nat, +v: Nat, +r: List<&2, CP()>) -> {L.lookup_code(k, Con{{(k, v) : CP()}, r}) == v : Nat}:
  %Equal.sym(Bool, Nat.is_eq(k, k), True{}, eq_refl(k)) : {L.pick(Nat, _, v, L.lookup_code(k, r)) == v : Nat}
  {==}

def ext.of(c: Cmp, +k1: Nat, +v1: Nat, +xr: List<&2, CP()>, +k2: Nat, +v2: Nat, +yr: List<&2, CP()>, +ks: List<&2, Nat>,
  +ec: {Nat.cmp(k1, k2) == c : Cmp},
  +ax: {L.codes_ascending(Con{{(k1, v1) : CP()}, xr}) == True{} : Bool}, +ay: {L.codes_ascending(Con{{(k2, v2) : CP()}, yr}) == True{} : Bool},
  +m1: {mem(k1, ks) == True{} : Bool}, +m2: {mem(k2, ks) == True{} : Bool},
  +h: {eqon(ks, Con{{(k1, v1) : CP()}, xr}, Con{{(k2, v2) : CP()}, yr}) == True{} : Bool},
  ih: {L.codes_ascending(xr) == True{} : Bool} -> {L.codes_ascending(yr) == True{} : Bool}
    -> {eqon(ks, xr, yr) == True{} : Bool} -> {xr == yr : List<&2, CP()>})
  -> {Con{{(k1, v1) : CP()}, xr} == Con{{(k2, v2) : CP()}, yr} : List<&2, CP()>}:
  match c:
    case LT{}:
      +xs = {Con{{(k1, v1) : CP()}, xr} : List<&2, CP()>}
      +ys = {Con{{(k2, v2) : CP()}, yr} : List<&2, CP()>}
      +hlt = Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), Nat.cmp(k1, k2), LT{}, ec)
      +e = {%lk_head(k1, v1, xr) : {_ == 0n : Nat};
            %Equal.sym(Nat, 0n, L.lookup_code(k1, ys), lk_below(k1, k2, v2, yr, hlt, asc_tail(k2, v2, yr, ay))) : {L.lookup_code(k1, xs) == _ : Nat};
            eqon_at(ks, k1, xs, ys, h, m1) : {v1 == 0n : Nat}}
      Empty.absurd({xs == ys : List<&2, CP()>}, gt0_ne(v1, asc_pos(k1, v1, xr, ax), e))
    case GT{}:
      +xs = {Con{{(k1, v1) : CP()}, xr} : List<&2, CP()>}
      +ys = {Con{{(k2, v2) : CP()}, yr} : List<&2, CP()>}
      +hlt = cmp_gt(k1, k2, ec)
      +e = {%lk_head(k2, v2, yr) : {_ == 0n : Nat};
            %Equal.sym(Nat, 0n, L.lookup_code(k2, xs), lk_below(k2, k1, v1, xr, hlt, asc_tail(k1, v1, xr, ax))) : {L.lookup_code(k2, ys) == _ : Nat};
            Equal.sym(Nat, L.lookup_code(k2, xs), L.lookup_code(k2, ys), eqon_at(ks, k2, xs, ys, h, m2)) : {v2 == 0n : Nat}}
      Empty.absurd({xs == ys : List<&2, CP()>}, gt0_ne(v2, asc_pos(k2, v2, yr, ay), e))
    case EQ{}:
      +xs = {Con{{(k1, v1) : CP()}, xr} : List<&2, CP()>}
      +kk = cmp_eq(k1, k2, ec)
      %kk : {xs == Con{{(_, v2) : CP()}, yr} : List<&2, CP()>}
      +ay2 = {%Equal.sym(Nat, k1, k2, kk) : {L.codes_ascending(Con{{(_, v2) : CP()}, yr}) == True{} : Bool}; ay : {L.codes_ascending(Con{{(k1, v2) : CP()}, yr}) == True{} : Bool}}
      +h2 = {%Equal.sym(Nat, k1, k2, kk) : {eqon(ks, xs, Con{{(_, v2) : CP()}, yr}) == True{} : Bool}; h : {eqon(ks, xs, Con{{(k1, v2) : CP()}, yr}) == True{} : Bool}}
      +vv = {%lk_head(k1, v1, xr) : {_ == v2 : Nat};
             %lk_head(k1, v2, yr) : {L.lookup_code(k1, xs) == _ : Nat};
             eqon_at(ks, k1, xs, Con{{(k1, v2) : CP()}, yr}, h2, m1) : {v1 == v2 : Nat}}
      %vv : {xs == Con{{(k1, _) : CP()}, yr} : List<&2, CP()>}
      +et = eqon_tail(ks, k1, v1, xr, v2, yr, h2, asc_tail(k1, v1, xr, ax), asc_tail(k1, v2, yr, ay2))
      %ih(asc_rest(k1, v1, xr, ax), asc_rest(k1, v2, yr, ay2), et) : {xs == Con{{(k1, v1) : CP()}, _} : List<&2, CP()>}
      {==}

def codes_ext(xs: List<&2, CP()>, ys: List<&2, CP()>, +ks: List<&2, Nat>,
  +ax: {L.codes_ascending(xs) == True{} : Bool}, +ay: {L.codes_ascending(ys) == True{} : Bool},
  +sx: {subk(xs, ks) == True{} : Bool}, +sy: {subk(ys, ks) == True{} : Bool}, +h: {eqon(ks, xs, ys) == True{} : Bool})
  -> {xs == ys : List<&2, CP()>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case Con{q, +yr}:
          match q:
            case (+k2, +v2):
              +ys2 = {Con{{(k2, v2) : CP()}, yr} : List<&2, CP()>}
              +m2 = and_l(mem(k2, ks), subk(yr, ks), sy)
              +e = {%lk_head(k2, v2, yr) : {0n == _ : Nat}; eqon_at(ks, k2, [], ys2, h, m2) : {0n == v2 : Nat}}
              Empty.absurd({[] == ys2 : List<&2, CP()>}, gt0_ne(v2, asc_pos(k2, v2, yr, ay), Equal.sym(Nat, 0n, v2, e)))
    case Con{p, +xr}:
      match p:
        case (+k1, +v1):
          match ys:
            case Nil{}:
              +xs2 = {Con{{(k1, v1) : CP()}, xr} : List<&2, CP()>}
              +m1 = and_l(mem(k1, ks), subk(xr, ks), sx)
              +e = {%lk_head(k1, v1, xr) : {_ == 0n : Nat}; eqon_at(ks, k1, xs2, [], h, m1) : {v1 == 0n : Nat}}
              Empty.absurd({xs2 == [] : List<&2, CP()>}, gt0_ne(v1, asc_pos(k1, v1, xr, ax), e))
            case Con{q, +yr}:
              match q:
                case (+k2, +v2):
                  ext.of(Nat.cmp(k1, k2), k1, v1, xr, k2, v2, yr, ks, {==}, ax, ay,
                    and_l(mem(k1, ks), subk(xr, ks), sx), and_l(mem(k2, ks), subk(yr, ks), sy), h,
                    a => b => c => codes_ext(xr, yr, ks, a, b, and_r(mem(k1, ks), subk(xr, ks), sx), and_r(mem(k2, ks), subk(yr, ks), sy), c))

def or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def mem_app(+k: Nat, k1: List<&2, Nat>, +r: List<&2, Nat>) -> {mem(k, List.append(&2, Nat, k1, Con{k, r})) == True{} : Bool}:
  match k1:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(k, k), True{}, eq_refl(k)) : {Bool.or(_, mem(k, r)) == True{} : Bool}
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Bool, mem(k, List.append(&2, Nat, rest, Con{k, r})), True{}, mem_app(k, rest, r)) : {Bool.or(Nat.is_eq(k, x), _) == True{} : Bool}
      or_true_r(Nat.is_eq(k, x))

def napp_assoc(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>)
  -> {List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) == List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %napp_assoc(r, ys, zs) : {Con{x, List.append(&2, Nat, r, List.append(&2, Nat, ys, zs))} == Con{x, _} : List<&2, Nat>}
      {==}

def subk_app(a: List<&2, CP()>, +k1: List<&2, Nat>, +k2: List<&2, Nat>)
  -> {subk(a, List.append(&2, Nat, k1, List.append(&2, Nat, keys(a), k2))) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{p, +r}:
      match p:
        case (+k, +v):
          +kk = List.append(&2, Nat, k1, Con{k, List.append(&2, Nat, keys(r), k2)})
          +ih = {%Equal.sym(List<&2, Nat>, kk, List.append(&2, Nat, List.append(&2, Nat, k1, [k]), List.append(&2, Nat, keys(r), k2)), napp_assoc(k1, [k], List.append(&2, Nat, keys(r), k2))) : {subk(r, _) == True{} : Bool};
                 subk_app(r, List.append(&2, Nat, k1, [k]), k2) : {subk(r, kk) == True{} : Bool}}
          and_i(mem(k, kk), subk(r, kk), mem_app(k, k1, List.append(&2, Nat, keys(r), k2)), ih)

def lk3(+k: Nat, +x: List<&2, CP()>, +y: List<&2, CP()>, +z: List<&2, CP()>,
  +ax: {L.codes_ascending(x) == True{} : Bool}, +ay: {L.codes_ascending(y) == True{} : Bool}, +az: {L.codes_ascending(z) == True{} : Bool})
  -> {L.lookup_code(k, Met.codes_merge(Met.codes_merge(x, y), z)) == L.lookup_code(k, Met.codes_merge(x, Met.codes_merge(y, z))) : Nat}:
  +mxy = Met.codes_merge(x, y)
  +myz = Met.codes_merge(y, z)
  +a = L.lookup_code(k, x)
  +b = L.lookup_code(k, y)
  +c = L.lookup_code(k, z)
  %lk_merge(mxy, z, k, asc_merge(x, y, ax, ay), az) : {_ == L.lookup_code(k, Met.codes_merge(x, myz)) : Nat}
  %lk_merge(x, y, k, ax, ay) : {Nat.add(_, c) == L.lookup_code(k, Met.codes_merge(x, myz)) : Nat}
  %lk_merge(x, myz, k, ax, asc_merge(y, z, ay, az)) : {Nat.add(Nat.add(a, b), c) == _ : Nat}
  %lk_merge(y, z, k, ay, az) : {Nat.add(Nat.add(a, b), c) == Nat.add(a, _) : Nat}
  Equal.sym(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), PNat.add_assoc(a, b, c))

def eq_of(-a: Nat, +b: Nat, +e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_eq(_, b) == True{} : Bool}
  eq_refl(b)

def eqon3(ks: List<&2, Nat>, +x: List<&2, CP()>, +y: List<&2, CP()>, +z: List<&2, CP()>,
  +ax: {L.codes_ascending(x) == True{} : Bool}, +ay: {L.codes_ascending(y) == True{} : Bool}, +az: {L.codes_ascending(z) == True{} : Bool})
  -> {eqon(ks, Met.codes_merge(Met.codes_merge(x, y), z), Met.codes_merge(x, Met.codes_merge(y, z))) == True{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +rest}:
      +A = Met.codes_merge(Met.codes_merge(x, y), z)
      +B = Met.codes_merge(x, Met.codes_merge(y, z))
      and_i(Nat.is_eq(L.lookup_code(k, A), L.lookup_code(k, B)), eqon(rest, A, B),
        eq_of(L.lookup_code(k, A), L.lookup_code(k, B), lk3(k, x, y, z, ax, ay, az)), eqon3(rest, x, y, z, ax, ay, az))

def codes_assoc(+x: List<&2, CP()>, +y: List<&2, CP()>, +z: List<&2, CP()>,
  +ax: {L.codes_ascending(x) == True{} : Bool}, +ay: {L.codes_ascending(y) == True{} : Bool}, +az: {L.codes_ascending(z) == True{} : Bool})
  -> {Met.codes_merge(Met.codes_merge(x, y), z) == Met.codes_merge(x, Met.codes_merge(y, z)) : List<&2, CP()>}:
  +A = Met.codes_merge(Met.codes_merge(x, y), z)
  +B = Met.codes_merge(x, Met.codes_merge(y, z))
  +ks = List.append(&2, Nat, keys(A), keys(B))
  +sb = {%Equal.sym(List<&2, Nat>, keys(B), List.append(&2, Nat, keys(B), []), app_nil(keys(B))) : {subk(B, List.append(&2, Nat, keys(A), _)) == True{} : Bool};
         subk_app(B, keys(A), []) : {subk(B, ks) == True{} : Bool}}
  codes_ext(A, B, ks, asc_merge(Met.codes_merge(x, y), z, asc_merge(x, y, ax, ay), az), asc_merge(x, Met.codes_merge(y, z), ax, asc_merge(y, z, ay, az)),
    subk_app(A, [], keys(B)), sb, eqon3(ks, x, y, z, ax, ay, az))

# ---------------------------------------------------------------------
# the error set merge is associative
# ---------------------------------------------------------------------

def so_trans.of(k1: Cmp, k2: Cmp, +c1: Char, +t1: String, +c2: Char, +t2: String, +c3: Char, +t3: String,
  +e1: {ccmp(c1, c2) == k1 : Cmp}, +e2: {ccmp(c2, c3) == k2 : Cmp},
  +h1: {cpick(k1, sord(t1, t2)) == LT{} : Cmp}, +h2: {cpick(k2, sord(t2, t3)) == LT{} : Cmp},
  ih: {sord(t1, t2) == LT{} : Cmp} -> {sord(t2, t3) == LT{} : Cmp} -> {sord(t1, t3) == LT{} : Cmp})
  -> {cpick(ccmp(c1, c3), sord(t1, t3)) == LT{} : Cmp}:
  match k1:
    case LT{}:
      match k2:
        case LT{}:
          %Equal.sym(Cmp, ccmp(c1, c3), LT{}, c_trans(c1, c2, c3, e1, e2)) : {cpick(_, sord(t1, t3)) == LT{} : Cmp}
          {==}
        case EQ{}:
          %c_eqv(c2, c3, e2) : {cpick(ccmp(c1, _), sord(t1, t3)) == LT{} : Cmp}
          %Equal.sym(Cmp, ccmp(c1, c2), LT{}, e1) : {cpick(_, sord(t1, t3)) == LT{} : Cmp}
          {==}
        case GT{}:
          Empty.absurd({cpick(ccmp(c1, c3), sord(t1, t3)) == LT{} : Cmp}, gt_ne_lt(h2))
    case EQ{}:
      match k2:
        case LT{}:
          %Equal.sym(Char, c1, c2, c_eqv(c1, c2, e1)) : {cpick(ccmp(_, c3), sord(t1, t3)) == LT{} : Cmp}
          %Equal.sym(Cmp, ccmp(c2, c3), LT{}, e2) : {cpick(_, sord(t1, t3)) == LT{} : Cmp}
          {==}
        case EQ{}:
          %Equal.sym(Char, c1, c2, c_eqv(c1, c2, e1)) : {cpick(ccmp(_, c3), sord(t1, t3)) == LT{} : Cmp}
          %Equal.sym(Cmp, ccmp(c2, c3), EQ{}, e2) : {cpick(_, sord(t1, t3)) == LT{} : Cmp}
          ih(h1, h2)
        case GT{}:
          Empty.absurd({cpick(ccmp(c1, c3), sord(t1, t3)) == LT{} : Cmp}, gt_ne_lt(h2))
    case GT{}:
      Empty.absurd({cpick(ccmp(c1, c3), sord(t1, t3)) == LT{} : Cmp}, gt_ne_lt(h1))

def so_trans(a: String, b: String, c: String, +h1: {sord(a, b) == LT{} : Cmp}, +h2: {sord(b, c) == LT{} : Cmp}) -> {sord(a, c) == LT{} : Cmp}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          Empty.absurd({sord("", c) == LT{} : Cmp}, eq_ne_lt(h1))
        case SCon{c2, t2}:
          match c:
            case SNil{}:
              Empty.absurd({EQ{} == LT{} : Cmp}, gt_ne_lt(h2))
            case SCon{c3, t3}:
              {==}
    case SCon{+c1, +t1}:
      match b:
        case SNil{}:
          Empty.absurd({sord(SCon{c1, t1}, c) == LT{} : Cmp}, gt_ne_lt(h1))
        case SCon{+c2, +t2}:
          match c:
            case SNil{}:
              Empty.absurd({GT{} == LT{} : Cmp}, gt_ne_lt(h2))
            case SCon{+c3, +t3}:
              so_trans.of(ccmp(c1, c2), ccmp(c2, c3), c1, t1, c2, t2, c3, t3, {==}, {==}, h1, h2, x => y => so_trans(t1, t2, t3, x, y))

def s_eq_self(+x: String) -> {String.eq(x, x) == True{} : Bool}:
  %s_eq(x, x) : {_ == True{} : Bool}
  %Equal.sym(Cmp, sord(x, x), EQ{}, so_refl(x)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def s_ne_lt(+x: String, +z: String, +h: {sord(x, z) == LT{} : Cmp}) -> {String.eq(x, z) == False{} : Bool}:
  %s_eq(x, z) : {_ == False{} : Bool}
  %Equal.sym(Cmp, sord(x, z), LT{}, h) : {Cmp.is_eq(_) == False{} : Bool}
  {==}

def s_lt_ord2(+x: String, +z: String, +h: {sord(x, z) == LT{} : Cmp}) -> {String.is_lt(x, z) == True{} : Bool}:
  %s_lt(x, z) : {_ == True{} : Bool}
  %Equal.sym(Cmp, sord(x, z), LT{}, h) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

# x no later than the bound b of a strictly ascending list: x is not in it
def nin.of(c: Cmp, +x: String, +b: String, +z: String, +ec: {sord(x, b) == c : Cmp}, +hbz: {sord(b, z) == LT{} : Cmp},
  +hx: {Cmp.is_gt(c) == False{} : Bool}) -> {sord(x, z) == LT{} : Cmp}:
  match c:
    case LT{}:
      so_trans(x, b, z, ec, hbz)
    case EQ{}:
      %Equal.sym(String, x, b, so_eqv(x, b, ec)) : {sord(_, z) == LT{} : Cmp}
      hbz
    case GT{}:
      Empty.absurd({sord(x, z) == LT{} : Cmp}, no_ft(Equal.sym(Bool, True{}, False{}, hx)))

def nin(r: List<&2, String>, +b: String, +x: String, +hr: {sa(r, b) == True{} : Bool}, +hx: {Cmp.is_gt(sord(x, b)) == False{} : Bool})
  -> {L.has_str(x, r) == False{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+z, +rest}:
      +hxz = nin.of(sord(x, b), x, b, z, {==}, s_lt_ord(b, z, sa_head(b, z, rest, hr)), hx)
      %Equal.sym(Bool, String.eq(x, z), False{}, s_ne_lt(x, z, hxz)) : {Bool.or(_, L.has_str(x, rest)) == False{} : Bool}
      nin(rest, z, x, sa_tail(b, z, rest, hr), {%Equal.sym(Cmp, sord(x, z), LT{}, hxz) : {Cmp.is_gt(_) == False{} : Bool}; {==} : {Cmp.is_gt(sord(x, z)) == False{} : Bool}})

def smem(+x: String, ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{+k, +rest}:
      Bool.or(String.eq(x, k), smem(x, rest))

def subs(xs: List<&2, String>, +ks: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(smem(x, ks), subs(rest, ks))

def beq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def eqs(ks: List<&2, String>, +xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+k, +rest}:
      Bool.and(beq(L.has_str(k, xs), L.has_str(k, ys)), eqs(rest, xs, ys))

def beq_eq(a: Bool, b: Bool, +h: {beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a:
    case True{}:
      Equal.sym(Bool, b, True{}, h)
    case False{}:
      match b:
        case True{}:
          Empty.absurd({False{} == True{} : Bool}, no_ft(h))
        case False{}:
          {==}

def beq_refl(a: Bool) -> {beq(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cmp_eq_t(c: Cmp, +h: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, no_ft(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, no_ft(h))

def seq_eq(+x: String, +k: String, +h: {String.eq(x, k) == True{} : Bool}) -> {x == k : String}:
  so_eqv(x, k, cmp_eq_t(sord(x, k), Equal.trans(Bool, Cmp.is_eq(sord(x, k)), String.eq(x, k), True{}, s_eq(x, k), h)))

def eqs_at.of(c: Bool, +e: String, +k: String, +rest: List<&2, String>, +xs: List<&2, String>, +ys: List<&2, String>, +ec: {String.eq(e, k) == c : Bool},
  +h: {eqs(Con{k, rest}, xs, ys) == True{} : Bool}, +hm: {Bool.or(c, smem(e, rest)) == True{} : Bool},
  ih: {eqs(rest, xs, ys) == True{} : Bool} -> {smem(e, rest) == True{} : Bool} -> {L.has_str(e, xs) == L.has_str(e, ys) : Bool})
  -> {L.has_str(e, xs) == L.has_str(e, ys) : Bool}:
  match c:
    case True{}:
      %Equal.sym(String, e, k, seq_eq(e, k, ec)) : {L.has_str(_, xs) == L.has_str(_, ys) : Bool}
      beq_eq(L.has_str(k, xs), L.has_str(k, ys), and_l(beq(L.has_str(k, xs), L.has_str(k, ys)), eqs(rest, xs, ys), h))
    case False{}:
      ih(and_r(beq(L.has_str(k, xs), L.has_str(k, ys)), eqs(rest, xs, ys), h), hm)

def eqs_at(ks: List<&2, String>, +e: String, +xs: List<&2, String>, +ys: List<&2, String>, +h: {eqs(ks, xs, ys) == True{} : Bool}, +hm: {smem(e, ks) == True{} : Bool})
  -> {L.has_str(e, xs) == L.has_str(e, ys) : Bool}:
  match ks:
    case Nil{}:
      Empty.absurd({L.has_str(e, xs) == L.has_str(e, ys) : Bool}, no_ft(hm))
    case Con{+k, +rest}:
      eqs_at.of(String.eq(e, k), e, k, rest, xs, ys, {==}, h, hm, h1 => h2 => eqs_at(rest, e, xs, ys, h1, h2))

def ex_self(+x: String) -> {Cmp.is_gt(sord(x, x)) == False{} : Bool}:
  %Equal.sym(Cmp, sord(x, x), EQ{}, so_refl(x)) : {Cmp.is_gt(_) == False{} : Bool}
  {==}

def et2.of(c: Bool, +e: String, +x: String, +xr: List<&2, String>, +yr: List<&2, String>, +ec: {String.eq(e, x) == c : Bool},
  +h: {beq(Bool.or(c, L.has_str(e, xr)), Bool.or(c, L.has_str(e, yr))) == True{} : Bool},
  +ax: {sa(xr, x) == True{} : Bool}, +ay: {sa(yr, x) == True{} : Bool})
  -> {beq(L.has_str(e, xr), L.has_str(e, yr)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(String, e, x, seq_eq(e, x, ec)) : {beq(L.has_str(_, xr), L.has_str(_, yr)) == True{} : Bool}
      %Equal.sym(Bool, L.has_str(x, xr), False{}, nin(xr, x, x, ax, ex_self(x))) : {beq(_, L.has_str(x, yr)) == True{} : Bool}
      %Equal.sym(Bool, L.has_str(x, yr), False{}, nin(yr, x, x, ay, ex_self(x))) : {beq(False{}, _) == True{} : Bool}
      {==}
    case False{}:
      h

def eqs_tail(ks: List<&2, String>, +x: String, +xr: List<&2, String>, +yr: List<&2, String>,
  +h: {eqs(ks, Con{x, xr}, Con{x, yr}) == True{} : Bool}, +ax: {sa(xr, x) == True{} : Bool}, +ay: {sa(yr, x) == True{} : Bool})
  -> {eqs(ks, xr, yr) == True{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      +a = beq(L.has_str(e, Con{x, xr}), L.has_str(e, Con{x, yr}))
      and_i(beq(L.has_str(e, xr), L.has_str(e, yr)), eqs(rest, xr, yr),
        et2.of(String.eq(e, x), e, x, xr, yr, {==}, and_l(a, eqs(rest, Con{x, xr}, Con{x, yr}), h), ax, ay),
        eqs_tail(rest, x, xr, yr, and_r(a, eqs(rest, Con{x, xr}, Con{x, yr}), h), ax, ay))

def sa_asc2(r: List<&2, String>, +x: String, +h: {sa(r, x) == True{} : Bool}) -> {L.strs_ascending(r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+z, +rest}:
      sa_mk(z, rest, sa_tail(x, z, rest, h))

def has_head(+x: String, +r: List<&2, String>) -> {L.has_str(x, Con{x, r}) == True{} : Bool}:
  %Equal.sym(Bool, String.eq(x, x), True{}, s_eq_self(x)) : {Bool.or(_, L.has_str(x, r)) == True{} : Bool}
  {==}

# x below the head y of a strictly ascending list: not in it
def has_below(+x: String, +y: String, +yr: List<&2, String>, +hxy: {sord(x, y) == LT{} : Cmp}, +hy: {sa(yr, y) == True{} : Bool})
  -> {L.has_str(x, Con{y, yr}) == False{} : Bool}:
  %Equal.sym(Bool, String.eq(x, y), False{}, s_ne_lt(x, y, hxy)) : {Bool.or(_, L.has_str(x, yr)) == False{} : Bool}
  nin(yr, y, x, hy, {%Equal.sym(Cmp, sord(x, y), LT{}, hxy) : {Cmp.is_gt(_) == False{} : Bool}; {==} : {Cmp.is_gt(sord(x, y)) == False{} : Bool}})

def exts.of(c: Cmp, +x: String, +xr: List<&2, String>, +y: String, +yr: List<&2, String>, +ks: List<&2, String>,
  +ec: {sord(x, y) == c : Cmp},
  +ax: {L.strs_ascending(Con{x, xr}) == True{} : Bool}, +ay: {L.strs_ascending(Con{y, yr}) == True{} : Bool},
  +m1: {smem(x, ks) == True{} : Bool}, +m2: {smem(y, ks) == True{} : Bool},
  +h: {eqs(ks, Con{x, xr}, Con{y, yr}) == True{} : Bool},
  ih: {L.strs_ascending(xr) == True{} : Bool} -> {L.strs_ascending(yr) == True{} : Bool}
    -> {eqs(ks, xr, yr) == True{} : Bool} -> {xr == yr : List<&2, String>})
  -> {Con{x, xr} == Con{y, yr} : List<&2, String>}:
  match c:
    case LT{}:
      +e = {%has_head(x, xr) : {_ == False{} : Bool};
            %has_below(x, y, yr, ec, sa_of(y, yr, ay)) : {L.has_str(x, Con{x, xr}) == _ : Bool};
            eqs_at(ks, x, Con{x, xr}, Con{y, yr}, h, m1) : {True{} == False{} : Bool}}
      Empty.absurd({Con{x, xr} == Con{y, yr} : List<&2, String>}, no_ft(Equal.sym(Bool, True{}, False{}, e)))
    case GT{}:
      +hyx = {%Equal.sym(Cmp, sord(y, x), flip(sord(x, y)), so_anti(x, y)) : {_ == LT{} : Cmp}; %Equal.sym(Cmp, sord(x, y), GT{}, ec) : {flip(_) == LT{} : Cmp}; {==} : {sord(y, x) == LT{} : Cmp}}
      +e = {%has_head(y, yr) : {False{} == _ : Bool};
            %has_below(y, x, xr, hyx, sa_of(x, xr, ax)) : {_ == L.has_str(y, Con{y, yr}) : Bool};
            eqs_at(ks, y, Con{x, xr}, Con{y, yr}, h, m2) : {False{} == True{} : Bool}}
      Empty.absurd({Con{x, xr} == Con{y, yr} : List<&2, String>}, no_ft(e))
    case EQ{}:
      +xy = so_eqv(x, y, ec)
      %xy : {Con{x, xr} == Con{_, yr} : List<&2, String>}
      +ay2 = {%Equal.sym(String, x, y, xy) : {L.strs_ascending(Con{_, yr}) == True{} : Bool}; ay : {L.strs_ascending(Con{x, yr}) == True{} : Bool}}
      +h2 = {%Equal.sym(String, x, y, xy) : {eqs(ks, Con{x, xr}, Con{_, yr}) == True{} : Bool}; h : {eqs(ks, Con{x, xr}, Con{x, yr}) == True{} : Bool}}
      +et = eqs_tail(ks, x, xr, yr, h2, sa_of(x, xr, ax), sa_of(x, yr, ay2))
      %ih(sa_asc2(xr, x, sa_of(x, xr, ax)), sa_asc2(yr, x, sa_of(x, yr, ay2)), et) : {Con{x, xr} == Con{x, _} : List<&2, String>}
      {==}

def strs_ext(xs: List<&2, String>, ys: List<&2, String>, +ks: List<&2, String>,
  +ax: {L.strs_ascending(xs) == True{} : Bool}, +ay: {L.strs_ascending(ys) == True{} : Bool},
  +sx: {subs(xs, ks) == True{} : Bool}, +sy: {subs(ys, ks) == True{} : Bool}, +h: {eqs(ks, xs, ys) == True{} : Bool})
  -> {xs == ys : List<&2, String>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case Con{+y, +yr}:
          +e = {%has_head(y, yr) : {False{} == _ : Bool};
                eqs_at(ks, y, [], Con{y, yr}, h, and_l(smem(y, ks), subs(yr, ks), sy)) : {False{} == True{} : Bool}}
          Empty.absurd({[] == Con{y, yr} : List<&2, String>}, no_ft(e))
    case Con{+x, +xr}:
      match ys:
        case Nil{}:
          +e = {%has_head(x, xr) : {_ == False{} : Bool};
                eqs_at(ks, x, Con{x, xr}, [], h, and_l(smem(x, ks), subs(xr, ks), sx)) : {True{} == False{} : Bool}}
          Empty.absurd({Con{x, xr} == [] : List<&2, String>}, no_ft(Equal.sym(Bool, True{}, False{}, e)))
        case Con{+y, +yr}:
          exts.of(sord(x, y), x, xr, y, yr, ks, {==}, ax, ay, and_l(smem(x, ks), subs(xr, ks), sx), and_l(smem(y, ks), subs(yr, ks), sy), h,
            a => b => c => strs_ext(xr, yr, ks, a, b, and_r(smem(x, ks), subs(xr, ks), sx), and_r(smem(y, ks), subs(yr, ks), sy), c))

def smem_app(+x: String, k1: List<&2, String>, +r: List<&2, String>) -> {smem(x, List.append(&2, String, k1, Con{x, r})) == True{} : Bool}:
  match k1:
    case Nil{}:
      %Equal.sym(Bool, String.eq(x, x), True{}, s_eq_self(x)) : {Bool.or(_, smem(x, r)) == True{} : Bool}
      {==}
    case Con{+k, +rest}:
      %Equal.sym(Bool, smem(x, List.append(&2, String, rest, Con{x, r})), True{}, smem_app(x, rest, r)) : {Bool.or(String.eq(x, k), _) == True{} : Bool}
      or_true_r(String.eq(x, k))

def sapp_assoc(xs: List<&2, String>, +ys: List<&2, String>, +zs: List<&2, String>)
  -> {List.append(&2, String, xs, List.append(&2, String, ys, zs)) == List.append(&2, String, List.append(&2, String, xs, ys), zs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %sapp_assoc(r, ys, zs) : {Con{x, List.append(&2, String, r, List.append(&2, String, ys, zs))} == Con{x, _} : List<&2, String>}
      {==}

def sapp_nil(xs: List<&2, String>) -> {xs == List.append(&2, String, xs, []) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %sapp_nil(rest) : {Con{x, rest} == Con{x, _} : List<&2, String>}
      {==}

def subs_app(a: List<&2, String>, +k1: List<&2, String>, +k2: List<&2, String>)
  -> {subs(a, List.append(&2, String, k1, List.append(&2, String, a, k2))) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +kk = List.append(&2, String, k1, Con{x, List.append(&2, String, r, k2)})
      +ih = {%Equal.sym(List<&2, String>, kk, List.append(&2, String, List.append(&2, String, k1, [x]), List.append(&2, String, r, k2)), sapp_assoc(k1, [x], List.append(&2, String, r, k2)))
               : {subs(r, _) == True{} : Bool};
             subs_app(r, List.append(&2, String, k1, [x]), k2) : {subs(r, kk) == True{} : Bool}}
      and_i(smem(x, kk), subs(r, kk), smem_app(x, k1, List.append(&2, String, r, k2)), ih)

def eqs3(ks: List<&2, String>, +x: List<&2, String>, +y: List<&2, String>, +z: List<&2, String>)
  -> {eqs(ks, Met.strs_merge(Met.strs_merge(x, y), z), Met.strs_merge(x, Met.strs_merge(y, z))) == True{} : Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      +A = Met.strs_merge(Met.strs_merge(x, y), z)
      +B = Met.strs_merge(x, Met.strs_merge(y, z))
      +hx = L.has_str(e, x)
      +hy = L.has_str(e, y)
      +hz = L.has_str(e, z)
      +same = {%hs_merge(Met.strs_merge(x, y), z, e) : {_ == L.has_str(e, B) : Bool};
               %hs_merge(x, y, e) : {Bool.or(_, hz) == L.has_str(e, B) : Bool};
               %hs_merge(x, Met.strs_merge(y, z), e) : {Bool.or(Bool.or(hx, hy), hz) == _ : Bool};
               %hs_merge(y, z, e) : {Bool.or(Bool.or(hx, hy), hz) == Bool.or(hx, _) : Bool};
               or_assoc(hx, hy, hz)
               : {L.has_str(e, A) == L.has_str(e, B) : Bool}}
      +b = {%same : {beq(L.has_str(e, A), _) == True{} : Bool}; beq_refl(L.has_str(e, A)) : {beq(L.has_str(e, A), L.has_str(e, B)) == True{} : Bool}}
      and_i(beq(L.has_str(e, A), L.has_str(e, B)), eqs(rest, A, B), b, eqs3(rest, x, y, z))

def strs_assoc(+x: List<&2, String>, +y: List<&2, String>, +z: List<&2, String>,
  +ax: {L.strs_ascending(x) == True{} : Bool}, +ay: {L.strs_ascending(y) == True{} : Bool}, +az: {L.strs_ascending(z) == True{} : Bool})
  -> {Met.strs_merge(Met.strs_merge(x, y), z) == Met.strs_merge(x, Met.strs_merge(y, z)) : List<&2, String>}:
  +A = Met.strs_merge(Met.strs_merge(x, y), z)
  +B = Met.strs_merge(x, Met.strs_merge(y, z))
  +ks = List.append(&2, String, A, B)
  +sb = {%Equal.sym(List<&2, String>, B, List.append(&2, String, B, []), sapp_nil(B)) : {subs(B, List.append(&2, String, A, _)) == True{} : Bool};
         subs_app(B, A, []) : {subs(B, ks) == True{} : Bool}}
  strs_ext(A, B, ks, as_merge(Met.strs_merge(x, y), z, as_merge(x, y, ax, ay), az), as_merge(x, Met.strs_merge(y, z), ax, as_merge(y, z, ay, az)),
    subs_app(A, [], B), sb, eqs3(ks, x, y, z))

# ---------------------------------------------------------------------
# Bigs are canonical: equal values, equal Bigs
# ---------------------------------------------------------------------

def tq_limb(+v: Nat, +h: Nat) -> {Nat.add(h, Nat.mul(10000n, v)) == tq(v, h, 9999n) : Nat}:
  %PNat.mul_comm(v, 10000n) : {Nat.add(h, _) == tq(v, h, 9999n) : Nat}
  PNat.add_comm(h, Nat.mul(v, 10000n))

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
          +hx = and_l(Nat.is_lt(x, 10000n), L.limbs_ok(xt), oka)
          +hy = and_l(Nat.is_lt(y, 10000n), L.limbs_ok(yt), okb)
          +et = {%tq_limb(vx, x) : {_ == tq(vy, y, 9999n) : Nat}; %tq_limb(vy, y) : {Nat.add(x, Nat.mul(10000n, vx)) == _ : Nat};
                 e : {tq(vx, x, 9999n) == tq(vy, y, 9999n) : Nat}}
          +ev = {%Equal.sym(Nat, vx, Nat.div(tq(vx, x, 9999n), 10000n), div_uq(vx, x, 9999n, hx)) : {_ == vy : Nat}; %Equal.sym(Nat, vy, Nat.div(tq(vy, y, 9999n), 10000n), div_uq(vy, y, 9999n, hy)) : {Nat.div(tq(vx, x, 9999n), 10000n) == _ : Nat};
                 %et : {Nat.div(tq(vx, x, 9999n), 10000n) == Nat.div(_, 10000n) : Nat}; {==} : {vx == vy : Nat}}
          +eh = {%Equal.sym(Nat, x, Nat.mod(tq(vx, x, 9999n), 10000n), mod_uq(vx, x, 9999n, hx)) : {_ == y : Nat}; %Equal.sym(Nat, y, Nat.mod(tq(vy, y, 9999n), 10000n), mod_uq(vy, y, 9999n, hy)) : {Nat.mod(tq(vx, x, 9999n), 10000n) == _ : Nat};
                 %et : {Nat.mod(tq(vx, x, 9999n), 10000n) == Nat.mod(_, 10000n) : Nat}; {==} : {x == y : Nat}}
          +et2 = big_inj(xt, yt, and_r(Nat.is_lt(x, 10000n), L.limbs_ok(xt), oka), and_r(Nat.is_lt(y, 10000n), L.limbs_ok(yt), okb),
                   PBig.lnz_tail(x, xt, lna), PBig.lnz_tail(y, yt, lnb), ev)
          %eh : {Con{x, xt} == Con{_, yt} : List<&2, Nat>}
          %et2 : {Con{x, xt} == Con{x, _} : List<&2, Nat>}
          {==}

def big_eq(a: Big.Big, b: Big.Big, +oka: {L.big_ok(a) == True{} : Bool}, +okb: {L.big_ok(b) == True{} : Bool}, +e: {L.big_val(a) == L.big_val(b) : Nat})
  -> {a == b : Big.Big}:
  match a:
    case Big.Big{+la}:
      match b:
        case Big.Big{+lb}:
          %big_inj(la, lb, and_l(L.limbs_ok(la), L.last_nonzero(la), oka), and_l(L.limbs_ok(lb), L.last_nonzero(lb), okb),
              and_r(L.limbs_ok(la), L.last_nonzero(la), oka), and_r(L.limbs_ok(lb), L.last_nonzero(lb), okb), e)
            : {Big.Big{la} == Big.Big{_} : Big.Big}
          {==}

def big_assoc(+a: Big.Big, +b: Big.Big, +c: Big.Big, +oka: {L.big_ok(a) == True{} : Bool}, +okb: {L.big_ok(b) == True{} : Bool}, +okc: {L.big_ok(c) == True{} : Bool})
  -> {Big.add(Big.add(a, b), c) == Big.add(a, Big.add(b, c)) : Big.Big}:
  +ab = Big.add(a, b)
  +bc = Big.add(b, c)
  +okab = big_add_ok(a, b, oka, okb)
  +okbc = big_add_ok(b, c, okb, okc)
  +va = L.big_val(a)
  +vb = L.big_val(b)
  +vc = L.big_val(c)
  big_eq(Big.add(ab, c), Big.add(a, bc), big_add_ok(ab, c, okab, okc), big_add_ok(a, bc, oka, okbc),
    {%big_add_val(ab, c, okab, okc) : {_ == L.big_val(Big.add(a, bc)) : Nat};
     %big_add_val(a, b, oka, okb) : {Nat.add(_, vc) == L.big_val(Big.add(a, bc)) : Nat};
     %big_add_val(a, bc, oka, okbc) : {Nat.add(Nat.add(va, vb), vc) == _ : Nat};
     %big_add_val(b, c, okb, okc) : {Nat.add(Nat.add(va, vb), vc) == Nat.add(va, _) : Nat};
     Equal.sym(Nat, Nat.add(va, Nat.add(vb, vc)), Nat.add(Nat.add(va, vb), vc), PNat.add_assoc(va, vb, vc))
     : {L.big_val(Big.add(ab, c)) == L.big_val(Big.add(a, bc)) : Nat}})

def big_zero_r(+a: Big.Big, +oka: {L.big_ok(a) == True{} : Bool}) -> {Big.add(a, Big.of(0n)) == a : Big.Big}:
  big_eq(Big.add(a, Big.of(0n)), a, big_add_ok(a, Big.of(0n), oka, big_of_ok(0n)), oka,
    {%big_add_val(a, Big.of(0n), oka, big_of_ok(0n)) : {_ == L.big_val(a) : Nat};
     Equal.sym(Nat, L.big_val(a), Nat.add(L.big_val(a), 0n), PNat.add_zero(L.big_val(a)))
     : {L.big_val(Big.add(a, Big.of(0n))) == L.big_val(a) : Nat}})

def big_zero_l(+a: Big.Big, +oka: {L.big_ok(a) == True{} : Bool}) -> {Big.add(Big.of(0n), a) == a : Big.Big}:
  big_eq(Big.add(Big.of(0n), a), a, big_add_ok(Big.of(0n), a, big_of_ok(0n), oka), oka,
    {%big_add_val(Big.of(0n), a, big_of_ok(0n), oka) : {_ == L.big_val(a) : Nat};
     {==} : {L.big_val(Big.add(Big.of(0n), a)) == L.big_val(a) : Nat}})

# ---------------------------------------------------------------------
# the extremes: mins and maxes of canonical times
# ---------------------------------------------------------------------

def min_assoc(a: Nat, b: Nat, c: Nat) -> {Nat.min(Nat.min(a, b), c) == Nat.min(a, Nat.min(b, c)) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          match c:
            case 0n:
              {==}
            case 1n+cp:
              {==}
    case 1n+ap:
      match b:
        case 0n:
          match c:
            case 0n:
              {==}
            case 1n+cp:
              {==}
        case 1n+bp:
          match c:
            case 0n:
              {==}
            case 1n+cp:
              succ_eq(Nat.min(Nat.min(ap, bp), cp), Nat.min(ap, Nat.min(bp, cp)), min_assoc(ap, bp, cp))

def max_assoc(a: Nat, b: Nat, c: Nat) -> {Nat.max(Nat.max(a, b), c) == Nat.max(a, Nat.max(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          match c:
            case 0n:
              {==}
            case 1n+cp:
              succ_eq(Nat.max(Nat.max(ap, bp), cp), Nat.max(ap, Nat.max(bp, cp)), max_assoc(ap, bp, cp))

# the components of a merge of extremes
def cx_lmin(x: Met.Ext, y: Met.Ext, +hx: {is_ext(x) == True{} : Bool}, +hy: {is_ext(y) == True{} : Bool})
  -> {Nat.min(x_lmin(x), x_lmin(y)) == x_lmin(Met.ext_merge(x, y)) : Nat}:
  match x:
    case Met.NoExt{}:
      Empty.absurd({Nat.min(0n, x_lmin(y)) == x_lmin(y) : Nat}, no_ft(hx))
    case Met.Ext{+a1, b1, es1, en1, ls1, ln1, xs1, xn1}:
      match y:
        case Met.NoExt{}:
          Empty.absurd({Nat.min(a1, 0n) == a1 : Nat}, no_ft(hy))
        case Met.Ext{+a2, b2, es2, en2, ls2, ln2, xs2, xn2}:
          nmin_min(a1, a2)

def cx_lmax(x: Met.Ext, y: Met.Ext, +hx: {is_ext(x) == True{} : Bool}, +hy: {is_ext(y) == True{} : Bool})
  -> {Nat.max(x_lmax(x), x_lmax(y)) == x_lmax(Met.ext_merge(x, y)) : Nat}:
  match x:
    case Met.NoExt{}:
      Empty.absurd({Nat.max(0n, x_lmax(y)) == x_lmax(y) : Nat}, no_ft(hx))
    case Met.Ext{a1, +b1, es1, en1, ls1, ln1, xs1, xn1}:
      match y:
        case Met.NoExt{}:
          Empty.absurd({Nat.max(b1, 0n) == b1 : Nat}, no_ft(hy))
        case Met.Ext{a2, +b2, es2, en2, ls2, ln2, xs2, xn2}:
          nmax_max(b1, b2)

def cx_te(x: Met.Ext, y: Met.Ext, +hx: {is_ext(x) == True{} : Bool}, +hy: {is_ext(y) == True{} : Bool},
  +okx1: {okx(x) == True{} : Bool}, +oky: {okx(y) == True{} : Bool})
  -> {Nat.min(tE(x), tE(y)) == tE(Met.ext_merge(x, y)) : Nat}:
  match x:
    case Met.NoExt{}:
      Empty.absurd({Nat.min(tE(Met.NoExt{}), tE(y)) == tE(y) : Nat}, no_ft(hx))
    case Met.Ext{a1, b1, +es1, +en1, ls1, +ln1, xs1, +xn1}:
      match y:
        case Met.NoExt{}:
          Empty.absurd({Nat.min(tq(es1, en1, B9()), tE(Met.NoExt{})) == tq(es1, en1, B9()) : Nat}, no_ft(hy))
        case Met.Ext{a2, b2, +es2, +en2, ls2, +ln2, xs2, +xn2}:
          +t1 = tq(es1, en1, B9())
          +t2 = tq(es2, en2, B9())
          +nl = Met.no_later(es1, en1, es2, en2)
          %pk(nl, es1, en1, es2, en2, B9()) : {Nat.min(t1, t2) == _ : Nat}
          %nl_same(Nat.cmp(es1, es2), es1, en1, es2, en2, B9(), {==},
              ok1(Nat.is_lt(en1, L.sec()), Nat.is_lt(ln1, L.sec()), Nat.is_lt(xn1, L.sec()), okx1),
              ok1(Nat.is_lt(en2, L.sec()), Nat.is_lt(ln2, L.sec()), Nat.is_lt(xn2, L.sec()), oky))
            : {Nat.min(t1, t2) == Met.pick(Nat, _, t1, t2) : Nat}
          nmin_min(t1, t2)

def cx_tl(x: Met.Ext, y: Met.Ext, +hx: {is_ext(x) == True{} : Bool}, +hy: {is_ext(y) == True{} : Bool},
  +okx1: {okx(x) == True{} : Bool}, +oky: {okx(y) == True{} : Bool})
  -> {Nat.max(tL(x), tL(y)) == tL(Met.ext_merge(x, y)) : Nat}:
  match x:
    case Met.NoExt{}:
      Empty.absurd({Nat.max(tL(Met.NoExt{}), tL(y)) == tL(y) : Nat}, no_ft(hx))
    case Met.Ext{a1, b1, es1, +en1, +ls1, +ln1, xs1, +xn1}:
      match y:
        case Met.NoExt{}:
          Empty.absurd({Nat.max(tq(ls1, ln1, B9()), tL(Met.NoExt{})) == tq(ls1, ln1, B9()) : Nat}, no_ft(hy))
        case Met.Ext{a2, b2, es2, +en2, +ls2, +ln2, xs2, +xn2}:
          +t1 = tq(ls1, ln1, B9())
          +t2 = tq(ls2, ln2, B9())
          +nl = Met.no_later(ls1, ln1, ls2, ln2)
          %pk(nl, ls2, ln2, ls1, ln1, B9()) : {Nat.max(t1, t2) == _ : Nat}
          %nl_same(Nat.cmp(ls1, ls2), ls1, ln1, ls2, ln2, B9(), {==},
              ok2(Nat.is_lt(en1, L.sec()), Nat.is_lt(ln1, L.sec()), Nat.is_lt(xn1, L.sec()), okx1),
              ok2(Nat.is_lt(en2, L.sec()), Nat.is_lt(ln2, L.sec()), Nat.is_lt(xn2, L.sec()), oky))
            : {Nat.max(t1, t2) == Met.pick(Nat, _, t2, t1) : Nat}
          nmax_max(t1, t2)

def cx_tn(x: Met.Ext, y: Met.Ext, +hx: {is_ext(x) == True{} : Bool}, +hy: {is_ext(y) == True{} : Bool},
  +okx1: {okx(x) == True{} : Bool}, +oky: {okx(y) == True{} : Bool})
  -> {Nat.max(tN(x), tN(y)) == tN(Met.ext_merge(x, y)) : Nat}:
  match x:
    case Met.NoExt{}:
      Empty.absurd({Nat.max(tN(Met.NoExt{}), tN(y)) == tN(y) : Nat}, no_ft(hx))
    case Met.Ext{a1, b1, es1, +en1, ls1, +ln1, +xs1, +xn1}:
      match y:
        case Met.NoExt{}:
          Empty.absurd({Nat.max(tq(xs1, xn1, B9()), tN(Met.NoExt{})) == tq(xs1, xn1, B9()) : Nat}, no_ft(hy))
        case Met.Ext{a2, b2, es2, +en2, ls2, +ln2, +xs2, +xn2}:
          +t1 = tq(xs1, xn1, B9())
          +t2 = tq(xs2, xn2, B9())
          +nl = Met.no_later(xs1, xn1, xs2, xn2)
          %pk(nl, xs2, xn2, xs1, xn1, B9()) : {Nat.max(t1, t2) == _ : Nat}
          %nl_same(Nat.cmp(xs1, xs2), xs1, xn1, xs2, xn2, B9(), {==},
              ok3(Nat.is_lt(en1, L.sec()), Nat.is_lt(ln1, L.sec()), Nat.is_lt(xn1, L.sec()), okx1),
              ok3(Nat.is_lt(en2, L.sec()), Nat.is_lt(ln2, L.sec()), Nat.is_lt(xn2, L.sec()), oky))
            : {Nat.max(t1, t2) == Met.pick(Nat, _, t2, t1) : Nat}
          nmax_max(t1, t2)

def okx_merge(x: Met.Ext, y: Met.Ext, +okx1: {okx(x) == True{} : Bool}, +oky: {okx(y) == True{} : Bool}) -> {okx(Met.ext_merge(x, y)) == True{} : Bool}:
  match x:
    case Met.NoExt{}:
      oky
    case Met.Ext{a1, b1, +es1, +en1, +ls1, +ln1, +xs1, +xn1}:
      match y:
        case Met.NoExt{}:
          okx1
        case Met.Ext{a2, b2, +es2, +en2, +ls2, +ln2, +xs2, +xn2}:
          +c1 = Nat.is_lt(en1, L.sec())
          +c2 = Nat.is_lt(ln1, L.sec())
          +c3 = Nat.is_lt(xn1, L.sec())
          +d1 = Nat.is_lt(en2, L.sec())
          +d2 = Nat.is_lt(ln2, L.sec())
          +d3 = Nat.is_lt(xn2, L.sec())
          ok_mk(Nat.is_lt(Met.pick(Nat, Met.no_later(es1, en1, es2, en2), en1, en2), L.sec()),
            Nat.is_lt(Met.pick(Nat, Met.no_later(ls1, ln1, ls2, ln2), ln2, ln1), L.sec()),
            Nat.is_lt(Met.pick(Nat, Met.no_later(xs1, xn1, xs2, xn2), xn2, xn1), L.sec()),
            pick_lt(Met.no_later(es1, en1, es2, en2), en1, en2, L.sec(), ok1(c1, c2, c3, okx1), ok1(d1, d2, d3, oky)),
            pick_lt(Met.no_later(ls1, ln1, ls2, ln2), ln2, ln1, L.sec(), ok2(d1, d2, d3, oky), ok2(c1, c2, c3, okx1)),
            pick_lt(Met.no_later(xs1, xn1, xs2, xn2), xn2, xn1, L.sec(), ok3(d1, d2, d3, oky), ok3(c1, c2, c3, okx1)))

def pe_s(+s1: Nat, +n1: Nat, +s2: Nat, +n2: Nat, +h1: {Nat.is_lt(n1, L.sec()) == True{} : Bool}, +h2: {Nat.is_lt(n2, L.sec()) == True{} : Bool},
  +e: {tq(s1, n1, B9()) == tq(s2, n2, B9()) : Nat}) -> {s1 == s2 : Nat}:
  %Equal.sym(Nat, s1, Nat.div(tq(s1, n1, B9()), L.sec()), div_uq(s1, n1, B9(), h1)) : {_ == s2 : Nat}
  %Equal.sym(Nat, s2, Nat.div(tq(s2, n2, B9()), L.sec()), div_uq(s2, n2, B9(), h2)) : {Nat.div(tq(s1, n1, B9()), L.sec()) == _ : Nat}
  %e : {Nat.div(tq(s1, n1, B9()), L.sec()) == Nat.div(_, L.sec()) : Nat}
  {==}

def pe_n(+s1: Nat, +n1: Nat, +s2: Nat, +n2: Nat, +h1: {Nat.is_lt(n1, L.sec()) == True{} : Bool}, +h2: {Nat.is_lt(n2, L.sec()) == True{} : Bool},
  +e: {tq(s1, n1, B9()) == tq(s2, n2, B9()) : Nat}) -> {n1 == n2 : Nat}:
  %Equal.sym(Nat, n1, Nat.mod(tq(s1, n1, B9()), L.sec()), mod_uq(s1, n1, B9(), h1)) : {_ == n2 : Nat}
  %Equal.sym(Nat, n2, Nat.mod(tq(s2, n2, B9()), L.sec()), mod_uq(s2, n2, B9(), h2)) : {Nat.mod(tq(s1, n1, B9()), L.sec()) == _ : Nat}
  %e : {Nat.mod(tq(s1, n1, B9()), L.sec()) == Nat.mod(_, L.sec()) : Nat}
  {==}

# extremes with the same components are the same
def ext_ext(x: Met.Ext, y: Met.Ext, +okx1: {okx(x) == True{} : Bool}, +oky: {okx(y) == True{} : Bool},
  +hx: {is_ext(x) == True{} : Bool}, +hy: {is_ext(y) == True{} : Bool},
  +e1: {x_lmin(x) == x_lmin(y) : Nat}, +e2: {x_lmax(x) == x_lmax(y) : Nat},
  +e3: {tE(x) == tE(y) : Nat}, +e4: {tL(x) == tL(y) : Nat}, +e5: {tN(x) == tN(y) : Nat})
  -> {x == y : Met.Ext}:
  match x:
    case Met.NoExt{}:
      Empty.absurd({Met.NoExt{} == y : Met.Ext}, no_ft(hx))
    case Met.Ext{+a1, +b1, +es1, +en1, +ls1, +ln1, +xs1, +xn1}:
      match y:
        case Met.NoExt{}:
          Empty.absurd({Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1} == Met.NoExt{} : Met.Ext}, no_ft(hy))
        case Met.Ext{+a2, +b2, +es2, +en2, +ls2, +ln2, +xs2, +xn2}:
          +c1 = Nat.is_lt(en1, L.sec())
          +c2 = Nat.is_lt(ln1, L.sec())
          +c3 = Nat.is_lt(xn1, L.sec())
          +d1 = Nat.is_lt(en2, L.sec())
          +d2 = Nat.is_lt(ln2, L.sec())
          +d3 = Nat.is_lt(xn2, L.sec())
          +X = {Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1} : Met.Ext}
          %e1 : {X == Met.Ext{_, b2, es2, en2, ls2, ln2, xs2, xn2} : Met.Ext}
          %e2 : {X == Met.Ext{a1, _, es2, en2, ls2, ln2, xs2, xn2} : Met.Ext}
          %pe_s(es1, en1, es2, en2, ok1(c1, c2, c3, okx1), ok1(d1, d2, d3, oky), e3) : {X == Met.Ext{a1, b1, _, en2, ls2, ln2, xs2, xn2} : Met.Ext}
          %pe_n(es1, en1, es2, en2, ok1(c1, c2, c3, okx1), ok1(d1, d2, d3, oky), e3) : {X == Met.Ext{a1, b1, es1, _, ls2, ln2, xs2, xn2} : Met.Ext}
          %pe_s(ls1, ln1, ls2, ln2, ok2(c1, c2, c3, okx1), ok2(d1, d2, d3, oky), e4) : {X == Met.Ext{a1, b1, es1, en1, _, ln2, xs2, xn2} : Met.Ext}
          %pe_n(ls1, ln1, ls2, ln2, ok2(c1, c2, c3, okx1), ok2(d1, d2, d3, oky), e4) : {X == Met.Ext{a1, b1, es1, en1, ls1, _, xs2, xn2} : Met.Ext}
          %pe_s(xs1, xn1, xs2, xn2, ok3(c1, c2, c3, okx1), ok3(d1, d2, d3, oky), e5) : {X == Met.Ext{a1, b1, es1, en1, ls1, ln1, _, xn2} : Met.Ext}
          %pe_n(xs1, xn1, xs2, xn2, ok3(c1, c2, c3, okx1), ok3(d1, d2, d3, oky), e5) : {X == Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, _} : Met.Ext}
          {==}

def ext_assoc3(+x: Met.Ext, +y: Met.Ext, +z: Met.Ext, +hx: {is_ext(x) == True{} : Bool}, +hy: {is_ext(y) == True{} : Bool}, +hz: {is_ext(z) == True{} : Bool},
  +okx1: {okx(x) == True{} : Bool}, +oky: {okx(y) == True{} : Bool}, +okz: {okx(z) == True{} : Bool})
  -> {Met.ext_merge(Met.ext_merge(x, y), z) == Met.ext_merge(x, Met.ext_merge(y, z)) : Met.Ext}:
  +xy = Met.ext_merge(x, y)
  +yz = Met.ext_merge(y, z)
  +hxy = x_merge_l(x, y, hx)
  +hyz = x_merge_l(y, z, hy)
  +oxy = okx_merge(x, y, okx1, oky)
  +oyz = okx_merge(y, z, oky, okz)
  +L1 = Met.ext_merge(xy, z)
  +R1 = Met.ext_merge(x, yz)
  ext_ext(L1, R1, okx_merge(xy, z, oxy, okz), okx_merge(x, yz, okx1, oyz), x_merge_l(xy, z, hxy), x_merge_l(x, yz, hx),
    {%cx_lmin(xy, z, hxy, hz) : {_ == x_lmin(R1) : Nat}; %cx_lmin(x, y, hx, hy) : {Nat.min(_, x_lmin(z)) == x_lmin(R1) : Nat};
     %cx_lmin(x, yz, hx, hyz) : {Nat.min(Nat.min(x_lmin(x), x_lmin(y)), x_lmin(z)) == _ : Nat};
     %cx_lmin(y, z, hy, hz) : {Nat.min(Nat.min(x_lmin(x), x_lmin(y)), x_lmin(z)) == Nat.min(x_lmin(x), _) : Nat};
     min_assoc(x_lmin(x), x_lmin(y), x_lmin(z)) : {x_lmin(L1) == x_lmin(R1) : Nat}},
    {%cx_lmax(xy, z, hxy, hz) : {_ == x_lmax(R1) : Nat}; %cx_lmax(x, y, hx, hy) : {Nat.max(_, x_lmax(z)) == x_lmax(R1) : Nat};
     %cx_lmax(x, yz, hx, hyz) : {Nat.max(Nat.max(x_lmax(x), x_lmax(y)), x_lmax(z)) == _ : Nat};
     %cx_lmax(y, z, hy, hz) : {Nat.max(Nat.max(x_lmax(x), x_lmax(y)), x_lmax(z)) == Nat.max(x_lmax(x), _) : Nat};
     max_assoc(x_lmax(x), x_lmax(y), x_lmax(z)) : {x_lmax(L1) == x_lmax(R1) : Nat}},
    {%cx_te(xy, z, hxy, hz, oxy, okz) : {_ == tE(R1) : Nat}; %cx_te(x, y, hx, hy, okx1, oky) : {Nat.min(_, tE(z)) == tE(R1) : Nat};
     %cx_te(x, yz, hx, hyz, okx1, oyz) : {Nat.min(Nat.min(tE(x), tE(y)), tE(z)) == _ : Nat};
     %cx_te(y, z, hy, hz, oky, okz) : {Nat.min(Nat.min(tE(x), tE(y)), tE(z)) == Nat.min(tE(x), _) : Nat};
     min_assoc(tE(x), tE(y), tE(z)) : {tE(L1) == tE(R1) : Nat}},
    {%cx_tl(xy, z, hxy, hz, oxy, okz) : {_ == tL(R1) : Nat}; %cx_tl(x, y, hx, hy, okx1, oky) : {Nat.max(_, tL(z)) == tL(R1) : Nat};
     %cx_tl(x, yz, hx, hyz, okx1, oyz) : {Nat.max(Nat.max(tL(x), tL(y)), tL(z)) == _ : Nat};
     %cx_tl(y, z, hy, hz, oky, okz) : {Nat.max(Nat.max(tL(x), tL(y)), tL(z)) == Nat.max(tL(x), _) : Nat};
     max_assoc(tL(x), tL(y), tL(z)) : {tL(L1) == tL(R1) : Nat}},
    {%cx_tn(xy, z, hxy, hz, oxy, okz) : {_ == tN(R1) : Nat}; %cx_tn(x, y, hx, hy, okx1, oky) : {Nat.max(_, tN(z)) == tN(R1) : Nat};
     %cx_tn(x, yz, hx, hyz, okx1, oyz) : {Nat.max(Nat.max(tN(x), tN(y)), tN(z)) == _ : Nat};
     %cx_tn(y, z, hy, hz, oky, okz) : {Nat.max(Nat.max(tN(x), tN(y)), tN(z)) == Nat.max(tN(x), _) : Nat};
     max_assoc(tN(x), tN(y), tN(z)) : {tN(L1) == tN(R1) : Nat}})

def ext_zero_r(x: Met.Ext) -> {Met.ext_merge(x, Met.NoExt{}) == x : Met.Ext}:
  match x:
    case Met.NoExt{}:
      {==}
    case Met.Ext{a, b, c, d, e, f, g, h}:
      {==}

def ext_assoc(x: Met.Ext, y: Met.Ext, z: Met.Ext, +okx1: {okx(x) == True{} : Bool}, +oky: {okx(y) == True{} : Bool}, +okz: {okx(z) == True{} : Bool})
  -> {Met.ext_merge(Met.ext_merge(x, y), z) == Met.ext_merge(x, Met.ext_merge(y, z)) : Met.Ext}:
  match x:
    case Met.NoExt{}:
      {==}
    case Met.Ext{+a1, +b1, +es1, +en1, +ls1, +ln1, +xs1, +xn1}:
      match y:
        case Met.NoExt{}:
          {==}
        case Met.Ext{+a2, +b2, +es2, +en2, +ls2, +ln2, +xs2, +xn2}:
          match z:
            case Met.NoExt{}:
              +X = {Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1} : Met.Ext}
              +Y = {Met.Ext{a2, b2, es2, en2, ls2, ln2, xs2, xn2} : Met.Ext}
              %ext_zero_r(Met.ext_merge(X, Y)) : {_ == Met.ext_merge(X, Y) : Met.Ext}
              {==}
            case Met.Ext{+a3, +b3, +es3, +en3, +ls3, +ln3, +xs3, +xn3}:
              ext_assoc3(Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}, Met.Ext{a2, b2, es2, en2, ls2, ln2, xs2, xn2}, Met.Ext{a3, b3, es3, en3, ls3, ln3, xs3, xn3},
                {==}, {==}, {==}, okx1, oky, okz)

# ---------------------------------------------------------------------
# accumulators: well formed, and their view without the rope
# ---------------------------------------------------------------------

def wf(+a: Met.Acc) -> Bool:
  Bool.and(L.codes_ascending(a_cs(a)), Bool.and(L.strs_ascending(a_es(a)), Bool.and(L.big_ok(a_lat(a)),
    Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a)))))))

def w1(+a: Met.Acc, +h: {wf(a) == True{} : Bool}) -> {L.codes_ascending(a_cs(a)) == True{} : Bool}:
  and_l(L.codes_ascending(a_cs(a)), Bool.and(L.strs_ascending(a_es(a)), Bool.and(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a)))))), h)

def wr1(+a: Met.Acc, +h: {wf(a) == True{} : Bool})
  -> {Bool.and(L.strs_ascending(a_es(a)), Bool.and(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a)))))) == True{} : Bool}:
  and_r(L.codes_ascending(a_cs(a)), Bool.and(L.strs_ascending(a_es(a)), Bool.and(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a)))))), h)

def w2(+a: Met.Acc, +h: {wf(a) == True{} : Bool}) -> {L.strs_ascending(a_es(a)) == True{} : Bool}:
  and_l(L.strs_ascending(a_es(a)), Bool.and(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))))), wr1(a, h))

def wr2(+a: Met.Acc, +h: {wf(a) == True{} : Bool})
  -> {Bool.and(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))))) == True{} : Bool}:
  and_r(L.strs_ascending(a_es(a)), Bool.and(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))))), wr1(a, h))

def w3(+a: Met.Acc, +h: {wf(a) == True{} : Bool}) -> {L.big_ok(a_lat(a)) == True{} : Bool}:
  and_l(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a)))), wr2(a, h))

def wr3(+a: Met.Acc, +h: {wf(a) == True{} : Bool}) -> {Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a)))) == True{} : Bool}:
  and_r(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a)))), wr2(a, h))

def w4(+a: Met.Acc, +h: {wf(a) == True{} : Bool}) -> {L.big_ok(a_bin(a)) == True{} : Bool}:
  and_l(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))), wr3(a, h))

def w5(+a: Met.Acc, +h: {wf(a) == True{} : Bool}) -> {L.big_ok(a_bout(a)) == True{} : Bool}:
  and_l(L.big_ok(a_bout(a)), okx(a_x(a)), and_r(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))), wr3(a, h)))

def w6(+a: Met.Acc, +h: {wf(a) == True{} : Bool}) -> {okx(a_x(a)) == True{} : Bool}:
  and_r(L.big_ok(a_bout(a)), okx(a_x(a)), and_r(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))), wr3(a, h)))

def wf_mk(+a: Met.Acc, +h1: {L.codes_ascending(a_cs(a)) == True{} : Bool}, +h2: {L.strs_ascending(a_es(a)) == True{} : Bool},
  +h3: {L.big_ok(a_lat(a)) == True{} : Bool}, +h4: {L.big_ok(a_bin(a)) == True{} : Bool}, +h5: {L.big_ok(a_bout(a)) == True{} : Bool},
  +h6: {okx(a_x(a)) == True{} : Bool}) -> {wf(a) == True{} : Bool}:
  %Equal.sym(Bool, L.codes_ascending(a_cs(a)), True{}, h1) : {Bool.and(_, Bool.and(L.strs_ascending(a_es(a)), Bool.and(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))))))) == True{} : Bool}
  %Equal.sym(Bool, L.strs_ascending(a_es(a)), True{}, h2) : {Bool.and(True{}, Bool.and(_, Bool.and(L.big_ok(a_lat(a)), Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))))))) == True{} : Bool}
  %Equal.sym(Bool, L.big_ok(a_lat(a)), True{}, h3) : {Bool.and(True{}, Bool.and(True{}, Bool.and(_, Bool.and(L.big_ok(a_bin(a)), Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))))))) == True{} : Bool}
  %Equal.sym(Bool, L.big_ok(a_bin(a)), True{}, h4) : {Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(_, Bool.and(L.big_ok(a_bout(a)), okx(a_x(a))))))) == True{} : Bool}
  %Equal.sym(Bool, L.big_ok(a_bout(a)), True{}, h5) : {Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(True{}, Bool.and(_, okx(a_x(a))))))) == True{} : Bool}
  h6

def wf_merge(+a: Met.Acc, +b: Met.Acc, +wa: {wf(a) == True{} : Bool}, +wb: {wf(b) == True{} : Bool}) -> {wf(Met.merge(a, b)) == True{} : Bool}:
  +m = Met.merge(a, b)
  wf_mk(m,
    {%m_cs(a, b) : {L.codes_ascending(_) == True{} : Bool}; asc_merge(a_cs(a), a_cs(b), w1(a, wa), w1(b, wb)) : {L.codes_ascending(a_cs(m)) == True{} : Bool}},
    {%m_es(a, b) : {L.strs_ascending(_) == True{} : Bool}; as_merge(a_es(a), a_es(b), w2(a, wa), w2(b, wb)) : {L.strs_ascending(a_es(m)) == True{} : Bool}},
    {%m_lat(a, b) : {L.big_ok(_) == True{} : Bool}; big_add_ok(a_lat(a), a_lat(b), w3(a, wa), w3(b, wb)) : {L.big_ok(a_lat(m)) == True{} : Bool}},
    {%m_bin(a, b) : {L.big_ok(_) == True{} : Bool}; big_add_ok(a_bin(a), a_bin(b), w4(a, wa), w4(b, wb)) : {L.big_ok(a_bin(m)) == True{} : Bool}},
    {%m_bout(a, b) : {L.big_ok(_) == True{} : Bool}; big_add_ok(a_bout(a), a_bout(b), w5(a, wa), w5(b, wb)) : {L.big_ok(a_bout(m)) == True{} : Bool}},
    {%m_x(a, b) : {okx(_) == True{} : Bool}; okx_merge(a_x(a), a_x(b), w6(a, wa), w6(b, wb)) : {okx(a_x(m)) == True{} : Bool}})

def wf_oh(h: Hit.Hit) -> {wf(Met.of_hit(h)) == True{} : Bool}:
  match h:
    case Hit.Hit{a, q, c, t, +l, +bo, +bi, +err, b, m, u, hs}:
      match t:
        case Civil.Time{+s0, +ns0, off}:
          +ns = Nat.mod(ns0, L.sec())
          +en2 = Nat.add(ns, Nat.mod(l, L.sec()))
          +o = Met.of_hit(Hit.Hit{a, q, c, Civil.Time{s0, ns0, off}, l, bo, bi, err, b, m, u, hs})
          wf_mk(o, {==}, pk_asc(String.is_empty(err), err), big_of_ok(l), big_of_ok(bi), big_of_ok(bo),
            ok_mk(Nat.is_lt(ns, L.sec()), Nat.is_lt(ns, L.sec()), Nat.is_lt(Nat.mod(en2, L.sec()), L.sec()),
              PNat.mod_lt(ns0, B9()), PNat.mod_lt(ns0, B9()), PNat.mod_lt(en2, B9())))

def wf_empty(+bs: List<&2, Nat>) -> {wf(Met.empty(bs)) == True{} : Bool}:
  {==}

def wf_fold(ys: List<&2, Hit.Hit>, +a: Met.Acc, +wa: {wf(a) == True{} : Bool}) -> {wf(L.acc_all(ys, a)) == True{} : Bool}:
  match ys:
    case Nil{}:
      wa
    case Con{+y, +rest}:
      wf_fold(rest, Met.add(a, y), wf_merge(a, Met.of_hit(y), wa, wf_oh(y)))

def strip(+a: Met.Acc) -> Met.Acc:
  Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} = a
  Met.Acc{[], n, ok, cs, es, l, i, o, x, Met.LNone{}}

def s_merge(a: Met.Acc, b: Met.Acc) -> {strip(Met.merge(a, b)) == strip(Met.merge(strip(a), strip(b))) : Met.Acc}:
  match a:
    case Met.Acc{bs, n, ok, cs, es, l, i, o, x, t}:
      match b:
        case Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}:
          {==}

def cong_l(+a: Met.Acc, +a2: Met.Acc, +b: Met.Acc, +e: {strip(a) == strip(a2) : Met.Acc}) -> {strip(Met.merge(a, b)) == strip(Met.merge(a2, b)) : Met.Acc}:
  Equal.trans(Met.Acc, strip(Met.merge(a, b)), strip(Met.merge(strip(a), strip(b))), strip(Met.merge(a2, b)), s_merge(a, b),
    Equal.trans(Met.Acc, strip(Met.merge(strip(a), strip(b))), strip(Met.merge(strip(a2), strip(b))), strip(Met.merge(a2, b)),
      Equal.cong(Met.Acc, Met.Acc, u => strip(Met.merge(u, strip(b))), strip(a), strip(a2), e),
      Equal.sym(Met.Acc, strip(Met.merge(a2, b)), strip(Met.merge(strip(a2), strip(b))), s_merge(a2, b))))

def cong_r(+a: Met.Acc, +b: Met.Acc, +b2: Met.Acc, +e: {strip(b) == strip(b2) : Met.Acc}) -> {strip(Met.merge(a, b)) == strip(Met.merge(a, b2)) : Met.Acc}:
  Equal.trans(Met.Acc, strip(Met.merge(a, b)), strip(Met.merge(strip(a), strip(b))), strip(Met.merge(a, b2)), s_merge(a, b),
    Equal.trans(Met.Acc, strip(Met.merge(strip(a), strip(b))), strip(Met.merge(strip(a), strip(b2))), strip(Met.merge(a, b2)),
      Equal.cong(Met.Acc, Met.Acc, u => strip(Met.merge(strip(a), u)), strip(b), strip(b2), e),
      Equal.sym(Met.Acc, strip(Met.merge(a, b2)), strip(Met.merge(strip(a), strip(b2))), s_merge(a, b2))))

def assoc_s(a: Met.Acc, b: Met.Acc, c: Met.Acc, +wa: {wf(a) == True{} : Bool}, +wb: {wf(b) == True{} : Bool}, +wc: {wf(c) == True{} : Bool})
  -> {strip(Met.merge(Met.merge(a, b), c)) == strip(Met.merge(a, Met.merge(b, c))) : Met.Acc}:
  match a:
    case Met.Acc{bs1, +n1, +ok1, +cs1, +es1, +l1, +i1, +o1, +x1, t1}:
      match b:
        case Met.Acc{bs2, +n2, +ok2, +cs2, +es2, +l2, +i2, +o2, +x2, t2}:
          match c:
            case Met.Acc{bs3, +n3, +ok3, +cs3, +es3, +l3, +i3, +o3, +x3, t3}:
              +A = {Met.Acc{bs1, n1, ok1, cs1, es1, l1, i1, o1, x1, t1} : Met.Acc}
              +B = {Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2} : Met.Acc}
              +C = {Met.Acc{bs3, n3, ok3, cs3, es3, l3, i3, o3, x3, t3} : Met.Acc}
              +LHS = {Met.Acc{[], Nat.add(Nat.add(n1, n2), n3), Nat.add(Nat.add(ok1, ok2), ok3), Met.codes_merge(Met.codes_merge(cs1, cs2), cs3),
                        Met.strs_merge(Met.strs_merge(es1, es2), es3), Big.add(Big.add(l1, l2), l3), Big.add(Big.add(i1, i2), i3),
                        Big.add(Big.add(o1, o2), o3), Met.ext_merge(Met.ext_merge(x1, x2), x3), Met.LNone{}} : Met.Acc}
              %Equal.sym(Nat, Nat.add(n1, Nat.add(n2, n3)), Nat.add(Nat.add(n1, n2), n3), PNat.add_assoc(n1, n2, n3)) : {LHS == Met.Acc{[], _, Nat.add(ok1, Nat.add(ok2, ok3)), Met.codes_merge(cs1, Met.codes_merge(cs2, cs3)),
                  Met.strs_merge(es1, Met.strs_merge(es2, es3)), Big.add(l1, Big.add(l2, l3)), Big.add(i1, Big.add(i2, i3)), Big.add(o1, Big.add(o2, o3)),
                  Met.ext_merge(x1, Met.ext_merge(x2, x3)), Met.LNone{}} : Met.Acc}
              %Equal.sym(Nat, Nat.add(ok1, Nat.add(ok2, ok3)), Nat.add(Nat.add(ok1, ok2), ok3), PNat.add_assoc(ok1, ok2, ok3)) : {LHS == Met.Acc{[], Nat.add(Nat.add(n1, n2), n3), _, Met.codes_merge(cs1, Met.codes_merge(cs2, cs3)),
                  Met.strs_merge(es1, Met.strs_merge(es2, es3)), Big.add(l1, Big.add(l2, l3)), Big.add(i1, Big.add(i2, i3)), Big.add(o1, Big.add(o2, o3)),
                  Met.ext_merge(x1, Met.ext_merge(x2, x3)), Met.LNone{}} : Met.Acc}
              %codes_assoc(cs1, cs2, cs3, w1(A, wa), w1(B, wb), w1(C, wc)) : {LHS == Met.Acc{[], Nat.add(Nat.add(n1, n2), n3), Nat.add(Nat.add(ok1, ok2), ok3), _,
                  Met.strs_merge(es1, Met.strs_merge(es2, es3)), Big.add(l1, Big.add(l2, l3)), Big.add(i1, Big.add(i2, i3)), Big.add(o1, Big.add(o2, o3)),
                  Met.ext_merge(x1, Met.ext_merge(x2, x3)), Met.LNone{}} : Met.Acc}
              %strs_assoc(es1, es2, es3, w2(A, wa), w2(B, wb), w2(C, wc)) : {LHS == Met.Acc{[], Nat.add(Nat.add(n1, n2), n3), Nat.add(Nat.add(ok1, ok2), ok3),
                  Met.codes_merge(Met.codes_merge(cs1, cs2), cs3), _, Big.add(l1, Big.add(l2, l3)), Big.add(i1, Big.add(i2, i3)), Big.add(o1, Big.add(o2, o3)),
                  Met.ext_merge(x1, Met.ext_merge(x2, x3)), Met.LNone{}} : Met.Acc}
              %big_assoc(l1, l2, l3, w3(A, wa), w3(B, wb), w3(C, wc)) : {LHS == Met.Acc{[], Nat.add(Nat.add(n1, n2), n3), Nat.add(Nat.add(ok1, ok2), ok3),
                  Met.codes_merge(Met.codes_merge(cs1, cs2), cs3), Met.strs_merge(Met.strs_merge(es1, es2), es3), _, Big.add(i1, Big.add(i2, i3)), Big.add(o1, Big.add(o2, o3)),
                  Met.ext_merge(x1, Met.ext_merge(x2, x3)), Met.LNone{}} : Met.Acc}
              %big_assoc(i1, i2, i3, w4(A, wa), w4(B, wb), w4(C, wc)) : {LHS == Met.Acc{[], Nat.add(Nat.add(n1, n2), n3), Nat.add(Nat.add(ok1, ok2), ok3),
                  Met.codes_merge(Met.codes_merge(cs1, cs2), cs3), Met.strs_merge(Met.strs_merge(es1, es2), es3), Big.add(Big.add(l1, l2), l3), _, Big.add(o1, Big.add(o2, o3)),
                  Met.ext_merge(x1, Met.ext_merge(x2, x3)), Met.LNone{}} : Met.Acc}
              %big_assoc(o1, o2, o3, w5(A, wa), w5(B, wb), w5(C, wc)) : {LHS == Met.Acc{[], Nat.add(Nat.add(n1, n2), n3), Nat.add(Nat.add(ok1, ok2), ok3),
                  Met.codes_merge(Met.codes_merge(cs1, cs2), cs3), Met.strs_merge(Met.strs_merge(es1, es2), es3), Big.add(Big.add(l1, l2), l3), Big.add(Big.add(i1, i2), i3), _,
                  Met.ext_merge(x1, Met.ext_merge(x2, x3)), Met.LNone{}} : Met.Acc}
              %ext_assoc(x1, x2, x3, w6(A, wa), w6(B, wb), w6(C, wc)) : {LHS == Met.Acc{[], Nat.add(Nat.add(n1, n2), n3), Nat.add(Nat.add(ok1, ok2), ok3),
                  Met.codes_merge(Met.codes_merge(cs1, cs2), cs3), Met.strs_merge(Met.strs_merge(es1, es2), es3), Big.add(Big.add(l1, l2), l3), Big.add(Big.add(i1, i2), i3),
                  Big.add(Big.add(o1, o2), o3), _, Met.LNone{}} : Met.Acc}
              {==}

def cp_app_nil(xs: List<&2, CP()>) -> {List.append(&2, CP(), xs, []) == xs : List<&2, CP()>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %cp_app_nil(rest) : {Con{x, List.append(&2, CP(), rest, [])} == Con{x, _} : List<&2, CP()>}
      {==}

def cgo_nil_r(f: Nat, cs: List<&2, CP()>) -> {Met.codes_merge.go(f, cs, []) == cs : List<&2, CP()>}:
  match f:
    case 0n:
      cp_app_nil(cs)
    case 1n+g:
      match cs:
        case Nil{}:
          {==}
        case Con{p, r}:
          {==}

def cgo_nil_l(f: Nat, +cs: List<&2, CP()>) -> {Met.codes_merge.go(f, [], cs) == cs : List<&2, CP()>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def sgo_nil_r(f: Nat, es: List<&2, String>) -> {Met.strs_merge.go(f, es, []) == es : List<&2, String>}:
  match f:
    case 0n:
      Equal.sym(List<&2, String>, es, List.append(&2, String, es, []), sapp_nil(es))
    case 1n+g:
      match es:
        case Nil{}:
          {==}
        case Con{p, r}:
          {==}

def sgo_nil_l(f: Nat, +es: List<&2, String>) -> {Met.strs_merge.go(f, [], es) == es : List<&2, String>}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      {==}

def zero_r_s(a: Met.Acc, +wa: {wf(a) == True{} : Bool}, +bs2: List<&2, Nat>) -> {strip(Met.merge(a, Met.empty(bs2))) == strip(a) : Met.Acc}:
  match a:
    case Met.Acc{bs, +n, +ok, +cs, +es, +l, +i, +o, +x, t}:
      +A = {Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} : Met.Acc}
      +R = {Met.Acc{[], n, ok, cs, es, l, i, o, x, Met.LNone{}} : Met.Acc}
      +z = Big.of(0n)
      %PNat.add_zero(n) : {Met.Acc{[], _, Nat.add(ok, 0n), Met.codes_merge(cs, []), Met.strs_merge(es, []), Big.add(l, z), Big.add(i, z), Big.add(o, z), Met.ext_merge(x, Met.NoExt{}), Met.LNone{}} == R : Met.Acc}
      %PNat.add_zero(ok) : {Met.Acc{[], n, _, Met.codes_merge(cs, []), Met.strs_merge(es, []), Big.add(l, z), Big.add(i, z), Big.add(o, z), Met.ext_merge(x, Met.NoExt{}), Met.LNone{}} == R : Met.Acc}
      %Equal.sym(List<&2, CP()>, Met.codes_merge(cs, []), cs, cgo_nil_r(Nat.add(List.length(&2, CP(), cs), 0n), cs))
        : {Met.Acc{[], n, ok, _, Met.strs_merge(es, []), Big.add(l, z), Big.add(i, z), Big.add(o, z), Met.ext_merge(x, Met.NoExt{}), Met.LNone{}} == R : Met.Acc}
      %Equal.sym(List<&2, String>, Met.strs_merge(es, []), es, sgo_nil_r(Nat.add(List.length(&2, String, es), 0n), es))
        : {Met.Acc{[], n, ok, cs, _, Big.add(l, z), Big.add(i, z), Big.add(o, z), Met.ext_merge(x, Met.NoExt{}), Met.LNone{}} == R : Met.Acc}
      %Equal.sym(Big.Big, Big.add(l, z), l, big_zero_r(l, w3(A, wa)))
        : {Met.Acc{[], n, ok, cs, es, _, Big.add(i, z), Big.add(o, z), Met.ext_merge(x, Met.NoExt{}), Met.LNone{}} == R : Met.Acc}
      %Equal.sym(Big.Big, Big.add(i, z), i, big_zero_r(i, w4(A, wa)))
        : {Met.Acc{[], n, ok, cs, es, l, _, Big.add(o, z), Met.ext_merge(x, Met.NoExt{}), Met.LNone{}} == R : Met.Acc}
      %Equal.sym(Big.Big, Big.add(o, z), o, big_zero_r(o, w5(A, wa)))
        : {Met.Acc{[], n, ok, cs, es, l, i, _, Met.ext_merge(x, Met.NoExt{}), Met.LNone{}} == R : Met.Acc}
      %Equal.sym(Met.Ext, Met.ext_merge(x, Met.NoExt{}), x, ext_zero_r(x))
        : {Met.Acc{[], n, ok, cs, es, l, i, o, _, Met.LNone{}} == R : Met.Acc}
      {==}

def zero_l_s(b: Met.Acc, +wb: {wf(b) == True{} : Bool}, +bs2: List<&2, Nat>) -> {strip(Met.merge(Met.empty(bs2), b)) == strip(b) : Met.Acc}:
  match b:
    case Met.Acc{bs, +n, +ok, +cs, +es, +l, +i, +o, +x, t}:
      +B = {Met.Acc{bs, n, ok, cs, es, l, i, o, x, t} : Met.Acc}
      +R = {Met.Acc{[], n, ok, cs, es, l, i, o, x, Met.LNone{}} : Met.Acc}
      +z = Big.of(0n)
      %Equal.sym(List<&2, CP()>, Met.codes_merge([], cs), cs, cgo_nil_l(List.length(&2, CP(), cs), cs))
        : {Met.Acc{[], n, ok, _, Met.strs_merge([], es), Big.add(z, l), Big.add(z, i), Big.add(z, o), x, Met.LNone{}} == R : Met.Acc}
      %Equal.sym(List<&2, String>, Met.strs_merge([], es), es, sgo_nil_l(List.length(&2, String, es), es))
        : {Met.Acc{[], n, ok, cs, _, Big.add(z, l), Big.add(z, i), Big.add(z, o), x, Met.LNone{}} == R : Met.Acc}
      %Equal.sym(Big.Big, Big.add(z, l), l, big_zero_l(l, w3(B, wb)))
        : {Met.Acc{[], n, ok, cs, es, _, Big.add(z, i), Big.add(z, o), x, Met.LNone{}} == R : Met.Acc}
      %Equal.sym(Big.Big, Big.add(z, i), i, big_zero_l(i, w4(B, wb)))
        : {Met.Acc{[], n, ok, cs, es, l, _, Big.add(z, o), x, Met.LNone{}} == R : Met.Acc}
      %Equal.sym(Big.Big, Big.add(z, o), o, big_zero_l(o, w5(B, wb)))
        : {Met.Acc{[], n, ok, cs, es, l, i, _, x, Met.LNone{}} == R : Met.Acc}
      {==}

# ---------------------------------------------------------------------
# folding results into an accumulator is merging their own accumulator
# ---------------------------------------------------------------------

def mlem(ys: List<&2, Hit.Hit>, +a: Met.Acc, +wa: {wf(a) == True{} : Bool}, +bs2: List<&2, Nat>)
  -> {strip(L.acc_all(ys, a)) == strip(Met.merge(a, L.acc_all(ys, Met.empty(bs2)))) : Met.Acc}:
  match ys:
    case Nil{}:
      Equal.sym(Met.Acc, strip(Met.merge(a, Met.empty(bs2))), strip(a), zero_r_s(a, wa, bs2))
    case Con{+y, +rest}:
      +E = Met.empty(bs2)
      +o = Met.of_hit(y)
      +wo = wf_oh(y)
      +R = L.acc_all(rest, E)
      +wR = wf_fold(rest, E, wf_empty(bs2))
      +ay = Met.add(a, y)
      +ey = Met.add(E, y)
      +wey = wf_merge(E, o, wf_empty(bs2), wo)
      +s1 = mlem(rest, ay, wf_merge(a, o, wa, wo), bs2)
      +s2 = assoc_s(a, o, R, wa, wo, wR)
      +s3 = cong_r(a, L.acc_all(rest, ey), Met.merge(ey, R), mlem(rest, ey, wey, bs2))
      +s4 = cong_r(a, Met.merge(ey, R), Met.merge(o, R),
              Equal.trans(Met.Acc, strip(Met.merge(ey, R)), strip(Met.merge(E, Met.merge(o, R))), strip(Met.merge(o, R)),
                assoc_s(E, o, R, wf_empty(bs2), wo, wR), zero_l_s(Met.merge(o, R), wf_merge(o, R, wo, wR), bs2)))
      Equal.trans(Met.Acc, strip(L.acc_all(rest, ay)), strip(Met.merge(ay, R)), strip(Met.merge(a, L.acc_all(rest, ey))), s1,
        Equal.trans(Met.Acc, strip(Met.merge(ay, R)), strip(Met.merge(a, Met.merge(o, R))), strip(Met.merge(a, L.acc_all(rest, ey))), s2,
          Equal.sym(Met.Acc, strip(Met.merge(a, L.acc_all(rest, ey))), strip(Met.merge(a, Met.merge(o, R))),
            Equal.trans(Met.Acc, strip(Met.merge(a, L.acc_all(rest, ey))), strip(Met.merge(a, Met.merge(ey, R))), strip(Met.merge(a, Met.merge(o, R))), s3, s4))))

def acc_app(xs: List<&2, Hit.Hit>, +ys: List<&2, Hit.Hit>, +a: Met.Acc)
  -> {L.acc_all(List.append(&2, Hit.Hit, xs, ys), a) == L.acc_all(ys, L.acc_all(xs, a)) : Met.Acc}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      acc_app(rest, ys, Met.add(a, x))

def wf_build(+bs: List<&2, Nat>, t: L.Build) -> {wf(L.build(bs, t)) == True{} : Bool}:
  match t:
    case L.BEmpty{}:
      wf_empty(bs)
    case L.BAdd{+b, +h}:
      wf_merge(L.build(bs, b), Met.of_hit(h), wf_build(bs, b), wf_oh(h))
    case L.BMerge{+l, +r}:
      wf_merge(L.build(bs, l), L.build(bs, r), wf_build(bs, l), wf_build(bs, r))

def tb(+bs: List<&2, Nat>, t: L.Build) -> {strip(L.build(bs, t)) == strip(L.acc_all(L.leaves(t), Met.empty(bs))) : Met.Acc}:
  match t:
    case L.BEmpty{}:
      {==}
    case L.BAdd{+b, +h}:
      +E = Met.empty(bs)
      +ab = L.acc_all(L.leaves(b), E)
      %Equal.sym(Met.Acc, L.acc_all(List.append(&2, Hit.Hit, L.leaves(b), [h]), E), L.acc_all([h], ab), acc_app(L.leaves(b), [h], E)) : {strip(Met.merge(L.build(bs, b), Met.of_hit(h))) == strip(_) : Met.Acc}
      cong_l(L.build(bs, b), ab, Met.of_hit(h), tb(bs, b))
    case L.BMerge{+l, +r}:
      +E = Met.empty(bs)
      +al = L.acc_all(L.leaves(l), E)
      +ar = L.acc_all(L.leaves(r), E)
      %Equal.sym(Met.Acc, L.acc_all(List.append(&2, Hit.Hit, L.leaves(l), L.leaves(r)), E), L.acc_all(L.leaves(r), al), acc_app(L.leaves(l), L.leaves(r), E)) : {strip(Met.merge(L.build(bs, l), L.build(bs, r))) == strip(_) : Met.Acc}
      Equal.trans(Met.Acc, strip(Met.merge(L.build(bs, l), L.build(bs, r))), strip(Met.merge(al, L.build(bs, r))), strip(L.acc_all(L.leaves(r), al)),
        cong_l(L.build(bs, l), al, L.build(bs, r), tb(bs, l)),
        Equal.trans(Met.Acc, strip(Met.merge(al, L.build(bs, r))), strip(Met.merge(al, ar)), strip(L.acc_all(L.leaves(r), al)),
          cong_r(al, L.build(bs, r), ar, tb(bs, r)),
          Equal.sym(Met.Acc, strip(L.acc_all(L.leaves(r), al)), strip(Met.merge(al, ar)), mlem(L.leaves(r), al, wf_fold(L.leaves(l), E, wf_empty(bs)), bs))))

# ---------------------------------------------------------------------
# the rope and the buckets of a built accumulator
# ---------------------------------------------------------------------

def lats_app(xs: List<&2, Hit.Hit>, +ys: List<&2, Hit.Hit>) -> {L.lats(List.append(&2, Hit.Hit, xs, ys)) == List.append(&2, Nat, L.lats(xs), L.lats(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %lats_app(rest, ys) : {Con{L.h_lat(x), L.lats(List.append(&2, Hit.Hit, rest, ys))} == Con{L.h_lat(x), _} : List<&2, Nat>}
      {==}

def fbt(+bs: List<&2, Nat>, t: L.Build, +acc: List<&2, Nat>)
  -> {Met.flatten(a_t(L.build(bs, t)), acc) == List.append(&2, Nat, L.lats(L.leaves(t)), acc) : List<&2, Nat>}:
  match t:
    case L.BEmpty{}:
      {==}
    case L.BAdd{+b, +h}:
      +tb2 = a_t(L.build(bs, b))
      +to = a_t(Met.of_hit(h))
      +lb = L.lats(L.leaves(b))
      +rhs = List.append(&2, Nat, L.lats(List.append(&2, Hit.Hit, L.leaves(b), [h])), acc)
      %m_t(L.build(bs, b), Met.of_hit(h)) : {Met.flatten(_, acc) == rhs : List<&2, Nat>}
      %fl_lcat(tb2, to, acc) : {_ == rhs : List<&2, Nat>}
      %oh_fl(h, acc) : {Met.flatten(tb2, _) == rhs : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Met.flatten(tb2, Con{L.h_lat(h), acc}), List.append(&2, Nat, lb, Con{L.h_lat(h), acc}), fbt(bs, b, Con{L.h_lat(h), acc}))
        : {_ == rhs : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, L.lats(List.append(&2, Hit.Hit, L.leaves(b), [h])), List.append(&2, Nat, lb, [L.h_lat(h)]), lats_app(L.leaves(b), [h]))
        : {List.append(&2, Nat, lb, Con{L.h_lat(h), acc}) == List.append(&2, Nat, _, acc) : List<&2, Nat>}
      napp_assoc(lb, [L.h_lat(h)], acc)
    case L.BMerge{+l, +r}:
      +tl = a_t(L.build(bs, l))
      +tr = a_t(L.build(bs, r))
      +ll = L.lats(L.leaves(l))
      +lr = L.lats(L.leaves(r))
      +rhs = List.append(&2, Nat, L.lats(List.append(&2, Hit.Hit, L.leaves(l), L.leaves(r))), acc)
      %m_t(L.build(bs, l), L.build(bs, r)) : {Met.flatten(_, acc) == rhs : List<&2, Nat>}
      %fl_lcat(tl, tr, acc) : {_ == rhs : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Met.flatten(tr, acc), List.append(&2, Nat, lr, acc), fbt(bs, r, acc)) : {Met.flatten(tl, _) == rhs : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Met.flatten(tl, List.append(&2, Nat, lr, acc)), List.append(&2, Nat, ll, List.append(&2, Nat, lr, acc)), fbt(bs, l, List.append(&2, Nat, lr, acc)))
        : {_ == rhs : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, L.lats(List.append(&2, Hit.Hit, L.leaves(l), L.leaves(r))), List.append(&2, Nat, ll, lr), lats_app(L.leaves(l), L.leaves(r)))
        : {List.append(&2, Nat, ll, List.append(&2, Nat, lr, acc)) == List.append(&2, Nat, _, acc) : List<&2, Nat>}
      napp_assoc(ll, lr, acc)

def bsb(+bs: List<&2, Nat>, t: L.Build) -> {a_bs(L.build(bs, t)) == bs : List<&2, Nat>}:
  match t:
    case L.BEmpty{}:
      {==}
    case L.BAdd{+b, +h}:
      %m_bs(L.build(bs, b), Met.of_hit(h)) : {_ == bs : List<&2, Nat>}
      bsb(bs, b)
    case L.BMerge{+l, +r}:
      %m_bs(L.build(bs, l), L.build(bs, r)) : {_ == bs : List<&2, Nat>}
      bsb(bs, l)

# ---------------------------------------------------------------------
# the same view closes to the same summary
# ---------------------------------------------------------------------

def close_t(x: Met.Ext, +bs: List<&2, Nat>, +n: Nat, +ok: Nat, +cs: List<&2, CP()>, +es: List<&2, String>, +l: Big.Big, +i: Big.Big, +o: Big.Big,
  +t1: Met.Lats, +t2: Met.Lats, +ef: {Met.flatten(t1, []) == Met.flatten(t2, []) : List<&2, Nat>})
  -> {Met.close(Met.Acc{bs, n, ok, cs, es, l, i, o, x, t1}) == Met.close(Met.Acc{bs, n, ok, cs, es, l, i, o, x, t2}) : Met.Summary}:
  match x:
    case Met.NoExt{}:
      {==}
    case Met.Ext{+a1, +b1, +es1, +en1, +ls1, +ln1, +xs1, +xn1}:
      %ef : {Met.close(Met.Acc{bs, n, ok, cs, es, l, i, o, Met.Ext{a1, b1, es1, en1, ls1, ln1, xs1, xn1}, t1})
             == Met.close.full(bs, n, ok, cs, es, l, i, o, a1, b1, es1, en1, ls1, ln1, xs1, xn1, Met.sort(_)) : Met.Summary}
      {==}

def close_eq(a: Met.Acc, b: Met.Acc, +es: {strip(a) == strip(b) : Met.Acc}, +eb: {a_bs(a) == a_bs(b) : List<&2, Nat>},
  +ef: {Met.flatten(a_t(a), []) == Met.flatten(a_t(b), []) : List<&2, Nat>}) -> {Met.close(a) == Met.close(b) : Met.Summary}:
  match a:
    case Met.Acc{+bs1, +n1, +ok1, +cs1, +es1, +l1, +i1, +o1, +x1, +t1}:
      match b:
        case Met.Acc{+bs2, +n2, +ok2, +cs2, +es2, +l2, +i2, +o2, +x2, +t2}:
          +A = {Met.Acc{bs1, n1, ok1, cs1, es1, l1, i1, o1, x1, t1} : Met.Acc}
          +B = {Met.Acc{bs2, n2, ok2, cs2, es2, l2, i2, o2, x2, t2} : Met.Acc}
          +sa2 = strip(A)
          +sb2 = strip(B)
          +cA = Met.close(A)
          %eb : {cA == Met.close(Met.Acc{_, n2, ok2, cs2, es2, l2, i2, o2, x2, t2}) : Met.Summary}
          %Equal.cong(Met.Acc, Nat, u => a_n(u), sa2, sb2, es) : {cA == Met.close(Met.Acc{bs1, _, ok2, cs2, es2, l2, i2, o2, x2, t2}) : Met.Summary}
          %Equal.cong(Met.Acc, Nat, u => a_ok(u), sa2, sb2, es) : {cA == Met.close(Met.Acc{bs1, n1, _, cs2, es2, l2, i2, o2, x2, t2}) : Met.Summary}
          %Equal.cong(Met.Acc, List<&2, CP()>, u => a_cs(u), sa2, sb2, es) : {cA == Met.close(Met.Acc{bs1, n1, ok1, _, es2, l2, i2, o2, x2, t2}) : Met.Summary}
          %Equal.cong(Met.Acc, List<&2, String>, u => a_es(u), sa2, sb2, es) : {cA == Met.close(Met.Acc{bs1, n1, ok1, cs1, _, l2, i2, o2, x2, t2}) : Met.Summary}
          %Equal.cong(Met.Acc, Big.Big, u => a_lat(u), sa2, sb2, es) : {cA == Met.close(Met.Acc{bs1, n1, ok1, cs1, es1, _, i2, o2, x2, t2}) : Met.Summary}
          %Equal.cong(Met.Acc, Big.Big, u => a_bin(u), sa2, sb2, es) : {cA == Met.close(Met.Acc{bs1, n1, ok1, cs1, es1, l1, _, o2, x2, t2}) : Met.Summary}
          %Equal.cong(Met.Acc, Big.Big, u => a_bout(u), sa2, sb2, es) : {cA == Met.close(Met.Acc{bs1, n1, ok1, cs1, es1, l1, i1, _, x2, t2}) : Met.Summary}
          %Equal.cong(Met.Acc, Met.Ext, u => a_x(u), sa2, sb2, es) : {cA == Met.close(Met.Acc{bs1, n1, ok1, cs1, es1, l1, i1, o1, _, t2}) : Met.Summary}
          close_t(x1, bs1, n1, ok1, cs1, es1, l1, i1, o1, t1, t2, ef)

def L.met_build(bs, t):
  +E = Met.empty(bs)
  +A = L.build(bs, t)
  +B = L.acc_all(L.leaves(t), E)
  +ls = L.lats(L.leaves(t))
  close_eq(A, B, tb(bs, t), Equal.trans(List<&2, Nat>, a_bs(A), bs, a_bs(B), bsb(bs, t), f_bs(L.leaves(t), E)),
    Equal.trans(List<&2, Nat>, Met.flatten(a_t(A), []), List.append(&2, Nat, ls, []), Met.flatten(a_t(B), []), fbt(bs, t, []),
      Equal.trans(List<&2, Nat>, List.append(&2, Nat, ls, []), ls, Met.flatten(a_t(B), []), Equal.sym(List<&2, Nat>, ls, List.append(&2, Nat, ls, []), app_nil(ls)),
        lats_all(bs, L.leaves(t)))))

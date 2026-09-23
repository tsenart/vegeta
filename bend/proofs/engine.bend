# Proofs of the engine laws (eng_*).
#
# Each checker of LAWS.bend is a fold over the timeline. For each one, the
# engine's state determines the checker's state (the seq is `next`, the
# busy list is the engine's own, ...), and the proof walks the engine's
# loops: settle, the dispatch to new workers (grow_*), the dispatch to
# idle workers (idle_*), then the events (steps_*) by induction. A loop
# lemma reads {chk(T, K(final state)) == chk(cmds ++ T, K(state))}.
import Base
import ../LAWS.bend as L
import ../lib/engine.bend as Eng
import ./nat.bend as N

# ---------------------------------------------------------------------
# Basics
# ---------------------------------------------------------------------

def eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def nx(s: Eng.State) -> Nat:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      next

def nw(s: Eng.State) -> Nat:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      now

def lst(s: Eng.State) -> Maybe<&2, Nat>:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      last

def bool_absurd(-x: Bool, -y: Bool, e: {False{} == True{} : Bool}) -> {x == y : Bool}:
  Empty.absurd({x == y : Bool}, N.false_ne_true(e))

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      bool_absurd(b, True{}, e)

def not_t(a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      bool_absurd(True{}, False{}, e)
    case False{}:
      {==}

# LAWS' config readers and the engine's agree
def slot_same(c: Eng.Cfg, +i: Nat) -> {Eng.slot(c, i) == L.slot(c, i) : Nat}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}

def bounded_same(c: Eng.Cfg) -> {Eng.bounded(c) == L.bounded(c) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}

def dur_same(c: Eng.Cfg) -> {Eng.dur(c) == L.e_dur(c) : Nat}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}

# not (a >= b) is a < b
def cmp_lt(x: Cmp, e: {Bool.not(Cmp.is_ge(x)) == True{} : Bool}) -> {True{} == Cmp.is_lt(x) : Bool}:
  match x:
    case LT{}:
      {==}
    case EQ{}:
      bool_absurd(True{}, False{}, e)
    case GT{}:
      bool_absurd(True{}, False{}, e)

# the start, spelled out
def i0(+c: Eng.Cfg) -> Nat:
  Eng.initial(c)

def r0(+c: Eng.Cfg) -> Nat:
  Nat.sub(Eng.max_workers(c), Eng.initial(c))

def ok0(+c: Eng.Cfg) -> Bool:
  Eng.may(c, 0n, 0n, None{})

def ic0(+c: Eng.Cfg) -> List<&2, Eng.Cmd>:
  Eng.idle_cs(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{})

def is0(+c: Eng.Cfg) -> Eng.State:
  Eng.idle_st(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{})

def initial_same(c: Eng.Cfg) -> {Eng.initial(c) == L.initial(c) : Nat}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}
# ---------------------------------------------------------------------
# Bool and Nat facts
# ---------------------------------------------------------------------

def or_false_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      {==}

def or_false_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Equal.sym(Bool, False{}, b, bool_absurd(False{}, b, Equal.sym(Bool, True{}, False{}, e)))
    case False{}:
      e

def or_true_r(a: Bool, -b: Bool, ea: {a == False{} : Bool}, e: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      bool_absurd(b, True{}, Equal.sym(Bool, True{}, False{}, ea))
    case False{}:
      e

def and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ea

def not_i(a: Bool, e: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  match a:
    case True{}:
      bool_absurd(False{}, True{}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      {==}

def eq_of(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, N.false_ne_true(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, N.false_ne_true(e))
    case 1n+p 1n+q:
      %eq_of(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def eq_sym_b(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      eq_sym_b(p, q)

def lt_succ(g: Nat) -> {Nat.is_lt(g, 1n+g) == True{} : Bool}:
  match g:
    case 0n:
      {==}
    case 1n+p:
      lt_succ(p)

def lt_succ_r(x: Nat, g: Nat, e: {Nat.is_lt(x, g) == True{} : Bool}) -> {Nat.is_lt(x, 1n+g) == True{} : Bool}:
  match x g:
    case 0n _:
      {==}
    case 1n+p 0n:
      bool_absurd(Nat.is_lt(p, 0n), True{}, e)
    case 1n+p 1n+q:
      lt_succ_r(p, q, e)

# x < g: g is not x
def lt_ne(x: Nat, g: Nat, e: {Nat.is_lt(x, g) == True{} : Bool}) -> {Nat.is_eq(g, x) == False{} : Bool}:
  match x g:
    case 0n 0n:
      bool_absurd(True{}, False{}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      lt_ne(p, q, e)

# room + 1 more to grow: grown is under max
def room_lt(+r: Nat, +g: Nat, +m: Nat, e: {Nat.is_eq(Nat.add(1n+r, g), m) == True{} : Bool}) -> {Nat.is_lt(g, m) == True{} : Bool}:
  %eq_of(Nat.add(1n+r, g), m, e) : {Nat.is_lt(g, _) == True{} : Bool}
  %N.add_comm(g, r) : {Nat.is_lt(g, 1n+_) == True{} : Bool}
  N.lt_of_add(g, r, Nat.add(g, r), {==})

# ---------------------------------------------------------------------
# Lists of worker ids (LAWS' has_nat and drop_nat)
# ---------------------------------------------------------------------

def has_same(+x: Nat, xs: List<&2, Nat>) -> {Eng.has_nat(x, xs) == L.has_nat(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %has_same(x, rest) : {Bool.or(Nat.is_eq(x, y), Eng.has_nat(x, rest)) == Bool.or(Nat.is_eq(x, y), _) : Bool}
      {==}

def picks(b: Bool, +r: List<&2, Nat>, -A: List<&2, Nat>, -B: List<&2, Nat>, e: {A == B : List<&2, Nat>})
  -> {Eng.pick(List<&2, Nat>, b, r, A) == L.pick(List<&2, Nat>, b, r, B) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def drop_same(+x: Nat, xs: List<&2, Nat>) -> {Eng.drop_nat(x, xs) == L.drop_nat(x, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      picks(Nat.is_eq(x, y), rest, Con{y, Eng.drop_nat(x, rest)}, Con{y, L.drop_nat(x, rest)},
        Equal.cong(List<&2, Nat>, List<&2, Nat>, zs => Con{y, zs}, Eng.drop_nat(x, rest), L.drop_nat(x, rest), drop_same(x, rest)))

def all_lt(xs: List<&2, Nat>, +g: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(Nat.is_lt(x, g), all_lt(rest, g))

def dist(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(Bool.not(L.has_nat(x, rest)), dist(rest))

# the idle workers: grown, not busy, each once
def iok(idle: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat) -> Bool:
  match idle:
    case Nil{}:
      True{}
    case Con{+u, +rest}:
      Bool.and(Nat.is_lt(u, g), Bool.and(Bool.not(L.has_nat(u, busy)), Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g))))

def or_f(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      bool_absurd(True{}, False{}, Equal.sym(Bool, True{}, False{}, ea))
    case False{}:
      eb

# a list without w is unchanged by dropping w
def drop_no(+w: Nat, xs: List<&2, Nat>, +e: {L.has_nat(w, xs) == False{} : Bool}) -> {xs == L.drop_nat(w, xs) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %Equal.sym(Bool, Nat.is_eq(w, y), False{}, or_false_l(Nat.is_eq(w, y), L.has_nat(w, rest), e))
        : {Con{y, rest} == L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)}) : List<&2, Nat>}
      %drop_no(w, rest, or_false_r(Nat.is_eq(w, y), L.has_nat(w, rest), e)) : {Con{y, rest} == Con{y, _} : List<&2, Nat>}
      {==}

def len_drop.of(b: Bool, +w: Nat, +y: Nat, +rest: List<&2, Nat>, +eb: {Nat.is_eq(w, y) == b : Bool},
  e: {Bool.or(Nat.is_eq(w, y), L.has_nat(w, rest)) == True{} : Bool},
  ih: {L.has_nat(w, rest) == True{} : Bool} -> {List.length(&2, Nat, rest) == 1n+List.length(&2, Nat, L.drop_nat(w, rest)) : Nat})
  -> {1n+List.length(&2, Nat, rest) == 1n+List.length(&2, Nat, L.pick(List<&2, Nat>, Nat.is_eq(w, y), rest, Con{y, L.drop_nat(w, rest)})) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), True{}, eb) : {1n+List.length(&2, Nat, rest) == 1n+List.length(&2, Nat, L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)})) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), False{}, eb) : {1n+List.length(&2, Nat, rest) == 1n+List.length(&2, Nat, L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)})) : Nat}
      %ih(or_true_r(Nat.is_eq(w, y), L.has_nat(w, rest), eb, e)) : {1n+List.length(&2, Nat, rest) == 1n+_ : Nat}
      {==}

# dropping a member shortens by one
def len_drop(+w: Nat, xs: List<&2, Nat>, e: {L.has_nat(w, xs) == True{} : Bool}) -> {List.length(&2, Nat, xs) == 1n+List.length(&2, Nat, L.drop_nat(w, xs)) : Nat}:
  match xs:
    case Nil{}:
      Empty.absurd({0n == 1n : Nat}, N.false_ne_true(e))
    case Con{+y, +rest}:
      len_drop.of(Nat.is_eq(w, y), w, y, rest, {==}, e, h => len_drop(w, rest, h))

def all_lt_drop.of(b: Bool, +w: Nat, +y: Nat, +rest: List<&2, Nat>, +g: Nat, +eb: {Nat.is_eq(w, y) == b : Bool},
  +e: {Bool.and(Nat.is_lt(y, g), all_lt(rest, g)) == True{} : Bool}, ih: {all_lt(L.drop_nat(w, rest), g) == True{} : Bool})
  -> {all_lt(L.pick(List<&2, Nat>, Nat.is_eq(w, y), rest, Con{y, L.drop_nat(w, rest)}), g) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), True{}, eb) : {all_lt(L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)}), g) == True{} : Bool}
      and_r(Nat.is_lt(y, g), all_lt(rest, g), e)
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), False{}, eb) : {all_lt(L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)}), g) == True{} : Bool}
      and_i(Nat.is_lt(y, g), all_lt(L.drop_nat(w, rest), g), and_l(Nat.is_lt(y, g), all_lt(rest, g), e), ih)

def all_lt_drop(+w: Nat, xs: List<&2, Nat>, +g: Nat, +e: {all_lt(xs, g) == True{} : Bool}) -> {all_lt(L.drop_nat(w, xs), g) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      all_lt_drop.of(Nat.is_eq(w, y), w, y, rest, g, {==}, e, all_lt_drop(w, rest, g, and_r(Nat.is_lt(y, g), all_lt(rest, g), e)))

def nhas_drop.of(b: Bool, +u: Nat, +w: Nat, +y: Nat, +rest: List<&2, Nat>, +eb: {Nat.is_eq(w, y) == b : Bool},
  +e: {Bool.or(Nat.is_eq(u, y), L.has_nat(u, rest)) == False{} : Bool}, ih: {L.has_nat(u, L.drop_nat(w, rest)) == False{} : Bool})
  -> {L.has_nat(u, L.pick(List<&2, Nat>, Nat.is_eq(w, y), rest, Con{y, L.drop_nat(w, rest)})) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), True{}, eb) : {L.has_nat(u, L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)})) == False{} : Bool}
      or_false_r(Nat.is_eq(u, y), L.has_nat(u, rest), e)
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), False{}, eb) : {L.has_nat(u, L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)})) == False{} : Bool}
      or_f(Nat.is_eq(u, y), L.has_nat(u, L.drop_nat(w, rest)), or_false_l(Nat.is_eq(u, y), L.has_nat(u, rest), e), ih)

# what is not in a list is not in it after a drop
def nhas_drop(+u: Nat, +w: Nat, xs: List<&2, Nat>, +e: {L.has_nat(u, xs) == False{} : Bool}) -> {L.has_nat(u, L.drop_nat(w, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      nhas_drop.of(Nat.is_eq(w, y), u, w, y, rest, {==}, e, nhas_drop(u, w, rest, or_false_r(Nat.is_eq(u, y), L.has_nat(u, rest), e)))

def dist_drop.of(b: Bool, +w: Nat, +y: Nat, +rest: List<&2, Nat>, +eb: {Nat.is_eq(w, y) == b : Bool},
  +e: {Bool.and(Bool.not(L.has_nat(y, rest)), dist(rest)) == True{} : Bool}, ih: {dist(L.drop_nat(w, rest)) == True{} : Bool})
  -> {dist(L.pick(List<&2, Nat>, Nat.is_eq(w, y), rest, Con{y, L.drop_nat(w, rest)})) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), True{}, eb) : {dist(L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)})) == True{} : Bool}
      and_r(Bool.not(L.has_nat(y, rest)), dist(rest), e)
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), False{}, eb) : {dist(L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)})) == True{} : Bool}
      and_i(Bool.not(L.has_nat(y, L.drop_nat(w, rest))), dist(L.drop_nat(w, rest)),
        not_i(L.has_nat(y, L.drop_nat(w, rest)), nhas_drop(y, w, rest, not_t(L.has_nat(y, rest), and_l(Bool.not(L.has_nat(y, rest)), dist(rest), e)))), ih)

def dist_drop(+w: Nat, xs: List<&2, Nat>, +e: {dist(xs) == True{} : Bool}) -> {dist(L.drop_nat(w, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      dist_drop.of(Nat.is_eq(w, y), w, y, rest, {==}, e, dist_drop(w, rest, and_r(Bool.not(L.has_nat(y, rest)), dist(rest), e)))

def dhas_drop.of(b: Bool, +w: Nat, +y: Nat, +rest: List<&2, Nat>, +eb: {Nat.is_eq(w, y) == b : Bool},
  +e: {Bool.and(Bool.not(L.has_nat(y, rest)), dist(rest)) == True{} : Bool}, ih: {L.has_nat(w, L.drop_nat(w, rest)) == False{} : Bool})
  -> {L.has_nat(w, L.pick(List<&2, Nat>, Nat.is_eq(w, y), rest, Con{y, L.drop_nat(w, rest)})) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), True{}, eb) : {L.has_nat(w, L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)})) == False{} : Bool}
      %Equal.sym(Nat, w, y, eq_of(w, y, eb)) : {L.has_nat(_, rest) == False{} : Bool}
      not_t(L.has_nat(y, rest), and_l(Bool.not(L.has_nat(y, rest)), dist(rest), e))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(w, y), False{}, eb) : {L.has_nat(w, L.pick(List<&2, Nat>, _, rest, Con{y, L.drop_nat(w, rest)})) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(w, y), False{}, eb) : {Bool.or(_, L.has_nat(w, L.drop_nat(w, rest))) == False{} : Bool}
      ih

# in a list without repeats, a dropped id is gone
def dhas_drop(+w: Nat, xs: List<&2, Nat>, +e: {dist(xs) == True{} : Bool}) -> {L.has_nat(w, L.drop_nat(w, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      dhas_drop.of(Nat.is_eq(w, y), w, y, rest, {==}, e, dhas_drop(w, rest, and_r(Bool.not(L.has_nat(y, rest)), dist(rest), e)))

def lt_has.of(b: Bool, +w: Nat, +y: Nat, +rest: List<&2, Nat>, +g: Nat, +eb: {Nat.is_eq(w, y) == b : Bool},
  +ea: {Bool.and(Nat.is_lt(y, g), all_lt(rest, g)) == True{} : Bool}, eh: {Bool.or(Nat.is_eq(w, y), L.has_nat(w, rest)) == True{} : Bool},
  ih: {L.has_nat(w, rest) == True{} : Bool} -> {Nat.is_lt(w, g) == True{} : Bool})
  -> {Nat.is_lt(w, g) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, w, y, eq_of(w, y, eb)) : {Nat.is_lt(_, g) == True{} : Bool}
      and_l(Nat.is_lt(y, g), all_lt(rest, g), ea)
    case False{}:
      ih(or_true_r(Nat.is_eq(w, y), L.has_nat(w, rest), eb, eh))

# a member of a list of ids under g is under g
def lt_has(+w: Nat, xs: List<&2, Nat>, +g: Nat, +ea: {all_lt(xs, g) == True{} : Bool}, eh: {L.has_nat(w, xs) == True{} : Bool})
  -> {Nat.is_lt(w, g) == True{} : Bool}:
  match xs:
    case Nil{}:
      bool_absurd(Nat.is_lt(w, g), True{}, eh)
    case Con{+y, +rest}:
      lt_has.of(Nat.is_eq(w, y), w, y, rest, g, {==}, ea, eh, h => lt_has(w, rest, g, and_r(Nat.is_lt(y, g), all_lt(rest, g), ea), h))

def all_lt_mono(xs: List<&2, Nat>, +g: Nat, +e: {all_lt(xs, g) == True{} : Bool}) -> {all_lt(xs, 1n+g) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      and_i(Nat.is_lt(x, 1n+g), all_lt(rest, 1n+g), lt_succ_r(x, g, and_l(Nat.is_lt(x, g), all_lt(rest, g), e)),
        all_lt_mono(rest, g, and_r(Nat.is_lt(x, g), all_lt(rest, g), e)))

# g is not among ids under g
def lt_nhas(xs: List<&2, Nat>, +g: Nat, +e: {all_lt(xs, g) == True{} : Bool}) -> {L.has_nat(g, xs) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      or_f(Nat.is_eq(g, x), L.has_nat(g, rest), lt_ne(x, g, and_l(Nat.is_lt(x, g), all_lt(rest, g), e)),
        lt_nhas(rest, g, and_r(Nat.is_lt(x, g), all_lt(rest, g), e)))

# the parts of iok for a first idle worker u
def ik1(+u: Nat, +rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, e: {iok(Con{u, rest}, busy, g) == True{} : Bool}) -> {Nat.is_lt(u, g) == True{} : Bool}:
  and_l(Nat.is_lt(u, g), Bool.and(Bool.not(L.has_nat(u, busy)), Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g))), e)

def ik234(+u: Nat, +rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, e: {iok(Con{u, rest}, busy, g) == True{} : Bool})
  -> {Bool.and(Bool.not(L.has_nat(u, busy)), Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g))) == True{} : Bool}:
  and_r(Nat.is_lt(u, g), Bool.and(Bool.not(L.has_nat(u, busy)), Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g))), e)

def ik2(+u: Nat, +rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, e: {iok(Con{u, rest}, busy, g) == True{} : Bool}) -> {L.has_nat(u, busy) == False{} : Bool}:
  not_t(L.has_nat(u, busy), and_l(Bool.not(L.has_nat(u, busy)), Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g)), ik234(u, rest, busy, g, e)))

def ik34(+u: Nat, +rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, e: {iok(Con{u, rest}, busy, g) == True{} : Bool})
  -> {Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g)) == True{} : Bool}:
  and_r(Bool.not(L.has_nat(u, busy)), Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g)), ik234(u, rest, busy, g, e))

def ik3(+u: Nat, +rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, e: {iok(Con{u, rest}, busy, g) == True{} : Bool}) -> {L.has_nat(u, rest) == False{} : Bool}:
  not_t(L.has_nat(u, rest), and_l(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g), ik34(u, rest, busy, g, e)))

def ik4(+u: Nat, +rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, e: {iok(Con{u, rest}, busy, g) == True{} : Bool}) -> {iok(rest, busy, g) == True{} : Bool}:
  and_r(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g), ik34(u, rest, busy, g, e))

def ikmk(+u: Nat, +rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, e1: {Nat.is_lt(u, g) == True{} : Bool}, e2: {L.has_nat(u, busy) == False{} : Bool},
  e3: {L.has_nat(u, rest) == False{} : Bool}, e4: {iok(rest, busy, g) == True{} : Bool}) -> {iok(Con{u, rest}, busy, g) == True{} : Bool}:
  and_i(Nat.is_lt(u, g), Bool.and(Bool.not(L.has_nat(u, busy)), Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g))), e1,
    and_i(Bool.not(L.has_nat(u, busy)), Bool.and(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g)), not_i(L.has_nat(u, busy), e2),
      and_i(Bool.not(L.has_nat(u, rest)), iok(rest, busy, g), not_i(L.has_nat(u, rest), e3), e4)))

def iok_nhas.of(b: Bool, +w: Nat, +u: Nat, +rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, +eb: {Nat.is_eq(w, u) == b : Bool},
  +ei: {iok(Con{u, rest}, busy, g) == True{} : Bool}, eh: {L.has_nat(w, busy) == True{} : Bool}, ih: {L.has_nat(w, rest) == False{} : Bool})
  -> {Bool.or(Nat.is_eq(w, u), L.has_nat(w, rest)) == False{} : Bool}:
  match b:
    case True{}:
      bool_absurd(Bool.or(Nat.is_eq(w, u), L.has_nat(w, rest)), False{},
        Equal.trans(Bool, False{}, L.has_nat(u, busy), True{}, Equal.sym(Bool, L.has_nat(u, busy), False{}, ik2(u, rest, busy, g, ei)),
          Equal.trans(Bool, L.has_nat(u, busy), L.has_nat(w, busy), True{},
            Equal.cong(Nat, Bool, x => L.has_nat(x, busy), u, w, Equal.sym(Nat, w, u, eq_of(w, u, eb))), eh)))
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(w, u), False{}, eb) : {Bool.or(_, L.has_nat(w, rest)) == False{} : Bool}
      ih

# a busy worker is not idle
def iok_nhas(+w: Nat, idle: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, +ei: {iok(idle, busy, g) == True{} : Bool}, +eh: {L.has_nat(w, busy) == True{} : Bool})
  -> {L.has_nat(w, idle) == False{} : Bool}:
  match idle:
    case Nil{}:
      {==}
    case Con{+u, +rest}:
      iok_nhas.of(Nat.is_eq(w, u), w, u, rest, busy, g, {==}, ei, eh, iok_nhas(w, rest, busy, g, ik4(u, rest, busy, g, ei), eh))

def iok_drop(+w: Nat, idle: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, +ei: {iok(idle, busy, g) == True{} : Bool})
  -> {iok(idle, L.drop_nat(w, busy), g) == True{} : Bool}:
  match idle:
    case Nil{}:
      {==}
    case Con{+u, +rest}:
      ikmk(u, rest, L.drop_nat(w, busy), g, ik1(u, rest, busy, g, ei), nhas_drop(u, w, busy, ik2(u, rest, busy, g, ei)),
        ik3(u, rest, busy, g, ei), iok_drop(w, rest, busy, g, ik4(u, rest, busy, g, ei)))

# the rest of the idle workers are not the one that took the hit
def iok_cons(+u: Nat, rest: List<&2, Nat>, +busy: List<&2, Nat>, +g: Nat, +ei: {iok(rest, busy, g) == True{} : Bool}, +en: {L.has_nat(u, rest) == False{} : Bool})
  -> {iok(rest, Con{u, busy}, g) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{+v, +r2}:
      ikmk(v, r2, Con{u, busy}, g, ik1(v, r2, busy, g, ei),
        or_f(Nat.is_eq(v, u), L.has_nat(v, busy),
          Equal.trans(Bool, Nat.is_eq(v, u), Nat.is_eq(u, v), False{}, eq_sym_b(v, u), or_false_l(Nat.is_eq(u, v), L.has_nat(u, r2), en)),
          ik2(v, r2, busy, g, ei)),
        ik3(v, r2, busy, g, ei), iok_cons(u, r2, busy, g, ik4(v, r2, busy, g, ei), or_false_r(Nat.is_eq(u, v), L.has_nat(u, r2), en)))
# ---------------------------------------------------------------------
# The worker invariant: room + grown = max-workers; busy and idle
# account for every grown worker; busy ids are grown and distinct; idle
# ids are grown, distinct and not busy
# ---------------------------------------------------------------------

def winv(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>) -> Bool:
  Bool.and(Nat.is_eq(Nat.add(room, g), L.e_max(c)),
    Bool.and(Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g),
      Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g)))))

def sinv(+c: Eng.Cfg, s: Eng.State) -> Bool:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      winv(c, grown, room, busy, idle)

def wv1(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, e: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {Nat.is_eq(Nat.add(room, g), L.e_max(c)) == True{} : Bool}:
  and_l(Nat.is_eq(Nat.add(room, g), L.e_max(c)), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g),
      Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g)))), e)

def wv2345(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, e: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {Bool.and(Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g), Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g)))) == True{} : Bool}:
  and_r(Nat.is_eq(Nat.add(room, g), L.e_max(c)), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g),
      Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g)))), e)

def wv2(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, e: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g) == True{} : Bool}:
  and_l(Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g), Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g))), wv2345(c, g, room, busy, idle, e))

def wv345(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, e: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g))) == True{} : Bool}:
  and_r(Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g), Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g))), wv2345(c, g, room, busy, idle, e))

def wv3(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, e: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {all_lt(busy, g) == True{} : Bool}:
  and_l(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g)), wv345(c, g, room, busy, idle, e))

def wv45(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, e: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {Bool.and(dist(busy), iok(idle, busy, g)) == True{} : Bool}:
  and_r(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g)), wv345(c, g, room, busy, idle, e))

def wv4(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, e: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {dist(busy) == True{} : Bool}:
  and_l(dist(busy), iok(idle, busy, g), wv45(c, g, room, busy, idle, e))

def wv5(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, e: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {iok(idle, busy, g) == True{} : Bool}:
  and_r(dist(busy), iok(idle, busy, g), wv45(c, g, room, busy, idle, e))

def wmk(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>,
  e1: {Nat.is_eq(Nat.add(room, g), L.e_max(c)) == True{} : Bool},
  e2: {Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g) == True{} : Bool},
  e3: {all_lt(busy, g) == True{} : Bool}, e4: {dist(busy) == True{} : Bool}, e5: {iok(idle, busy, g) == True{} : Bool})
  -> {winv(c, g, room, busy, idle) == True{} : Bool}:
  and_i(Nat.is_eq(Nat.add(room, g), L.e_max(c)), Bool.and(Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g),
      Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g)))), e1,
    and_i(Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g), Bool.and(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g))), e2,
      and_i(all_lt(busy, g), Bool.and(dist(busy), iok(idle, busy, g)), e3, and_i(dist(busy), iok(idle, busy, g), e4, e5))))

# an idle worker takes a hit
def wv_fire_idle(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +u: Nat, +rest: List<&2, Nat>, +hv: {winv(c, g, room, busy, Con{u, rest}) == True{} : Bool})
  -> {winv(c, g, room, Con{u, busy}, rest) == True{} : Bool}:
  +ei = wv5(c, g, room, busy, Con{u, rest}, hv)
  wmk(c, g, room, Con{u, busy}, rest, wv1(c, g, room, busy, Con{u, rest}, hv),
    Equal.trans(Bool, Nat.is_eq(1n+Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, rest)), g),
      Nat.is_eq(Nat.add(List.length(&2, Nat, busy), 1n+List.length(&2, Nat, rest)), g), True{},
      Equal.cong(Nat, Bool, x => Nat.is_eq(x, g), 1n+Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, rest)),
        Nat.add(List.length(&2, Nat, busy), 1n+List.length(&2, Nat, rest)), N.add_succ(List.length(&2, Nat, busy), List.length(&2, Nat, rest))),
      wv2(c, g, room, busy, Con{u, rest}, hv)),
    and_i(Nat.is_lt(u, g), all_lt(busy, g), ik1(u, rest, busy, g, ei), wv3(c, g, room, busy, Con{u, rest}, hv)),
    and_i(Bool.not(L.has_nat(u, busy)), dist(busy), not_i(L.has_nat(u, busy), ik2(u, rest, busy, g, ei)), wv4(c, g, room, busy, Con{u, rest}, hv)),
    iok_cons(u, rest, busy, g, ik4(u, rest, busy, g, ei), ik3(u, rest, busy, g, ei)))

# a new worker takes a hit
def wv_fire_grow(+c: Eng.Cfg, +g: Nat, +r: Nat, +busy: List<&2, Nat>, +hv: {winv(c, g, 1n+r, busy, []) == True{} : Bool})
  -> {winv(c, 1n+g, r, Con{g, busy}, []) == True{} : Bool}:
  +e3 = wv3(c, g, 1n+r, busy, [], hv)
  wmk(c, 1n+g, r, Con{g, busy}, [],
    Equal.trans(Bool, Nat.is_eq(Nat.add(r, 1n+g), L.e_max(c)), Nat.is_eq(1n+Nat.add(r, g), L.e_max(c)), True{},
      Equal.cong(Nat, Bool, x => Nat.is_eq(x, L.e_max(c)), Nat.add(r, 1n+g), 1n+Nat.add(r, g), Equal.sym(Nat, 1n+Nat.add(r, g), Nat.add(r, 1n+g), N.add_succ(r, g))),
      wv1(c, g, 1n+r, busy, [], hv)),
    wv2(c, g, 1n+r, busy, [], hv),
    and_i(Nat.is_lt(g, 1n+g), all_lt(busy, 1n+g), lt_succ(g), all_lt_mono(busy, g, e3)),
    and_i(Bool.not(L.has_nat(g, busy)), dist(busy), not_i(L.has_nat(g, busy), lt_nhas(busy, g, e3)), wv4(c, g, 1n+r, busy, [], hv)),
    {==})

def wv_freed.of(b: Bool, +c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +w: Nat,
  +eb: {L.has_nat(w, busy) == b : Bool}, +hv: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {winv(c, g, room, L.drop_nat(w, busy), Eng.freed_idle(b, w, idle)) == True{} : Bool}:
  match b:
    case True{}:
      +e3 = wv3(c, g, room, busy, idle, hv)
      +e4 = wv4(c, g, room, busy, idle, hv)
      +e5 = wv5(c, g, room, busy, idle, hv)
      wmk(c, g, room, L.drop_nat(w, busy), Con{w, idle}, wv1(c, g, room, busy, idle, hv),
        Equal.trans(Bool, Nat.is_eq(Nat.add(List.length(&2, Nat, L.drop_nat(w, busy)), 1n+List.length(&2, Nat, idle)), g),
          Nat.is_eq(Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)), g), True{},
          Equal.cong(Nat, Bool, x => Nat.is_eq(x, g), Nat.add(List.length(&2, Nat, L.drop_nat(w, busy)), 1n+List.length(&2, Nat, idle)),
            Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)),
            Equal.trans(Nat, Nat.add(List.length(&2, Nat, L.drop_nat(w, busy)), 1n+List.length(&2, Nat, idle)),
              1n+Nat.add(List.length(&2, Nat, L.drop_nat(w, busy)), List.length(&2, Nat, idle)),
              Nat.add(List.length(&2, Nat, busy), List.length(&2, Nat, idle)),
              Equal.sym(Nat, 1n+Nat.add(List.length(&2, Nat, L.drop_nat(w, busy)), List.length(&2, Nat, idle)),
                Nat.add(List.length(&2, Nat, L.drop_nat(w, busy)), 1n+List.length(&2, Nat, idle)), N.add_succ(List.length(&2, Nat, L.drop_nat(w, busy)), List.length(&2, Nat, idle))),
              Equal.cong(Nat, Nat, x => Nat.add(x, List.length(&2, Nat, idle)), 1n+List.length(&2, Nat, L.drop_nat(w, busy)), List.length(&2, Nat, busy),
                Equal.sym(Nat, List.length(&2, Nat, busy), 1n+List.length(&2, Nat, L.drop_nat(w, busy)), len_drop(w, busy, eb))))),
          wv2(c, g, room, busy, idle, hv)),
        all_lt_drop(w, busy, g, e3), dist_drop(w, busy, e4),
        ikmk(w, idle, L.drop_nat(w, busy), g, lt_has(w, busy, g, e3, eb), dhas_drop(w, busy, e4), iok_nhas(w, idle, busy, g, e5, eb), iok_drop(w, idle, busy, g, e5)))
    case False{}:
      %drop_no(w, busy, eb) : {winv(c, g, room, _, idle) == True{} : Bool}
      hv

# a worker freed
def wv_freed(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +w: Nat, +hv: {winv(c, g, room, busy, idle) == True{} : Bool})
  -> {winv(c, g, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, Eng.drop_nat(w, busy), L.drop_nat(w, busy), drop_same(w, busy))
    : {winv(c, g, room, _, Eng.freed_idle(Eng.has_nat(w, busy), w, idle)) == True{} : Bool}
  %Equal.sym(Bool, Eng.has_nat(w, busy), L.has_nat(w, busy), has_same(w, busy))
    : {winv(c, g, room, L.drop_nat(w, busy), Eng.freed_idle(_, w, idle)) == True{} : Bool}
  wv_freed.of(L.has_nat(w, busy), c, g, room, busy, idle, w, {==}, hv)

# the loops keep it
def inv_settle.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {sinv(c, Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  match b:
    case True{}:
      hv
    case False{}:
      hv

def inv_settle.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {sinv(c, Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  match b:
    case True{}:
      hv
    case False{}:
      inv_settle.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, hv)

def inv_settle(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {sinv(c, Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  inv_settle.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, hv)

def inv_grow(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +hv: {winv(c, grown, room, busy, []) == True{} : Bool})
  -> {sinv(c, Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)) == True{} : Bool}:
  match room:
    case 0n:
      inv_settle(c, now, next, grown, 0n, busy, [], nap, last, hv)
    case 1n+(+r):
      match ok:
        case True{}:
          inv_grow(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, wv_fire_grow(c, grown, r, busy, hv))
        case False{}:
          inv_settle(c, now, next, grown, 1n+r, busy, [], nap, last, hv)

def inv_idle(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {sinv(c, Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)) == True{} : Bool}:
  match idle:
    case Nil{}:
      inv_grow(room, ok, c, now, next, grown, busy, nap, last, hv)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          inv_idle(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, wv_fire_idle(c, grown, room, busy, w, rest, hv))
        case False{}:
          inv_settle(c, now, next, grown, room, busy, Con{w, rest}, nap, last, hv)

# ---------------------------------------------------------------------
# The start keeps the worker invariant
# ---------------------------------------------------------------------

def lt_add1(+f: Nat, +p: Nat, +g: Nat, e: {Nat.add(f, 1n+p) == g : Nat}) -> {Nat.is_lt(f, g) == True{} : Bool}:
  %e : {Nat.is_lt(f, _) == True{} : Bool}
  %N.add_succ(f, p) : {Nat.is_lt(f, _) == True{} : Bool}
  N.lt_of_add(f, p, Nat.add(f, p), {==})

def len_ids(n: Nat, +f: Nat) -> {List.length(&2, Nat, Eng.ids(n, f)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, Nat, Eng.ids(p, 1n+f)), p, len_ids(p, 1n+f))

def ids_nhas(n: Nat, +k: Nat, +f: Nat, +e: {Nat.is_lt(k, f) == True{} : Bool}) -> {L.has_nat(k, Eng.ids(n, f)) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      or_f(Nat.is_eq(k, f), L.has_nat(k, Eng.ids(p, 1n+f)), Equal.trans(Bool, Nat.is_eq(k, f), Nat.is_eq(f, k), False{}, eq_sym_b(k, f), lt_ne(k, f, e)),
        ids_nhas(p, k, 1n+f, lt_succ_r(k, f, e)))

def iok_ids(n: Nat, +f: Nat, +g: Nat, +e: {Nat.add(f, n) == g : Nat}) -> {iok(Eng.ids(n, f), [], g) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      ikmk(f, Eng.ids(p, 1n+f), [], g, lt_add1(f, p, g, e), {==}, ids_nhas(p, f, 1n+f, lt_succ(f)),
        iok_ids(p, 1n+f, g, Equal.trans(Nat, 1n+Nat.add(f, p), Nat.add(f, 1n+p), g, N.add_succ(f, p), e)))

def sub_min(w: Nat, m: Nat) -> {Nat.add(Nat.sub(m, Nat.min(w, m)), Nat.min(w, m)) == m : Nat}:
  match w m:
    case 0n 0n:
      {==}
    case 0n 1n+(+q):
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(q, 0n), q, Equal.sym(Nat, q, Nat.add(q, 0n), N.add_zero(q)))
    case 1n+v 0n:
      {==}
    case 1n+(+v) 1n+(+q):
      Equal.trans(Nat, Nat.add(Nat.sub(q, Nat.min(v, q)), 1n+Nat.min(v, q)), 1n+Nat.add(Nat.sub(q, Nat.min(v, q)), Nat.min(v, q)), 1n+q,
        Equal.sym(Nat, 1n+Nat.add(Nat.sub(q, Nat.min(v, q)), Nat.min(v, q)), Nat.add(Nat.sub(q, Nat.min(v, q)), 1n+Nat.min(v, q)), N.add_succ(Nat.sub(q, Nat.min(v, q)), Nat.min(v, q))),
        Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.sub(q, Nat.min(v, q)), Nat.min(v, q)), q, sub_min(v, q)))

def min_le(w: Nat, m: Nat) -> {Nat.is_le(Nat.min(w, m), m) == True{} : Bool}:
  match w m:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+v 0n:
      {==}
    case 1n+(+v) 1n+(+q):
      min_le(v, q)

def room0(+c: Eng.Cfg) -> {Nat.is_eq(Nat.add(r0(c), i0(c)), L.e_max(c)) == True{} : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      %Equal.sym(Nat, Nat.add(Nat.sub(m, Nat.min(w, m)), Nat.min(w, m)), m, sub_min(w, m)) : {Nat.is_eq(_, m) == True{} : Bool}
      Equal.sym(Bool, True{}, Nat.is_eq(m, m), eq_refl(m))

def le0(+c: Eng.Cfg) -> {Nat.is_le(Nat.add(0n, i0(c)), L.e_max(c)) == True{} : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      min_le(w, m)

def winv0(+c: Eng.Cfg) -> {winv(c, i0(c), r0(c), [], Eng.ids(i0(c), 0n)) == True{} : Bool}:
  wmk(c, i0(c), r0(c), [], Eng.ids(i0(c), 0n), room0(c),
    Equal.trans(Bool, Nat.is_eq(List.length(&2, Nat, Eng.ids(i0(c), 0n)), i0(c)), Nat.is_eq(i0(c), i0(c)), True{},
      Equal.cong(Nat, Bool, x => Nat.is_eq(x, i0(c)), List.length(&2, Nat, Eng.ids(i0(c), 0n)), i0(c), len_ids(i0(c), 0n)),
      Equal.sym(Bool, True{}, Nat.is_eq(i0(c), i0(c)), eq_refl(i0(c)))),
    {==}, {==}, iok_ids(i0(c), 0n, i0(c), {==}))

def is0_inv(+c: Eng.Cfg) -> {sinv(c, is0(c)) == True{} : Bool}:
  inv_idle(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, winv0(c))
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

def rr_ok(c: Eng.Cfg, +q: Nat) -> {True{} == Nat.is_eq(Nat.mod(q, Eng.targets(c)), Nat.mod(q, L.e_targets(c))) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      eq_refl(Nat.mod(q, t))

# no nap at an unbounded rate
def wn_false(c: Eng.Cfg, +now: Nat, +next: Nat, +nap: Bool, hb: {Eng.bounded(c) == False{} : Bool})
  -> {Eng.wants_nap(c, now, next, nap) == False{} : Bool}:
  %Equal.sym(Bool, Eng.bounded(c), False{}, hb) : {Bool.and(_, Bool.and(Bool.not(nap), Nat.is_gt(Eng.slot(c, next), now))) == False{} : Bool}
  {==}

def unb_bounded.go(f: Nat, p: Nat, h: {Bool.or(Nat.is_eq(f, 0n), Nat.is_eq(p, 0n)) == True{} : Bool})
  -> {Bool.and(Nat.is_gt(f, 0n), Nat.is_ge(p, f)) == False{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match p:
        case 0n:
          {==}
        case 1n+q:
          bool_absurd(Bool.and(True{}, Nat.is_ge(1n+q, 1n+g)), False{}, h)

def unb_bounded(c: Eng.Cfg, h: {Bool.or(Nat.is_eq(L.e_freq(c), 0n), Nat.is_eq(L.e_per(c), 0n)) == True{} : Bool}) -> {Eng.bounded(c) == False{} : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      unb_bounded.go(f, p, h)

def slot_eqt(c: Eng.Cfg, +i: Nat) -> {True{} == Nat.is_eq(Eng.slot(c, i), L.slot(c, i)) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      eq_refl(Nat.mul(1n+i, Nat.div(p, f)))

def wn_gt(+c: Eng.Cfg, +now: Nat, +next: Nat, +nap: Bool, en: {Eng.wants_nap(c, now, next, nap) == True{} : Bool})
  -> {True{} == Nat.is_gt(Eng.slot(c, next), now) : Bool}:
  Equal.sym(Bool, Nat.is_gt(Eng.slot(c, next), now), True{},
    and_r(Bool.not(nap), Nat.is_gt(Eng.slot(c, next), now), and_r(Eng.bounded(c), Bool.and(Bool.not(nap), Nat.is_gt(Eng.slot(c, next), now)), en)))

def due_ge(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, hb: {b == True{} : Bool}, e: {Eng.due.of(b, c, now, next) == True{} : Bool})
  -> {True{} == Nat.is_ge(now, Eng.slot(c, next)) : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, Nat.is_ge(now, Eng.slot(c, next)), True{}, e)
    case False{}:
      bool_absurd(True{}, Nat.is_ge(now, Eng.slot(c, next)), hb)

def early_ok(+c: Eng.Cfg, +now: Nat, +next: Nat, +last: Maybe<&2, Nat>, h: {L.bounded(c) == True{} : Bool}, e: {Eng.may(c, now, next, last) == True{} : Bool})
  -> {True{} == Nat.is_ge(now, L.slot(c, next)) : Bool}:
  %slot_same(c, next) : {True{} == Nat.is_ge(now, _) : Bool}
  due_ge(Eng.bounded(c), c, now, next, Equal.trans(Bool, Eng.bounded(c), L.bounded(c), True{}, bounded_same(c), h),
    and_r(Bool.not(Eng.stop_due(Eng.dur(c), last)), Eng.due(c, now, next), e))

def dl_ok.go(d: Nat, last: Maybe<&2, Nat>, h: {Nat.is_gt(d, 0n) == True{} : Bool}, e: {Bool.not(Eng.stop_due(d, last)) == True{} : Bool})
  -> {True{} == Nat.is_lt(Maybe.default(&2, Nat, last, 0n), d) : Bool}:
  match d:
    case 0n:
      bool_absurd(True{}, Nat.is_lt(Maybe.default(&2, Nat, last, 0n), 0n), h)
    case 1n+q:
      match last:
        case None{}:
          {==}
        case Some{t}:
          cmp_lt(Nat.cmp(t, 1n+q), e)

def dl_ok(c: Eng.Cfg, +last: Maybe<&2, Nat>, h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, e: {Bool.not(Eng.stop_due(Eng.dur(c), last)) == True{} : Bool})
  -> {True{} == Nat.is_lt(Maybe.default(&2, Nat, last, 0n), L.e_dur(c)) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      dl_ok.go(d, last, h, e)

def gr(s: Eng.State) -> Nat:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      grown

def bz(s: Eng.State) -> List<&2, Nat>:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      busy

def le_lt(f: Nat, +p: Nat, m: Nat, e: {Nat.is_le(Nat.add(f, 1n+p), m) == True{} : Bool}) -> {Nat.is_lt(f, m) == True{} : Bool}:
  match f m:
    case 0n 0n:
      bool_absurd(False{}, True{}, e)
    case 0n 1n+q:
      {==}
    case 1n+g 0n:
      bool_absurd(False{}, True{}, e)
    case 1n+g 1n+q:
      le_lt(g, p, q, e)

def or_ok(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# with no idle worker, every grown worker is busy
def len_g(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, hv: {winv(c, g, room, busy, []) == True{} : Bool})
  -> {Nat.is_eq(List.length(&2, Nat, busy), g) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, busy), Nat.add(List.length(&2, Nat, busy), 0n), N.add_zero(List.length(&2, Nat, busy))) : {Nat.is_eq(_, g) == True{} : Bool}
  wv2(c, g, room, busy, [], hv)
# ---------------------------------------------------------------------
# The schedule invariant (bounded rate with a duration): the last hit
# went out at least `next` intervals in, and `next` is within the schedule
# ---------------------------------------------------------------------

def ov(s: Eng.State) -> Bool:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      over

def rel(+c: Eng.Cfg, +next: Nat, last: Maybe<&2, Nat>) -> Bool:
  match last:
    case None{}:
      Nat.is_eq(next, 0n)
    case Some{t}:
      Nat.is_le(Nat.mul(next, L.interval(c)), t)

def qinv.of(b: Bool, +c: Eng.Cfg, +next: Nat, +last: Maybe<&2, Nat>) -> Bool:
  match b:
    case True{}:
      Bool.and(rel(c, next, last), Nat.is_le(next, L.scheduled(c)))
    case False{}:
      True{}

def qinv(+c: Eng.Cfg, +next: Nat, +last: Maybe<&2, Nat>) -> Bool:
  qinv.of(Bool.and(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n)), c, next, last)

def sq(+c: Eng.Cfg, s: Eng.State) -> Bool:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      qinv(c, next, last)

def rel_lt(+c: Eng.Cfg, +next: Nat, last: Maybe<&2, Nat>, +hd: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, hr: {rel(c, next, last) == True{} : Bool},
  hn: {Bool.not(Eng.stop_due(Eng.dur(c), last)) == True{} : Bool})
  -> {Nat.is_lt(Nat.mul(next, L.interval(c)), L.e_dur(c)) == True{} : Bool}:
  match last:
    case None{}:
      %Equal.sym(Nat, next, 0n, eq_of(next, 0n, hr)) : {Nat.is_lt(Nat.mul(_, L.interval(c)), L.e_dur(c)) == True{} : Bool}
      gt0_lt(L.e_dur(c), hd)
    case Some{+t}:
      le_lt_trans(Nat.mul(next, L.interval(c)), t, L.e_dur(c), hr,
        Equal.sym(Bool, True{}, Nat.is_lt(t, L.e_dur(c)), dl_ok(c, Some{t}, hd, hn)))

def bnd_e(+g: Nat, +p: Nat, hb: {Nat.is_ge(p, 1n+g) == True{} : Bool}) -> {Nat.is_le(Nat.mul(1n, 1n+g), p) == True{} : Bool}:
  %N.add_zero(g) : {Nat.is_le(1n+_, p) == True{} : Bool}
  Equal.trans(Bool, Nat.is_le(1n+g, p), Nat.is_ge(p, 1n+g), True{}, Equal.sym(Bool, Nat.is_ge(p, 1n+g), Nat.is_le(1n+g, p), ge_le(p, 1n+g)), hb)

# a bounded rate's interval is at least 1 ns
def bnd_q(f: Nat, +p: Nat, hb: {Bool.and(Nat.is_gt(f, 0n), Nat.is_ge(p, f)) == True{} : Bool}) -> {Nat.is_le(1n, Nat.div(p, f)) == True{} : Bool}:
  match f:
    case 0n:
      bool_absurd(Nat.is_le(1n, Nat.div(p, 0n)), True{}, hb)
    case 1n+(+g):
      mul_le_div(1n, p, g, bnd_e(g, p, hb))

def sched_q(q: Nat, +k: Nat, +d: Nat, e1: {Nat.is_le(1n, q) == True{} : Bool}, e: {Nat.is_lt(Nat.mul(k, q), d) == True{} : Bool})
  -> {Nat.is_le(1n+k, Nat.div(Nat.add(d, Nat.sub(q, 1n)), q)) == True{} : Bool}:
  match q:
    case 0n:
      bool_absurd(Nat.is_le(1n+k, Nat.div(Nat.add(d, Nat.sub(0n, 1n)), 0n)), True{}, e1)
    case 1n+(+j):
      %sub_zero(j) : {Nat.is_le(1n+k, Nat.div(Nat.add(d, _), 1n+j)) == True{} : Bool}
      sched_ok(k, j, d, e)

def sched_c(+c: Eng.Cfg, +k: Nat, hb: {L.bounded(c) == True{} : Bool}, e: {Nat.is_lt(Nat.mul(k, L.interval(c)), L.e_dur(c)) == True{} : Bool})
  -> {Nat.is_le(1n+k, L.scheduled(c)) == True{} : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      sched_q(Nat.div(p, f), k, d, bnd_q(f, p, hb), e)

def qfire.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +last: Maybe<&2, Nat>, +eb: {Bool.and(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n)) == b : Bool},
  +eok: {Eng.may(c, now, next, last) == True{} : Bool}, +hq: {qinv.of(b, c, next, last) == True{} : Bool})
  -> {qinv.of(b, c, 1n+next, Some{now}) == True{} : Bool}:
  match b:
    case True{}:
      +hb = and_l(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n), eb)
      +hd = and_r(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n), eb)
      and_i(rel(c, 1n+next, Some{now}), Nat.is_le(1n+next, L.scheduled(c)),
        Equal.trans(Bool, Nat.is_le(L.slot(c, next), now), Nat.is_ge(now, L.slot(c, next)), True{},
          Equal.sym(Bool, Nat.is_ge(now, L.slot(c, next)), Nat.is_le(L.slot(c, next), now), ge_le(now, L.slot(c, next))),
          Equal.sym(Bool, True{}, Nat.is_ge(now, L.slot(c, next)), early_ok(c, now, next, last, hb, eok))),
        sched_c(c, next, hb, rel_lt(c, next, last, hd, and_l(rel(c, next, last), Nat.is_le(next, L.scheduled(c)), hq),
          and_l(Bool.not(Eng.stop_due(Eng.dur(c), last)), Eng.due(c, now, next), eok))))
    case False{}:
      {==}

def qfire(+c: Eng.Cfg, +now: Nat, +next: Nat, +last: Maybe<&2, Nat>, eok: {Eng.may(c, now, next, last) == True{} : Bool}, hq: {qinv(c, next, last) == True{} : Bool})
  -> {qinv(c, 1n+next, Some{now}) == True{} : Bool}:
  qfire.of(Bool.and(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n)), c, now, next, last, {==}, eok, hq)

def q_settle.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  hq: {qinv(c, next, last) == True{} : Bool})
  -> {sq(c, Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  match b:
    case True{}:
      hq
    case False{}:
      hq

def q_settle.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  hq: {qinv(c, next, last) == True{} : Bool})
  -> {sq(c, Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  match b:
    case True{}:
      hq
    case False{}:
      q_settle.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, hq)

def q_settle(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  hq: {qinv(c, next, last) == True{} : Bool})
  -> {sq(c, Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  q_settle.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, hq)

def q_grow(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  hq: {qinv(c, next, last) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {sq(c, Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)) == True{} : Bool}:
  match room:
    case 0n:
      q_settle(c, now, next, grown, 0n, busy, [], nap, last, hq)
    case 1n+(+r):
      match ok:
        case True{}:
          q_grow(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, qfire(c, now, next, last, eok, hq), {==})
        case False{}:
          q_settle(c, now, next, grown, 1n+r, busy, [], nap, last, hq)

def q_idle(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  hq: {qinv(c, next, last) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {sq(c, Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)) == True{} : Bool}:
  match idle:
    case Nil{}:
      q_grow(room, ok, c, now, next, grown, busy, nap, last, hq, eok)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          q_idle(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, qfire(c, now, next, last, eok, hq), {==})
        case False{}:
          q_settle(c, now, next, grown, room, busy, Con{w, rest}, nap, last, hq)

def q0.of(b: Bool, +c: Eng.Cfg) -> {qinv.of(b, c, 0n, None{}) == True{} : Bool}:
  match b:
    case True{}:
      le_zero(L.scheduled(c))
    case False{}:
      {==}

def is0_q(+c: Eng.Cfg) -> {sq(c, is0(c)) == True{} : Bool}:
  q_idle(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, q0.of(Bool.and(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n)), c), {==})

# the quit's accounting
def sd_pos(c: Eng.Cfg, last: Maybe<&2, Nat>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}) -> {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      match last:
        case None{}:
          bool_absurd(Nat.is_gt(d, 0n), True{}, es)
        case Some{u}:
          and_l(Nat.is_gt(d, 0n), Nat.is_ge(u, d), es)

def stopdue_same(c: Eng.Cfg, last: Maybe<&2, Nat>) -> {Eng.stop_due(Eng.dur(c), last) == L.stop_due(L.e_dur(c), last) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      match last:
        case None{}:
          {==}
        case Some{u}:
          {==}

def sched_same(c: Eng.Cfg) -> {Eng.scheduled(c) == L.scheduled(c) : Nat}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}

def drop_ok.of(b: Bool, +c: Eng.Cfg, +next: Nat, +last: Maybe<&2, Nat>, eb: {L.bounded(c) == b : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool},
  hq: {qinv(c, next, last) == True{} : Bool})
  -> {True{} == L.pick(Bool, b, Nat.is_eq(Nat.add(next, Eng.dropped.of(b, c, next)), L.scheduled(c)), Nat.is_eq(Eng.dropped.of(b, c, next), 0n)) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, Eng.scheduled(c), L.scheduled(c), sched_same(c)) : {True{} == Nat.is_eq(Nat.add(next, Nat.sub(_, next)), L.scheduled(c)) : Bool}
      %Equal.sym(Nat, Nat.add(next, Nat.sub(L.scheduled(c), next)), L.scheduled(c),
        add_sub(next, L.scheduled(c), and_r(rel(c, next, last), Nat.is_le(next, L.scheduled(c)),
          Equal.trans(Bool, qinv.of(True{}, c, next, last), qinv(c, next, last), True{},
            Equal.cong(Bool, Bool, x => qinv.of(x, c, next, last), True{}, Bool.and(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n)),
              Equal.sym(Bool, Bool.and(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n)), True{}, and_i(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n), eb, sd_pos(c, last, es)))),
            hq))))
        : {True{} == Nat.is_eq(_, L.scheduled(c)) : Bool}
      eq_refl(L.scheduled(c))
    case False{}:
      {==}

def drop_ok(+c: Eng.Cfg, +next: Nat, +last: Maybe<&2, Nat>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, hq: {qinv(c, next, last) == True{} : Bool})
  -> {True{} == L.pick(Bool, L.bounded(c), Nat.is_eq(Nat.add(next, Eng.dropped(c, next)), L.scheduled(c)), Nat.is_eq(Eng.dropped(c, next), 0n)) : Bool}:
  %Equal.sym(Bool, Eng.bounded(c), L.bounded(c), bounded_same(c))
    : {True{} == L.pick(Bool, L.bounded(c), Nat.is_eq(Nat.add(next, Eng.dropped.of(_, c, next)), L.scheduled(c)), Nat.is_eq(Eng.dropped.of(_, c, next), 0n)) : Bool}
  drop_ok.of(L.bounded(c), c, next, last, {==}, es, hq)
# ---------------------------------------------------------------------
# Liveness: after every event the engine waits legitimately
# ---------------------------------------------------------------------

def np(s: Eng.State) -> Bool:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      nap

def allb(+c: Eng.Cfg, +grown: Nat, +busy: List<&2, Nat>) -> Bool:
  Bool.and(Nat.is_gt(List.length(&2, Nat, busy), 0n), Bool.and(Nat.is_eq(List.length(&2, Nat, busy), grown), Nat.is_eq(grown, L.e_max(c))))

def spend(+c: Eng.Cfg, s: Eng.State) -> Bool:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      L.pending(c, nap, grown, busy, over, last)

def or1(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      bool_absurd(b, True{}, e)

def or_true_l(a: Bool, -b: Bool, eb: {b == False{} : Bool}, e: {Bool.or(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, eb), e)

def ge_false_gt(a: Nat, b: Nat, e: {Nat.is_ge(a, b) == False{} : Bool}) -> {Nat.is_gt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      bool_absurd(False{}, True{}, Equal.sym(Bool, True{}, False{}, e))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      bool_absurd(False{}, True{}, Equal.sym(Bool, True{}, False{}, e))
    case 1n+p 1n+q:
      ge_false_gt(p, q, e)

def ge1_gt0(m: Nat, e: {Nat.is_ge(m, 1n) == True{} : Bool}) -> {Nat.is_gt(m, 0n) == True{} : Bool}:
  match m:
    case 0n:
      e
    case 1n+q:
      {==}

def nap_of_w2(nap: Bool, -y: Bool, ey: {y == True{} : Bool}, e: {Bool.and(Bool.not(nap), y) == False{} : Bool}) -> {nap == True{} : Bool}:
  match nap:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, False{}, y, True{}, Equal.sym(Bool, y, False{}, e), ey)

# a hit not due, and no nap wanted: a nap is open
def nap_open(x: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +nap: Bool, ed: {Eng.due.of(x, c, now, next) == False{} : Bool},
  en: {Bool.and(x, Bool.and(Bool.not(nap), Nat.is_gt(Eng.slot(c, next), now))) == False{} : Bool}) -> {nap == True{} : Bool}:
  match x:
    case True{}:
      nap_of_w2(nap, Nat.is_gt(Eng.slot(c, next), now), ge_false_gt(now, Eng.slot(c, next), ed), en)
    case False{}:
      bool_absurd(nap, True{}, Equal.sym(Bool, True{}, False{}, ed))

def live_core.of(ab: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  eab: {allb(c, grown, busy) == ab : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool},
  en: {Eng.wants_nap(c, now, next, nap) == False{} : Bool}, h: {Bool.or(Bool.not(Eng.may(c, now, next, last)), allb(c, grown, busy)) == True{} : Bool})
  -> {Bool.or(nap, allb(c, grown, busy)) == True{} : Bool}:
  match ab:
    case True{}:
      or_ok(nap, allb(c, grown, busy), eab)
    case False{}:
      %Equal.sym(Bool, nap, True{}, nap_open(Eng.bounded(c), c, now, next, nap,
          Equal.trans(Bool, Eng.due(c, now, next), Eng.may(c, now, next, last), False{},
            Equal.cong(Bool, Bool, x => Bool.and(Bool.not(x), Eng.due(c, now, next)), False{}, Eng.stop_due(Eng.dur(c), last), Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, es)),
            not_t(Eng.may(c, now, next, last), or_true_l(Bool.not(Eng.may(c, now, next, last)), allb(c, grown, busy), eab, h))),
          en))
        : {Bool.or(_, allb(c, grown, busy)) == True{} : Bool}
      {==}

def sd_false(c: Eng.Cfg, +last: Maybe<&2, Nat>, es: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}) -> {False{} == L.stop_due(L.e_dur(c), last) : Bool}:
  Equal.trans(Bool, False{}, Eng.stop_due(Eng.dur(c), last), L.stop_due(L.e_dur(c), last), Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, es), stopdue_same(c, last))

def sd_true(c: Eng.Cfg, +last: Maybe<&2, Nat>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}) -> {True{} == L.stop_due(L.e_dur(c), last) : Bool}:
  Equal.trans(Bool, True{}, Eng.stop_due(Eng.dur(c), last), L.stop_due(L.e_dur(c), last), Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), True{}, es), stopdue_same(c, last))

def pend_nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +es: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, en: {Eng.wants_nap(c, now, next, nap) == b : Bool},
  h: {Bool.or(Bool.not(Eng.may(c, now, next, last)), allb(c, grown, busy)) == True{} : Bool})
  -> {spend(c, Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  match b:
    case True{}:
      %sd_false(c, last, es) : {Bool.or(False{}, L.pick(Bool, _, Nat.is_gt(List.length(&2, Nat, busy), 0n), Bool.or(True{}, allb(c, grown, busy)))) == True{} : Bool}
      {==}
    case False{}:
      %sd_false(c, last, es) : {Bool.or(False{}, L.pick(Bool, _, Nat.is_gt(List.length(&2, Nat, busy), 0n), Bool.or(nap, allb(c, grown, busy)))) == True{} : Bool}
      live_core.of(allb(c, grown, busy), c, now, next, grown, busy, nap, last, {==}, es, en, h)

def pend_quit(busy: List<&2, Nat>, +c: Eng.Cfg, +grown: Nat, +nap: Bool, +last: Maybe<&2, Nat>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool})
  -> {L.pending(c, nap, grown, busy, List.is_empty(&2, Nat, busy), last) == True{} : Bool}:
  match busy:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %sd_true(c, last, es) : {Bool.or(False{}, L.pick(Bool, _, Nat.is_gt(1n+List.length(&2, Nat, r), 0n), Bool.or(nap, allb(c, grown, Con{x, r})))) == True{} : Bool}
      {==}

def pend_settle.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  es: {Eng.stop_due(Eng.dur(c), last) == b : Bool}, h: {Bool.or(Bool.not(Eng.may(c, now, next, last)), allb(c, grown, busy)) == True{} : Bool})
  -> {spend(c, Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  match b:
    case True{}:
      pend_quit(busy, c, grown, nap, last, es)
    case False{}:
      pend_nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, es, {==}, h)

def pend_settle(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  h: {Bool.or(Bool.not(Eng.may(c, now, next, last)), allb(c, grown, busy)) == True{} : Bool})
  -> {spend(c, Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  pend_settle.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, {==}, h)

# no room and no idle worker: every allowed worker is busy
def allb0(+c: Eng.Cfg, +g: Nat, +busy: List<&2, Nat>, hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {winv(c, g, 0n, busy, []) == True{} : Bool})
  -> {allb(c, g, busy) == True{} : Bool}:
  +el = len_g(c, g, 0n, busy, hv)
  +em = wv1(c, g, 0n, busy, [], hv)
  and_i(Nat.is_gt(List.length(&2, Nat, busy), 0n), Bool.and(Nat.is_eq(List.length(&2, Nat, busy), g), Nat.is_eq(g, L.e_max(c))),
    Equal.trans(Bool, Nat.is_gt(List.length(&2, Nat, busy), 0n), Nat.is_gt(L.e_max(c), 0n), True{},
      Equal.cong(Nat, Bool, x => Nat.is_gt(x, 0n), List.length(&2, Nat, busy), L.e_max(c),
        Equal.trans(Nat, List.length(&2, Nat, busy), g, L.e_max(c), eq_of(List.length(&2, Nat, busy), g, el), eq_of(g, L.e_max(c), em))),
      ge1_gt0(L.e_max(c), and_r(Nat.is_ge(L.e_targets(c), 1n), Nat.is_ge(L.e_max(c), 1n),
        and_l(Bool.and(Nat.is_ge(L.e_targets(c), 1n), Nat.is_ge(L.e_max(c), 1n)),
          Bool.or(Bool.or(Nat.is_eq(L.e_freq(c), 0n), Nat.is_eq(L.e_per(c), 0n)), Nat.is_ge(L.e_per(c), L.e_freq(c))), hok)))),
    and_i(Nat.is_eq(List.length(&2, Nat, busy), g), Nat.is_eq(g, L.e_max(c)), el, em))

def pend_grow(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {winv(c, grown, room, busy, []) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {spend(c, Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)) == True{} : Bool}:
  match room:
    case 0n:
      pend_settle(c, now, next, grown, 0n, busy, [], nap, last, or_ok(Bool.not(Eng.may(c, now, next, last)), allb(c, grown, busy), allb0(c, grown, busy, hok, hv)))
    case 1n+(+r):
      match ok:
        case True{}:
          pend_grow(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, hok, wv_fire_grow(c, grown, r, busy, hv), {==})
        case False{}:
          pend_settle(c, now, next, grown, 1n+r, busy, [], nap, last, or1(Bool.not(Eng.may(c, now, next, last)), allb(c, grown, busy), not_i(Eng.may(c, now, next, last), eok)))

def pend_idle(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {spend(c, Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)) == True{} : Bool}:
  match idle:
    case Nil{}:
      pend_grow(room, ok, c, now, next, grown, busy, nap, last, hok, hv, eok)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          pend_idle(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, hok, wv_fire_idle(c, grown, room, busy, w, rest, hv), {==})
        case False{}:
          pend_settle(c, now, next, grown, room, busy, Con{w, rest}, nap, last, or1(Bool.not(Eng.may(c, now, next, last)), allb(c, grown, busy), not_i(Eng.may(c, now, next, last), eok)))
# ---------------------------------------------------------------------
# eng_ends, part 1: the engine's state after a list of events, and what
# the timeline's readers (has_quit, busy_of, nap_of) see of it
# ---------------------------------------------------------------------

def fin(evs: List<&2, Eng.Ev>, +c: Eng.Cfg, +s: Eng.State) -> Eng.State:
  match evs:
    case Nil{}:
      s
    case Con{+e, +rest}:
      fin(rest, c, L.st_of(Eng.step(c, s, e)))

def hqc(T: List<&2, L.Item>, o: Bool) -> Bool:
  Bool.or(o, L.has_quit(T))

def fin_app(A: List<&2, Eng.Ev>, +B: List<&2, Eng.Ev>, +c: Eng.Cfg, +s: Eng.State)
  -> {fin(List.append(&2, Eng.Ev, A, B), c, s) == fin(B, c, fin(A, c, s)) : Eng.State}:
  match A:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      fin_app(rest, B, c, L.st_of(Eng.step(c, s, e)))

def ov_abs(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, h: {ov(s) == True{} : Bool}) -> {ov(fin(evs, c, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  ov_abs(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, {==})
                case False{}:
                  bool_absurd(ov(fin(rest, c, L.st_of(Eng.step(c, Eng.EState{now, next, grown, room, busy, idle, nap, last, False{}}, Eng.Clock{t})))), True{}, h)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  ov_abs(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, {==})
                case False{}:
                  bool_absurd(ov(fin(rest, c, L.st_of(Eng.step(c, Eng.EState{now, next, grown, room, busy, idle, nap, last, False{}}, Eng.Freed{w, t})))), True{}, h)

def app_assoc(xs: List<&2, L.Item>, +ys: List<&2, L.Item>, +zs: List<&2, L.Item>)
  -> {List.append(&2, L.Item, List.append(&2, L.Item, xs, ys), zs) == List.append(&2, L.Item, xs, List.append(&2, L.Item, ys, zs)) : List<&2, L.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(List<&2, L.Item>, List<&2, L.Item>, l => Con{x, l}, List.append(&2, L.Item, List.append(&2, L.Item, rest, ys), zs),
        List.append(&2, L.Item, rest, List.append(&2, L.Item, ys, zs)), app_assoc(rest, ys, zs))

def steps_app(A: List<&2, Eng.Ev>, +B: List<&2, Eng.Ev>, +c: Eng.Cfg, +s: Eng.State)
  -> {L.steps(List.append(&2, Eng.Ev, A, B), c, s) == List.append(&2, L.Item, L.steps(A, c, s), L.steps(B, c, fin(A, c, s))) : List<&2, L.Item>}:
  match A:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      %Equal.sym(List<&2, L.Item>, L.steps(List.append(&2, Eng.Ev, rest, B), c, L.st_of(Eng.step(c, s, e))),
          List.append(&2, L.Item, L.steps(rest, c, L.st_of(Eng.step(c, s, e))), L.steps(B, c, fin(rest, c, L.st_of(Eng.step(c, s, e))))),
          steps_app(rest, B, c, L.st_of(Eng.step(c, s, e))))
        : {Con{L.IEv{e}, List.append(&2, L.Item, L.cmds_items(L.cs_of(Eng.step(c, s, e))), _)}
          == Con{L.IEv{e}, List.append(&2, L.Item, List.append(&2, L.Item, L.cmds_items(L.cs_of(Eng.step(c, s, e))), L.steps(rest, c, L.st_of(Eng.step(c, s, e)))),
            L.steps(B, c, fin(rest, c, L.st_of(Eng.step(c, s, e)))))} : List<&2, L.Item>}
      %app_assoc(L.cmds_items(L.cs_of(Eng.step(c, s, e))), L.steps(rest, c, L.st_of(Eng.step(c, s, e))), L.steps(B, c, fin(rest, c, L.st_of(Eng.step(c, s, e)))))
        : {Con{L.IEv{e}, _}
          == Con{L.IEv{e}, List.append(&2, L.Item, List.append(&2, L.Item, L.cmds_items(L.cs_of(Eng.step(c, s, e))), L.steps(rest, c, L.st_of(Eng.step(c, s, e)))),
            L.steps(B, c, fin(rest, c, L.st_of(Eng.step(c, s, e)))))} : List<&2, L.Item>}
      {==}

def tl_app(+c: Eng.Cfg, +A: List<&2, Eng.Ev>, +B: List<&2, Eng.Ev>)
  -> {L.timeline(c, List.append(&2, Eng.Ev, A, B)) == List.append(&2, L.Item, L.timeline(c, A), L.steps(B, c, fin(A, c, is0(c)))) : List<&2, L.Item>}:
  %Equal.sym(List<&2, L.Item>, L.steps(List.append(&2, Eng.Ev, A, B), c, is0(c)), List.append(&2, L.Item, L.steps(A, c, is0(c)), L.steps(B, c, fin(A, c, is0(c)))), steps_app(A, B, c, is0(c)))
    : {List.append(&2, L.Item, L.cmds_items(L.cs_of(Eng.start(c))), _) == List.append(&2, L.Item, L.timeline(c, A), L.steps(B, c, fin(A, c, is0(c)))) : List<&2, L.Item>}
  %app_assoc(L.cmds_items(L.cs_of(Eng.start(c))), L.steps(A, c, is0(c)), L.steps(B, c, fin(A, c, is0(c))))
    : {_ == List.append(&2, L.Item, L.timeline(c, A), L.steps(B, c, fin(A, c, is0(c)))) : List<&2, L.Item>}
  {==}

def nap_app(xs: List<&2, L.Item>, +ys: List<&2, L.Item>, +n: Maybe<&2, Nat>)
  -> {L.nap_of(List.append(&2, L.Item, xs, ys), n) == L.nap_of(ys, L.nap_of(xs, n)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      match x:
        case L.IEv{+e}:
          match e:
            case Eng.Clock{+t}:
              nap_app(rest, ys, None{})
            case Eng.Freed{+w, +t}:
              nap_app(rest, ys, n)
        case L.ICmd{+k}:
          match k:
            case Eng.Nap{+u}:
              nap_app(rest, ys, Some{u})
            case Eng.Grow{+w}:
              nap_app(rest, ys, n)
            case Eng.Fire{+w, +q, +g, +t}:
              nap_app(rest, ys, n)
            case Eng.Quit{+a, +d}:
              nap_app(rest, ys, n)

# ---------------------------------------------------------------------
# eng: seq
# ---------------------------------------------------------------------

def seqA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, n: Nat) -> Bool:
  L.chk_seq(List.append(&2, L.Item, L.cmds_items(xs), T), n)

def settle_seq.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_seq(T, nx(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == seqA(Eng.settle.nap_cs(b, c, next), T, next) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_seq.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_seq(T, nx(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == seqA(Eng.settle.quit_cs(b, c, next), T, next) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_seq.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_seq(T, nx(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == seqA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, next) : Bool}:
  match b:
    case True{}:
      settle_seq.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, es, {==})
    case False{}:
      settle_seq.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def settle_seq(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_seq(T, nx(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == seqA(Eng.settle_cs(c, now, next, busy, nap, last), T, next) : Bool}:
  settle_seq.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def grow_seq(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_seq(T, nx(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == seqA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, next) : Bool}:
  match room:
    case 0n:
      settle_seq(c, now, next, grown, 0n, busy, [], nap, last, T)
    case 1n+(+r):
      match ok:
        case True{}:
          %eq_refl(next) : {L.chk_seq(T, nx(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}))) == Bool.and(_, seqA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, 1n+next)) : Bool}
          grow_seq(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T)
        case False{}:
          settle_seq(c, now, next, grown, 1n+r, busy, [], nap, last, T)

def idle_seq(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_seq(T, nx(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == seqA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, next) : Bool}:
  match idle:
    case Nil{}:
      grow_seq(room, ok, c, now, next, grown, busy, nap, last, T)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          %eq_refl(next) : {L.chk_seq(T, nx(Eng.idle_st(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}))) == Bool.and(_, seqA(Eng.idle_cs(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}), T, 1n+next)) : Bool}
          idle_seq(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T)
        case False{}:
          settle_seq(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T)

def steps_seq(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg) -> {L.chk_seq(L.steps(evs, c, s), nx(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_seq(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c)
                case False{}:
                  %idle_seq(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : {_ == True{} : Bool}
                  steps_seq(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_seq(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c)
                case False{}:
                  %idle_seq(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : {_ == True{} : Bool}
                  steps_seq(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c)

def pre_seq(n: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +k: Nat)
  -> {seqA(X, T, k) == seqA(List.append(&2, Eng.Cmd, Eng.grows(n, from), X), T, k) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pre_seq(p, 1n+from, X, T, k)

def L.eng_seq(c, evs):
  %pre_seq(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), 0n) : {_ == True{} : Bool}
  %idle_seq(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c))) : {_ == True{} : Bool}
  steps_seq(evs, is0(c), c)

# ---------------------------------------------------------------------
# eng: rr
# ---------------------------------------------------------------------

def rrA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, n: Nat) -> Bool:
  L.chk_rr(List.append(&2, L.Item, L.cmds_items(xs), T), n)

def settle_rr.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_rr(T, L.e_targets(c)) == rrA(Eng.settle.nap_cs(b, c, next), T, L.e_targets(c)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_rr.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_rr(T, L.e_targets(c)) == rrA(Eng.settle.quit_cs(b, c, next), T, L.e_targets(c)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_rr.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_rr(T, L.e_targets(c)) == rrA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, L.e_targets(c)) : Bool}:
  match b:
    case True{}:
      settle_rr.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, es, {==})
    case False{}:
      settle_rr.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def settle_rr(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_rr(T, L.e_targets(c)) == rrA(Eng.settle_cs(c, now, next, busy, nap, last), T, L.e_targets(c)) : Bool}:
  settle_rr.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def grow_rr(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_rr(T, L.e_targets(c)) == rrA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, L.e_targets(c)) : Bool}:
  match room:
    case 0n:
      settle_rr(c, now, next, grown, 0n, busy, [], nap, last, T)
    case 1n+(+r):
      match ok:
        case True{}:
          %rr_ok(c, next) : {L.chk_rr(T, L.e_targets(c)) == Bool.and(_, rrA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, L.e_targets(c))) : Bool}
          grow_rr(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T)
        case False{}:
          settle_rr(c, now, next, grown, 1n+r, busy, [], nap, last, T)

def idle_rr(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_rr(T, L.e_targets(c)) == rrA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, L.e_targets(c)) : Bool}:
  match idle:
    case Nil{}:
      grow_rr(room, ok, c, now, next, grown, busy, nap, last, T)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          %rr_ok(c, next) : {L.chk_rr(T, L.e_targets(c)) == Bool.and(_, rrA(Eng.idle_cs(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}), T, L.e_targets(c))) : Bool}
          idle_rr(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T)
        case False{}:
          settle_rr(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T)

def steps_rr(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg) -> {L.chk_rr(L.steps(evs, c, s), L.e_targets(c)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_rr(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c)
                case False{}:
                  %idle_rr(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : {_ == True{} : Bool}
                  steps_rr(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_rr(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c)
                case False{}:
                  %idle_rr(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : {_ == True{} : Bool}
                  steps_rr(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c)

def pre_rr(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {rrA(X, T, L.e_targets(c)) == rrA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, L.e_targets(c)) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_rr(p, 1n+from, X, T, c)

def L.eng_round_robin(c, evs, h):
  %pre_rr(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_rr(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c))) : {_ == True{} : Bool}
  steps_rr(evs, is0(c), c)

# ---------------------------------------------------------------------
# eng: now
# ---------------------------------------------------------------------

def nowA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, n: Nat) -> Bool:
  L.chk_now(List.append(&2, L.Item, L.cmds_items(xs), T), n)

def settle_now.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_now(T, nw(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == nowA(Eng.settle.nap_cs(b, c, next), T, now) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_now.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_now(T, nw(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == nowA(Eng.settle.quit_cs(b, c, next), T, now) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_now.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_now(T, nw(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == nowA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, now) : Bool}:
  match b:
    case True{}:
      settle_now.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, es, {==})
    case False{}:
      settle_now.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def settle_now(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_now(T, nw(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == nowA(Eng.settle_cs(c, now, next, busy, nap, last), T, now) : Bool}:
  settle_now.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def grow_now(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_now(T, nw(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == nowA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, now) : Bool}:
  match room:
    case 0n:
      settle_now(c, now, next, grown, 0n, busy, [], nap, last, T)
    case 1n+(+r):
      match ok:
        case True{}:
          %eq_refl(now) : {L.chk_now(T, nw(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}))) == Bool.and(_, nowA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, now)) : Bool}
          grow_now(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T)
        case False{}:
          settle_now(c, now, next, grown, 1n+r, busy, [], nap, last, T)

def idle_now(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_now(T, nw(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == nowA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, now) : Bool}:
  match idle:
    case Nil{}:
      grow_now(room, ok, c, now, next, grown, busy, nap, last, T)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          %eq_refl(now) : {L.chk_now(T, nw(Eng.idle_st(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}))) == Bool.and(_, nowA(Eng.idle_cs(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}), T, now)) : Bool}
          idle_now(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T)
        case False{}:
          settle_now(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T)

def steps_now(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg) -> {L.chk_now(L.steps(evs, c, s), nw(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_now(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c)
                case False{}:
                  %idle_now(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : {_ == True{} : Bool}
                  steps_now(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_now(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c)
                case False{}:
                  %idle_now(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : {_ == True{} : Bool}
                  steps_now(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c)

def pre_now(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {nowA(X, T, 0n) == nowA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, 0n) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_now(p, 1n+from, X, T, c)

def L.eng_now(c, evs):
  %pre_now(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_now(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c))) : {_ == True{} : Bool}
  steps_now(evs, is0(c), c)

# ---------------------------------------------------------------------
# eng: unb
# ---------------------------------------------------------------------

def unbA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>) -> Bool:
  L.no_nap(List.append(&2, L.Item, L.cmds_items(xs), T))

def settle_unb.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hb: {Eng.bounded(c) == False{} : Bool}, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.no_nap(T) == unbA(Eng.settle.nap_cs(b, c, next), T) : Bool}:
  match b:
    case True{}:
      bool_absurd(L.no_nap(T), unbA(Eng.settle.nap_cs(True{}, c, next), T), Equal.trans(Bool, False{}, Eng.wants_nap(c, now, next, nap), True{}, Equal.sym(Bool, Eng.wants_nap(c, now, next, nap), False{}, wn_false(c, now, next, nap, hb)), en))
    case False{}:
      {==}

def settle_unb.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hb: {Eng.bounded(c) == False{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.no_nap(T) == unbA(Eng.settle.quit_cs(b, c, next), T) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_unb.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hb: {Eng.bounded(c) == False{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.no_nap(T) == unbA(Eng.settle.of_cs(b, c, now, next, busy, nap), T) : Bool}:
  match b:
    case True{}:
      settle_unb.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, hb, es, {==})
    case False{}:
      settle_unb.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, hb, {==})

def settle_unb(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hb: {Eng.bounded(c) == False{} : Bool})
  -> {L.no_nap(T) == unbA(Eng.settle_cs(c, now, next, busy, nap, last), T) : Bool}:
  settle_unb.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, hb, {==})

def grow_unb(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hb: {Eng.bounded(c) == False{} : Bool})
  -> {L.no_nap(T) == unbA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T) : Bool}:
  match room:
    case 0n:
      settle_unb(c, now, next, grown, 0n, busy, [], nap, last, T, hb)
    case 1n+(+r):
      match ok:
        case True{}:
          grow_unb(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T, hb)
        case False{}:
          settle_unb(c, now, next, grown, 1n+r, busy, [], nap, last, T, hb)

def idle_unb(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hb: {Eng.bounded(c) == False{} : Bool})
  -> {L.no_nap(T) == unbA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T) : Bool}:
  match idle:
    case Nil{}:
      grow_unb(room, ok, c, now, next, grown, busy, nap, last, T, hb)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          idle_unb(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T, hb)
        case False{}:
          settle_unb(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T, hb)

def steps_unb(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, +hb: {Eng.bounded(c) == False{} : Bool}) -> {L.no_nap(L.steps(evs, c, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_unb(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, hb)
                case False{}:
                  %idle_unb(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last)), hb) : {_ == True{} : Bool}
                  steps_unb(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c, hb)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_unb(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, hb)
                case False{}:
                  %idle_unb(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), hb) : {_ == True{} : Bool}
                  steps_unb(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c, hb)

def pre_unb(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {unbA(X, T) == unbA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_unb(p, 1n+from, X, T, c)

def L.eng_unbounded(c, evs, h):
  +hb = unb_bounded(c, h)
  %pre_unb(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_unb(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), hb) : {_ == True{} : Bool}
  steps_unb(evs, is0(c), c, hb)

# ---------------------------------------------------------------------
# eng: nap
# ---------------------------------------------------------------------

def napA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, c2: Eng.Cfg, n: Nat, t: Nat) -> Bool:
  L.chk_nap(List.append(&2, L.Item, L.cmds_items(xs), T), c2, n, t)

def settle_nap.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_nap(T, c, nx(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), nw(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == napA(Eng.settle.nap_cs(b, c, next), T, c, next, now) : Bool}:
  match b:
    case True{}:
      %slot_eqt(c, next) : {L.chk_nap(T, c, next, now) == Bool.and(Bool.and(_, Nat.is_gt(Eng.slot(c, next), now)), L.chk_nap(T, c, next, now)) : Bool}
      %wn_gt(c, now, next, nap, en) : {L.chk_nap(T, c, next, now) == Bool.and(Bool.and(True{}, _), L.chk_nap(T, c, next, now)) : Bool}
      {==}
    case False{}:
      {==}

def settle_nap.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_nap(T, c, nx(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), nw(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == napA(Eng.settle.quit_cs(b, c, next), T, c, next, now) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_nap.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_nap(T, c, nx(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), nw(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == napA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, c, next, now) : Bool}:
  match b:
    case True{}:
      settle_nap.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, es, {==})
    case False{}:
      settle_nap.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def settle_nap(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_nap(T, c, nx(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), nw(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == napA(Eng.settle_cs(c, now, next, busy, nap, last), T, c, next, now) : Bool}:
  settle_nap.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def grow_nap(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_nap(T, c, nx(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), nw(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == napA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, c, next, now) : Bool}:
  match room:
    case 0n:
      settle_nap(c, now, next, grown, 0n, busy, [], nap, last, T)
    case 1n+(+r):
      match ok:
        case True{}:
          grow_nap(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T)
        case False{}:
          settle_nap(c, now, next, grown, 1n+r, busy, [], nap, last, T)

def idle_nap(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_nap(T, c, nx(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), nw(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == napA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, c, next, now) : Bool}:
  match idle:
    case Nil{}:
      grow_nap(room, ok, c, now, next, grown, busy, nap, last, T)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          idle_nap(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T)
        case False{}:
          settle_nap(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T)

def steps_nap(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg) -> {L.chk_nap(L.steps(evs, c, s), c, nx(s), nw(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_nap(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c)
                case False{}:
                  %idle_nap(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : {_ == True{} : Bool}
                  steps_nap(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_nap(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c)
                case False{}:
                  %idle_nap(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : {_ == True{} : Bool}
                  steps_nap(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c)

def pre_nap(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {napA(X, T, c, 0n, 0n) == napA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, c, 0n, 0n) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_nap(p, 1n+from, X, T, c)

def L.eng_nap(c, evs, h):
  %pre_nap(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_nap(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c))) : {_ == True{} : Bool}
  steps_nap(evs, is0(c), c)

# ---------------------------------------------------------------------
# eng: early
# ---------------------------------------------------------------------

def earlyA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, c2: Eng.Cfg) -> Bool:
  L.chk_early(List.append(&2, L.Item, L.cmds_items(xs), T), c2)

def settle_early.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {L.bounded(c) == True{} : Bool}, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_early(T, c) == earlyA(Eng.settle.nap_cs(b, c, next), T, c) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_early.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {L.bounded(c) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_early(T, c) == earlyA(Eng.settle.quit_cs(b, c, next), T, c) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_early.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {L.bounded(c) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_early(T, c) == earlyA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, c) : Bool}:
  match b:
    case True{}:
      settle_early.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, h, es, {==})
    case False{}:
      settle_early.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, h, {==})

def settle_early(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {L.bounded(c) == True{} : Bool})
  -> {L.chk_early(T, c) == earlyA(Eng.settle_cs(c, now, next, busy, nap, last), T, c) : Bool}:
  settle_early.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, h, {==})

def grow_early(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {L.bounded(c) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {L.chk_early(T, c) == earlyA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, c) : Bool}:
  match room:
    case 0n:
      settle_early(c, now, next, grown, 0n, busy, [], nap, last, T, h)
    case 1n+(+r):
      match ok:
        case True{}:
          %early_ok(c, now, next, last, h, eok) : {L.chk_early(T, c) == Bool.and(_, earlyA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, c)) : Bool}
          grow_early(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T, h, {==})
        case False{}:
          settle_early(c, now, next, grown, 1n+r, busy, [], nap, last, T, h)

def idle_early(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {L.bounded(c) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {L.chk_early(T, c) == earlyA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, c) : Bool}:
  match idle:
    case Nil{}:
      grow_early(room, ok, c, now, next, grown, busy, nap, last, T, h, eok)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          %early_ok(c, now, next, last, h, eok) : {L.chk_early(T, c) == Bool.and(_, earlyA(Eng.idle_cs(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}), T, c)) : Bool}
          idle_early(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T, h, {==})
        case False{}:
          settle_early(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T, h)

def steps_early(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, +h: {L.bounded(c) == True{} : Bool}) -> {L.chk_early(L.steps(evs, c, s), c) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_early(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, h)
                case False{}:
                  %idle_early(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last)), h, {==}) : {_ == True{} : Bool}
                  steps_early(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c, h)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_early(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, h)
                case False{}:
                  %idle_early(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), h, {==}) : {_ == True{} : Bool}
                  steps_early(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c, h)

def pre_early(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {earlyA(X, T, c) == earlyA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, c) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_early(p, 1n+from, X, T, c)

def L.eng_never_early(c, evs, h):
  +hh = h
  %pre_early(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_early(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), hh, {==}) : {_ == True{} : Bool}
  steps_early(evs, is0(c), c, hh)

# ---------------------------------------------------------------------
# eng: dl
# ---------------------------------------------------------------------

def dlA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, d: Nat, l: Nat) -> Bool:
  L.chk_deadline(List.append(&2, L.Item, L.cmds_items(xs), T), d, l)

def settle_dl.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), 0n)) == dlA(Eng.settle.nap_cs(b, c, next), T, L.e_dur(c), Maybe.default(&2, Nat, last, 0n)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_dl.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), 0n)) == dlA(Eng.settle.quit_cs(b, c, next), T, L.e_dur(c), Maybe.default(&2, Nat, last, 0n)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_dl.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), 0n)) == dlA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, L.e_dur(c), Maybe.default(&2, Nat, last, 0n)) : Bool}:
  match b:
    case True{}:
      settle_dl.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, h, es, {==})
    case False{}:
      settle_dl.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, h, {==})

def settle_dl(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool})
  -> {L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), 0n)) == dlA(Eng.settle_cs(c, now, next, busy, nap, last), T, L.e_dur(c), Maybe.default(&2, Nat, last, 0n)) : Bool}:
  settle_dl.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, h, {==})

def grow_dl(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), 0n)) == dlA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, L.e_dur(c), Maybe.default(&2, Nat, last, 0n)) : Bool}:
  match room:
    case 0n:
      settle_dl(c, now, next, grown, 0n, busy, [], nap, last, T, h)
    case 1n+(+r):
      match ok:
        case True{}:
          %dl_ok(c, last, h, and_l(Bool.not(Eng.stop_due(Eng.dur(c), last)), Eng.due(c, now, next), eok))
            : {L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now})), 0n)) == Bool.and(_, dlA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, L.e_dur(c), now)) : Bool}
          grow_dl(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T, h, {==})
        case False{}:
          settle_dl(c, now, next, grown, 1n+r, busy, [], nap, last, T, h)

def idle_dl(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), 0n)) == dlA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, L.e_dur(c), Maybe.default(&2, Nat, last, 0n)) : Bool}:
  match idle:
    case Nil{}:
      grow_dl(room, ok, c, now, next, grown, busy, nap, last, T, h, eok)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          %dl_ok(c, last, h, and_l(Bool.not(Eng.stop_due(Eng.dur(c), last)), Eng.due(c, now, next), eok))
            : {L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst(Eng.idle_st(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now})), 0n)) == Bool.and(_, dlA(Eng.idle_cs(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}), T, L.e_dur(c), now)) : Bool}
          idle_dl(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T, h, {==})
        case False{}:
          settle_dl(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T, h)

def steps_dl(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, +h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}) -> {L.chk_deadline(L.steps(evs, c, s), L.e_dur(c), Maybe.default(&2, Nat, lst(s), 0n)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_dl(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, h)
                case False{}:
                  %idle_dl(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last)), h, {==}) : {_ == True{} : Bool}
                  steps_dl(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c, h)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_dl(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, h)
                case False{}:
                  %idle_dl(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), h, {==}) : {_ == True{} : Bool}
                  steps_dl(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c, h)

def pre_dl(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {dlA(X, T, L.e_dur(c), 0n) == dlA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, L.e_dur(c), 0n) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_dl(p, 1n+from, X, T, c)

def L.eng_deadline(c, evs, h):
  +hh = h
  %pre_dl(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_dl(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), hh, {==}) : {_ == True{} : Bool}
  steps_dl(evs, is0(c), c, hh)

# ---------------------------------------------------------------------
# eng_initial
# ---------------------------------------------------------------------

def take_zero(xs: List<&2, L.Item>) -> {List.take(&2, L.Item, xs, 0n) == [] : List<&2, L.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      {==}

def take_gr(n: Nat, +f: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>)
  -> {List.take(&2, L.Item, List.append(&2, L.Item, L.cmds_items(List.append(&2, Eng.Cmd, Eng.grows(n, f), X)), T), n) == L.grows(n, f) : List<&2, L.Item>}:
  match n:
    case 0n:
      take_zero(List.append(&2, L.Item, L.cmds_items(X), T))
    case 1n+p:
      %take_gr(p, 1n+f, X, T) : {Con{L.ICmd{Eng.Grow{f}}, List.take(&2, L.Item, List.append(&2, L.Item, L.cmds_items(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X)), T), p)}
        == Con{L.ICmd{Eng.Grow{f}}, _} : List<&2, L.Item>}
      {==}


def L.eng_initial(c, evs):
  %initial_same(c) : {List.take(&2, L.Item, L.timeline(c, evs), _) == L.grows(_, 0n) : List<&2, L.Item>}
  take_gr(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)))

# ---------------------------------------------------------------------
# eng: workers
# ---------------------------------------------------------------------

def workersA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, m: Nat, g: Nat, b: List<&2, Nat>) -> Bool:
  L.chk_workers(List.append(&2, L.Item, L.cmds_items(xs), T), m, g, b)

def settle_workers.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool}, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_workers(T, L.e_max(c), gr(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == workersA(Eng.settle.nap_cs(b, c, next), T, L.e_max(c), grown, busy) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_workers.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_workers(T, L.e_max(c), gr(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), bz(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == workersA(Eng.settle.quit_cs(b, c, next), T, L.e_max(c), grown, busy) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_workers.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_workers(T, L.e_max(c), gr(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == workersA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, L.e_max(c), grown, busy) : Bool}:
  match b:
    case True{}:
      settle_workers.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, hv, es, {==})
    case False{}:
      settle_workers.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, hv, {==})

def settle_workers(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {L.chk_workers(T, L.e_max(c), gr(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == workersA(Eng.settle_cs(c, now, next, busy, nap, last), T, L.e_max(c), grown, busy) : Bool}:
  settle_workers.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, hv, {==})

def grow_workers(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, []) == True{} : Bool})
  -> {L.chk_workers(T, L.e_max(c), gr(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), bz(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == workersA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, L.e_max(c), grown, busy) : Bool}:
  match room:
    case 0n:
      settle_workers(c, now, next, grown, 0n, busy, [], nap, last, T, hv)
    case 1n+(+r):
      match ok:
        case True{}:
          %eq_refl(grown) : {L.chk_workers(T, L.e_max(c), gr(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now})), bz(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}))) == Bool.and(Bool.and(_, Nat.is_lt(grown, L.e_max(c))), Bool.and(Bool.and(Nat.is_lt(grown, 1n+grown), Bool.not(L.has_nat(grown, busy))), workersA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, L.e_max(c), 1n+grown, Con{grown, busy}))) : Bool}
          %Equal.sym(Bool, Nat.is_lt(grown, L.e_max(c)), True{}, room_lt(r, grown, L.e_max(c), wv1(c, grown, 1n+r, busy, [], hv)))
            : {L.chk_workers(T, L.e_max(c), gr(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now})), bz(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}))) == Bool.and(Bool.and(True{}, _), Bool.and(Bool.and(Nat.is_lt(grown, 1n+grown), Bool.not(L.has_nat(grown, busy))), workersA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, L.e_max(c), 1n+grown, Con{grown, busy}))) : Bool}
          %Equal.sym(Bool, Nat.is_lt(grown, 1n+grown), True{}, lt_succ(grown)) : {L.chk_workers(T, L.e_max(c), gr(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now})), bz(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}))) == Bool.and(Bool.and(_, Bool.not(L.has_nat(grown, busy))), workersA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, L.e_max(c), 1n+grown, Con{grown, busy})) : Bool}
          %Equal.sym(Bool, Bool.not(L.has_nat(grown, busy)), True{}, not_i(L.has_nat(grown, busy), lt_nhas(busy, grown, wv3(c, grown, 1n+r, busy, [], hv))))
            : {L.chk_workers(T, L.e_max(c), gr(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now})), bz(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}))) == Bool.and(Bool.and(True{}, _), workersA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, L.e_max(c), 1n+grown, Con{grown, busy})) : Bool}
          grow_workers(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T, wv_fire_grow(c, grown, r, busy, hv))
        case False{}:
          settle_workers(c, now, next, grown, 1n+r, busy, [], nap, last, T, hv)

def idle_workers(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {L.chk_workers(T, L.e_max(c), gr(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), bz(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == workersA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, L.e_max(c), grown, busy) : Bool}:
  match idle:
    case Nil{}:
      grow_workers(room, ok, c, now, next, grown, busy, nap, last, T, hv)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          %Equal.sym(Bool, Nat.is_lt(w, grown), True{}, ik1(w, rest, busy, grown, wv5(c, grown, room, busy, Con{w, rest}, hv))) : {L.chk_workers(T, L.e_max(c), gr(Eng.idle_st(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now})), bz(Eng.idle_st(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}))) == Bool.and(Bool.and(_, Bool.not(L.has_nat(w, busy))), workersA(Eng.idle_cs(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}), T, L.e_max(c), grown, Con{w, busy})) : Bool}
          %Equal.sym(Bool, Bool.not(L.has_nat(w, busy)), True{}, not_i(L.has_nat(w, busy), ik2(w, rest, busy, grown, wv5(c, grown, room, busy, Con{w, rest}, hv)))) : {L.chk_workers(T, L.e_max(c), gr(Eng.idle_st(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now})), bz(Eng.idle_st(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}))) == Bool.and(Bool.and(True{}, _), workersA(Eng.idle_cs(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}), T, L.e_max(c), grown, Con{w, busy})) : Bool}
          idle_workers(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T, wv_fire_idle(c, grown, room, busy, w, rest, hv))
        case False{}:
          settle_workers(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T, hv)

def steps_workers(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, +hv: {sinv(c, s) == True{} : Bool}) -> {L.chk_workers(L.steps(evs, c, s), L.e_max(c), gr(s), bz(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_workers(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, hv)
                case False{}:
                  %idle_workers(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last)), hv) : {_ == True{} : Bool}
                  steps_workers(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c, inv_idle(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, hv))
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  +hv2 = wv_freed(c, grown, room, busy, idle, w, hv)
                  %drop_same(w, busy) : {L.chk_workers(L.steps(rest, c, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}), L.e_max(c), grown, _) == True{} : Bool}
                  steps_workers(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, hv2)
                case False{}:
                  +hv2 = wv_freed(c, grown, room, busy, idle, w, hv)
                  %drop_same(w, busy) : {workersA(Eng.idle_cs(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), L.e_max(c), grown, _) == True{} : Bool}
                  %idle_workers(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), hv2) : {_ == True{} : Bool}
                  steps_workers(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c, inv_idle(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, hv2))

def pre_workers(k: Nat, +f: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg, +e: {Nat.is_le(Nat.add(f, k), L.e_max(c)) == True{} : Bool})
  -> {workersA(X, T, L.e_max(c), Nat.add(f, k), []) == workersA(List.append(&2, Eng.Cmd, Eng.grows(k, f), X), T, L.e_max(c), f, []) : Bool}:
  match k:
    case 0n:
      %N.add_zero(f) : {workersA(X, T, L.e_max(c), _, []) == workersA(X, T, L.e_max(c), f, []) : Bool}
      {==}
    case 1n+(+p):
      %N.add_succ(f, p) : {workersA(X, T, L.e_max(c), _, [])
        == Bool.and(Bool.and(Nat.is_eq(f, f), Nat.is_lt(f, L.e_max(c))), workersA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.e_max(c), 1n+f, [])) : Bool}
      %eq_refl(f) : {workersA(X, T, L.e_max(c), 1n+Nat.add(f, p), [])
        == Bool.and(Bool.and(_, Nat.is_lt(f, L.e_max(c))), workersA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.e_max(c), 1n+f, [])) : Bool}
      %Equal.sym(Bool, Nat.is_lt(f, L.e_max(c)), True{}, le_lt(f, p, L.e_max(c), e)) : {workersA(X, T, L.e_max(c), 1n+Nat.add(f, p), [])
        == Bool.and(Bool.and(True{}, _), workersA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.e_max(c), 1n+f, [])) : Bool}
      pre_workers(p, 1n+f, X, T, c, Equal.trans(Bool, Nat.is_le(1n+Nat.add(f, p), L.e_max(c)), Nat.is_le(Nat.add(f, 1n+p), L.e_max(c)), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, L.e_max(c)), 1n+Nat.add(f, p), Nat.add(f, 1n+p), N.add_succ(f, p)), e))

def L.eng_workers(c, evs):
  %pre_workers(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c, le0(c)) : {_ == True{} : Bool}
  %idle_workers(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), winv0(c)) : {_ == True{} : Bool}
  steps_workers(evs, is0(c), c, is0_inv(c))

# ---------------------------------------------------------------------
# eng: grow
# ---------------------------------------------------------------------

def growA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, w0: Nat, g: Nat, b: List<&2, Nat>) -> Bool:
  L.chk_grow(List.append(&2, L.Item, L.cmds_items(xs), T), w0, g, b)

def settle_grow.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool}, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_grow(T, L.initial(c), gr(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == growA(Eng.settle.nap_cs(b, c, next), T, L.initial(c), grown, busy) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_grow.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_grow(T, L.initial(c), gr(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), bz(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == growA(Eng.settle.quit_cs(b, c, next), T, L.initial(c), grown, busy) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_grow.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_grow(T, L.initial(c), gr(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == growA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, L.initial(c), grown, busy) : Bool}:
  match b:
    case True{}:
      settle_grow.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, hv, es, {==})
    case False{}:
      settle_grow.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, hv, {==})

def settle_grow(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {L.chk_grow(T, L.initial(c), gr(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == growA(Eng.settle_cs(c, now, next, busy, nap, last), T, L.initial(c), grown, busy) : Bool}:
  settle_grow.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, hv, {==})

def grow_grow(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, []) == True{} : Bool})
  -> {L.chk_grow(T, L.initial(c), gr(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), bz(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == growA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, L.initial(c), grown, busy) : Bool}:
  match room:
    case 0n:
      settle_grow(c, now, next, grown, 0n, busy, [], nap, last, T, hv)
    case 1n+(+r):
      match ok:
        case True{}:
          %Equal.sym(Bool, Bool.or(Nat.is_lt(grown, L.initial(c)), Bool.and(Nat.is_eq(List.length(&2, Nat, busy), grown), Nat.is_eq(grown, grown))), True{}, or_ok(Nat.is_lt(grown, L.initial(c)), Bool.and(Nat.is_eq(List.length(&2, Nat, busy), grown), Nat.is_eq(grown, grown)), and_i(Nat.is_eq(List.length(&2, Nat, busy), grown), Nat.is_eq(grown, grown), len_g(c, grown, 1n+r, busy, hv), Equal.sym(Bool, True{}, Nat.is_eq(grown, grown), eq_refl(grown)))))
            : {L.chk_grow(T, L.initial(c), gr(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now})), bz(Eng.grow_st(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}))) == Bool.and(_, growA(Eng.grow_cs(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}), T, L.initial(c), 1n+grown, Con{grown, busy})) : Bool}
          grow_grow(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T, wv_fire_grow(c, grown, r, busy, hv))
        case False{}:
          settle_grow(c, now, next, grown, 1n+r, busy, [], nap, last, T, hv)

def idle_grow(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {L.chk_grow(T, L.initial(c), gr(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), bz(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == growA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, L.initial(c), grown, busy) : Bool}:
  match idle:
    case Nil{}:
      grow_grow(room, ok, c, now, next, grown, busy, nap, last, T, hv)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          idle_grow(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T, wv_fire_idle(c, grown, room, busy, w, rest, hv))
        case False{}:
          settle_grow(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T, hv)

def steps_grow(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, +hv: {sinv(c, s) == True{} : Bool}) -> {L.chk_grow(L.steps(evs, c, s), L.initial(c), gr(s), bz(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_grow(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, hv)
                case False{}:
                  %idle_grow(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last)), hv) : {_ == True{} : Bool}
                  steps_grow(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c, inv_idle(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, hv))
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  +hv2 = wv_freed(c, grown, room, busy, idle, w, hv)
                  %drop_same(w, busy) : {L.chk_grow(L.steps(rest, c, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}), L.initial(c), grown, _) == True{} : Bool}
                  steps_grow(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, hv2)
                case False{}:
                  +hv2 = wv_freed(c, grown, room, busy, idle, w, hv)
                  %drop_same(w, busy) : {growA(Eng.idle_cs(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), L.initial(c), grown, _) == True{} : Bool}
                  %idle_grow(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), hv2) : {_ == True{} : Bool}
                  steps_grow(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c, inv_idle(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, hv2))

def pre_grow(k: Nat, +f: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg, +e: {Nat.add(f, k) == L.initial(c) : Nat})
  -> {growA(X, T, L.initial(c), Nat.add(f, k), []) == growA(List.append(&2, Eng.Cmd, Eng.grows(k, f), X), T, L.initial(c), f, []) : Bool}:
  match k:
    case 0n:
      %N.add_zero(f) : {growA(X, T, L.initial(c), _, []) == growA(X, T, L.initial(c), f, []) : Bool}
      {==}
    case 1n+(+p):
      %N.add_succ(f, p) : {growA(X, T, L.initial(c), _, [])
        == Bool.and(Bool.or(Nat.is_lt(f, L.initial(c)), Bool.and(Nat.is_eq(0n, f), L.next_fires(f, List.append(&2, L.Item, L.cmds_items(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X)), T)))),
          growA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.initial(c), 1n+f, [])) : Bool}
      %Equal.sym(Bool, Nat.is_lt(f, L.initial(c)), True{}, lt_add1(f, p, L.initial(c), e)) : {growA(X, T, L.initial(c), 1n+Nat.add(f, p), [])
        == Bool.and(Bool.or(_, Bool.and(Nat.is_eq(0n, f), L.next_fires(f, List.append(&2, L.Item, L.cmds_items(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X)), T)))),
          growA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.initial(c), 1n+f, [])) : Bool}
      pre_grow(p, 1n+f, X, T, c, Equal.trans(Nat, 1n+Nat.add(f, p), Nat.add(f, 1n+p), L.initial(c), N.add_succ(f, p), e))

def L.eng_grow(c, evs):
  %pre_grow(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c, initial_same(c)) : {_ == True{} : Bool}
  %idle_grow(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), winv0(c)) : {_ == True{} : Bool}
  steps_grow(evs, is0(c), c, is0_inv(c))

# ---------------------------------------------------------------------
# eng: quit
# ---------------------------------------------------------------------

def quitA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, c2: Eng.Cfg, s: Nat, q: Bool, l: Maybe<&2, Nat>, b: List<&2, Nat>) -> Bool:
  L.chk_quit(List.append(&2, L.Item, L.cmds_items(xs), T), c2, s, q, l, b)

def settle_quit.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hq: {qinv(c, next, last) == True{} : Bool}, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_quit(T, c, nx(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), ov(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), lst(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == quitA(Eng.settle.nap_cs(b, c, next), T, c, next, False{}, last, busy) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_quit.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hq: {qinv(c, next, last) == True{} : Bool}, +es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_quit(T, c, nx(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), ov(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), lst(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), bz(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == quitA(Eng.settle.quit_cs(b, c, next), T, c, next, False{}, last, busy) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, L.stop_due(L.e_dur(c), last), True{}, Equal.trans(Bool, L.stop_due(L.e_dur(c), last), Eng.stop_due(Eng.dur(c), last), True{},
        Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), L.stop_due(L.e_dur(c), last), stopdue_same(c, last)), es))
        : {L.chk_quit(T, c, next, True{}, last, busy) == Bool.and(Bool.and(_, List.is_empty(&2, Nat, busy)), Bool.and(Bool.and(Nat.is_eq(next, next), L.pick(Bool, L.bounded(c), Nat.is_eq(Nat.add(next, Eng.dropped(c, next)), L.scheduled(c)), Nat.is_eq(Eng.dropped(c, next), 0n))), L.chk_quit(T, c, next, True{}, last, busy))) : Bool}
      %Equal.sym(Bool, List.is_empty(&2, Nat, busy), True{}, eq) : {L.chk_quit(T, c, next, True{}, last, busy) == Bool.and(Bool.and(True{}, _), Bool.and(Bool.and(Nat.is_eq(next, next), L.pick(Bool, L.bounded(c), Nat.is_eq(Nat.add(next, Eng.dropped(c, next)), L.scheduled(c)), Nat.is_eq(Eng.dropped(c, next), 0n))), L.chk_quit(T, c, next, True{}, last, busy))) : Bool}
      %eq_refl(next) : {L.chk_quit(T, c, next, True{}, last, busy) == Bool.and(Bool.and(_, L.pick(Bool, L.bounded(c), Nat.is_eq(Nat.add(next, Eng.dropped(c, next)), L.scheduled(c)), Nat.is_eq(Eng.dropped(c, next), 0n))), L.chk_quit(T, c, next, True{}, last, busy)) : Bool}
      %drop_ok(c, next, last, es, hq) : {L.chk_quit(T, c, next, True{}, last, busy) == Bool.and(Bool.and(True{}, _), L.chk_quit(T, c, next, True{}, last, busy)) : Bool}
      {==}
    case False{}:
      {==}

def settle_quit.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hq: {qinv(c, next, last) == True{} : Bool}, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_quit(T, c, nx(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), ov(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), lst(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == quitA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, c, next, False{}, last, busy) : Bool}:
  match b:
    case True{}:
      settle_quit.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, hq, es, {==})
    case False{}:
      settle_quit.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, hq, {==})

def settle_quit(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hq: {qinv(c, next, last) == True{} : Bool})
  -> {L.chk_quit(T, c, nx(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), ov(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), lst(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == quitA(Eng.settle_cs(c, now, next, busy, nap, last), T, c, next, False{}, last, busy) : Bool}:
  settle_quit.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, hq, {==})

def grow_quit(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hq: {qinv(c, next, last) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {L.chk_quit(T, c, nx(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), ov(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), lst(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), bz(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == quitA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, c, next, False{}, last, busy) : Bool}:
  match room:
    case 0n:
      settle_quit(c, now, next, grown, 0n, busy, [], nap, last, T, hq)
    case 1n+(+r):
      match ok:
        case True{}:
          grow_quit(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T, qfire(c, now, next, last, eok, hq), {==})
        case False{}:
          settle_quit(c, now, next, grown, 1n+r, busy, [], nap, last, T, hq)

def idle_quit(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, +hq: {qinv(c, next, last) == True{} : Bool}, eok: {Eng.may(c, now, next, last) == ok : Bool})
  -> {L.chk_quit(T, c, nx(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), ov(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), lst(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), bz(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == quitA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, c, next, False{}, last, busy) : Bool}:
  match idle:
    case Nil{}:
      grow_quit(room, ok, c, now, next, grown, busy, nap, last, T, hq, eok)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          idle_quit(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T, qfire(c, now, next, last, eok, hq), {==})
        case False{}:
          settle_quit(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T, hq)

def steps_quit(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, +hq: {sq(c, s) == True{} : Bool}) -> {L.chk_quit(L.steps(evs, c, s), c, nx(s), ov(s), lst(s), bz(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_quit(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, hq)
                case False{}:
                  %idle_quit(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last)), hq, {==}) : {_ == True{} : Bool}
                  steps_quit(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c, q_idle(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, hq, {==}))
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  %drop_same(w, busy) : {L.chk_quit(L.steps(rest, c, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}), c, next, True{}, last, _) == True{} : Bool}
                  steps_quit(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, hq)
                case False{}:
                  %drop_same(w, busy) : {quitA(Eng.idle_cs(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), c, next, False{}, last, _) == True{} : Bool}
                  %idle_quit(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), hq, {==}) : {_ == True{} : Bool}
                  steps_quit(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c, q_idle(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, hq, {==}))

def pre_quit(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {quitA(X, T, c, 0n, False{}, None{}, []) == quitA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, c, 0n, False{}, None{}, []) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_quit(p, 1n+from, X, T, c)

def L.eng_quit(c, evs):
  %pre_quit(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_quit(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), q0.of(Bool.and(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n)), c), {==}) : {_ == True{} : Bool}
  steps_quit(evs, is0(c), c, is0_q(c))

# ---------------------------------------------------------------------
# eng: live
# ---------------------------------------------------------------------

def liveA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, c2: Eng.Cfg, n: Bool, g: Nat, b: List<&2, Nat>, q: Bool, l: Maybe<&2, Nat>) -> Bool:
  L.chk_live(List.append(&2, L.Item, L.cmds_items(xs), T), c2, n, g, b, q, l)

def settle_live.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.chk_live(T, c, np(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), gr(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), ov(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)), lst(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == liveA(Eng.settle.nap_cs(b, c, next), T, c, nap, grown, busy, False{}, last) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_live.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.chk_live(T, c, np(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), gr(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), bz(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), ov(Eng.EState{now, next, grown, room, busy, idle, nap, last, b}), lst(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == liveA(Eng.settle.quit_cs(b, c, next), T, c, nap, grown, busy, False{}, last) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_live.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.chk_live(T, c, np(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), gr(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), ov(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)), lst(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == liveA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, c, nap, grown, busy, False{}, last) : Bool}:
  match b:
    case True{}:
      settle_live.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, es, {==})
    case False{}:
      settle_live.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def settle_live(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_live(T, c, np(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), gr(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), bz(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), ov(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)), lst(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == liveA(Eng.settle_cs(c, now, next, busy, nap, last), T, c, nap, grown, busy, False{}, last) : Bool}:
  settle_live.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def grow_live(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_live(T, c, np(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), gr(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), bz(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), ov(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)), lst(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == liveA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, c, nap, grown, busy, False{}, last) : Bool}:
  match room:
    case 0n:
      settle_live(c, now, next, grown, 0n, busy, [], nap, last, T)
    case 1n+(+r):
      match ok:
        case True{}:
          grow_live(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T)
        case False{}:
          settle_live(c, now, next, grown, 1n+r, busy, [], nap, last, T)

def idle_live(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.chk_live(T, c, np(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), gr(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), bz(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), ov(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)), lst(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == liveA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, c, nap, grown, busy, False{}, last) : Bool}:
  match idle:
    case Nil{}:
      grow_live(room, ok, c, now, next, grown, busy, nap, last, T)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          idle_live(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T)
        case False{}:
          settle_live(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T)

def steps_live(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, +hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {sinv(c, s) == True{} : Bool}, +hp: {spend(c, s) == True{} : Bool})
  -> {L.chk_live(L.steps(evs, c, s), c, np(s), gr(s), bz(s), ov(s), lst(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      match s:
        case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
          hp
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  %Equal.sym(Bool, L.pending(c, nap, grown, busy, True{}, last), True{}, hp) : {Bool.and(_, L.chk_live(L.steps(rest, c, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}), c, False{}, grown, busy, True{}, last)) == True{} : Bool}
                  steps_live(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, hok, hv, {==})
                case False{}:
                  %Equal.sym(Bool, L.pending(c, nap, grown, busy, False{}, last), True{}, hp) : {Bool.and(_, liveA(Eng.idle_cs(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last)), c, False{}, grown, busy, False{}, last)) == True{} : Bool}
                  %idle_live(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : {_ == True{} : Bool}
                  steps_live(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c, hok, inv_idle(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, hv), pend_idle(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, hok, hv, {==}))
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  +hv2 = wv_freed(c, grown, room, busy, idle, w, hv)
                  %Equal.sym(Bool, L.pending(c, nap, grown, busy, True{}, last), True{}, hp) : {Bool.and(_, L.chk_live(L.steps(rest, c, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}), c, nap, grown, L.drop_nat(w, busy), True{}, last)) == True{} : Bool}
                  %drop_same(w, busy) : {L.chk_live(L.steps(rest, c, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}), c, nap, grown, _, True{}, last) == True{} : Bool}
                  steps_live(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, hok, hv2, {==})
                case False{}:
                  +hv2 = wv_freed(c, grown, room, busy, idle, w, hv)
                  %Equal.sym(Bool, L.pending(c, nap, grown, busy, False{}, last), True{}, hp) : {Bool.and(_, liveA(Eng.idle_cs(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), c, nap, grown, L.drop_nat(w, busy), False{}, last)) == True{} : Bool}
                  %drop_same(w, busy) : {liveA(Eng.idle_cs(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), c, nap, grown, _, False{}, last) == True{} : Bool}
                  %idle_live(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : {_ == True{} : Bool}
                  steps_live(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c, hok, inv_idle(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, hv2), pend_idle(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, hok, hv2, {==}))

def pre_live(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {liveA(X, T, c, False{}, Nat.add(from, k), [], False{}, None{}) == liveA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, c, False{}, from, [], False{}, None{}) : Bool}:
  match k:
    case 0n:
      %N.add_zero(from) : {liveA(X, T, c, False{}, _, [], False{}, None{}) == liveA(X, T, c, False{}, from, [], False{}, None{}) : Bool}
      {==}
    case 1n+(+p):
      %N.add_succ(from, p) : {liveA(X, T, c, False{}, _, [], False{}, None{}) == liveA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+from), X), T, c, False{}, 1n+from, [], False{}, None{}) : Bool}
      pre_live(p, 1n+from, X, T, c)

def L.eng_live(c, evs, h):
  +hh = h
  %pre_live(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_live(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c))) : {_ == True{} : Bool}
  steps_live(evs, is0(c), c, hh, is0_inv(c), pend_idle(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, hh, winv0(c), {==}))

# ---------------------------------------------------------------------
# eng: hq
# ---------------------------------------------------------------------

def hqA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, o: Bool) -> Bool:
  hqc(List.append(&2, L.Item, L.cmds_items(xs), T), o)

def settle_hq.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {hqc(T, ov(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == hqA(Eng.settle.nap_cs(b, c, next), T, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_hq.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {hqc(T, ov(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == hqA(Eng.settle.quit_cs(b, c, next), T, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_hq.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {hqc(T, ov(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == hqA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, False{}) : Bool}:
  match b:
    case True{}:
      settle_hq.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, es, {==})
    case False{}:
      settle_hq.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def settle_hq(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {hqc(T, ov(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == hqA(Eng.settle_cs(c, now, next, busy, nap, last), T, False{}) : Bool}:
  settle_hq.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def grow_hq(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {hqc(T, ov(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == hqA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, False{}) : Bool}:
  match room:
    case 0n:
      settle_hq(c, now, next, grown, 0n, busy, [], nap, last, T)
    case 1n+(+r):
      match ok:
        case True{}:
          grow_hq(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T)
        case False{}:
          settle_hq(c, now, next, grown, 1n+r, busy, [], nap, last, T)

def idle_hq(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {hqc(T, ov(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == hqA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, False{}) : Bool}:
  match idle:
    case Nil{}:
      grow_hq(room, ok, c, now, next, grown, busy, nap, last, T)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          idle_hq(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T)
        case False{}:
          settle_hq(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T)

def pre_hq(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {hqA(X, T, False{}) == hqA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, False{}) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_hq(p, 1n+from, X, T, c)

# ---------------------------------------------------------------------
# eng: bo
# ---------------------------------------------------------------------

def boA(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>, b: List<&2, Nat>) -> List<&2, Nat>:
  L.busy_of(List.append(&2, L.Item, L.cmds_items(xs), T), b)

def settle_bo.nap(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, en: {Eng.wants_nap(c, now, next, nap) == b : Bool})
  -> {L.busy_of(T, bz(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last))) == boA(Eng.settle.nap_cs(b, c, next), T, busy) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_bo.quit(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq: {List.is_empty(&2, Nat, busy) == b : Bool})
  -> {L.busy_of(T, bz(Eng.EState{now, next, grown, room, busy, idle, nap, last, b})) == boA(Eng.settle.quit_cs(b, c, next), T, busy) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def settle_bo.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>, es: {Eng.stop_due(Eng.dur(c), last) == b : Bool})
  -> {L.busy_of(T, bz(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last))) == boA(Eng.settle.of_cs(b, c, now, next, busy, nap), T, busy) : List<&2, Nat>}:
  match b:
    case True{}:
      settle_bo.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T, es, {==})
    case False{}:
      settle_bo.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def settle_bo(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.busy_of(T, bz(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last))) == boA(Eng.settle_cs(c, now, next, busy, nap, last), T, busy) : List<&2, Nat>}:
  settle_bo.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T, {==})

def grow_bo(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.busy_of(T, bz(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last))) == boA(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T, busy) : List<&2, Nat>}:
  match room:
    case 0n:
      settle_bo(c, now, next, grown, 0n, busy, [], nap, last, T)
    case 1n+(+r):
      match ok:
        case True{}:
          grow_bo(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now}, T)
        case False{}:
          settle_bo(c, now, next, grown, 1n+r, busy, [], nap, last, T)

def idle_bo(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>)
  -> {L.busy_of(T, bz(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last))) == boA(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T, busy) : List<&2, Nat>}:
  match idle:
    case Nil{}:
      grow_bo(room, ok, c, now, next, grown, busy, nap, last, T)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          idle_bo(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now}, T)
        case False{}:
          settle_bo(c, now, next, grown, room, busy, Con{w, rest}, nap, last, T)

def steps_hq(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg) -> {Bool.or(ov(s), L.has_quit(L.steps(evs, c, s))) == ov(fin(evs, c, s)) : Bool}:
  match evs:
    case Nil{}:
      match s:
        case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
          match over:
            case True{}:
              {==}
            case False{}:
              {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  Equal.sym(Bool, ov(fin(rest, c, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}})), True{}, ov_abs(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c, {==}))
                case False{}:
                  %idle_hq(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : {_ == ov(fin(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : Bool}
                  steps_hq(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  Equal.sym(Bool, ov(fin(rest, c, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}})), True{}, ov_abs(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c, {==}))
                case False{}:
                  %idle_hq(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : {_ == ov(fin(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : Bool}
                  steps_hq(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c)

def steps_bo(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg) -> {L.busy_of(L.steps(evs, c, s), bz(s)) == bz(fin(evs, c, s)) : List<&2, Nat>}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Eng.Clock{+t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  steps_bo(rest, Eng.EState{t, next, grown, room, busy, idle, False{}, last, True{}}, c)
                case False{}:
                  %idle_bo(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, L.steps(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : {_ == bz(fin(rest, c, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last))) : List<&2, Nat>}
                  steps_bo(rest, Eng.idle_st(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last), c)
        case Eng.Freed{+w, +t}:
          match s:
            case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
              match over:
                case True{}:
                  %drop_same(w, busy) : {L.busy_of(L.steps(rest, c, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}), _) == bz(fin(rest, c, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}})) : List<&2, Nat>}
                  steps_bo(rest, Eng.EState{t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, True{}}, c)
                case False{}:
                  %drop_same(w, busy) : {boA(Eng.idle_cs(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)), _) == bz(fin(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : List<&2, Nat>}
                  %idle_bo(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last, L.steps(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : {_ == bz(fin(rest, c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last))) : List<&2, Nat>}
                  steps_bo(rest, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last), c)

def pre_bo(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>)
  -> {boA(X, T, []) == boA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, []) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pre_bo(p, 1n+from, X, T)

def hq_tl(+c: Eng.Cfg, +E: List<&2, Eng.Ev>) -> {L.has_quit(L.timeline(c, E)) == ov(fin(E, c, is0(c))) : Bool}:
  %pre_hq(i0(c), 0n, ic0(c), L.steps(E, c, is0(c)), c) : {_ == ov(fin(E, c, is0(c))) : Bool}
  %idle_hq(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(E, c, is0(c))) : {_ == ov(fin(E, c, is0(c))) : Bool}
  steps_hq(E, is0(c), c)

def bo_tl(+c: Eng.Cfg, +E: List<&2, Eng.Ev>) -> {L.busy_of(L.timeline(c, E), []) == bz(fin(E, c, is0(c))) : List<&2, Nat>}:
  %pre_bo(i0(c), 0n, ic0(c), L.steps(E, c, is0(c))) : {_ == bz(fin(E, c, is0(c))) : List<&2, Nat>}
  %idle_bo(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(E, c, is0(c))) : {_ == bz(fin(E, c, is0(c))) : List<&2, Nat>}
  steps_bo(E, is0(c), c)


# ---------------------------------------------------------------------
# eng_ends, part 2: a round of the responsive environment
# ---------------------------------------------------------------------

def idle_false(idle: List<&2, Nat>, room: Nat, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>)
  -> {Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last) == Eng.idle_st(idle, False{}, c, now, next, grown, room, busy, nap, last) : Eng.State}:
  match idle room:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+r:
      {==}
    case Con{w, rest} _:
      {==}

def idle_false_cs(idle: List<&2, Nat>, room: Nat, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>)
  -> {Eng.settle_cs(c, now, next, busy, nap, last) == Eng.idle_cs(idle, False{}, c, now, next, grown, room, busy, nap, last) : List<&2, Eng.Cmd>}:
  match idle room:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+r:
      {==}
    case Con{w, rest} _:
      {==}

def may_false(+c: Eng.Cfg, +now: Nat, +next: Nat, +last: Maybe<&2, Nat>, h: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool})
  -> {False{} == Eng.may(c, now, next, last) : Bool}:
  %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), True{}, h) : {False{} == Bool.and(Bool.not(_), Eng.due(c, now, next)) : Bool}
  {==}

def may_true(+c: Eng.Cfg, +now: Nat, +next: Nat, +last: Maybe<&2, Nat>, hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, hd: {Eng.due(c, now, next) == True{} : Bool})
  -> {True{} == Eng.may(c, now, next, last) : Bool}:
  %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, hs) : {True{} == Bool.and(Bool.not(_), Eng.due(c, now, next)) : Bool}
  Equal.sym(Bool, Eng.due(c, now, next), True{}, hd)

def may_f2(+c: Eng.Cfg, +now: Nat, +next: Nat, +last: Maybe<&2, Nat>, hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, hd: {Eng.due(c, now, next) == False{} : Bool})
  -> {False{} == Eng.may(c, now, next, last) : Bool}:
  %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, hs) : {False{} == Bool.and(Bool.not(_), Eng.due(c, now, next)) : Bool}
  Equal.sym(Bool, Eng.due(c, now, next), False{}, hd)

def drop_head(+w: Nat, +rest: List<&2, Nat>) -> {rest == Eng.drop_nat(w, Con{w, rest}) : List<&2, Nat>}:
  %eq_refl(w) : {rest == Eng.pick(List<&2, Nat>, _, rest, Con{w, Eng.drop_nat(w, rest)}) : List<&2, Nat>}
  {==}

def has_head(+w: Nat, +rest: List<&2, Nat>) -> {True{} == Eng.has_nat(w, Con{w, rest}) : Bool}:
  %eq_refl(w) : {True{} == Bool.or(_, Eng.has_nat(w, rest)) : Bool}
  {==}

# the stop decided, or the attack over
def dd(+c: Eng.Cfg, +s: Eng.State) -> Bool:
  Bool.or(ov(s), Eng.stop_due(Eng.dur(c), lst(s)))

def dd_settle(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +h: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool})
  -> {dd(c, Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)) == True{} : Bool}:
  %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), True{}, h)
    : {Bool.or(ov(Eng.settle.of_st(_, c, now, next, grown, room, busy, idle, nap, last)), Eng.stop_due(Eng.dur(c), lst(Eng.settle.of_st(_, c, now, next, grown, room, busy, idle, nap, last)))) == True{} : Bool}
  or_ok(List.is_empty(&2, Nat, busy), Eng.stop_due(Eng.dur(c), last), h)

def dd_step(e: Eng.Ev, +s: Eng.State, +c: Eng.Cfg, +h: {dd(c, s) == True{} : Bool}) -> {dd(c, L.st_of(Eng.step(c, s, e))) == True{} : Bool}:
  match e:
    case Eng.Clock{+t}:
      match s:
        case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
          match over:
            case True{}:
              {==}
            case False{}:
              %may_false(c, t, next, last, h) : {dd(c, Eng.idle_st(idle, _, c, t, next, grown, room, busy, False{}, last)) == True{} : Bool}
              %idle_false(idle, room, c, t, next, grown, busy, False{}, last) : {dd(c, _) == True{} : Bool}
              dd_settle(c, t, next, grown, room, busy, idle, False{}, last, h)
    case Eng.Freed{+w, +t}:
      match s:
        case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
          match over:
            case True{}:
              {==}
            case False{}:
              %may_false(c, t, next, last, h)
                : {dd(c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), _, c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last)) == True{} : Bool}
              %idle_false(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), room, c, t, next, grown, Eng.drop_nat(w, busy), nap, last) : {dd(c, _) == True{} : Bool}
              dd_settle(c, t, next, grown, room, Eng.drop_nat(w, busy), Eng.freed_idle(Eng.has_nat(w, busy), w, idle), nap, last, h)

def dd_sticky(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, h: {dd(c, s) == True{} : Bool}) -> {dd(c, fin(evs, c, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case Con{+e, +rest}:
      dd_sticky(rest, L.st_of(Eng.step(c, s, e)), c, dd_step(e, s, c, h))

def step_inv(e: Eng.Ev, +s: Eng.State, +c: Eng.Cfg, +hv: {sinv(c, s) == True{} : Bool}) -> {sinv(c, L.st_of(Eng.step(c, s, e))) == True{} : Bool}:
  match e:
    case Eng.Clock{+t}:
      match s:
        case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
          match over:
            case True{}:
              hv
            case False{}:
              inv_idle(idle, Eng.may(c, t, next, last), c, t, next, grown, room, busy, False{}, last, hv)
    case Eng.Freed{+w, +t}:
      match s:
        case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
          match over:
            case True{}:
              wv_freed(c, grown, room, busy, idle, w, hv)
            case False{}:
              inv_idle(Eng.freed_idle(Eng.has_nat(w, busy), w, idle), Eng.may(c, t, next, last), c, t, next, grown, room, Eng.drop_nat(w, busy), nap, last,
                wv_freed(c, grown, room, busy, idle, w, hv))

def fin_inv(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, hv: {sinv(c, s) == True{} : Bool}) -> {sinv(c, fin(evs, c, s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      hv
    case Con{+e, +rest}:
      fin_inv(rest, L.st_of(Eng.step(c, s, e)), c, step_inv(e, s, c, hv))

# the last hit's time through the loops
def last_settle.nap(b: Bool, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>)
  -> {last == lst(Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def last_settle.of(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>)
  -> {last == lst(Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      last_settle.nap(Eng.wants_nap(c, now, next, nap), now, next, grown, room, busy, idle, nap, last)

def last_settle(+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>)
  -> {last == lst(Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)) : Maybe<&2, Nat>}:
  last_settle.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last)

def last_grow(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool)
  -> {Some{now} == lst(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, Some{now})) : Maybe<&2, Nat>}:
  match room:
    case 0n:
      last_settle(c, now, next, grown, 0n, busy, [], nap, Some{now})
    case 1n+(+r):
      match ok:
        case True{}:
          last_grow(r, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap)
        case False{}:
          last_settle(c, now, next, grown, 1n+r, busy, [], nap, Some{now})

def last_idle(idle: List<&2, Nat>, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool)
  -> {Some{now} == lst(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, Some{now})) : Maybe<&2, Nat>}:
  match idle:
    case Nil{}:
      last_grow(room, ok, c, now, next, grown, busy, nap)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          last_idle(rest, Eng.may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap)
        case False{}:
          last_settle(c, now, next, grown, room, busy, Con{w, rest}, nap, Some{now})

def dd_fired_idle(+idle: List<&2, Nat>, +ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool,
  hT: {Eng.stop_due(Eng.dur(c), Some{now}) == True{} : Bool})
  -> {dd(c, Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, Some{now})) == True{} : Bool}:
  %last_idle(idle, ok, c, now, next, grown, room, busy, nap)
    : {Bool.or(ov(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, Some{now})), Eng.stop_due(Eng.dur(c), _)) == True{} : Bool}
  or_ok(ov(Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, Some{now})), Eng.stop_due(Eng.dur(c), Some{now}), hT)

def dd_fired_grow(+room: Nat, +ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool,
  hT: {Eng.stop_due(Eng.dur(c), Some{now}) == True{} : Bool})
  -> {dd(c, Eng.grow_st(room, ok, c, now, next, grown, busy, nap, Some{now})) == True{} : Bool}:
  %last_grow(room, ok, c, now, next, grown, busy, nap)
    : {Bool.or(ov(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, Some{now})), Eng.stop_due(Eng.dur(c), _)) == True{} : Bool}
  or_ok(ov(Eng.grow_st(room, ok, c, now, next, grown, busy, nap, Some{now})), Eng.stop_due(Eng.dur(c), Some{now}), hT)

# once the stop is decided, freeing every busy worker ends the attack
def frees_stop(B: List<&2, Nat>, +c: Eng.Cfg, +T: Nat, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +h: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool})
  -> {ov(fin(L.frees(B, T), c, Eng.EState{now, next, grown, room, B, idle, nap, last, List.is_empty(&2, Nat, B)})) == True{} : Bool}:
  match B:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      %may_false(c, T, next, last, h)
        : {ov(fin(L.frees(rest, T), c, Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), _, c, T, next, grown, room, Eng.drop_nat(w, Con{w, rest}), nap, last))) == True{} : Bool}
      %idle_false(Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), room, c, T, next, grown, Eng.drop_nat(w, Con{w, rest}), nap, last)
        : {ov(fin(L.frees(rest, T), c, _)) == True{} : Bool}
      %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), True{}, h)
        : {ov(fin(L.frees(rest, T), c, Eng.settle.of_st(_, c, T, next, grown, room, Eng.drop_nat(w, Con{w, rest}), Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), nap, last))) == True{} : Bool}
      %drop_head(w, rest)
        : {ov(fin(L.frees(rest, T), c, Eng.EState{T, next, grown, room, _, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), nap, last, List.is_empty(&2, Nat, _)})) == True{} : Bool}
      frees_stop(rest, c, T, T, next, grown, room, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), nap, last, h)

# a round once the stop is decided ends the attack
def r1_stop(+s: Eng.State, +c: Eng.Cfg, +T: Nat, +h: {Eng.stop_due(Eng.dur(c), lst(s)) == True{} : Bool})
  -> {ov(fin(Con{Eng.Clock{T}, L.frees(bz(s), T)}, c, s)) == True{} : Bool}:
  match s:
    case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
      match over:
        case True{}:
          ov_abs(Con{Eng.Clock{T}, L.frees(busy, T)}, Eng.EState{now, next, grown, room, busy, idle, nap, last, True{}}, c, {==})
        case False{}:
          %may_false(c, T, next, last, h) : {ov(fin(L.frees(busy, T), c, Eng.idle_st(idle, _, c, T, next, grown, room, busy, False{}, last))) == True{} : Bool}
          %idle_false(idle, room, c, T, next, grown, busy, False{}, last) : {ov(fin(L.frees(busy, T), c, _)) == True{} : Bool}
          %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), True{}, h) : {ov(fin(L.frees(busy, T), c, Eng.settle.of_st(_, c, T, next, grown, room, busy, idle, False{}, last))) == True{} : Bool}
          frees_stop(busy, c, T, T, next, grown, room, idle, False{}, last, h)


# a round where a hit is due: after it, the stop is decided (or the
# attack is over)
def no_empty(+c: Eng.Cfg, +g: Nat, hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {winv(c, g, 0n, [], []) == True{} : Bool}) -> Empty:
  N.false_ne_true(Equal.trans(Bool, Nat.is_ge(0n, 1n), Nat.is_ge(L.e_max(c), 1n), True{},
    Equal.cong(Nat, Bool, x => Nat.is_ge(x, 1n), 0n, L.e_max(c),
      Equal.trans(Nat, 0n, g, L.e_max(c), eq_of(0n, g, wv2(c, g, 0n, [], [], hv)), eq_of(g, L.e_max(c), wv1(c, g, 0n, [], [], hv)))),
    and_r(Nat.is_ge(L.e_targets(c), 1n), Nat.is_ge(L.e_max(c), 1n),
      and_l(Bool.and(Nat.is_ge(L.e_targets(c), 1n), Nat.is_ge(L.e_max(c), 1n)),
        Bool.or(Bool.or(Nat.is_eq(L.e_freq(c), 0n), Nat.is_eq(L.e_per(c), 0n)), Nat.is_ge(L.e_per(c), L.e_freq(c))), hok))))

def r_fire.w(busy: List<&2, Nat>, +nap: Bool, +c: Eng.Cfg, +T: Nat, +next: Nat, +grown: Nat, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hd: {Eng.due(c, T, next) == True{} : Bool}, +hT: {Eng.stop_due(Eng.dur(c), Some{T}) == True{} : Bool},
  +hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {winv(c, grown, 0n, busy, []) == True{} : Bool})
  -> {dd(c, fin(L.frees(busy, T), c, Eng.EState{T, next, grown, 0n, busy, [], nap, last, False{}})) == True{} : Bool}:
  match busy:
    case Nil{}:
      Empty.absurd({dd(c, fin(L.frees([], T), c, Eng.EState{T, next, grown, 0n, [], [], nap, last, False{}})) == True{} : Bool}, no_empty(c, grown, hok, hv))
    case Con{+w1, +brest}:
      %has_head(w1, brest)
        : {dd(c, fin(L.frees(brest, T), c, Eng.idle_st(Eng.freed_idle(_, w1, []), Eng.may(c, T, next, last), c, T, next, grown, 0n, Eng.drop_nat(w1, Con{w1, brest}), nap, last))) == True{} : Bool}
      %may_true(c, T, next, last, hs, hd)
        : {dd(c, fin(L.frees(brest, T), c, Eng.idle_st(Con{w1, []}, _, c, T, next, grown, 0n, Eng.drop_nat(w1, Con{w1, brest}), nap, last))) == True{} : Bool}
      dd_sticky(L.frees(brest, T), Eng.idle_st([], Eng.may(c, T, 1n+next, Some{T}), c, T, 1n+next, grown, 0n, Con{w1, Eng.drop_nat(w1, Con{w1, brest})}, nap, Some{T}), c,
        dd_fired_idle([], Eng.may(c, T, 1n+next, Some{T}), c, T, 1n+next, grown, 0n, Con{w1, Eng.drop_nat(w1, Con{w1, brest})}, nap, hT))

def r_fire.z(b: Bool, +busy: List<&2, Nat>, +c: Eng.Cfg, +T: Nat, +next: Nat, +grown: Nat, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hd: {Eng.due(c, T, next) == True{} : Bool}, +hT: {Eng.stop_due(Eng.dur(c), Some{T}) == True{} : Bool},
  +hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {winv(c, grown, 0n, busy, []) == True{} : Bool})
  -> {dd(c, fin(L.frees(busy, T), c, Eng.settle.nap_st(b, T, next, grown, 0n, busy, [], False{}, last))) == True{} : Bool}:
  match b:
    case True{}:
      r_fire.w(busy, True{}, c, T, next, grown, last, hs, hd, hT, hok, hv)
    case False{}:
      r_fire.w(busy, False{}, c, T, next, grown, last, hs, hd, hT, hok, hv)

def r_fire.idle(idle: List<&2, Nat>, +room: Nat, +busy: List<&2, Nat>, +c: Eng.Cfg, +T: Nat, +next: Nat, +grown: Nat, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hd: {Eng.due(c, T, next) == True{} : Bool}, +hT: {Eng.stop_due(Eng.dur(c), Some{T}) == True{} : Bool},
  +hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {winv(c, grown, room, busy, idle) == True{} : Bool})
  -> {dd(c, fin(L.frees(busy, T), c, Eng.idle_st(idle, True{}, c, T, next, grown, room, busy, False{}, last))) == True{} : Bool}:
  match idle room:
    case Con{+w, +rest} _:
      dd_sticky(L.frees(busy, T), Eng.idle_st(rest, Eng.may(c, T, 1n+next, Some{T}), c, T, 1n+next, grown, room, Con{w, busy}, False{}, Some{T}), c,
        dd_fired_idle(rest, Eng.may(c, T, 1n+next, Some{T}), c, T, 1n+next, grown, room, Con{w, busy}, False{}, hT))
    case Nil{} 1n+(+r):
      dd_sticky(L.frees(busy, T), Eng.grow_st(r, Eng.may(c, T, 1n+next, Some{T}), c, T, 1n+next, 1n+grown, Con{grown, busy}, False{}, Some{T}), c,
        dd_fired_grow(r, Eng.may(c, T, 1n+next, Some{T}), c, T, 1n+next, 1n+grown, Con{grown, busy}, False{}, hT))
    case Nil{} 0n:
      %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, hs)
        : {dd(c, fin(L.frees(busy, T), c, Eng.settle.of_st(_, c, T, next, grown, 0n, busy, [], False{}, last))) == True{} : Bool}
      r_fire.z(Eng.wants_nap(c, T, next, False{}), busy, c, T, next, grown, last, hs, hd, hT, hok, hv)

def r_fire(+s: Eng.State, +c: Eng.Cfg, +T: Nat, +hs: {Eng.stop_due(Eng.dur(c), lst(s)) == False{} : Bool}, +hd: {Eng.due(c, T, nx(s)) == True{} : Bool},
  +hT: {Eng.stop_due(Eng.dur(c), Some{T}) == True{} : Bool}, +hok: {L.cfg_ok(c) == True{} : Bool}, +hv: {sinv(c, s) == True{} : Bool})
  -> {dd(c, fin(Con{Eng.Clock{T}, L.frees(bz(s), T)}, c, s)) == True{} : Bool}:
  match s:
    case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
      match over:
        case True{}:
          or1(ov(fin(Con{Eng.Clock{T}, L.frees(busy, T)}, c, Eng.EState{now, next, grown, room, busy, idle, nap, last, True{}})),
            Eng.stop_due(Eng.dur(c), lst(fin(Con{Eng.Clock{T}, L.frees(busy, T)}, c, Eng.EState{now, next, grown, room, busy, idle, nap, last, True{}}))),
            ov_abs(Con{Eng.Clock{T}, L.frees(busy, T)}, Eng.EState{now, next, grown, room, busy, idle, nap, last, True{}}, c, {==}))
        case False{}:
          %may_true(c, T, next, last, hs, hd) : {dd(c, fin(L.frees(busy, T), c, Eng.idle_st(idle, _, c, T, next, grown, room, busy, False{}, last))) == True{} : Bool}
          r_fire.idle(idle, room, busy, c, T, next, grown, last, hs, hd, hT, hok, hv)

# a round at a bounded rate before the next slot: a nap until it, and
# nothing else
def hnd_ge(+c: Eng.Cfg, +T: Nat, +next: Nat, hb: {Eng.bounded(c) == True{} : Bool}, hnd: {Eng.due(c, T, next) == False{} : Bool})
  -> {Nat.is_ge(T, Eng.slot(c, next)) == False{} : Bool}:
  Equal.trans(Bool, Eng.due.of(True{}, c, T, next), Eng.due(c, T, next), False{},
    Equal.cong(Bool, Bool, x => Eng.due.of(x, c, T, next), True{}, Eng.bounded(c), Equal.sym(Bool, Eng.bounded(c), True{}, hb)), hnd)

def clock_st(+c: Eng.Cfg, +now: Nat, +T: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, next) == False{} : Bool})
  -> {Eng.EState{T, next, grown, room, busy, idle, True{}, last, False{}} == L.st_of(Eng.step(c, Eng.EState{now, next, grown, room, busy, idle, nap, last, False{}}, Eng.Clock{T})) : Eng.State}:
  %may_f2(c, T, next, last, hs, hnd) : {Eng.EState{T, next, grown, room, busy, idle, True{}, last, False{}} == Eng.idle_st(idle, _, c, T, next, grown, room, busy, False{}, last) : Eng.State}
  %idle_false(idle, room, c, T, next, grown, busy, False{}, last) : {Eng.EState{T, next, grown, room, busy, idle, True{}, last, False{}} == _ : Eng.State}
  %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, hs)
    : {Eng.EState{T, next, grown, room, busy, idle, True{}, last, False{}} == Eng.settle.of_st(_, c, T, next, grown, room, busy, idle, False{}, last) : Eng.State}
  %Equal.sym(Bool, Eng.bounded(c), True{}, hb)
    : {Eng.EState{T, next, grown, room, busy, idle, True{}, last, False{}}
      == Eng.settle.nap_st(Bool.and(_, Bool.and(True{}, Nat.is_gt(Eng.slot(c, next), T))), T, next, grown, room, busy, idle, False{}, last) : Eng.State}
  %Equal.sym(Bool, Nat.is_gt(Eng.slot(c, next), T), True{}, ge_false_gt(T, Eng.slot(c, next), hnd_ge(c, T, next, hb, hnd)))
    : {Eng.EState{T, next, grown, room, busy, idle, True{}, last, False{}}
      == Eng.settle.nap_st(Bool.and(True{}, Bool.and(True{}, _)), T, next, grown, room, busy, idle, False{}, last) : Eng.State}
  {==}

def clock_cs(+c: Eng.Cfg, +now: Nat, +T: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, next) == False{} : Bool})
  -> {[Eng.Nap{Eng.slot(c, next)}] == L.cs_of(Eng.step(c, Eng.EState{now, next, grown, room, busy, idle, nap, last, False{}}, Eng.Clock{T})) : List<&2, Eng.Cmd>}:
  %may_f2(c, T, next, last, hs, hnd) : {[Eng.Nap{Eng.slot(c, next)}] == Eng.idle_cs(idle, _, c, T, next, grown, room, busy, False{}, last) : List<&2, Eng.Cmd>}
  %idle_false_cs(idle, room, c, T, next, grown, busy, False{}, last) : {[Eng.Nap{Eng.slot(c, next)}] == _ : List<&2, Eng.Cmd>}
  %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, hs)
    : {[Eng.Nap{Eng.slot(c, next)}] == Eng.settle.of_cs(_, c, T, next, busy, False{}) : List<&2, Eng.Cmd>}
  %Equal.sym(Bool, Eng.bounded(c), True{}, hb)
    : {[Eng.Nap{Eng.slot(c, next)}] == Eng.settle.nap_cs(Bool.and(_, Bool.and(True{}, Nat.is_gt(Eng.slot(c, next), T))), c, next) : List<&2, Eng.Cmd>}
  %Equal.sym(Bool, Nat.is_gt(Eng.slot(c, next), T), True{}, ge_false_gt(T, Eng.slot(c, next), hnd_ge(c, T, next, hb, hnd)))
    : {[Eng.Nap{Eng.slot(c, next)}] == Eng.settle.nap_cs(Bool.and(True{}, Bool.and(True{}, _)), c, next) : List<&2, Eng.Cmd>}
  {==}

def quiet_st(+w: Nat, +rest: List<&2, Nat>, +c: Eng.Cfg, +now: Nat, +T: Nat, +next: Nat, +grown: Nat, +room: Nat, +idle: List<&2, Nat>, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, next) == False{} : Bool})
  -> {Eng.EState{T, next, grown, room, rest, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last, False{}}
      == L.st_of(Eng.step(c, Eng.EState{now, next, grown, room, Con{w, rest}, idle, True{}, last, False{}}, Eng.Freed{w, T})) : Eng.State}:
  %may_f2(c, T, next, last, hs, hnd)
    : {Eng.EState{T, next, grown, room, rest, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last, False{}}
      == Eng.idle_st(Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), _, c, T, next, grown, room, Eng.drop_nat(w, Con{w, rest}), True{}, last) : Eng.State}
  %idle_false(Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), room, c, T, next, grown, Eng.drop_nat(w, Con{w, rest}), True{}, last)
    : {Eng.EState{T, next, grown, room, rest, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last, False{}} == _ : Eng.State}
  %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, hs)
    : {Eng.EState{T, next, grown, room, rest, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last, False{}}
      == Eng.settle.of_st(_, c, T, next, grown, room, Eng.drop_nat(w, Con{w, rest}), Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last) : Eng.State}
  %Equal.sym(Bool, Eng.bounded(c), True{}, hb)
    : {Eng.EState{T, next, grown, room, rest, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last, False{}}
      == Eng.settle.nap_st(Bool.and(_, False{}), T, next, grown, room, Eng.drop_nat(w, Con{w, rest}), Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last) : Eng.State}
  %drop_head(w, rest)
    : {Eng.EState{T, next, grown, room, rest, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last, False{}}
      == Eng.EState{T, next, grown, room, _, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), True{}, last, False{}} : Eng.State}
  {==}

def quiet_cs(+w: Nat, +rest: List<&2, Nat>, +c: Eng.Cfg, +now: Nat, +T: Nat, +next: Nat, +grown: Nat, +room: Nat, +idle: List<&2, Nat>, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, next) == False{} : Bool})
  -> {[] == L.cs_of(Eng.step(c, Eng.EState{now, next, grown, room, Con{w, rest}, idle, True{}, last, False{}}, Eng.Freed{w, T})) : List<&2, Eng.Cmd>}:
  %may_f2(c, T, next, last, hs, hnd)
    : {[] == Eng.idle_cs(Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), _, c, T, next, grown, room, Eng.drop_nat(w, Con{w, rest}), True{}, last) : List<&2, Eng.Cmd>}
  %idle_false_cs(Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), room, c, T, next, grown, Eng.drop_nat(w, Con{w, rest}), True{}, last) : {[] == _ : List<&2, Eng.Cmd>}
  %Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), False{}, hs) : {[] == Eng.settle.of_cs(_, c, T, next, Eng.drop_nat(w, Con{w, rest}), True{}) : List<&2, Eng.Cmd>}
  %Equal.sym(Bool, Eng.bounded(c), True{}, hb) : {[] == Eng.settle.nap_cs(Bool.and(_, False{}), c, next) : List<&2, Eng.Cmd>}
  {==}

def quiet_nap(B: List<&2, Nat>, +c: Eng.Cfg, +T: Nat, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +idle: List<&2, Nat>, +last: Maybe<&2, Nat>, +n: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, next) == False{} : Bool})
  -> {n == L.nap_of(L.steps(L.frees(B, T), c, Eng.EState{now, next, grown, room, B, idle, True{}, last, False{}}), n) : Maybe<&2, Nat>}:
  match B:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      %quiet_cs(w, rest, c, now, T, next, grown, room, idle, last, hs, hb, hnd)
        : {n == L.nap_of(List.append(&2, L.Item, L.cmds_items(_),
            L.steps(L.frees(rest, T), c, L.st_of(Eng.step(c, Eng.EState{now, next, grown, room, Con{w, rest}, idle, True{}, last, False{}}, Eng.Freed{w, T})))), n) : Maybe<&2, Nat>}
      %quiet_st(w, rest, c, now, T, next, grown, room, idle, last, hs, hb, hnd) : {n == L.nap_of(L.steps(L.frees(rest, T), c, _), n) : Maybe<&2, Nat>}
      quiet_nap(rest, c, T, T, next, grown, room, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), last, n, hs, hb, hnd)

def quiet_nx(B: List<&2, Nat>, +c: Eng.Cfg, +T: Nat, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +idle: List<&2, Nat>, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, next) == False{} : Bool})
  -> {next == nx(fin(L.frees(B, T), c, Eng.EState{now, next, grown, room, B, idle, True{}, last, False{}})) : Nat}:
  match B:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      %quiet_st(w, rest, c, now, T, next, grown, room, idle, last, hs, hb, hnd) : {next == nx(fin(L.frees(rest, T), c, _)) : Nat}
      quiet_nx(rest, c, T, T, next, grown, room, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), last, hs, hb, hnd)

def quiet_lst(B: List<&2, Nat>, +c: Eng.Cfg, +T: Nat, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +idle: List<&2, Nat>, +last: Maybe<&2, Nat>,
  +hs: {Eng.stop_due(Eng.dur(c), last) == False{} : Bool}, +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, next) == False{} : Bool})
  -> {last == lst(fin(L.frees(B, T), c, Eng.EState{now, next, grown, room, B, idle, True{}, last, False{}})) : Maybe<&2, Nat>}:
  match B:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      %quiet_st(w, rest, c, now, T, next, grown, room, idle, last, hs, hb, hnd) : {last == lst(fin(L.frees(rest, T), c, _)) : Maybe<&2, Nat>}
      quiet_lst(rest, c, T, T, next, grown, room, Eng.freed_idle(Eng.has_nat(w, Con{w, rest}), w, idle), last, hs, hb, hnd)

def r_nap_nap(+s: Eng.State, +c: Eng.Cfg, +T: Nat, +n: Maybe<&2, Nat>, ho: {ov(s) == False{} : Bool}, +hs: {Eng.stop_due(Eng.dur(c), lst(s)) == False{} : Bool},
  +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, nx(s)) == False{} : Bool})
  -> {Some{Eng.slot(c, nx(s))} == L.nap_of(L.steps(Con{Eng.Clock{T}, L.frees(bz(s), T)}, c, s), n) : Maybe<&2, Nat>}:
  match s:
    case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
      match over:
        case True{}:
          Empty.absurd({Some{Eng.slot(c, next)} == L.nap_of(L.steps(Con{Eng.Clock{T}, L.frees(busy, T)}, c, Eng.EState{now, next, grown, room, busy, idle, nap, last, True{}}), n) : Maybe<&2, Nat>},
            N.false_ne_true(Equal.sym(Bool, True{}, False{}, ho)))
        case False{}:
          %clock_cs(c, now, T, next, grown, room, busy, idle, nap, last, hs, hb, hnd)
            : {Some{Eng.slot(c, next)} == L.nap_of(List.append(&2, L.Item, L.cmds_items(_),
                L.steps(L.frees(busy, T), c, L.st_of(Eng.step(c, Eng.EState{now, next, grown, room, busy, idle, nap, last, False{}}, Eng.Clock{T})))), None{}) : Maybe<&2, Nat>}
          %clock_st(c, now, T, next, grown, room, busy, idle, nap, last, hs, hb, hnd)
            : {Some{Eng.slot(c, next)} == L.nap_of(L.steps(L.frees(busy, T), c, _), Some{Eng.slot(c, next)}) : Maybe<&2, Nat>}
          quiet_nap(busy, c, T, T, next, grown, room, idle, last, Some{Eng.slot(c, next)}, hs, hb, hnd)

def r_nap_nx(+s: Eng.State, +c: Eng.Cfg, +T: Nat, ho: {ov(s) == False{} : Bool}, +hs: {Eng.stop_due(Eng.dur(c), lst(s)) == False{} : Bool},
  +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, nx(s)) == False{} : Bool})
  -> {nx(s) == nx(fin(Con{Eng.Clock{T}, L.frees(bz(s), T)}, c, s)) : Nat}:
  match s:
    case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
      match over:
        case True{}:
          Empty.absurd({next == nx(fin(Con{Eng.Clock{T}, L.frees(busy, T)}, c, Eng.EState{now, next, grown, room, busy, idle, nap, last, True{}})) : Nat},
            N.false_ne_true(Equal.sym(Bool, True{}, False{}, ho)))
        case False{}:
          %clock_st(c, now, T, next, grown, room, busy, idle, nap, last, hs, hb, hnd) : {next == nx(fin(L.frees(busy, T), c, _)) : Nat}
          quiet_nx(busy, c, T, T, next, grown, room, idle, last, hs, hb, hnd)

def r_nap_lst(+s: Eng.State, +c: Eng.Cfg, +T: Nat, ho: {ov(s) == False{} : Bool}, +hs: {Eng.stop_due(Eng.dur(c), lst(s)) == False{} : Bool},
  +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, T, nx(s)) == False{} : Bool})
  -> {lst(s) == lst(fin(Con{Eng.Clock{T}, L.frees(bz(s), T)}, c, s)) : Maybe<&2, Nat>}:
  match s:
    case Eng.EState{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}:
      match over:
        case True{}:
          Empty.absurd({last == lst(fin(Con{Eng.Clock{T}, L.frees(busy, T)}, c, Eng.EState{now, next, grown, room, busy, idle, nap, last, True{}})) : Maybe<&2, Nat>},
            N.false_ne_true(Equal.sym(Bool, True{}, False{}, ho)))
        case False{}:
          %clock_st(c, now, T, next, grown, room, busy, idle, nap, last, hs, hb, hnd) : {last == lst(fin(L.frees(busy, T), c, _)) : Maybe<&2, Nat>}
          quiet_lst(busy, c, T, T, next, grown, room, idle, last, hs, hb, hnd)


# ---------------------------------------------------------------------
# eng_ends, part 3: four rounds
# ---------------------------------------------------------------------

def nowr(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat) -> Nat:
  Nat.max(t, Maybe.default(&2, Nat, L.nap_of(L.timeline(c, E), None{}), t))

def rnd(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat) -> List<&2, Eng.Ev>:
  List.append(&2, Eng.Ev, E, Con{Eng.Clock{nowr(c, E, t)}, L.frees(L.busy_of(L.timeline(c, E), []), nowr(c, E, t))})

def s_of(+c: Eng.Cfg, +E: List<&2, Eng.Ev>) -> Eng.State:
  fin(E, c, is0(c))

def rb(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat) -> List<&2, Eng.Ev>:
  Con{Eng.Clock{nowr(c, E, t)}, L.frees(bz(s_of(c, E)), nowr(c, E, t))}

def rnd_fin(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat) -> {fin(rb(c, E, t), c, s_of(c, E)) == fin(rnd(c, E, t), c, is0(c)) : Eng.State}:
  %Equal.sym(Eng.State, fin(rnd(c, E, t), c, is0(c)),
      fin(Con{Eng.Clock{nowr(c, E, t)}, L.frees(L.busy_of(L.timeline(c, E), []), nowr(c, E, t))}, c, fin(E, c, is0(c))),
      fin_app(E, Con{Eng.Clock{nowr(c, E, t)}, L.frees(L.busy_of(L.timeline(c, E), []), nowr(c, E, t))}, c, is0(c)))
    : {fin(rb(c, E, t), c, s_of(c, E)) == _ : Eng.State}
  %Equal.sym(List<&2, Nat>, L.busy_of(L.timeline(c, E), []), bz(fin(E, c, is0(c))), bo_tl(c, E))
    : {fin(rb(c, E, t), c, s_of(c, E)) == fin(Con{Eng.Clock{nowr(c, E, t)}, L.frees(_, nowr(c, E, t))}, c, fin(E, c, is0(c))) : Eng.State}
  {==}

def rnd_abs(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, h: {ov(s_of(c, E)) == True{} : Bool}) -> {ov(s_of(c, rnd(c, E, t))) == True{} : Bool}:
  %rnd_fin(c, E, t) : {ov(_) == True{} : Bool}
  ov_abs(rb(c, E, t), s_of(c, E), c, h)

def r1_rnd(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, h: {Eng.stop_due(Eng.dur(c), lst(s_of(c, E))) == True{} : Bool})
  -> {ov(s_of(c, rnd(c, E, t))) == True{} : Bool}:
  %rnd_fin(c, E, t) : {ov(_) == True{} : Bool}
  r1_stop(s_of(c, E), c, nowr(c, E, t), h)

def dd_next.of(b: Bool, +c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, +eb: {ov(s_of(c, E)) == b : Bool}, hD: {dd(c, s_of(c, E)) == True{} : Bool})
  -> {ov(s_of(c, rnd(c, E, t))) == True{} : Bool}:
  match b:
    case True{}:
      rnd_abs(c, E, t, eb)
    case False{}:
      r1_rnd(c, E, t, or_true_r(ov(s_of(c, E)), Eng.stop_due(Eng.dur(c), lst(s_of(c, E))), eb, hD))

def dd_next(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, hD: {dd(c, s_of(c, E)) == True{} : Bool}) -> {ov(s_of(c, rnd(c, E, t))) == True{} : Bool}:
  dd_next.of(ov(s_of(c, E)), c, E, t, {==}, hD)

def rfire_rnd(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, hs: {Eng.stop_due(Eng.dur(c), lst(s_of(c, E))) == False{} : Bool},
  hd: {Eng.due(c, nowr(c, E, t), nx(s_of(c, E))) == True{} : Bool}, hT: {Eng.stop_due(Eng.dur(c), Some{nowr(c, E, t)}) == True{} : Bool}, hok: {L.cfg_ok(c) == True{} : Bool})
  -> {dd(c, s_of(c, rnd(c, E, t))) == True{} : Bool}:
  %rnd_fin(c, E, t) : {dd(c, _) == True{} : Bool}
  r_fire(s_of(c, E), c, nowr(c, E, t), hs, hd, hT, hok, fin_inv(E, is0(c), c, is0_inv(c)))

def ge_refl(a: Nat) -> {Nat.is_ge(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      ge_refl(p)

def max_ge_r(a: Nat, b: Nat) -> {Nat.is_ge(Nat.max(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      ge_refl(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      max_ge_r(p, q)

def max_ge_l(a: Nat, b: Nat) -> {Nat.is_ge(Nat.max(a, b), a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      ge_refl(p)
    case 1n+p 1n+q:
      max_ge_l(p, q)

def ge_trans(x: Nat, y: Nat, z: Nat, e1: {Nat.is_ge(x, y) == True{} : Bool}, e2: {Nat.is_ge(y, z) == True{} : Bool}) -> {Nat.is_ge(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      e2
    case 0n 1n+q _:
      bool_absurd(Nat.is_ge(0n, z), True{}, e1)
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      bool_absurd(Nat.is_ge(1n+p, 1n+r), True{}, e2)
    case 1n+p 1n+q 0n:
      {==}
    case 1n+p 1n+q 1n+r:
      ge_trans(p, q, r, e1, e2)

def ge_max(+a: Nat, +b: Nat, +d: Nat, e: {Nat.is_ge(a, d) == True{} : Bool}) -> {Nat.is_ge(Nat.max(a, b), d) == True{} : Bool}:
  ge_trans(Nat.max(a, b), a, d, max_ge_l(a, b), e)

def cmp_gt_ge(x: Cmp, e: {Cmp.is_gt(x) == True{} : Bool}) -> {Cmp.is_ge(x) == True{} : Bool}:
  match x:
    case LT{}:
      e
    case EQ{}:
      {==}
    case GT{}:
      {==}

def hT_of(+c: Eng.Cfg, +T: Nat, h1: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, hge: {Nat.is_ge(T, L.e_dur(c)) == True{} : Bool})
  -> {Eng.stop_due(Eng.dur(c), Some{T}) == True{} : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      and_i(Nat.is_gt(d, 0n), Nat.is_ge(T, d), h1, hge)

def due_bnd.of(b: Bool, +c: Eng.Cfg, +T: Nat, +next: Nat, eb: {Eng.bounded(c) == b : Bool}, hnd: {Eng.due.of(b, c, T, next) == False{} : Bool})
  -> {Eng.bounded(c) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      bool_absurd(Eng.bounded(c), True{}, Equal.sym(Bool, True{}, False{}, hnd))

def due_at(+c: Eng.Cfg, +T: Nat, +next: Nat, hb: {Eng.bounded(c) == True{} : Bool}, hge: {Nat.is_ge(T, Eng.slot(c, next)) == True{} : Bool})
  -> {Eng.due(c, T, next) == True{} : Bool}:
  %Equal.sym(Bool, Eng.bounded(c), True{}, hb) : {Eng.due.of(_, c, T, next) == True{} : Bool}
  hge

def nap1_lem(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, eo: {ov(s_of(c, E)) == False{} : Bool}, +hs: {Eng.stop_due(Eng.dur(c), lst(s_of(c, E))) == False{} : Bool},
  +hb: {Eng.bounded(c) == True{} : Bool}, +hnd: {Eng.due(c, nowr(c, E, t), nx(s_of(c, E))) == False{} : Bool})
  -> {Some{Eng.slot(c, nx(s_of(c, E)))} == L.nap_of(L.timeline(c, rnd(c, E, t)), None{}) : Maybe<&2, Nat>}:
  %Equal.sym(List<&2, L.Item>, L.timeline(c, rnd(c, E, t)),
      List.append(&2, L.Item, L.timeline(c, E), L.steps(Con{Eng.Clock{nowr(c, E, t)}, L.frees(L.busy_of(L.timeline(c, E), []), nowr(c, E, t))}, c, s_of(c, E))),
      tl_app(c, E, Con{Eng.Clock{nowr(c, E, t)}, L.frees(L.busy_of(L.timeline(c, E), []), nowr(c, E, t))}))
    : {Some{Eng.slot(c, nx(s_of(c, E)))} == L.nap_of(_, None{}) : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>,
      L.nap_of(List.append(&2, L.Item, L.timeline(c, E), L.steps(Con{Eng.Clock{nowr(c, E, t)}, L.frees(L.busy_of(L.timeline(c, E), []), nowr(c, E, t))}, c, s_of(c, E))), None{}),
      L.nap_of(L.steps(Con{Eng.Clock{nowr(c, E, t)}, L.frees(L.busy_of(L.timeline(c, E), []), nowr(c, E, t))}, c, s_of(c, E)), L.nap_of(L.timeline(c, E), None{})),
      nap_app(L.timeline(c, E), L.steps(Con{Eng.Clock{nowr(c, E, t)}, L.frees(L.busy_of(L.timeline(c, E), []), nowr(c, E, t))}, c, s_of(c, E)), None{}))
    : {Some{Eng.slot(c, nx(s_of(c, E)))} == _ : Maybe<&2, Nat>}
  %Equal.sym(List<&2, Nat>, L.busy_of(L.timeline(c, E), []), bz(s_of(c, E)), bo_tl(c, E))
    : {Some{Eng.slot(c, nx(s_of(c, E)))} == L.nap_of(L.steps(Con{Eng.Clock{nowr(c, E, t)}, L.frees(_, nowr(c, E, t))}, c, s_of(c, E)), L.nap_of(L.timeline(c, E), None{})) : Maybe<&2, Nat>}
  r_nap_nap(s_of(c, E), c, nowr(c, E, t), L.nap_of(L.timeline(c, E), None{}), eo, hs, hb, hnd)

def hge2(+c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, enx: {nx(s_of(c, E)) == nx(s_of(c, rnd(c, E, t))) : Nat},
  enap: {Some{Eng.slot(c, nx(s_of(c, E)))} == L.nap_of(L.timeline(c, rnd(c, E, t)), None{}) : Maybe<&2, Nat>})
  -> {Nat.is_ge(nowr(c, rnd(c, E, t), nowr(c, E, t)), Eng.slot(c, nx(s_of(c, rnd(c, E, t))))) == True{} : Bool}:
  %enx : {Nat.is_ge(nowr(c, rnd(c, E, t), nowr(c, E, t)), Eng.slot(c, _)) == True{} : Bool}
  %enap : {Nat.is_ge(Nat.max(nowr(c, E, t), Maybe.default(&2, Nat, _, nowr(c, E, t))), Eng.slot(c, nx(s_of(c, E)))) == True{} : Bool}
  max_ge_r(nowr(c, E, t), Eng.slot(c, nx(s_of(c, E))))

def ends.c(b: Bool, +c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, +eb: {Eng.due(c, nowr(c, E, t), nx(s_of(c, E))) == b : Bool},
  +hs: {Eng.stop_due(Eng.dur(c), lst(s_of(c, E))) == False{} : Bool}, +eo: {ov(s_of(c, E)) == False{} : Bool},
  +hok: {L.cfg_ok(c) == True{} : Bool}, +hd1: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, +hge1: {Nat.is_ge(nowr(c, E, t), L.e_dur(c)) == True{} : Bool})
  -> {ov(s_of(c, rnd(c, rnd(c, rnd(c, E, t), nowr(c, E, t)), nowr(c, rnd(c, E, t), nowr(c, E, t))))) == True{} : Bool}:
  match b:
    case True{}:
      rnd_abs(c, rnd(c, rnd(c, E, t), nowr(c, E, t)), nowr(c, rnd(c, E, t), nowr(c, E, t)),
        dd_next(c, rnd(c, E, t), nowr(c, E, t), rfire_rnd(c, E, t, hs, eb, hT_of(c, nowr(c, E, t), hd1, hge1), hok)))
    case False{}:
      +hb = due_bnd.of(Eng.bounded(c), c, nowr(c, E, t), nx(s_of(c, E)), {==}, eb)
      +enx = Equal.trans(Nat, nx(s_of(c, E)), nx(fin(rb(c, E, t), c, s_of(c, E))), nx(s_of(c, rnd(c, E, t))),
        r_nap_nx(s_of(c, E), c, nowr(c, E, t), eo, hs, hb, eb),
        Equal.cong(Eng.State, Nat, x => nx(x), fin(rb(c, E, t), c, s_of(c, E)), s_of(c, rnd(c, E, t)), rnd_fin(c, E, t)))
      +elst = Equal.trans(Maybe<&2, Nat>, lst(s_of(c, E)), lst(fin(rb(c, E, t), c, s_of(c, E))), lst(s_of(c, rnd(c, E, t))),
        r_nap_lst(s_of(c, E), c, nowr(c, E, t), eo, hs, hb, eb),
        Equal.cong(Eng.State, Maybe<&2, Nat>, x => lst(x), fin(rb(c, E, t), c, s_of(c, E)), s_of(c, rnd(c, E, t)), rnd_fin(c, E, t)))
      +enap = nap1_lem(c, E, t, eo, hs, hb, eb)
      dd_next(c, rnd(c, rnd(c, E, t), nowr(c, E, t)), nowr(c, rnd(c, E, t), nowr(c, E, t)),
        rfire_rnd(c, rnd(c, E, t), nowr(c, E, t),
          Equal.trans(Bool, Eng.stop_due(Eng.dur(c), lst(s_of(c, rnd(c, E, t)))), Eng.stop_due(Eng.dur(c), lst(s_of(c, E))), False{},
            Equal.cong(Maybe<&2, Nat>, Bool, x => Eng.stop_due(Eng.dur(c), x), lst(s_of(c, rnd(c, E, t))), lst(s_of(c, E)),
              Equal.sym(Maybe<&2, Nat>, lst(s_of(c, E)), lst(s_of(c, rnd(c, E, t))), elst)), hs),
          due_at(c, nowr(c, rnd(c, E, t), nowr(c, E, t)), nx(s_of(c, rnd(c, E, t))), hb, hge2(c, E, t, enx, enap)),
          hT_of(c, nowr(c, rnd(c, E, t), nowr(c, E, t)), hd1,
            ge_max(nowr(c, E, t), Maybe.default(&2, Nat, L.nap_of(L.timeline(c, rnd(c, E, t)), None{}), nowr(c, E, t)), L.e_dur(c), hge1)),
          hok))

def ends.b(b: Bool, +c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, +eb: {Eng.stop_due(Eng.dur(c), lst(s_of(c, E))) == b : Bool},
  +eo: {ov(s_of(c, E)) == False{} : Bool}, +hok: {L.cfg_ok(c) == True{} : Bool}, +hd1: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool},
  +hge1: {Nat.is_ge(nowr(c, E, t), L.e_dur(c)) == True{} : Bool})
  -> {ov(s_of(c, rnd(c, rnd(c, rnd(c, E, t), nowr(c, E, t)), nowr(c, rnd(c, E, t), nowr(c, E, t))))) == True{} : Bool}:
  match b:
    case True{}:
      rnd_abs(c, rnd(c, rnd(c, E, t), nowr(c, E, t)), nowr(c, rnd(c, E, t), nowr(c, E, t)),
        rnd_abs(c, rnd(c, E, t), nowr(c, E, t), r1_rnd(c, E, t, eb)))
    case False{}:
      ends.c(Eng.due(c, nowr(c, E, t), nx(s_of(c, E))), c, E, t, {==}, eb, eo, hok, hd1, hge1)

def ends.a(b: Bool, +c: Eng.Cfg, +E: List<&2, Eng.Ev>, +t: Nat, +eb: {ov(s_of(c, E)) == b : Bool},
  +hok: {L.cfg_ok(c) == True{} : Bool}, +hd1: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, +hge1: {Nat.is_ge(nowr(c, E, t), L.e_dur(c)) == True{} : Bool})
  -> {ov(s_of(c, rnd(c, rnd(c, rnd(c, E, t), nowr(c, E, t)), nowr(c, rnd(c, E, t), nowr(c, E, t))))) == True{} : Bool}:
  match b:
    case True{}:
      rnd_abs(c, rnd(c, rnd(c, E, t), nowr(c, E, t)), nowr(c, rnd(c, E, t), nowr(c, E, t)),
        rnd_abs(c, rnd(c, E, t), nowr(c, E, t), rnd_abs(c, E, t, eb)))
    case False{}:
      ends.b(Eng.stop_due(Eng.dur(c), lst(s_of(c, E))), c, E, t, {==}, eb, hok, hd1, hge1)

def L.eng_ends(c, evs, t, h0, h1, h2):
  +hge1 = ge_max(t, Maybe.default(&2, Nat, L.nap_of(L.timeline(c, evs), None{}), t), L.e_dur(c),
    cmp_gt_ge(Nat.cmp(t, L.e_dur(c)), and_l(Nat.is_gt(t, L.e_dur(c)), Nat.is_ge(t, L.max_time(evs)), h2)))
  %Equal.sym(Bool, L.has_quit(L.timeline(c, L.respond(4n, c, evs, t))), ov(fin(L.respond(4n, c, evs, t), c, is0(c))), hq_tl(c, L.respond(4n, c, evs, t)))
    : {_ == True{} : Bool}
  rnd_abs(c, rnd(c, rnd(c, rnd(c, evs, t), nowr(c, evs, t)), nowr(c, rnd(c, evs, t), nowr(c, evs, t))),
    nowr(c, rnd(c, rnd(c, evs, t), nowr(c, evs, t)), nowr(c, rnd(c, evs, t), nowr(c, evs, t))),
    ends.a(ov(s_of(c, evs)), c, evs, t, {==}, h0, h1, hge1))

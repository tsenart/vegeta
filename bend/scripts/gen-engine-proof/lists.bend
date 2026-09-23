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

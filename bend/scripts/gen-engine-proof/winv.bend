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

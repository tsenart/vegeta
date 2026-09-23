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

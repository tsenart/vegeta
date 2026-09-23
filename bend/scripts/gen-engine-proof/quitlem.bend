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

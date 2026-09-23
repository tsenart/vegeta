
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

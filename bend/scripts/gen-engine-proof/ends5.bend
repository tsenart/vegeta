
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

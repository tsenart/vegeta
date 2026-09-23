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

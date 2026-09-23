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

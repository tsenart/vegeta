
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

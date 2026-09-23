# The attack's scheduler, as a pure machine: pacing, dispatch to workers,
# worker growth, and the stop with its accounting. Times are ns since the
# attack began, read from the clock by the shell.
#
# Go's Attack loop (lib/attack.go) and ConstantPacer (lib/pacer.go): hit i
# is due at (i + 1) intervals; a hit goes to an idle worker, or to a new
# one when every worker is busy and max-workers allows; after each send
# the loop stops once the hit went out at or past the duration, and the
# attack ends when the last busy worker is done.
#
# Written for proof and for the strict compiled lane. The state mirrors
# what LAWS.bend's checkers track (the busy list grows by `Con` and
# shrinks by `drop_nat`; the nap flag is set by a nap and cleared by the
# clock). The dispatch runs in two loops, each structural: first over the
# idle workers, then over the room left under max-workers (one new worker
# per hit). Each loop gets its verdict (may a hit go out?) as a parameter
# computed by the caller. The next state and the commands are computed by
# twin defs of the same shape (`*_st` and `*_cs`).
import Base

# freq = 0 or per = 0: unbounded rate; dur = 0: forever; targets >= 1
type Cfg is Data:
  ECfg{freq: Nat, per: Nat, dur: Nat, workers: Nat, max_workers: Nat, targets: Nat}

type Ev is Data:
  Clock{t: Nat}
  Freed{w: Nat, t: Nat}

type Cmd is Data:
  Nap{until: Nat}
  Grow{w: Nat}
  Fire{w: Nat, seq: Nat, target: Nat, t: Nat}
  Quit{sent: Nat, dropped: Nat}

# now: the time of the last event; next: the hits sent (the next seq);
# grown: workers started (ids 0..grown-1); room: workers that may still
# be started (max-workers - grown); busy: workers with a hit out; idle:
# the started workers without one (the last freed first); nap: a nap is
# open (since the last clock); last: the last hit's time; over: quit
type State is Data:
  EState{now: Nat, next: Nat, grown: Nat, room: Nat, busy: List<&2, Nat>, idle: List<&2, Nat>, nap: Bool, last: Maybe<&2, Nat>, over: Bool}

def freq(+c: Cfg) -> Nat:
  ECfg{f, p, d, w, m, t} = c
  f

def per(+c: Cfg) -> Nat:
  ECfg{f, p, d, w, m, t} = c
  p

def dur(+c: Cfg) -> Nat:
  ECfg{f, p, d, w, m, t} = c
  d

def workers(+c: Cfg) -> Nat:
  ECfg{f, p, d, w, m, t} = c
  w

def max_workers(+c: Cfg) -> Nat:
  ECfg{f, p, d, w, m, t} = c
  m

def targets(+c: Cfg) -> Nat:
  ECfg{f, p, d, w, m, t} = c
  t

# a bounded rate, at most one hit per ns
def bounded(+c: Cfg) -> Bool:
  Bool.and(Nat.is_gt(freq(c), 0n), Nat.is_ge(per(c), freq(c)))

# Go's pacer interval, in whole ns
def interval(+c: Cfg) -> Nat:
  Nat.div(per(c), freq(c))

# hit i is due at (i + 1) intervals
def slot(+c: Cfg, +i: Nat) -> Nat:
  Nat.mul(1n+i, interval(c))

# the hits an attack of this length is scheduled to send
def scheduled(+c: Cfg) -> Nat:
  Nat.div(Nat.add(dur(c), Nat.sub(interval(c), 1n)), interval(c))

def initial(+c: Cfg) -> Nat:
  Nat.min(workers(c), max_workers(c))

# a strict choice: both branches are evaluated (keep loops out of them)
def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def has_nat(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, +rest}:
      Bool.or(Nat.is_eq(x, y), has_nat(x, rest))

def drop_nat(+x: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case Con{+y, +rest}:
      pick(List<&2, Nat>, Nat.is_eq(x, y), rest, Con{y, drop_nat(x, rest)})

# the stop is decided: a hit went out at or past the deadline
def stop_due(+d: Nat, +last: Maybe<&2, Nat>) -> Bool:
  match last:
    case None{}:
      False{}
    case Some{t}:
      Bool.and(Nat.is_gt(d, 0n), Nat.is_ge(t, d))

# a hit is due now: its slot has come (bounded), or always (unbounded)
def due.of(b: Bool, +c: Cfg, +now: Nat, +next: Nat) -> Bool:
  match b:
    case True{}:
      Nat.is_ge(now, slot(c, next))
    case False{}:
      True{}

def due(+c: Cfg, +now: Nat, +next: Nat) -> Bool:
  due.of(bounded(c), c, now, next)

# a hit may go out now: the stop is not decided, and one is due
def may(+c: Cfg, +now: Nat, +next: Nat, +last: Maybe<&2, Nat>) -> Bool:
  Bool.and(Bool.not(stop_due(dur(c), last)), due(c, now, next))

def dropped.of(b: Bool, +c: Cfg, +sent: Nat) -> Nat:
  match b:
    case True{}:
      Nat.sub(scheduled(c), sent)
    case False{}:
      0n

def dropped(+c: Cfg, +sent: Nat) -> Nat:
  dropped.of(bounded(c), c, sent)

# a nap is wanted: bounded, none open, and the next slot still ahead
def wants_nap(+c: Cfg, +now: Nat, +next: Nat, +nap: Bool) -> Bool:
  Bool.and(bounded(c), Bool.and(Bool.not(nap), Nat.is_gt(slot(c, next), now)))

def fire(+c: Cfg, +w: Nat, +next: Nat, +now: Nat) -> Cmd:
  Fire{w, next, Nat.mod(next, targets(c)), now}

# ---------------------------------------------------------------------
# After dispatch: the stop once no worker is busy, or a nap until the
# next slot
# ---------------------------------------------------------------------

def settle.quit_cs(q: Bool, +c: Cfg, +next: Nat) -> List<&2, Cmd>:
  match q:
    case True{}:
      [Quit{next, dropped(c, next)}]
    case False{}:
      []

def settle.nap_cs(n: Bool, +c: Cfg, +next: Nat) -> List<&2, Cmd>:
  match n:
    case True{}:
      [Nap{slot(c, next)}]
    case False{}:
      []

def settle.of_cs(stop: Bool, +c: Cfg, +now: Nat, +next: Nat, +busy: List<&2, Nat>, +nap: Bool) -> List<&2, Cmd>:
  match stop:
    case True{}:
      settle.quit_cs(List.is_empty(&2, Nat, busy), c, next)
    case False{}:
      settle.nap_cs(wants_nap(c, now, next, nap), c, next)

def settle_cs(+c: Cfg, +now: Nat, +next: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>) -> List<&2, Cmd>:
  settle.of_cs(stop_due(dur(c), last), c, now, next, busy, nap)

def settle.nap_st(n: Bool, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>) -> State:
  match n:
    case True{}:
      EState{now, next, grown, room, busy, idle, True{}, last, False{}}
    case False{}:
      EState{now, next, grown, room, busy, idle, nap, last, False{}}

def settle.of_st(stop: Bool, +c: Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>) -> State:
  match stop:
    case True{}:
      EState{now, next, grown, room, busy, idle, nap, last, List.is_empty(&2, Nat, busy)}
    case False{}:
      settle.nap_st(wants_nap(c, now, next, nap), now, next, grown, room, busy, idle, nap, last)

def settle_st(+c: Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>) -> State:
  settle.of_st(stop_due(dur(c), last), c, now, next, grown, room, busy, idle, nap, last)

# ---------------------------------------------------------------------
# Dispatch to new workers: one per due hit while there is room
# ---------------------------------------------------------------------

def grow_cs(room: Nat, ok: Bool, +c: Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>) -> List<&2, Cmd>:
  match room:
    case 0n:
      settle_cs(c, now, next, busy, nap, last)
    case 1n+r:
      match ok:
        case True{}:
          Con{Grow{grown}, Con{fire(c, grown, next, now),
            grow_cs(r, may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now})}}
        case False{}:
          settle_cs(c, now, next, busy, nap, last)

def grow_st(room: Nat, ok: Bool, +c: Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>) -> State:
  match room:
    case 0n:
      settle_st(c, now, next, grown, 0n, busy, [], nap, last)
    case 1n+r:
      match ok:
        case True{}:
          grow_st(r, may(c, now, 1n+next, Some{now}), c, now, 1n+next, 1n+grown, Con{grown, busy}, nap, Some{now})
        case False{}:
          settle_st(c, now, next, grown, 1n+r, busy, [], nap, last)

# ---------------------------------------------------------------------
# Dispatch to idle workers: one per due hit while one is idle, then to
# new ones
# ---------------------------------------------------------------------

def idle_cs(idle: List<&2, Nat>, ok: Bool, +c: Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>) -> List<&2, Cmd>:
  match idle:
    case Nil{}:
      grow_cs(room, ok, c, now, next, grown, busy, nap, last)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          Con{fire(c, w, next, now),
            idle_cs(rest, may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now})}
        case False{}:
          settle_cs(c, now, next, busy, nap, last)

def idle_st(idle: List<&2, Nat>, ok: Bool, +c: Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>) -> State:
  match idle:
    case Nil{}:
      grow_st(room, ok, c, now, next, grown, busy, nap, last)
    case Con{+w, +rest}:
      match ok:
        case True{}:
          idle_st(rest, may(c, now, 1n+next, Some{now}), c, now, 1n+next, grown, room, Con{w, busy}, nap, Some{now})
        case False{}:
          settle_st(c, now, next, grown, room, busy, Con{w, rest}, nap, last)

# the engine's answer once it has taken an event in: dispatch, then settle
def react(+c: Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>)
  -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  (idle_st(idle, may(c, now, next, last), c, now, next, grown, room, busy, nap, last),
   idle_cs(idle, may(c, now, next, last), c, now, next, grown, room, busy, nap, last))

def ids(n: Nat, +from: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{from, ids(p, 1n+from)}

def grows(n: Nat, +from: Nat) -> List<&2, Cmd>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{Grow{from}, grows(p, 1n+from)}

def start(+c: Cfg) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  +i = initial(c)
  +room = Nat.sub(max_workers(c), i)
  (idle_st(ids(i, 0n), may(c, 0n, 0n, None{}), c, 0n, 0n, i, room, [], False{}, None{}),
   List.append(&2, Cmd, grows(i, 0n), idle_cs(ids(i, 0n), may(c, 0n, 0n, None{}), c, 0n, 0n, i, room, [], False{}, None{})))

# a freed worker that was busy goes idle
def freed_idle(b: Bool, +w: Nat, +idle: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Con{w, idle}
    case False{}:
      idle

# after the quit an event is still taken in, and nothing is answered
def step.go(over: Bool, +c: Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>)
  -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match over:
    case True{}:
      (EState{now, next, grown, room, busy, idle, nap, last, True{}}, [])
    case False{}:
      react(c, now, next, grown, room, busy, idle, nap, last)

# the event taken in: the time; a clock ends the nap; a busy worker freed
# goes idle
def step.ev(e: Ev, +over: Bool, +c: Cfg, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>)
  -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match e:
    case Clock{t}:
      step.go(over, c, t, next, grown, room, busy, idle, False{}, last)
    case Freed{+w, t}:
      step.go(over, c, t, next, grown, room, drop_nat(w, busy), freed_idle(has_nat(w, busy), w, idle), nap, last)

def step(+c: Cfg, +s: State, e: Ev) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match s:
    case EState{now, next, grown, room, busy, idle, nap, last, over}:
      step.ev(e, over, c, next, grown, room, busy, idle, nap, last)

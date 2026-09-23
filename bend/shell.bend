# The shell: the only IO loop of an attack. It runs the engine's and the
# clients' commands as effects and feeds back what happened; every
# decision is theirs (lib/engine.bend, lib/conn.bend), proven in LAWS.bend.
#
# One event loop, as an epoll server: each worker the engine grows is a
# slot (its connection and the hit in flight), not a computation. When
# nothing is left to run, the loop waits on every connection at once
# (Fd.wait), then steps every ready connection's client machine, and
# encodes every finished result, in a parallel call tree: Bend spreads
# parallel calls over the cores, while IO computations share one. The
# loop reads the clock when it takes events in, so the engine's times
# never go back.
import Base
import ./lib/sys.bend as Sys
import ./lib/engine.bend as Eng
import ./lib/conn.bend as Conn
import ./lib/target.bend as Tgt
import ./lib/civil.bend as Civil
import ./lib/hit.bend as Hit

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# a target ready to send: parsed URL, resolved address, and the body (the
# target's @file, or -body's, read in)
type Prep is Data:
  Prep{target: Tgt.Target, url: Tgt.Url, ip: String, body: String}

# what every hit shares: client config, attack name, output format (JSON
# lines, or CSV), the targets
type WEnv is Data:
  WEnv{cc: Conn.Cfg, name: String, json: Bool, preps: List<&2, Prep>}

def e_cc(+e: WEnv) -> Conn.Cfg:
  WEnv{cc, name, json, preps} = e
  cc

def e_name(+e: WEnv) -> String:
  WEnv{cc, name, json, preps} = e
  name

def e_json(+e: WEnv) -> Bool:
  WEnv{cc, name, json, preps} = e
  json

def e_preps(+e: WEnv) -> List<&2, Prep>:
  WEnv{cc, name, json, preps} = e
  preps

def timeout(+c: Conn.Cfg) -> Nat:
  Conn.CCfg{ka, to, mb, rd} = c
  to

def st_of(+r: Sigma<&2, &2, Conn.State, _ => List<&2, Conn.Cmd>>) -> Conn.State:
  (s, cs) = r
  s

def cs_of(+r: Sigma<&2, &2, Conn.State, _ => List<&2, Conn.Cmd>>) -> List<&2, Conn.Cmd>:
  (s, cs) = r
  cs

def est_of(+r: Sigma<&2, &2, Eng.State, _ => List<&2, Eng.Cmd>>) -> Eng.State:
  (s, cs) = r
  s

def ecs_of(+r: Sigma<&2, &2, Eng.State, _ => List<&2, Eng.Cmd>>) -> List<&2, Eng.Cmd>:
  (s, cs) = r
  cs

def prep_at(+ps: List<&2, Prep>, +i: Nat) -> Prep:
  Maybe.default(&2, Prep, List.get(&2, Prep, ps, i), Prep{Tgt.Target{"", "", [], None{}}, Tgt.Url{"", "", None{}, ""}, "", ""})

def req_of(+p: Prep, +seq: Nat, +name: String) -> Conn.Req:
  Prep{t, u, ip, body} = p
  Conn.Req{t, u, ip, body, seq, name}

def req_method(+p: Prep) -> String:
  Prep{t, u, ip, b} = p
  Tgt.Target{method, url, hs, body} = t
  method

def req_url(+p: Prep) -> String:
  Prep{t, u, ip, b} = p
  Tgt.Target{method, url, hs, body} = t
  url

def req_len(+p: Prep) -> Nat:
  Prep{t, u, ip, body} = p
  String.length(body)

# a match, not a pick: pick is strict and would encode both ways
def encode(json: Bool, +h: Hit.Hit) -> String:
  match json:
    case True{}:
      Hit.to_json(h)
    case False{}:
      Hit.to_csv(h)

def wall_time.of(+sec: Nat, r: Nat & U32) -> Civil.Time:
  (nsec, off) = r
  Civil.Time{sec, nsec, U32.to_nat(off)}

def wall_time(w: Nat & Nat & U32) -> Civil.Time:
  (sec, rest) = w
  wall_time.of(sec, rest)

# ---------------------------------------------------------------------
# Slots: a worker's connection and the hit it has in flight
# ---------------------------------------------------------------------

# a hit in flight: the client machine, the hit's seq and target, its
# start (mono ns and wall time), and its deadline (mono ns, 0: none)
type Fly is Data:
  Fly{st: Conn.State, seq: Nat, ti: Nat, t0: Nat, ts: Civil.Time, dl: Nat}

type Slot is Data:
  Slot{w: Nat, fd: Maybe<&2, U32>, fly: Maybe<&2, Fly>}

def fly_st(+f: Fly) -> Conn.State:
  Fly{st, seq, ti, t0, ts, dl} = f
  st

def fly_with(+f: Fly, +st: Conn.State) -> Fly:
  Fly{s0, seq, ti, t0, ts, dl} = f
  Fly{st, seq, ti, t0, ts, dl}

def fly_dl(+f: Fly) -> Nat:
  Fly{st, seq, ti, t0, ts, dl} = f
  dl

# the result line of a finished hit, at mono time t1
def fly_line(+e: WEnv, +f: Fly, +t1: Nat, +o: Conn.Out) -> String:
  Fly{st, seq, ti, t0, ts, dl} = f
  +p = prep_at(e_preps(e), ti)
  encode(e_json(e), Conn.to_hit(e_name(e), seq, ts, Nat.sub(t1, t0), req_method(p), req_url(p), req_len(p), o))

def slot_w(+s: Slot) -> Nat:
  Slot{w, fd, fly} = s
  w

def slot_fd(+s: Slot) -> Maybe<&2, U32>:
  Slot{w, fd, fly} = s
  fd

def slot_open(+s: Slot) -> Bool:
  Maybe.is_some(&2, U32, slot_fd(s))

def put.of(grow: Bool, slots: List<&2, Slot>, +s: Slot) -> List<&2, Slot>:
  match grow:
    case True{}:
      List.append(&2, Slot, slots, [s])
    case False{}:
      List.set(&2, Slot, slots, slot_w(s), s)

# replaces worker w's slot; workers are numbered in order, so a new one
# is appended
def put(+slots: List<&2, Slot>, +s: Slot) -> List<&2, Slot>:
  put.of(Nat.is_ge(slot_w(s), List.length(&2, Slot, slots)), slots, s)

def get_w(+slots: List<&2, Slot>, +w: Nat) -> Slot:
  Maybe.default(&2, Slot, List.get(&2, Slot, slots, w), Slot{w, None{}, None{}})

def fd_is(+m: Maybe<&2, U32>, +fd: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      U32.is_eq(x, fd)

# the slot on fd (a strict pick: the walk is whole either way, and only a
# Maybe is built)
def get_fd(slots: List<&2, Slot>, +fd: U32) -> Maybe<&2, Slot>:
  match slots:
    case Nil{}:
      None{}
    case Con{+x, rest}:
      pick(Maybe<&2, Slot>, fd_is(slot_fd(x), fd), Some{x}, get_fd(rest, fd))

def fds.of(fd: Maybe<&2, U32>, +acc: List<&2, U32>) -> List<&2, U32>:
  match fd:
    case None{}:
      acc
    case Some{d}:
      Con{d, acc}

# every open connection, to wait on
def fds(slots: List<&2, Slot>) -> List<&2, U32>:
  match slots:
    case Nil{}:
      []
    case Con{+x, rest}:
      fds.of(slot_fd(x), fds(rest))

def min_dl.of(fly: Maybe<&2, Fly>, +acc: Nat) -> Nat:
  match fly:
    case None{}:
      acc
    case Some{+f}:
      +d = fly_dl(f)
      pick(Nat, Bool.and(Nat.is_gt(d, 0n), Bool.or(Nat.is_eq(acc, 0n), Nat.is_lt(d, acc))), d, acc)

def slot_fly(+s: Slot) -> Maybe<&2, Fly>:
  Slot{w, fd, fly} = s
  fly

# the earliest deadline of the hits in flight (0: none)
def min_dl(slots: List<&2, Slot>, +acc: Nat) -> Nat:
  match slots:
    case Nil{}:
      acc
    case Con{+x, rest}:
      min_dl(rest, min_dl.of(slot_fly(x), acc))

# ---------------------------------------------------------------------
# Running one slot's client commands (sequential IO): until the machine
# waits for bytes (Recv) or finishes
# ---------------------------------------------------------------------

# what a slot's run ends in: the slot, and the result line if the hit
# finished
type Ran is Data:
  Ran{slot: Slot, line: Maybe<&2, String>}

type Drv is Type:
  Run{cmds: List<&2, Conn.Cmd>}
  Feed{ev: Conn.Ev}
  OpenRes{r: Result<&1, &1, U32 & String, U32>}
  SendRes{r: Result<&1, &1, U32 & String, Unit>}
  DnsRes{r: Result<&1, &1, U32 & String, String>}

def close(fd: Maybe<&2, U32>) -> IO(Unit):
  match fd:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{d}:
      Sys.Fd.close(d)

def sent(r: Result<&1, &1, U32 & String, Unit>) -> Conn.Ev:
  match r:
    case Done{u}:
      Conn.Sent{}
    case Fail{(code, msg)}:
      Conn.SendFailed{msg}

def resolved(r: Result<&1, &1, U32 & String, String>) -> Conn.Ev:
  match r:
    case Done{ip}:
      Conn.Resolved{ip}
    case Fail{(code, msg)}:
      Conn.ResolveFailed{msg}

# a hit's end: its line, and the connection closed unless kept
def finish(keep: Bool, +w: Nat, fd: Maybe<&2, U32>, +line: String) -> IO(Ran):
  match keep:
    case True{}:
      IO.pure(Ran, Ran{Slot{w, fd, None{}}, Some{line}})
    case False{}:
      do IO<Ran>:
        close(fd)
        return Ran{Slot{w, None{}, None{}}, Some{line}}

@unsafe def srun(m: Drv, +e: WEnv, +w: Nat, fd: Maybe<&2, U32>, +f: Fly) -> IO(Ran):
  match m:
    case Feed{ev}:
      +r = Conn.step(e_cc(e), fly_st(f), ev)
      srun(Run{cs_of(r)}, e, w, fd, fly_with(f, st_of(r)))
    case OpenRes{r}:
      match r:
        case Done{d}:
          srun(Feed{Conn.Opened{}}, e, w, Some{d}, f)
        case Fail{(code, msg)}:
          srun(Feed{Conn.OpenFailed{msg}}, e, w, None{}, f)
    case SendRes{r}:
      srun(Feed{sent(r)}, e, w, fd, f)
    case DnsRes{r}:
      srun(Feed{resolved(r)}, e, w, fd, f)
    case Run{cmds}:
      match cmds:
        case Nil{}:
          do IO<Ran>:
            +t1 : Nat <- Sys.Clock.mono_ns()
            finish(False{}, w, fd, fly_line(e, f, t1, Conn.Failed{"bend: the client stopped without an answer", None{}}))
        case Con{cmd, rest}:
          match cmd:
            case Conn.Recv{}:
              IO.pure(Ran, Ran{Slot{w, fd, Some{f}}, None{}})
            case Conn.Finish{o, keep}:
              do IO<Ran>:
                +t1 : Nat <- Sys.Clock.mono_ns()
                finish(keep, w, fd, fly_line(e, f, t1, o))
            case Conn.Shut{}:
              do IO<Ran>:
                close(fd)
                srun(Run{rest}, e, w, None{}, f)
            case Conn.Open{ip, port}:
              do IO<Ran>:
                close(fd)
                r : Result<&1, &1, U32 & String, U32> <- Sys.Fd.connect(ip, U32.from_nat(port))
                srun(OpenRes{r}, e, w, None{}, f)
            case Conn.Send{d}:
              match fd:
                case None{}:
                  srun(Feed{Conn.SendFailed{"bend: no connection"}}, e, w, None{}, f)
                case Some{+x}:
                  do IO<Ran>:
                    r : Result<&1, &1, U32 & String, Unit> <- Sys.Fd.send(x, d)
                    srun(SendRes{r}, e, w, Some{x}, f)
            case Conn.Resolve{h}:
              do IO<Ran>:
                r : Result<&1, &1, U32 & String, String> <- Sys.Dns.resolve(h)
                srun(DnsRes{r}, e, w, fd, f)

# ---------------------------------------------------------------------
# The parallel step: every ready connection's machine takes its event
# ---------------------------------------------------------------------

# a slot with a hit in flight and the event it takes
type Item is Data:
  Item{w: Nat, fd: Maybe<&2, U32>, fly: Fly, ev: Conn.Ev}

# the step taken: the slot's new machine and commands, and the result line
# when the commands are just a finish (keep: the connection stays)
type Stepped is Data:
  Stepped{w: Nat, fd: Maybe<&2, U32>, fly: Fly, cmds: List<&2, Conn.Cmd>, done: Maybe<&2, String>, keep: Bool}

def fin_only(cs: List<&2, Conn.Cmd>) -> Maybe<&2, Conn.Out>:
  match cs:
    case Con{c, rest}:
      match c:
        case Conn.Finish{o, k}:
          Some{o}
        case _:
          None{}
    case Nil{}:
      None{}

def fin_keep(cs: List<&2, Conn.Cmd>) -> Bool:
  match cs:
    case Con{c, rest}:
      match c:
        case Conn.Finish{o, k}:
          k
        case _:
          False{}
    case Nil{}:
      False{}

def done_line(m: Maybe<&2, Conn.Out>, +e: WEnv, +f: Fly, +t1: Nat) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{o}:
      Some{fly_line(e, f, t1, o)}

def step1(+e: WEnv, +t1: Nat, it: Item) -> Stepped:
  Item{w, fd, +f, ev} = it
  +r = Conn.step(e_cc(e), fly_st(f), ev)
  +cs = cs_of(r)
  +f2 = fly_with(f, st_of(r))
  Stepped{w, fd, f2, cs, done_line(fin_only(cs), e, f2, t1), fin_keep(cs)}

type Tree is Data:
  TNil{}
  TOne{x: Item}
  TTwo{l: Tree, r: Tree}

def tree1(xs: List<&2, Item>) -> Tree:
  match xs:
    case Nil{}:
      TNil{}
    case Con{x, rest}:
      TOne{x}

# a balanced tree of the items (n of them)
@unsafe def tree(+n: Nat, +xs: List<&2, Item>) -> Tree:
  match n:
    case 0n:
      TNil{}
    case 1n+m:
      match m:
        case 0n:
          tree1(xs)
        case 1n+k:
          +h = Nat.div(Nat.add(k, 2n), 2n)
          TTwo{tree(h, List.take(&2, Item, xs, h)), tree(Nat.sub(Nat.add(k, 2n), h), List.drop(&2, Item, xs, h))}

# the steps, in parallel: the two halves of the tree are a parallel call
def psteps(t: Tree, +e: WEnv, +t1: Nat) -> List<&2, Stepped>:
  match t:
    case TNil{}:
      []
    case TOne{x}:
      [step1(e, t1, x)]
    case TTwo{l, r}:
      a b = psteps(l, e, t1) psteps(r, e, t1)
      List.append(&2, Stepped, a, b)

# ---------------------------------------------------------------------
# Taking in what a wait found
# ---------------------------------------------------------------------

# the events for the slots: bytes or a close for a hit in flight; idle
# connections that closed (or spoke out of turn) are dropped, as Go's
# transport drops an idle connection its read loop saw closed
type Taken is Data:
  Taken{items: List<&2, Item>, dead: List<&2, Nat>}

def ev_of(d: String) -> Conn.Ev:
  match d:
    case SNil{}:
      Conn.Eof{}
    case SCon{c, rest}:
      Conn.Got{SCon{c, rest}}

def take_fly(fly: Maybe<&2, Fly>, +w: Nat, +fd: Maybe<&2, U32>, +d: String, +acc: Taken) -> Taken:
  match fly:
    case None{}:
      Taken{items, dead} = acc
      Taken{items, Con{w, dead}}
    case Some{f}:
      Taken{items, dead} = acc
      Taken{Con{Item{w, fd, f, ev_of(d)}, items}, dead}

def take_one(m: Maybe<&2, Slot>, +d: String, +acc: Taken) -> Taken:
  match m:
    case None{}:
      acc
    case Some{s}:
      Slot{w, fd, fly} = s
      take_fly(fly, w, fd, d, acc)

def take_p(p: Sigma<&2, &2, U32, _ => String>, +slots: List<&2, Slot>, +acc: Taken) -> Taken:
  (fd, d) = p
  take_one(get_fd(slots, fd), d, acc)

def take(rs: List<&2, Sigma<&2, &2, U32, _ => String>>, +slots: List<&2, Slot>, +acc: Taken) -> Taken:
  match rs:
    case Nil{}:
      acc
    case Con{p, rest}:
      take(rest, slots, take_p(p, slots, acc))

def item_w(+it: Item) -> Nat:
  Item{w, fd, f, ev} = it
  w

def has_w(+w: Nat, its: List<&2, Item>) -> Bool:
  match its:
    case Nil{}:
      False{}
    case Con{+it, rest}:
      Bool.or(Nat.is_eq(w, item_w(it)), has_w(w, rest))

def lates.add(yes: Bool, +it: Item, +its: List<&2, Item>) -> List<&2, Item>:
  match yes:
    case True{}:
      Con{it, its}
    case False{}:
      its

def lates.of(fly: Maybe<&2, Fly>, +w: Nat, +fd: Maybe<&2, U32>, +now: Nat, +its: List<&2, Item>) -> List<&2, Item>:
  match fly:
    case None{}:
      its
    case Some{+f}:
      +d = fly_dl(f)
      lates.add(Bool.and(Bool.and(Nat.is_gt(d, 0n), Nat.is_ge(now, d)), Bool.not(has_w(w, its))), Item{w, fd, f, Conn.Late{}}, its)

# hits past their deadline that got nothing this round take a Late
def lates(slots: List<&2, Slot>, +now: Nat, +its: List<&2, Item>) -> List<&2, Item>:
  match slots:
    case Nil{}:
      its
    case Con{s, rest}:
      Slot{w, fd, fly} = s
      lates(rest, now, lates.of(fly, w, fd, now, its))

# ---------------------------------------------------------------------
# The loop
# ---------------------------------------------------------------------

# the loop's state: when the attack began (mono ns), the engine, the
# slots, the nap's end (attack ns), the workers freed and not yet told
# to the engine, the result lines not yet written (newest first)
type Lp is Data:
  Lp{t0: Nat, st: Eng.State, slots: List<&2, Slot>, nap: Maybe<&2, Nat>, freed: List<&2, Nat>, lines: List<&2, String>}

def lp_slots(+l: Lp) -> List<&2, Slot>:
  Lp{t0, st, slots, nap, freed, lines} = l
  slots

def lp_lines(+l: Lp) -> List<&2, String>:
  Lp{t0, st, slots, nap, freed, lines} = l
  lines

def no_lines(+l: Lp) -> Lp:
  Lp{t0, st, slots, nap, freed, lines} = l
  Lp{t0, st, slots, nap, freed, []}

def with_slots(+l: Lp, +ss: List<&2, Slot>) -> Lp:
  Lp{t0, st, slots, nap, freed, lines} = l
  Lp{t0, st, ss, nap, freed, lines}

def with_slot(+l: Lp, +s: Slot) -> Lp:
  Lp{t0, st, slots, nap, freed, lines} = l
  Lp{t0, st, put(slots, s), nap, freed, lines}

def with_nap(+l: Lp, +u: Nat) -> Lp:
  Lp{t0, st, slots, nap, freed, lines} = l
  Lp{t0, st, slots, Some{u}, freed, lines}

def with_line(line: Maybe<&2, String>, +w: Nat, +l: Lp) -> Lp:
  match line:
    case None{}:
      l
    case Some{x}:
      Lp{t0, st, slots, nap, freed, lines} = l
      Lp{t0, st, slots, nap, List.append(&2, Nat, freed, [w]), Con{x, lines}}

def with_ran(+l: Lp, +r: Ran) -> Lp:
  Ran{s, line} = r
  with_line(line, slot_w(s), with_slot(l, s))

def deadline(+c: Conn.Cfg, +t0: Nat) -> Nat:
  pick(Nat, Nat.is_eq(timeout(c), 0n), 0n, Nat.add(t0, timeout(c)))

def nap_abs(+t0: Nat, +nap: Maybe<&2, Nat>) -> Nat:
  match nap:
    case None{}:
      0n
    case Some{u}:
      Nat.add(t0, u)

def earliest(+a: Nat, +b: Nat) -> Nat:
  pick(Nat, Nat.is_eq(a, 0n), b, pick(Nat, Bool.or(Nat.is_eq(b, 0n), Nat.is_lt(a, b)), a, b))

# how long to wait (ms): until the nap ends or the earliest deadline, else
# a second (the loop then looks again)
def wait_ms(+l: Lp, +now: Nat) -> U32:
  Lp{t0, st, slots, nap, freed, lines} = l
  +until = earliest(nap_abs(t0, nap), min_dl(slots, 0n))
  pick(U32, Nat.is_eq(until, 0n), 1000,
    U32.from_nat(pick(Nat, Nat.is_gt(until, now), Nat.div(Nat.add(Nat.sub(until, now), 999999n), 1000000n), 0n)))

def close_all(slots: List<&2, Slot>) -> IO(Unit):
  match slots:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+s, rest}:
      do IO<Unit>:
        close(slot_fd(s))
        close_all(rest)

def close_dead(dead: List<&2, Nat>, +slots: List<&2, Slot>) -> IO(List<&2, Slot>):
  match dead:
    case Nil{}:
      IO.pure(List<&2, Slot>, slots)
    case Con{+w, rest}:
      do IO<List<&2, Slot>>:
        close(slot_fd(get_w(slots, w)))
        close_dead(rest, put(slots, Slot{w, None{}, None{}}))

# the lines oldest first, as one string
def joined(ls: List<&2, String>, acc: String) -> String:
  match ls:
    case Nil{}:
      acc
    case Con{x, rest}:
      joined(rest, x ++ acc)

def flush(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{x, rest}:
      Sys.Out.write(joined(Con{x, rest}, ""))

# what the engine takes next: the clock when the nap is over, else the
# next freed worker; None when there is nothing, and the loop waits
type Nx is Data:
  Nx{l: Lp, cs: Maybe<&2, List<&2, Eng.Cmd>>}

def next_freed(freed: List<&2, Nat>, +t0: Nat, +st: Eng.State, +slots: List<&2, Slot>, +nap: Maybe<&2, Nat>, +lines: List<&2, String>, +ec: Eng.Cfg, +t: Nat) -> Nx:
  match freed:
    case Nil{}:
      Nx{Lp{t0, st, slots, nap, [], lines}, None{}}
    case Con{+w, rest}:
      +r = Eng.step(ec, st, Eng.Freed{w, t})
      Nx{Lp{t0, est_of(r), slots, nap, rest, lines}, Some{ecs_of(r)}}

def next_nap(due: Bool, +u: Nat, +freed: List<&2, Nat>, +t0: Nat, +st: Eng.State, +slots: List<&2, Slot>, +lines: List<&2, String>, +ec: Eng.Cfg, +t: Nat) -> Nx:
  match due:
    case True{}:
      +r = Eng.step(ec, st, Eng.Clock{t})
      Nx{Lp{t0, est_of(r), slots, None{}, freed, lines}, Some{ecs_of(r)}}
    case False{}:
      next_freed(freed, t0, st, slots, Some{u}, lines, ec, t)

def next_ev.of(nap: Maybe<&2, Nat>, +freed: List<&2, Nat>, +t0: Nat, +st: Eng.State, +slots: List<&2, Slot>, +lines: List<&2, String>, +ec: Eng.Cfg, +t: Nat) -> Nx:
  match nap:
    case Some{+u}:
      next_nap(Nat.is_ge(t, u), u, freed, t0, st, slots, lines, ec, t)
    case None{}:
      next_freed(freed, t0, st, slots, None{}, lines, ec, t)

def next_ev(+l: Lp, +ec: Eng.Cfg, +now: Nat) -> Nx:
  Lp{t0, st, slots, nap, freed, lines} = l
  next_ev.of(nap, freed, t0, st, slots, lines, ec, Nat.sub(now, t0))

# the loop's next move: run the engine's commands; decide what the engine
# takes next; start a fired hit; take in a slot's run, a wait's findings,
# or the parallel step's results one by one
type Am is Type:
  Cmds{cs: List<&2, Eng.Cmd>}
  Idle{}
  Decide{nx: Nx, now: Nat}
  Fired{cs: List<&2, Eng.Cmd>, w: Nat, seq: Nat, ti: Nat, t0: Nat, wall: Nat & Nat & U32}
  Slotted{cs: List<&2, Eng.Cmd>, r: Ran}
  Waited{rs: List<&2, Sigma<&2, &2, U32, _ => String>>, now: Nat}
  Took{tk: Taken, now: Nat}
  Stepping{xs: List<&2, Stepped>}

@unsafe def attack(a: Am, +ec: Eng.Cfg, +e: WEnv, +l: Lp) -> IO(Nat & Nat):
  match a:
    case Idle{}:
      do IO<Nat & Nat>:
        +now : Nat <- Sys.Clock.mono_ns()
        attack(Decide{next_ev(l, ec, now), now}, ec, e, l)
    case Decide{nx, +now}:
      match nx:
        case Nx{+l2, m}:
          match m:
            case Some{cs}:
              attack(Cmds{cs}, ec, e, l2)
            case None{}:
              do IO<Nat & Nat>:
                flush(lp_lines(l2))
                rs : List<&2, Sigma<&2, &2, U32, _ => String>> <- Sys.Fd.wait(fds(lp_slots(l2)), 65536, wait_ms(l2, now))
                +now2 : Nat <- Sys.Clock.mono_ns()
                attack(Waited{rs, now2}, ec, e, no_lines(l2))
    case Cmds{cs}:
      match cs:
        case Nil{}:
          attack(Idle{}, ec, e, l)
        case Con{c, rest}:
          match c:
            case Eng.Grow{+w}:
              attack(Cmds{rest}, ec, e, with_slot(l, Slot{w, None{}, None{}}))
            case Eng.Nap{u}:
              attack(Cmds{rest}, ec, e, with_nap(l, u))
            case Eng.Fire{+w, +seq, +ti, t}:
              do IO<Nat & Nat>:
                +h0 : Nat <- Sys.Clock.mono_ns()
                wall : Nat & Nat & U32 <- Sys.Clock.wall()
                attack(Fired{rest, w, seq, ti, h0, wall}, ec, e, l)
            case Eng.Quit{sent, dropped}:
              do IO<Nat & Nat>:
                flush(lp_lines(l))
                close_all(lp_slots(l))
                return (sent, dropped)
    case Fired{cs, +w, +seq, +ti, +h0, wall}:
      +s = get_w(lp_slots(l), w)
      +r0 = Conn.start(e_cc(e), req_of(prep_at(e_preps(e), ti), seq, e_name(e)), slot_open(s))
      do IO<Nat & Nat>:
        r : Ran <- srun(Run{cs_of(r0)}, e, w, slot_fd(s), Fly{st_of(r0), seq, ti, h0, wall_time(wall), deadline(e_cc(e), h0)})
        attack(Slotted{cs, r}, ec, e, l)
    case Slotted{cs, r}:
      attack(Cmds{cs}, ec, e, with_ran(l, r))
    case Waited{rs, +now}:
      attack(Took{take(rs, lp_slots(l), Taken{[], []}), now}, ec, e, l)
    case Took{tk, +now}:
      match tk:
        case Taken{items, dead}:
          +its = lates(lp_slots(l), now, items)
          do IO<Nat & Nat>:
            ss : List<&2, Slot> <- close_dead(dead, lp_slots(l))
            attack(Stepping{psteps(tree(List.length(&2, Item, its), its), e, now)}, ec, e, with_slots(l, ss))
    case Stepping{xs}:
      match xs:
        case Nil{}:
          attack(Idle{}, ec, e, l)
        case Con{x, rest}:
          match x:
            case Stepped{+w, fd, f, cmds, done, keep}:
              match done:
                case Some{line}:
                  do IO<Nat & Nat>:
                    r : Ran <- finish(keep, w, fd, line)
                    attack(Stepping{rest}, ec, e, with_ran(l, r))
                case None{}:
                  do IO<Nat & Nat>:
                    r : Ran <- srun(Run{cmds}, e, w, fd, f)
                    attack(Stepping{rest}, ec, e, with_ran(l, r))

# runs an attack to its end, writing the results as they come; answers
# (sent, dropped)
def run(+ec: Eng.Cfg, +e: WEnv) -> IO(Nat & Nat):
  +r = Eng.start(ec)
  do IO<Nat & Nat>:
    +t0 : Nat <- Sys.Clock.mono_ns()
    attack(Cmds{ecs_of(r)}, ec, e, Lp{t0, est_of(r), [], None{}, [], []})

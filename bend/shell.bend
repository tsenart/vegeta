# The shell: the only IO loop of an attack. It runs the engine's and the
# clients' commands as effects and feeds back what happened; every
# decision is theirs (lib/engine.bend, lib/conn.bend), proven in LAWS.bend.
#
# One event loop, as an epoll server: each worker the engine grows is a
# slot (its connection and the hit in flight), not a computation. When
# nothing is left to run, the loop waits on every connection at once
# (Fd.next, over kqueue or epoll, to the nanosecond), then steps every ready connection's client machine, and
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

# a hit's deadline (mono ns): its start plus the timeout (0: none)
def deadline(+c: Conn.Cfg, +t0: Nat) -> Nat:
  pick(Nat, Nat.is_eq(timeout(c), 0n), 0n, Nat.add(t0, timeout(c)))

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

# the slots, as a tree keyed by worker: worker 0 at the root, worker
# 1 + k down the left (k even) or right (k odd) child at k / 2
type Tr is Data:
  TrE{}
  TrN{s: Maybe<&2, Slot>, l: Tr, r: Tr}

def tr_child(even: Bool, +l: Tr, +r: Tr) -> Tr:
  match even:
    case True{}:
      l
    case False{}:
      r

def tr_join(even: Bool, +s0: Maybe<&2, Slot>, +l: Tr, +r: Tr, +c: Tr) -> Tr:
  match even:
    case True{}:
      TrN{s0, c, r}
    case False{}:
      TrN{s0, l, c}

@unsafe def tr_get(t: Tr, +w: Nat) -> Maybe<&2, Slot>:
  match t:
    case TrE{}:
      None{}
    case TrN{s0, +l, +r}:
      match w:
        case 0n:
          s0
        case 1n+(+k):
          tr_get(tr_child(Nat.is_eq(Nat.mod(k, 2n), 0n), l, r), Nat.div(k, 2n))

@unsafe def tr_put(t: Tr, +w: Nat, +s: Slot) -> Tr:
  match t:
    case TrE{}:
      tr_put(TrN{None{}, TrE{}, TrE{}}, w, s)
    case TrN{+s0, +l, +r}:
      match w:
        case 0n:
          TrN{Some{s}, l, r}
        case 1n+(+k):
          +even = Nat.is_eq(Nat.mod(k, 2n), 0n)
          tr_join(even, s0, l, r, tr_put(tr_child(even, l, r), Nat.div(k, 2n), s))

def tr_list.of(s0: Maybe<&2, Slot>, +rest: List<&2, Slot>) -> List<&2, Slot>:
  match s0:
    case None{}:
      rest
    case Some{x}:
      Con{x, rest}

# every slot (in no particular order)
def tr_list(t: Tr, +acc: List<&2, Slot>) -> List<&2, Slot>:
  match t:
    case TrE{}:
      acc
    case TrN{s0, l, r}:
      tr_list.of(s0, tr_list(l, tr_list(r, acc)))

def put(+t: Tr, +s: Slot) -> Tr:
  tr_put(t, slot_w(s), s)

def get_w(+t: Tr, +w: Nat) -> Slot:
  Maybe.default(&2, Slot, tr_get(t, w), Slot{w, None{}, None{}})

def min_dl.of(fly: Maybe<&2, Fly>, +now: Nat, +acc: Nat) -> Nat:
  match fly:
    case None{}:
      acc
    case Some{+f}:
      +d = fly_dl(f)
      pick(Nat, Bool.and(Nat.is_gt(d, now), Bool.or(Nat.is_eq(acc, 0n), Nat.is_lt(d, acc))), d, acc)

def slot_fly(+s: Slot) -> Maybe<&2, Fly>:
  Slot{w, fd, fly} = s
  fly

# the earliest deadline after now of the hits in flight (0: none)
def min_dl(slots: List<&2, Slot>, +now: Nat, +acc: Nat) -> Nat:
  match slots:
    case Nil{}:
      acc
    case Con{+x, rest}:
      min_dl(rest, now, min_dl.of(slot_fly(x), now, acc))

# ---------------------------------------------------------------------
# Running one slot's client commands (sequential IO): until the machine
# waits for bytes (Recv) or finishes
# ---------------------------------------------------------------------

# what a slot's run ends in: the slot, and the result line if the hit
# finished
type Ran is Data:
  Ran{slot: Slot, line: Maybe<&2, List<&2, U32>>}

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
def finish(keep: Bool, +w: Nat, fd: Maybe<&2, U32>, +line: List<&2, U32>) -> IO(Ran):
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
            finish(False{}, w, fd, Sys.Packed.pack(fly_line(e, f, t1, Conn.Failed{"bend: the client stopped without an answer", None{}})))
        case Con{cmd, rest}:
          match cmd:
            case Conn.Recv{}:
              IO.pure(Ran, Ran{Slot{w, fd, Some{f}}, None{}})
            case Conn.Finish{o, keep}:
              do IO<Ran>:
                +t1 : Nat <- Sys.Clock.mono_ns()
                finish(keep, w, fd, Sys.Packed.pack(fly_line(e, f, t1, o)))
            case Conn.Shut{}:
              do IO<Ran>:
                close(fd)
                srun(Run{rest}, e, w, None{}, f)
            case Conn.Open{ip, port}:
              do IO<Ran>:
                close(fd)
                r : Result<&1, &1, U32 & String, U32> <- Sys.Fd.connect(ip, U32.from_nat(port), U32.from_nat(w))
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
# what a connection gave: bytes (packed; none at a close), or its
# deadline passed
type Raw is Data:
  RData{ws: List<&2, U32>}
  RLate{}

type Item is Data:
  Item{w: Nat, fd: Maybe<&2, U32>, fly: Fly, raw: Raw}

# the step taken: a finished hit's result line (packed, so the loop never
# walks it byte by byte; the machine's state is freed in the parallel
# task) and whether the connection stays; or the slot's new machine and
# commands, with the first request already packed when there is one
type Stepped is Data:
  SDone{w: Nat, fd: Maybe<&2, U32>, line: List<&2, U32>, keep: Bool}
  SMore{w: Nat, fd: Maybe<&2, U32>, fly: Fly, cmds: List<&2, Conn.Cmd>, sendp: Maybe<&2, List<&2, U32>>}

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

def ev_of(d: String) -> Conn.Ev:
  match d:
    case SNil{}:
      Conn.Eof{}
    case SCon{c, rest}:
      Conn.Got{SCon{c, rest}}

def ev_raw(r: Raw) -> Conn.Ev:
  match r:
    case RLate{}:
      Conn.Late{}
    case RData{ws}:
      ev_of(Sys.Packed.bytes(ws))

def step1.of(m: Maybe<&2, Conn.Out>, +e: WEnv, +t1: Nat, +w: Nat, +fd: Maybe<&2, U32>, +f2: Fly, +cs: List<&2, Conn.Cmd>) -> Stepped:
  match m:
    case Some{o}:
      SDone{w, fd, Sys.Packed.pack(fly_line(e, f2, t1, o)), fin_keep(cs)}
    case None{}:
      SMore{w, fd, f2, cs, None{}}

def step1(+e: WEnv, +t1: Nat, it: Item) -> Stepped:
  Item{w, fd, +f, raw} = it
  +r = Conn.step(e_cc(e), fly_st(f), ev_raw(raw))
  +cs = cs_of(r)
  step1.of(fin_only(cs), e, t1, w, fd, fly_with(f, st_of(r)), cs)

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
# Fired hits, started in parallel: each machine starts (rendering its
# request) in a parallel call tree, then the loop sends them
# ---------------------------------------------------------------------

# a fired hit: its worker, the worker's connection (if open), seq, target
type Pre is Data:
  Pre{w: Nat, fd: Maybe<&2, U32>, seq: Nat, ti: Nat}

type PTree is Data:
  PNil{}
  POne{x: Pre}
  PTwo{l: PTree, r: PTree}

def ptree1(xs: List<&2, Pre>) -> PTree:
  match xs:
    case Nil{}:
      PNil{}
    case Con{x, rest}:
      POne{x}

@unsafe def ptree(+n: Nat, +xs: List<&2, Pre>) -> PTree:
  match n:
    case 0n:
      PNil{}
    case 1n+m:
      match m:
        case 0n:
          ptree1(xs)
        case 1n+k:
          +h = Nat.div(Nat.add(k, 2n), 2n)
          PTwo{ptree(h, List.take(&2, Pre, xs, h)), ptree(Nat.sub(Nat.add(k, 2n), h), List.drop(&2, Pre, xs, h))}

# a start whose first command is the Send (a kept connection): the request
# packed, and the commands after it
def start_send(cs: List<&2, Conn.Cmd>, +w: Nat, +fd: Maybe<&2, U32>, +f: Fly) -> Stepped:
  match cs:
    case Con{c, rest}:
      match c:
        case Conn.Send{d}:
          SMore{w, fd, f, rest, Some{Sys.Packed.pack(d)}}
        case _:
          SMore{w, fd, f, Con{c, rest}, None{}}
    case Nil{}:
      SMore{w, fd, f, [], None{}}

def start1(+e: WEnv, +h0: Nat, +ts: Civil.Time, p: Pre) -> Stepped:
  Pre{w, +fd, +seq, +ti} = p
  +r0 = Conn.start(e_cc(e), req_of(prep_at(e_preps(e), ti), seq, e_name(e)), Maybe.is_some(&2, U32, fd))
  start_send(cs_of(r0), w, fd, Fly{st_of(r0), seq, ti, h0, ts, deadline(e_cc(e), h0)})

def pstarts(t: PTree, +e: WEnv, +h0: Nat, +ts: Civil.Time) -> List<&2, Stepped>:
  match t:
    case PNil{}:
      []
    case POne{x}:
      [start1(e, h0, ts, x)]
    case PTwo{l, r}:
      a b = pstarts(l, e, h0, ts) pstarts(r, e, h0, ts)
      List.append(&2, Stepped, a, b)

# ---------------------------------------------------------------------
# Taking in what a wait found
# ---------------------------------------------------------------------

# the events for the slots: bytes or a close for a hit in flight; idle
# connections that closed (or spoke out of turn) are dropped, as Go's
# transport drops an idle connection its read loop saw closed
type Taken is Data:
  Taken{items: List<&2, Item>, dead: List<&2, Nat>}

def take_fly(fly: Maybe<&2, Fly>, +w: Nat, +fd: Maybe<&2, U32>, +d: List<&2, U32>, +acc: Taken) -> Taken:
  match fly:
    case None{}:
      Taken{items, dead} = acc
      Taken{items, Con{w, dead}}
    case Some{f}:
      Taken{items, dead} = acc
      Taken{Con{Item{w, fd, f, RData{d}}, items}, dead}

def take_s(+s: Slot, +d: List<&2, U32>, +acc: Taken) -> Taken:
  Slot{w, fd, fly} = s
  take_fly(fly, w, fd, d, acc)

def take_p(p: Sigma<&2, &2, U32, _ => List<&2, U32>>, +slots: Tr, +acc: Taken) -> Taken:
  (tag, d) = p
  take_s(get_w(slots, U32.to_nat(tag)), d, acc)

def take(rs: List<&2, Sigma<&2, &2, U32, _ => List<&2, U32>>>, +slots: Tr, +acc: Taken) -> Taken:
  match rs:
    case Nil{}:
      acc
    case Con{p, rest}:
      take(rest, slots, take_p(p, slots, acc))

def item_w(+it: Item) -> Nat:
  Item{w, fd, f, raw} = it
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
      lates.add(Bool.and(Bool.and(Nat.is_gt(d, 0n), Nat.is_ge(now, d)), Bool.not(has_w(w, its))), Item{w, fd, f, RLate{}}, its)

# hits past their deadline that got nothing this round take a Late (a
# walk over every slot: only when the next deadline to check has come)
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

# a started hit: its packed request goes out at once (a kept connection),
# else its commands run
def send_first(sendp: Maybe<&2, List<&2, U32>>, fd: Maybe<&2, U32>, +e: WEnv, +w: Nat, +f: Fly, cmds: List<&2, Conn.Cmd>) -> IO(Ran):
  match sendp:
    case None{}:
      srun(Run{cmds}, e, w, fd, f)
    case Some{ws}:
      match fd:
        case None{}:
          srun(Run{cmds}, e, w, None{}, f)
        case Some{+x}:
          do IO<Ran>:
            r : Result<&1, &1, U32 & String, Unit> <- Sys.Fd.send_packed(x, ws)
            srun(SendRes{r}, e, w, Some{x}, f)

# the loop's state: when the attack began (mono ns), the engine, the
# slots, the nap's end (attack ns), the workers freed and not yet told
# to the engine, the result lines not yet written (newest first), and
# when to look for hits past their deadline (mono ns, 0: none)
type Lp is Data:
  Lp{t0: Nat, st: Eng.State, slots: Tr, nap: Maybe<&2, Nat>, freed: List<&2, Nat>, lines: List<&2, List<&2, U32>>, dln: Nat}

def lp_slots(+l: Lp) -> Tr:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  slots

def lp_lines(+l: Lp) -> List<&2, List<&2, U32>>:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  lines

def no_lines(+l: Lp) -> Lp:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  Lp{t0, st, slots, nap, freed, [], dln}

def with_slots(+l: Lp, +ss: Tr) -> Lp:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  Lp{t0, st, ss, nap, freed, lines, dln}

def with_slot(+l: Lp, +s: Slot) -> Lp:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  Lp{t0, st, put(slots, s), nap, freed, lines, dln}

def with_nap(+l: Lp, +u: Nat) -> Lp:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  Lp{t0, st, slots, Some{u}, freed, lines, dln}

def with_line(line: Maybe<&2, List<&2, U32>>, +w: Nat, +l: Lp) -> Lp:
  match line:
    case None{}:
      l
    case Some{x}:
      Lp{t0, st, slots, nap, freed, lines, dln} = l
      Lp{t0, st, slots, nap, List.append(&2, Nat, freed, [w]), Con{x, lines}, dln}

def with_ran(+l: Lp, +r: Ran) -> Lp:
  Ran{s, line} = r
  with_line(line, slot_w(s), with_slot(l, s))

# a match, not a pick: the walk happens only when the check is due
def lates_if(chk: Bool, +slots: Tr, +now: Nat, +items: List<&2, Item>) -> List<&2, Item>:
  match chk:
    case True{}:
      lates(tr_list(slots, []), now, items)
    case False{}:
      items

def lp_dln(+l: Lp) -> Nat:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  dln

# after a deadline check, the next one is the earliest deadline still ahead
def with_dln(chk: Bool, +now: Nat, +l: Lp) -> Lp:
  match chk:
    case False{}:
      l
    case True{}:
      Lp{t0, st, slots, nap, freed, lines, dln} = l
      Lp{t0, st, slots, nap, freed, lines, min_dl(tr_list(slots, []), now, 0n)}


def nap_abs(+t0: Nat, +nap: Maybe<&2, Nat>) -> Nat:
  match nap:
    case None{}:
      0n
    case Some{u}:
      Nat.add(t0, u)

def earliest(+a: Nat, +b: Nat) -> Nat:
  pick(Nat, Nat.is_eq(a, 0n), b, pick(Nat, Bool.or(Nat.is_eq(b, 0n), Nat.is_lt(a, b)), a, b))

# how long to wait (ns): until the nap ends or the next deadline check,
# else a second (the loop then looks again)
def wait_ns(+l: Lp, +now: Nat) -> Nat:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  +until = earliest(nap_abs(t0, nap), dln)
  pick(Nat, Nat.is_eq(until, 0n), 1000000000n, pick(Nat, Nat.is_gt(until, now), Nat.sub(until, now), 0n))

# a fired hit's deadline joins the ones to check
def with_dl(+l: Lp, +d: Nat) -> Lp:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  Lp{t0, st, slots, nap, freed, lines, earliest(dln, d)}

def close_all(slots: List<&2, Slot>) -> IO(Unit):
  match slots:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+s, rest}:
      do IO<Unit>:
        close(slot_fd(s))
        close_all(rest)

def close_dead(dead: List<&2, Nat>, +slots: Tr) -> IO(Tr):
  match dead:
    case Nil{}:
      IO.pure(Tr, slots)
    case Con{+w, rest}:
      do IO<Tr>:
        close(slot_fd(get_w(slots, w)))
        close_dead(rest, put(slots, Slot{w, None{}, None{}}))

def flush(ls: List<&2, List<&2, U32>>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{x, rest}:
      Sys.Out.packed(Con{x, rest})

# what the engine takes next: the clock when the nap is over, else the
# next freed worker; None when there is nothing, and the loop waits
type Nx is Data:
  Nx{l: Lp, cs: Maybe<&2, List<&2, Eng.Cmd>>}

def next_freed(freed: List<&2, Nat>, +t0: Nat, +st: Eng.State, +slots: Tr, +nap: Maybe<&2, Nat>, +lines: List<&2, List<&2, U32>>, +dln: Nat, +ec: Eng.Cfg, +t: Nat) -> Nx:
  match freed:
    case Nil{}:
      Nx{Lp{t0, st, slots, nap, [], lines, dln}, None{}}
    case Con{+w, rest}:
      +r = Eng.step(ec, st, Eng.Freed{w, t})
      Nx{Lp{t0, est_of(r), slots, nap, rest, lines, dln}, Some{ecs_of(r)}}

def next_nap(due: Bool, +u: Nat, +freed: List<&2, Nat>, +t0: Nat, +st: Eng.State, +slots: Tr, +lines: List<&2, List<&2, U32>>, +dln: Nat, +ec: Eng.Cfg, +t: Nat) -> Nx:
  match due:
    case True{}:
      +r = Eng.step(ec, st, Eng.Clock{t})
      Nx{Lp{t0, est_of(r), slots, None{}, freed, lines, dln}, Some{ecs_of(r)}}
    case False{}:
      next_freed(freed, t0, st, slots, Some{u}, lines, dln, ec, t)

def next_ev.of(nap: Maybe<&2, Nat>, +freed: List<&2, Nat>, +t0: Nat, +st: Eng.State, +slots: Tr, +lines: List<&2, List<&2, U32>>, +dln: Nat, +ec: Eng.Cfg, +t: Nat) -> Nx:
  match nap:
    case Some{+u}:
      next_nap(Nat.is_ge(t, u), u, freed, t0, st, slots, lines, dln, ec, t)
    case None{}:
      next_freed(freed, t0, st, slots, None{}, lines, dln, ec, t)

def next_ev(+l: Lp, +ec: Eng.Cfg, +now: Nat) -> Nx:
  Lp{t0, st, slots, nap, freed, lines, dln} = l
  next_ev.of(nap, freed, t0, st, slots, lines, dln, ec, Nat.sub(now, t0))

# the loop's next move: run the engine's commands; decide what the engine
# takes next; start a fired hit; take in a slot's run, a wait's findings,
# or the parallel step's results one by one
type Am is Type:
  Cmds{cs: List<&2, Eng.Cmd>}
  Idle{}
  Decide{nx: Nx, now: Nat}
  Gather{cs: List<&2, Eng.Cmd>, fs: List<&2, Pre>}
  Launch{fs: List<&2, Pre>}
  Launched{fs: List<&2, Pre>, t0: Nat, wall: Nat & Nat & U32}
  Waited{rs: List<&2, Sigma<&2, &2, U32, _ => List<&2, U32>>>, now: Nat}
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
                rs : List<&2, Sigma<&2, &2, U32, _ => List<&2, U32>>> <- Sys.Fd.next(65536, wait_ns(l2, now))
                +now2 : Nat <- Sys.Clock.mono_ns()
                attack(Waited{rs, now2}, ec, e, no_lines(l2))
    case Cmds{cs}:
      attack(Gather{cs, []}, ec, e, l)
    case Gather{cs, fs}:
      match cs:
        case Nil{}:
          attack(Launch{List.reverse(&2, Pre, fs)}, ec, e, l)
        case Con{c, rest}:
          match c:
            case Eng.Grow{+w}:
              attack(Gather{rest, fs}, ec, e, with_slot(l, Slot{w, None{}, None{}}))
            case Eng.Nap{u}:
              attack(Gather{rest, fs}, ec, e, with_nap(l, u))
            case Eng.Fire{+w, +seq, +ti, t}:
              attack(Gather{rest, Con{Pre{w, slot_fd(get_w(lp_slots(l), w)), seq, ti}, fs}}, ec, e, l)
            case Eng.Quit{sent, dropped}:
              do IO<Nat & Nat>:
                flush(lp_lines(l))
                close_all(tr_list(lp_slots(l), []))
                return (sent, dropped)
    case Launch{fs}:
      match fs:
        case Nil{}:
          attack(Idle{}, ec, e, l)
        case Con{f, rest}:
          do IO<Nat & Nat>:
            +h0 : Nat <- Sys.Clock.mono_ns()
            wall : Nat & Nat & U32 <- Sys.Clock.wall()
            attack(Launched{Con{f, rest}, h0, wall}, ec, e, l)
    case Launched{+fs, +h0, wall}:
      attack(Stepping{pstarts(ptree(List.length(&2, Pre, fs), fs), e, h0, wall_time(wall))}, ec, e, with_dl(l, deadline(e_cc(e), h0)))
    case Waited{rs, +now}:
      attack(Took{take(rs, lp_slots(l), Taken{[], []}), now}, ec, e, l)
    case Took{tk, +now}:
      match tk:
        case Taken{items, dead}:
          +chk = Bool.and(Nat.is_gt(lp_dln(l), 0n), Nat.is_ge(now, lp_dln(l)))
          +its = lates_if(chk, lp_slots(l), now, items)
          do IO<Nat & Nat>:
            ss : Tr <- close_dead(dead, lp_slots(l))
            attack(Stepping{psteps(tree(List.length(&2, Item, its), its), e, now)}, ec, e, with_dln(chk, now, with_slots(l, ss)))
    case Stepping{xs}:
      match xs:
        case Nil{}:
          attack(Idle{}, ec, e, l)
        case Con{x, rest}:
          match x:
            case SDone{+w, fd, line, keep}:
              do IO<Nat & Nat>:
                r : Ran <- finish(keep, w, fd, line)
                attack(Stepping{rest}, ec, e, with_ran(l, r))
            case SMore{+w, fd, f, cmds, sendp}:
              do IO<Nat & Nat>:
                r : Ran <- send_first(sendp, fd, e, w, f, cmds)
                attack(Stepping{rest}, ec, e, with_ran(l, r))

# runs an attack to its end, writing the results as they come; answers
# (sent, dropped)
def run(+ec: Eng.Cfg, +e: WEnv) -> IO(Nat & Nat):
  +r = Eng.start(ec)
  do IO<Nat & Nat>:
    +t0 : Nat <- Sys.Clock.mono_ns()
    attack(Cmds{ecs_of(r)}, ec, e, Lp{t0, est_of(r), TrE{}, None{}, [], [], 0n})

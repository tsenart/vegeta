# LAWS.bend's engine checkers on the timelines of scripted environments.
# Each line: seq now early deadline rr workers initial grow unbounded nap
# quit live, then ends (from four prefixes); "-" where a law's hypothesis
# does not hold.
import Base
import ../.build/laws_helpers.bend as L
import ../lib/engine.bend as Eng

# times in a small unit (the checker helpers run on unary-ish Nats):
# ms(n) is n units and a second is 1000
def ms(+n: Nat) -> Nat:
  n

def sec() -> Nat:
  1000n

def st_of(+r: Sigma<&2, &2, Eng.State, _ => List<&2, Eng.Cmd>>) -> Eng.State:
  (st, cs) = r
  st

def cs_of(+r: Sigma<&2, &2, Eng.State, _ => List<&2, Eng.Cmd>>) -> List<&2, Eng.Cmd>:
  (st, cs) = r
  cs

def sel(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def ev_t(+e: Eng.Ev) -> Nat:
  match e:
    case Eng.Clock{t}:
      t
    case Eng.Freed{w, t}:
      t

# insert by time, after the events at the same time
def insert(+e: Eng.Ev, q: List<&2, Eng.Ev>) -> List<&2, Eng.Ev>:
  match q:
    case Nil{}:
      [e]
    case Con{+x, +rest}:
      sel(List<&2, Eng.Ev>, Nat.is_lt(ev_t(e), ev_t(x)), Con{e, Con{x, rest}}, Con{x, insert(e, rest)})

# the environment's answers: a hit is done resp after it went out, a
# nap is answered late after its end
def enq(cs: List<&2, Eng.Cmd>, q: List<&2, Eng.Ev>, +resp: Nat, +late: Nat) -> List<&2, Eng.Ev>:
  match cs:
    case Nil{}:
      q
    case Con{+k, +rest}:
      match k:
        case Eng.Fire{w, n, g, t}:
          enq(rest, insert(Eng.Freed{w, Nat.add(t, resp)}, q), resp, late)
        case Eng.Nap{u}:
          enq(rest, insert(Eng.Clock{Nat.add(u, late)}, q), resp, late)
        case _:
          enq(rest, q, resp, late)

# the events an environment feeds the engine, in order
def drive(fuel: Nat, q: List<&2, Eng.Ev>, +c: Eng.Cfg, +s: Eng.State, +resp: Nat, +late: Nat, fed: List<&2, Eng.Ev>) -> List<&2, Eng.Ev>:
  match fuel:
    case 0n:
      fed
    case 1n+f:
      match q:
        case Nil{}:
          fed
        case Con{+e, +rest}:
          drive(f, enq(cs_of(Eng.step(c, s, e)), rest, resp, late), c, st_of(Eng.step(c, s, e)), resp, late, List.append(&2, Eng.Ev, fed, [e]))

def run_env(+c: Eng.Cfg, +resp: Nat, +late: Nat) -> List<&2, Eng.Ev>:
  drive(200n, enq(cs_of(Eng.start(c)), [], resp, late), c, st_of(Eng.start(c)), resp, late, [])

# 50/s for 200 ms, 2 workers (max 10), 3 targets
def c50(+mx: Nat) -> Eng.Cfg:
  Eng.ECfg{50n, sec(), ms(200n), 2n, mx, 3n}

# unbounded, 1 worker to start, max 3, 100 ms
def cun() -> Eng.Cfg:
  Eng.ECfg{0n, sec(), ms(100n), 1n, 3n, 2n}

# freed idle workers
def ev_idle() -> List<&2, Eng.Ev>:
  [Eng.Freed{5n, ms(10n)}, Eng.Clock{ms(20n)}, Eng.Freed{1n, ms(25n)}, Eng.Freed{0n, ms(26n)}, Eng.Freed{0n, ms(27n)},
   Eng.Clock{ms(40n)}, Eng.Clock{ms(60n)}, Eng.Freed{7n, ms(61n)}, Eng.Clock{ms(250n)}, Eng.Freed{0n, ms(251n)}, Eng.Freed{1n, ms(252n)},
   Eng.Freed{2n, ms(253n)}, Eng.Clock{ms(300n)}]

# a clock that goes backwards
def ev_back() -> List<&2, Eng.Ev>:
  [Eng.Clock{ms(60n)}, Eng.Clock{ms(10n)}, Eng.Freed{0n, ms(5n)}, Eng.Clock{ms(50n)}, Eng.Freed{1n, ms(3n)}, Eng.Clock{ms(0n)},
   Eng.Freed{2n, ms(1n)}, Eng.Clock{ms(80n)}, Eng.Clock{ms(79n)}, Eng.Freed{0n, ms(210n)}, Eng.Freed{3n, ms(100n)}, Eng.Freed{1n, ms(0n)},
   Eng.Freed{2n, ms(0n)}, Eng.Freed{4n, ms(0n)}]

def tf(b: Bool) -> String:
  match b:
    case True{}:
      "T"
    case False{}:
      "F"

def gate(h: Bool, v: Bool) -> String:
  match h:
    case True{}:
      tf(v)
    case False{}:
      "-"

# the timeline starts with Grow{from}, Grow{from + 1}, ... (n of them)
def grows_ok(n: Nat, xs: List<&2, L.Item>, +from: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match xs:
        case Nil{}:
          False{}
        case Con{+x, +rest}:
          match x:
            case L.ICmd{k}:
              match k:
                case Eng.Grow{w}:
                  Bool.and(Nat.is_eq(w, from), grows_ok(p, rest, 1n+from))
                case _:
                  False{}
            case _:
              False{}

def unb(+c: Eng.Cfg) -> Bool:
  Bool.or(Nat.is_eq(L.e_freq(c), 0n), Nat.is_eq(L.e_per(c), 0n))

def ends(+c: Eng.Cfg, +evs: List<&2, Eng.Ev>) -> String:
  +t = Nat.max(1n+L.e_dur(c), L.max_time(evs))
  gate(Bool.and(L.cfg_ok(c), Nat.is_gt(L.e_dur(c), 0n)), L.has_quit(L.timeline(c, L.respond(4n, c, evs, t))))

def laws(+c: Eng.Cfg, +evs: List<&2, Eng.Ev>) -> String:
  +x = L.timeline(c, evs)
  +b = L.bounded(c)
  tf(L.chk_seq(x, 0n)) ++ tf(L.chk_now(x, 0n)) ++ gate(b, L.chk_early(x, c))
    ++ gate(Nat.is_gt(L.e_dur(c), 0n), L.chk_deadline(x, L.e_dur(c), 0n))
    ++ gate(L.cfg_ok(c), L.chk_rr(x, L.e_targets(c)))
    ++ tf(L.chk_workers(x, L.e_max(c), 0n, []))
    ++ tf(grows_ok(L.initial(c), x, 0n))
    ++ tf(L.chk_grow(x, L.initial(c), 0n, []))
    ++ gate(unb(c), L.no_nap(x))
    ++ gate(b, L.chk_nap(x, c, 0n, 0n))
    ++ tf(L.chk_quit(x, c, 0n, False{}, None{}, []))
    ++ gate(L.cfg_ok(c), L.chk_live(x, c, False{}, 0n, [], False{}, None{}))
    ++ " " ++ ends(c, []) ++ ends(c, List.take(&2, Eng.Ev, evs, 3n)) ++ ends(c, List.take(&2, Eng.Ev, evs, 7n)) ++ ends(c, evs)
    ++ " " ++ tf(L.has_quit(x))

def lcg(+x: Nat) -> Nat:
  Nat.mod(Nat.add(Nat.mul(x, 75n), 74n), 65537n)

def rand_ev(+r: Nat) -> Eng.Ev:
  L.pick(Eng.Ev, Nat.is_eq(Nat.mod(r, 3n), 0n), Eng.Clock{Nat.mod(r, 300n)}, Eng.Freed{Nat.mod(Nat.div(r, 3n), 5n), Nat.mod(Nat.div(r, 7n), 300n)})

# n pseudo-random events: clocks and frees in any order, any worker
def gen(n: Nat, +x: Nat) -> List<&2, Eng.Ev>:
  match n:
    case 0n:
      []
    case 1n+p:
      Con{rand_ev(lcg(x)), gen(p, lcg(x))}

def fuzz(+c: Eng.Cfg) -> String:
  laws(c, gen(40n, 1n)) ++ " | " ++ laws(c, gen(40n, 2n)) ++ " | " ++ laws(c, gen(40n, 3n)) ++ " | " ++ laws(c, gen(40n, 4n))

# no end
def cforever() -> Eng.Cfg:
  Eng.ECfg{50n, sec(), 0n, 2n, 3n, 2n}

# more workers asked than allowed; one target
def cwide() -> Eng.Cfg:
  Eng.ECfg{7n, sec(), ms(250n), 5n, 2n, 1n}

# no worker allowed, no target, more hits than ns
def codd1() -> Eng.Cfg:
  Eng.ECfg{3n, 2n, ms(10n), 2n, 0n, 0n}

def codd2() -> Eng.Cfg:
  Eng.ECfg{3n, 2n, ms(10n), 0n, 2n, 0n}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(laws(c50(10n), run_env(c50(10n), 0n, 0n)))
    IO.print(laws(c50(10n), run_env(c50(10n), 0n, ms(50n))))
    IO.print(laws(c50(10n), run_env(c50(10n), 0n, ms(60n))))
    IO.print(laws(c50(1n), run_env(c50(1n), ms(30n), 0n)))
    IO.print(laws(cun(), run_env(cun(), ms(10n), 0n)))
    IO.print(laws(cforever(), run_env(cforever(), ms(30n), ms(5n))))
    IO.print(laws(cwide(), run_env(cwide(), ms(300n), ms(1n))))
    IO.print(laws(c50(10n), ev_idle()))
    IO.print(laws(c50(10n), ev_back()))
    IO.print(laws(cun(), ev_back()))
    IO.print(fuzz(c50(10n)))
    IO.print(fuzz(c50(1n)))
    IO.print(fuzz(cun()))
    IO.print(fuzz(cforever()))
    IO.print(fuzz(cwide()))
    IO.print(fuzz(codd1()))
    IO.print(fuzz(codd2()))

#|TTTTTTTT-TTT TTTT T
#|TTTTTTTT-TTT TTTT T
#|TTTTTTTT-TTT TTTT T
#|TTTTTTTT-TTT TTTT T
#|TT-TTTTTT-TT TTTT T
#|TTT-TTTT-TTT ---- F
#|TTTTTTTT-TTT TTTT T
#|TTTTTTTT-TTT TTTT T
#|TTTTTTTT-TTT TTTT T
#|TT-TTTTTT-TT TTTT F
#|TTTTTTTT-TTT TTTT F | TTTTTTTT-TTT TTTT F | TTTTTTTT-TTT TTTT T | TTTTTTTT-TTT TTTT T
#|TTTTTTTT-TTT TTTT T | TTTTTTTT-TTT TTTT T | TTTTTTTT-TTT TTTT T | TTTTTTTT-TTT TTTT F
#|TT-TTTTTT-TT TTTT T | TT-TTTTTT-TT TTTT T | TT-TTTTTT-TT TTTT T | TT-TTTTTT-TT TTTT T
#|TTT-TTTT-TTT ---- F | TTT-TTTT-TTT ---- F | TTT-TTTT-TTT ---- F | TTT-TTTT-TTT ---- F
#|TTTTTTTT-TTT TTTT F | TTTTTTTT-TTT TTTT F | TTTTTTTT-TTT TTTT T | TTTTTTTT-TTT TTTT T
#|TT-T-TTT--T- ---- F | TT-T-TTT--T- ---- F | TT-T-TTT--T- ---- F | TT-T-TTT--T- ---- F
#|TT-T-TTT--T- ---- T | TT-T-TTT--T- ---- T | TT-T-TTT--T- ---- T | TT-T-TTT--T- ---- T

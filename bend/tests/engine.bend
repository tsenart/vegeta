# The engine driven by scripted environments: each line is an event and
# the commands it drew (times in ms; F<seq>w<worker>g<target>@<t>).
import Base
import ../lib/engine.bend as Eng

# times are ns; ms(n) is n ms
def ms(+n: Nat) -> Nat:
  Nat.mul(n, 1000000n)

def sec() -> Nat:
  1000000000n

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

def show_ms(+n: Nat) -> String:
  Nat.show(Nat.div(n, 1000000n))

def show_cmd(+k: Eng.Cmd) -> String:
  match k:
    case Eng.Nap{u}:
      " N" ++ show_ms(u)
    case Eng.Grow{w}:
      " G" ++ Nat.show(w)
    case Eng.Fire{w, n, g, t}:
      " F" ++ Nat.show(n) ++ "w" ++ Nat.show(w) ++ "g" ++ Nat.show(g) ++ "@" ++ show_ms(t)
    case Eng.Quit{s, d}:
      " Q" ++ Nat.show(s) ++ "/" ++ Nat.show(d)

def show_cmds(cs: List<&2, Eng.Cmd>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{+k, +rest}:
      show_cmd(k) ++ show_cmds(rest)

def show_ev(+e: Eng.Ev) -> String:
  match e:
    case Eng.Clock{t}:
      "C" ++ show_ms(t) ++ ":"
    case Eng.Freed{w, t}:
      "R" ++ Nat.show(w) ++ "@" ++ show_ms(t) ++ ":"

def lines(evs: List<&2, Eng.Ev>, +c: Eng.Cfg, +s: Eng.State) -> List<&2, String>:
  match evs:
    case Nil{}:
      []
    case Con{+e, +rest}:
      Con{show_ev(e) ++ show_cmds(cs_of(Eng.step(c, s, e))), lines(rest, c, st_of(Eng.step(c, s, e)))}

def tl(+name: String, +c: Eng.Cfg, +evs: List<&2, Eng.Ev>) -> List<&2, String>:
  Con{"== " ++ name, Con{"start:" ++ show_cmds(cs_of(Eng.start(c))), lines(evs, c, st_of(Eng.start(c)))}}

def print_all(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{x, rest}:
      do IO<Unit>:
        IO.print(x)
        print_all(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    print_all(tl("punctual", c50(10n), run_env(c50(10n), 0n, 0n)))
    print_all(tl("late 50ms", c50(10n), run_env(c50(10n), 0n, ms(50n))))
    print_all(tl("late 60ms", c50(10n), run_env(c50(10n), 0n, ms(60n))))
    print_all(tl("slow worker", c50(1n), run_env(c50(1n), ms(30n), 0n)))
    print_all(tl("unbounded", cun(), run_env(cun(), ms(10n), 0n)))
    print_all(tl("idle frees", c50(10n), ev_idle()))
    print_all(tl("backwards", c50(10n), ev_back()))

#|== punctual
#|start: G0 G1 N20
#|C20: F0w0g0@20 N40
#|R0@20:
#|C40: F1w0g1@40 N60
#|R0@40:
#|C60: F2w0g2@60 N80
#|R0@60:
#|C80: F3w0g0@80 N100
#|R0@80:
#|C100: F4w0g1@100 N120
#|R0@100:
#|C120: F5w0g2@120 N140
#|R0@120:
#|C140: F6w0g0@140 N160
#|R0@140:
#|C160: F7w0g1@160 N180
#|R0@160:
#|C180: F8w0g2@180 N200
#|R0@180:
#|C200: F9w0g0@200
#|R0@200: Q10/0
#|== late 50ms
#|start: G0 G1 N20
#|C70: F0w0g0@70 F1w1g1@70 G2 F2w2g2@70 N80
#|R0@70:
#|R1@70:
#|R2@70:
#|C130: F3w2g0@130 F4w1g1@130 F5w0g2@130 N140
#|R2@130:
#|R1@130:
#|R0@130:
#|C190: F6w0g0@190 F7w1g1@190 F8w2g2@190 N200
#|R0@190:
#|R1@190:
#|R2@190:
#|C250: F9w2g0@250
#|R2@250: Q10/0
#|== late 60ms
#|start: G0 G1 N20
#|C80: F0w0g0@80 F1w1g1@80 G2 F2w2g2@80 G3 F3w3g0@80 N100
#|R0@80:
#|R1@80:
#|R2@80:
#|R3@80:
#|C160: F4w3g1@160 F5w2g2@160 F6w1g0@160 F7w0g1@160 N180
#|R3@160:
#|R2@160:
#|R1@160:
#|R0@160:
#|C240: F8w0g2@240
#|R0@240: Q9/1
#|== slow worker
#|start: G0 N20
#|C20: F0w0g0@20 N40
#|C40:
#|R0@50: F1w0g1@50 N60
#|C60:
#|R0@80: F2w0g2@80
#|R0@110: F3w0g0@110
#|R0@140: F4w0g1@140
#|R0@170: F5w0g2@170
#|R0@200: F6w0g0@200
#|R0@230: Q7/3
#|== unbounded
#|start: G0 F0w0g0@0 G1 F1w1g1@0 G2 F2w2g0@0
#|R0@10: F3w0g1@10
#|R1@10: F4w1g0@10
#|R2@10: F5w2g1@10
#|R0@20: F6w0g0@20
#|R1@20: F7w1g1@20
#|R2@20: F8w2g0@20
#|R0@30: F9w0g1@30
#|R1@30: F10w1g0@30
#|R2@30: F11w2g1@30
#|R0@40: F12w0g0@40
#|R1@40: F13w1g1@40
#|R2@40: F14w2g0@40
#|R0@50: F15w0g1@50
#|R1@50: F16w1g0@50
#|R2@50: F17w2g1@50
#|R0@60: F18w0g0@60
#|R1@60: F19w1g1@60
#|R2@60: F20w2g0@60
#|R0@70: F21w0g1@70
#|R1@70: F22w1g0@70
#|R2@70: F23w2g1@70
#|R0@80: F24w0g0@80
#|R1@80: F25w1g1@80
#|R2@80: F26w2g0@80
#|R0@90: F27w0g1@90
#|R1@90: F28w1g0@90
#|R2@90: F29w2g1@90
#|R0@100: F30w0g0@100
#|R1@100:
#|R2@100:
#|R0@110: Q31/0
#|== idle frees
#|start: G0 G1 N20
#|R5@10:
#|C20: F0w0g0@20 N40
#|R1@25:
#|R0@26:
#|R0@27:
#|C40: F1w0g1@40 N60
#|C60: F2w1g2@60 N80
#|R7@61:
#|C250: G2 F3w2g0@250
#|R0@251:
#|R1@252:
#|R2@253: Q4/6
#|C300:
#|== backwards
#|start: G0 G1 N20
#|C60: F0w0g0@60 F1w1g1@60 G2 F2w2g2@60 N80
#|C10: N80
#|R0@5:
#|C50: N80
#|R1@3:
#|C0: N80
#|R2@1:
#|C80: F3w2g0@80 N100
#|C79: N100
#|R0@210: F4w1g1@210
#|R3@100:
#|R1@0:
#|R2@0: Q5/5
#|R4@0:

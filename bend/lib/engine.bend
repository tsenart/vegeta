# The attack's scheduler, as a pure machine: pacing, dispatch to workers,
# worker growth, and the stop with its accounting. Times are ns since the
# attack began, read from the clock by the shell. STUB.
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
  Idle{}
  Quit{sent: Nat, dropped: Nat}

type State is Data:
  EState{now: Nat, over: Bool}

def start(+c: Cfg) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  (EState{0n, False{}}, [])

def step(+c: Cfg, +s: State, e: Ev) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  (s, [])

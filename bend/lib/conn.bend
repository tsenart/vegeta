# The HTTP client of one worker, as a pure machine: the shell runs its
# commands and feeds back what happened. One machine per request; the
# connection may be carried over from the previous request. STUB.
import Base
import ./http.bend as Http
import ./target.bend as Tgt
import ./civil.bend as Civil
import ./hit.bend as Hit

type Cfg is Data:
  CCfg{keepalive: Bool, timeout: Nat, max_body: Maybe<&2, Nat>, redirects: Maybe<&2, Nat>}

type Req is Data:
  Req{target: Tgt.Target, url: Tgt.Url, ip: String, body: String, seq: Nat, name: String}

type Ev is Data:
  Opened{}
  OpenFailed{msg: String}
  Sent{}
  SendFailed{msg: String}
  Got{data: String}
  Eof{}
  Late{}
  Resolved{ip: String}
  ResolveFailed{msg: String}

type Out is Data:
  Answered{resp: Http.Resp}
  Failed{msg: String}

type Cmd is Data:
  Resolve{host: String}
  Open{ip: String, port: Nat}
  Send{data: String}
  Recv{}
  Shut{}
  Finish{out: Out, open: Bool}

type State is Data:
  CState{req: Req, open: Bool, over: Bool}

# open: whether the worker's connection from its last request is still open
def start(+c: Cfg, +r: Req, open: Bool) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  (CState{r, open, False{}}, [])

def step(+c: Cfg, +s: State, e: Ev) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  (s, [])

# the result the shell records for a finished request: attack name, seq,
# start time, latency, the request's method, URL and body size, and the outcome
def to_hit(+name: String, +seq: Nat, +ts: Civil.Time, +lat: Nat, +method: String, +url: String, +out_bytes: Nat, +o: Out) -> Hit.Hit:
  Hit.Hit{name, seq, 0n, ts, lat, out_bytes, 0n, "", None{}, method, url, None{}}

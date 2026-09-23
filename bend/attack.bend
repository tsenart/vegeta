# The attack command: flags, targets, addresses, then the shell. Each
# step answers a Result the next one takes as a parameter (a match may
# not follow a bind).
import Base
import ./lib/sys.bend as Sys
import ./lib/flags.bend as Flags
import ./lib/pacer.bend as Pace
import ./lib/target.bend as Tgt
import ./lib/engine.bend as Eng
import ./lib/conn.bend as Conn
import ./lib/hdr.bend as Hdr
import ./lib/dec.bend as Dec
import ./shell.bend as Sh

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def die(+msg: String) -> IO(Unit):
  do IO<Unit>:
    Sys.Out.write_err(msg ++ "\n")
    IO.die(Unit, 1, "")

# Go's default -timeout (30s) and -max-workers (unbounded)
def default_timeout() -> Nat:
  Nat.mul(30n, 1000000000n)

def unbounded() -> Nat:
  4294967295n

def eng_cfg(+a: Flags.Attack, +n: Nat) -> Eng.Cfg:
  Flags.Attack{rate, dur, tg, fmt, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Pace.Rate{f, p} = rate
  Eng.ECfg{f, p, dur, w, Maybe.default(&2, Nat, mw, unbounded()), n}

def conn_cfg(+a: Flags.Attack) -> Conn.Cfg:
  Flags.Attack{rate, dur, tg, fmt, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Conn.CCfg{ka, Maybe.default(&2, Nat, to, default_timeout()), mb, rd}

def a_targets(+a: Flags.Attack) -> String:
  Flags.Attack{rate, dur, tg, fmt, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  tg

def a_output(+a: Flags.Attack) -> String:
  Flags.Attack{rate, dur, tg, fmt, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  out

def a_name(+a: Flags.Attack) -> String:
  Flags.Attack{rate, dur, tg, fmt, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  name

def a_json(+a: Flags.Attack) -> Bool:
  Flags.Attack{rate, dur, tg, fmt, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  String.eq(enc, "json")

def apply_all(ts: List<&2, Tgt.Target>, +a: Flags.Attack) -> List<&2, Tgt.Target>:
  match ts:
    case Nil{}:
      []
    case Con{t, rest}:
      Flags.Attack{rate, dur, tg, fmt, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
      Con{Tgt.apply(t, hs, body), apply_all(rest, a)}

# ---------------------------------------------------------------------
# Reading the targets
# ---------------------------------------------------------------------

def concat(cs: List<&2, String>, acc: String) -> String:
  match cs:
    case Nil{}:
      acc
    case Con{c, rest}:
      concat(rest, c ++ acc)

# stdin to its end; chunks kept newest first
@unsafe def slurp(r: Result<&1, &1, U32 & String, String>, cs: List<&2, String>) -> IO(Result<&1, &1, U32 & String, String>):
  match r:
    case Fail{e}:
      IO.pure(Result<&1, &1, U32 & String, String>, Fail{e})
    case Done{d}:
      match d:
        case SNil{}:
          IO.pure(Result<&1, &1, U32 & String, String>, Done{concat(cs, "")})
        case SCon{c, rest}:
          do IO<Result<&1, &1, U32 & String, String>>:
            r2 : Result<&1, &1, U32 & String, String> <- Sys.Stdin.read(65536)
            slurp(r2, Con{SCon{c, rest}, cs})

def read_src(stdin: Bool, +path: String) -> IO(Result<&1, &1, U32 & String, String>):
  match stdin:
    case True{}:
      do IO<Result<&1, &1, U32 & String, String>>:
        r : Result<&1, &1, U32 & String, String> <- Sys.Stdin.read(65536)
        slurp(r, [])
    case False{}:
      Sys.Files.read(path)

# ---------------------------------------------------------------------
# Addresses: each target's host resolved once, up front
# ---------------------------------------------------------------------

def t_body(+t: Tgt.Target) -> Maybe<&2, String>:
  Tgt.Target{m, u, hs, b} = t
  b

def u_host(+u: Tgt.Url) -> String:
  Tgt.Url{scheme, host, port, path} = u
  host

def prep_of(r: Result<&1, &1, U32 & String, String>, b: Result<&1, &1, U32 & String, String>, +t: Tgt.Target, +u: Tgt.Url) -> Result<&2, &2, String, Sh.Prep>:
  match r:
    case Done{ip}:
      match b:
        case Done{body}:
          Done{Sh.Prep{t, u, ip, body}}
        case Fail{(code, msg)}:
          Fail{"error: open " ++ Maybe.default(&2, String, t_body(t), "") ++ ": " ++ msg}
    case Fail{(code, msg)}:
      Fail{"error: lookup " ++ u_host(u) ++ ": " ++ msg}

# the body file's bytes (none: empty)
def load_body(m: Maybe<&2, String>) -> IO(Result<&1, &1, U32 & String, String>):
  match m:
    case None{}:
      IO.pure(Result<&1, &1, U32 & String, String>, Done{""})
    case Some{p}:
      Sys.Files.read(p)

def prep_one(r: Result<&2, &2, String, Tgt.Url>, +t: Tgt.Target) -> IO(Result<&2, &2, String, Sh.Prep>):
  match r:
    case Fail{m}:
      IO.pure(Result<&2, &2, String, Sh.Prep>, Fail{"error: " ++ m})
    case Done{+u}:
      do IO<Result<&2, &2, String, Sh.Prep>>:
        d : Result<&1, &1, U32 & String, String> <- Sys.Dns.resolve(u_host(u))
        b : Result<&1, &1, U32 & String, String> <- load_body(t_body(t))
        return prep_of(d, b, t, u)

def t_url(+t: Tgt.Target) -> String:
  Tgt.Target{m, u, hs, b} = t
  u

def cons_res(p: Result<&2, &2, String, Sh.Prep>, ps: Result<&2, &2, String, List<&2, Sh.Prep>>) -> Result<&2, &2, String, List<&2, Sh.Prep>>:
  match p:
    case Fail{m}:
      Fail{m}
    case Done{x}:
      match ps:
        case Fail{m}:
          Fail{m}
        case Done{xs}:
          Done{Con{x, xs}}

def prep_all(ts: List<&2, Tgt.Target>) -> IO(Result<&2, &2, String, List<&2, Sh.Prep>>):
  match ts:
    case Nil{}:
      IO.pure(Result<&2, &2, String, List<&2, Sh.Prep>>, Done{[]})
    case Con{+t, rest}:
      do IO<Result<&2, &2, String, List<&2, Sh.Prep>>>:
        p : Result<&2, &2, String, Sh.Prep> <- prep_one(Tgt.parse_url(t_url(t)), t)
        ps : Result<&2, &2, String, List<&2, Sh.Prep>> <- prep_all(rest)
        return cons_res(p, ps)

# ---------------------------------------------------------------------
# The steps
# ---------------------------------------------------------------------

def done.of(none: Bool, +sent: Nat, +dropped: Nat) -> IO(Unit):
  match none:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      Sys.Out.write_err("bend: " ++ Dec.show(dropped) ++ " of " ++ Dec.show(Nat.add(sent, dropped)) ++ " scheduled hits dropped (all workers busy)\n")

def done(r: Nat & Nat) -> IO(Unit):
  (+sent, +dropped) = r
  done.of(Nat.is_eq(dropped, 0n), sent, dropped)

def set_output(stdout: Bool, +path: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  match stdout:
    case True{}:
      IO.pure(Result<&1, &1, U32 & String, Unit>, Done{Unit{}})
    case False{}:
      Sys.Out.to_file(path)

def go_run(o: Result<&1, &1, U32 & String, Unit>, +ps: List<&2, Sh.Prep>, +a: Flags.Attack) -> IO(Unit):
  match o:
    case Fail{(code, msg)}:
      die("error: open " ++ a_output(a) ++ ": " ++ msg)
    case Done{u}:
      do IO<Unit>:
        sd : Nat & Nat <- Sh.run(eng_cfg(a, List.length(&2, Sh.Prep, ps)), Sh.WEnv{conn_cfg(a), a_name(a), a_json(a), ps})
        done(sd)

def go_preps(r: Result<&2, &2, String, List<&2, Sh.Prep>>, +a: Flags.Attack) -> IO(Unit):
  match r:
    case Fail{m}:
      die(m)
    case Done{+ps}:
      do IO<Unit>:
        o : Result<&1, &1, U32 & String, Unit> <- set_output(String.eq(a_output(a), "stdout"), a_output(a))
        go_run(o, ps, a)

def go_targets(r: Result<&2, &2, String, List<&2, Tgt.Target>>, +a: Flags.Attack) -> IO(Unit):
  match r:
    case Fail{m}:
      die("error: " ++ m)
    case Done{ts}:
      match ts:
        case Nil{}:
          die("error: no targets to attack")
        case Con{t, rest}:
          do IO<Unit>:
            ps : Result<&2, &2, String, List<&2, Sh.Prep>> <- prep_all(apply_all(Con{t, rest}, a))
            go_preps(ps, a)

def go_text(r: Result<&1, &1, U32 & String, String>, +a: Flags.Attack) -> IO(Unit):
  match r:
    case Fail{(code, msg)}:
      die("error: open " ++ a_targets(a) ++ ": " ++ msg)
    case Done{text}:
      go_targets(Tgt.parse_all(text), a)

def go_flags(r: Result<&2, &2, String, Flags.Attack>) -> IO(Unit):
  match r:
    case Fail{m}:
      die(m)
    case Done{+a}:
      do IO<Unit>:
        t : Result<&1, &1, U32 & String, String> <- read_src(String.eq(a_targets(a), "stdin"), a_targets(a))
        go_text(t, a)

def run(+args: List<&2, String>) -> IO(Unit):
  go_flags(Flags.parse_attack(args))

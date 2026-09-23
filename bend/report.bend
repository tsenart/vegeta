# The report command: reads results (CSV or JSON lines, told apart per
# record) from files or stdin as they stream in, folds them into metrics,
# and writes the text, JSON or histogram report. Each step answers what
# the next one takes as a parameter (a match may not follow a bind).
import Base
import ./lib/sys.bend as Sys
import ./lib/flags.bend as Flags
import ./lib/hit.bend as Hit
import ./lib/metrics.bend as Met
import ./lib/report.bend as Rep
import ./lib/civil.bend as Civil

def die(+msg: String) -> IO(Unit):
  do IO<Unit>:
    Sys.Out.write_err(msg ++ "\n")
    IO.die(Unit, 1, "")

def fold(hs: List<&2, Hit.Hit>, +acc: Met.Acc) -> Met.Acc:
  match hs:
    case Nil{}:
      acc
    case Con{h, rest}:
      fold(rest, Met.add(acc, h))

# ---------------------------------------------------------------------
# Streaming: each chunk's complete lines are decoded as they come; a
# record cut by a chunk (a quoted newline) waits for more
# ---------------------------------------------------------------------

def pick_nat(c: Bool, +a: Nat, +b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

# the length of the next piece of s to decode: through the last newline
# in its first 64 KiB, or through the first newline past them (0 without a
# newline), so no decode takes a whole file at once
def is_nl(c: Char) -> Bool:
  Chr{k} = c
  U32.is_eq(k, 10)

def piece.go(s: String, stop: Bool, +i: Nat, +at: Nat) -> Nat:
  match s:
    case SNil{}:
      at
    case SCon{c, rest}:
      match stop:
        case True{}:
          at
        case False{}:
          +nat = pick_nat(is_nl(c), 1n+i, at)
          piece.go(rest, Bool.and(Nat.is_ge(1n+i, 65536n), Nat.is_gt(nat, 0n)), 1n+i, nat)

def piece(s: String) -> Nat:
  piece.go(s, False{}, 0n, 0n)

type Rd is Type:
  Next{}
  Split{}
  Pieced{none: Bool, n: Nat}
  Chunk{r: Result<&1, &1, U32 & String, String>}
  Decoded{m: Maybe<&2, List<&2, Hit.Hit>>, buf: String, cut: Nat}
  Last{m: Maybe<&2, List<&2, Hit.Hit>>}

def more(stdin: Bool) -> IO(Result<&1, &1, U32 & String, String>):
  match stdin:
    case True{}:
      Sys.Stdin.read(65536)
    case False{}:
      IO.pure(Result<&1, &1, U32 & String, String>, Done{""})

def open_src(stdin: Bool, +path: String) -> IO(Result<&1, &1, U32 & String, String>):
  match stdin:
    case True{}:
      Sys.Stdin.read(65536)
    case False{}:
      Sys.Files.read(path)

# reads every source in turn: buf holds the input not decoded yet, stdin
# whether the current source is stdin, src its name
@unsafe def feed(m: Rd, +buf: String, +acc: Met.Acc, +stdin: Bool, +src: String, +files: List<&2, String>)
  -> IO(Result<&2, &2, String, Met.Acc>):
  match m:
    case Next{}:
      match files:
        case Nil{}:
          IO.pure(Result<&2, &2, String, Met.Acc>, Done{acc})
        case Con{+f, rest}:
          do IO<Result<&2, &2, String, Met.Acc>>:
            r : Result<&1, &1, U32 & String, String> <- open_src(String.eq(f, "stdin"), f)
            feed(Chunk{r}, "", acc, String.eq(f, "stdin"), f, rest)
    case Chunk{r}:
      match r:
        case Fail{(code, msg)}:
          IO.pure(Result<&2, &2, String, Met.Acc>, Fail{"error: open " ++ src ++ ": " ++ msg})
        case Done{d}:
          match d:
            case SNil{}:
              feed(Last{Hit.decode_all(buf)}, "", acc, stdin, src, files)
            case SCon{c, rest}:
              feed(Split{}, buf ++ SCon{c, rest}, acc, stdin, src, files)
    case Split{}:
      +n = piece(buf)
      feed(Pieced{Nat.is_eq(n, 0n), n}, buf, acc, stdin, src, files)
    case Pieced{none, +n}:
      match none:
        case True{}:
          do IO<Result<&2, &2, String, Met.Acc>>:
            r : Result<&1, &1, U32 & String, String> <- more(stdin)
            feed(Chunk{r}, buf, acc, stdin, src, files)
        case False{}:
          feed(Decoded{Hit.decode_all(String.take(buf, n)), buf, n}, "", acc, stdin, src, files)
    case Decoded{m, b, +n}:
      match m:
        case Some{hs}:
          feed(Split{}, String.drop(b, n), fold(hs, acc), stdin, src, files)
        case None{}:
          do IO<Result<&2, &2, String, Met.Acc>>:
            r : Result<&1, &1, U32 & String, String> <- more(stdin)
            feed(Chunk{r}, b, acc, stdin, src, files)
    case Last{m}:
      match m:
        case None{}:
          IO.pure(Result<&2, &2, String, Met.Acc>, Fail{"error: decode: " ++ src ++ ": not a result in CSV or JSON"})
        case Some{hs}:
          feed(Next{}, "", fold(hs, acc), stdin, src, files)

# ---------------------------------------------------------------------
# Writing the report
# ---------------------------------------------------------------------

def r_kind(+r: Flags.Report) -> Flags.RKind:
  Flags.Report{k, out, files} = r
  k

def r_output(+r: Flags.Report) -> String:
  Flags.Report{k, out, files} = r
  out

def r_files(+r: Flags.Report) -> List<&2, String>:
  Flags.Report{k, out, files} = r
  match files:
    case Nil{}:
      ["stdin"]
    case Con{f, rest}:
      Con{f, rest}

def buckets(k: Flags.RKind) -> List<&2, Nat>:
  match k:
    case Flags.AsText{}:
      []
    case Flags.AsJson{bs}:
      bs
    case Flags.AsHist{bs}:
      bs

def s_sec(+m: Maybe<&2, Civil.Time>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{t}:
      Civil.Time{s, ns, off} = t
      s

def s_times(+s: Met.Summary) -> List<&2, Nat>:
  Met.Summary{rq, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, en, d, w, bs, h} = s
  [s_sec(e), s_sec(l), s_sec(en)]

def zones_of(zs: List<&2, Nat>) -> Rep.Zones:
  match zs:
    case Con{a, r1}:
      match r1:
        case Con{b, r2}:
          match r2:
            case Con{c, r3}:
              Rep.Zones{a, b, c}
            case Nil{}:
              Rep.Zones{86400n, 86400n, 86400n}
        case Nil{}:
          Rep.Zones{86400n, 86400n, 86400n}
    case Nil{}:
      Rep.Zones{86400n, 86400n, 86400n}

# the local offsets at each of the given seconds
def offsets(ss: List<&2, Nat>) -> IO(List<&2, Nat>):
  match ss:
    case Nil{}:
      IO.pure(List<&2, Nat>, [])
    case Con{s, rest}:
      do IO<List<&2, Nat>>:
        o : Nat <- Sys.Clock.offset_at(s)
        os : List<&2, Nat> <- offsets(rest)
        return Con{o, os}

def render(k: Flags.RKind, +s: Met.Summary) -> IO(Unit):
  match k:
    case Flags.AsText{}:
      Sys.Out.write(Rep.text(s))
    case Flags.AsHist{bs}:
      Sys.Out.write(Rep.hist(s))
    case Flags.AsJson{bs}:
      do IO<Unit>:
        os : List<&2, Nat> <- offsets(s_times(s))
        Sys.Out.write(Rep.json(s, zones_of(os)))

def write_out(o: Result<&1, &1, U32 & String, Unit>, +r: Flags.Report, +acc: Met.Acc) -> IO(Unit):
  match o:
    case Fail{(code, msg)}:
      die("error: open " ++ r_output(r) ++ ": " ++ msg)
    case Done{u}:
      render(r_kind(r), Met.close(acc))

def set_output(stdout: Bool, +path: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  match stdout:
    case True{}:
      IO.pure(Result<&1, &1, U32 & String, Unit>, Done{Unit{}})
    case False{}:
      Sys.Out.to_file(path)

def go_span(ok: Bool, +r: Flags.Report, +acc: Met.Acc) -> IO(Unit):
  match ok:
    case False{}:
      die("error: the results span 281474s (about 78h) or more, past the Bend port's durations")
    case True{}:
      do IO<Unit>:
        o : Result<&1, &1, U32 & String, Unit> <- set_output(String.eq(r_output(r), "stdout"), r_output(r))
        write_out(o, r, acc)

def go_acc(res: Result<&2, &2, String, Met.Acc>, +r: Flags.Report) -> IO(Unit):
  match res:
    case Fail{m}:
      die(m)
    case Done{+acc}:
      go_span(Met.span_ok(acc), r, acc)

def go_flags(res: Result<&2, &2, String, Flags.Report>) -> IO(Unit):
  match res:
    case Fail{m}:
      die(m)
    case Done{+r}:
      do IO<Unit>:
        a : Result<&2, &2, String, Met.Acc> <- feed(Next{}, "", Met.empty(buckets(r_kind(r))), False{}, "", r_files(r))
        go_acc(a, r)

def run(+args: List<&2, String>) -> IO(Unit):
  go_flags(Flags.parse_report(args))

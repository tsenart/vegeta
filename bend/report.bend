# The report command: reads results (CSV or JSON lines, told apart per
# record) from files or stdin, decodes them in parallel into metrics,
# and writes the text, JSON or histogram report. Each step answers what
# the next one takes as a parameter (a match may not follow a bind).
import Base
import ./lib/sys.bend as Sys
import ./lib/flags.bend as Flags
import ./lib/metrics.bend as Met
import ./lib/report.bend as Rep
import ./lib/civil.bend as Civil
import ./lib/rdec.bend as RD

def die(+msg: String) -> IO(Unit):
  do IO<Unit>:
    Sys.Out.write_err(msg ++ "\n")
    IO.die(Unit, 1, "")

# ---------------------------------------------------------------------
# Reading: the input comes in batches (a few MiB) of pieces of whole
# lines (Sys's Pieces.read); a batch's pieces are decoded in parallel,
# each into metrics of its own (lib/rdec.bend), and merged in order, and
# the next batch is read meanwhile. A record that fails to decode (one
# cut by the end of its piece, at a raw LF inside it, or no result at
# all) waits, with all the input after it, for more: the input is then
# decoded from there as one, at the end of the source at the latest. The metrics are those of
# Hit.decode_all over the whole source: it reads each record from its
# own bytes, so it reads the same records from the pieces.
# ---------------------------------------------------------------------

# the pieces, as a balanced tree (still packed, or read), each with its
# index in its batch
type PT is Data:
  PLeaf{i: U32, p: List<&2, List<&2, U32>>}
  PText{i: U32, s: String}
  PNode{l: PT, r: PT}

def leaves(xs: List<&2, List<&2, List<&2, U32>>>, +i: U32) -> List<&2, PT>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Con{PLeaf{i, x}, leaves(rest, (i + 1 : U32))}

def pairs(ts: List<&2, PT>) -> List<&2, PT>:
  match ts:
    case Nil{}:
      []
    case Con{a, r1}:
      match r1:
        case Nil{}:
          [a]
        case Con{b, r2}:
          Con{PNode{a, b}, pairs(r2)}

# fuel: the depth left (a list of n trees needs log2(n))
def tree(fuel: Nat, ts: List<&2, PT>) -> PT:
  match fuel:
    case 0n:
      PText{0, ""}
    case 1n+f:
      match ts:
        case Nil{}:
          PText{0, ""}
        case Con{t, rest}:
          match rest:
            case Nil{}:
              t
            case Con{u, more}:
              tree(f, pairs(Con{t, Con{u, more}}))

# A batch's pieces decoded, in order, as runs: metrics (SOk); a piece the
# fast path stopped in, at its line j, with the metrics of the lines
# before (SRedo: add_lines reads the rest, from the lines again); a
# record that failed, in the piece at index i, with the metrics before it
# and the input from it to the end of its piece (SBad: what follows is
# read again).
type Seg is Data:
  SOk{acc: Met.Acc}
  SRedo{i: U32, j: U32, acc: Met.Acc}
  SBad{acc: Met.Acc, rest: String, i: U32}

def seg_of(+i: U32, r: RD.Res) -> Seg:
  match r:
    case RD.AOk{a}:
      SOk{a}
    case RD.ABad{a, rest}:
      SBad{a, rest, i}

def seg_fast(+i: U32, r: RD.Fast) -> Seg:
  match r:
    case RD.FAll{a}:
      SOk{a}
    case RD.FStop{a, j}:
      SRedo{i, j, a}

# the metrics a, then the runs b
def meet.ok(a: Met.Acc, b: List<&2, Seg>) -> List<&2, Seg>:
  match b:
    case Nil{}:
      [SOk{a}]
    case Con{y, more}:
      match y:
        case SOk{c}:
          Con{SOk{Met.merge(a, c)}, more}
        case SRedo{i, j, c}:
          Con{SOk{a}, Con{SRedo{i, j, c}, more}}
        case SBad{c, rest, i}:
          Con{SOk{a}, Con{SBad{c, rest, i}, more}}

# the run x, then the runs b (nothing after a failed record)
def meet(x: Seg, b: List<&2, Seg>) -> List<&2, Seg>:
  match x:
    case SOk{a}:
      meet.ok(a, b)
    case SRedo{i, j, a}:
      Con{SRedo{i, j, a}, b}
    case SBad{a, rest, i}:
      [SBad{a, rest, i}]

# the runs a, then the runs b
def runs(a: List<&2, Seg>, b: List<&2, Seg>) -> List<&2, Seg>:
  match a:
    case Nil{}:
      b
    case Con{x, rest}:
      match rest:
        case Nil{}:
          meet(x, b)
        case Con{y, more}:
          Con{x, runs(Con{y, more}, b)}

# both halves at once
def run_tree(t: PT) -> List<&2, Seg>:
  match t:
    case PLeaf{i, p}:
      [seg_fast(i, RD.add_fast(p, Met.empty([])))]
    case PText{i, s}:
      [seg_of(i, RD.add_all(s, Met.empty([])))]
    case PNode{l, r}:
      a b = run_tree(l) run_tree(r)
      runs(a, b)

# the runs after the fast path: a piece it stopped in comes with the
# lines from the one it stopped at
type Work is Data:
  WDone{s: Seg}
  WLines{i: U32, acc: Met.Acc, ls: List<&2, List<&2, U32>>}

type WT is Data:
  WLeaf{w: Work}
  WNode{l: WT, r: WT}

def wleaves(ws: List<&2, Work>) -> List<&2, WT>:
  match ws:
    case Nil{}:
      []
    case Con{w, rest}:
      Con{WLeaf{w}, wleaves(rest)}

def wpairs(ts: List<&2, WT>) -> List<&2, WT>:
  match ts:
    case Nil{}:
      []
    case Con{a, r1}:
      match r1:
        case Nil{}:
          [a]
        case Con{b, r2}:
          Con{WNode{a, b}, wpairs(r2)}

def wtree(fuel: Nat, ts: List<&2, WT>) -> WT:
  match fuel:
    case 0n:
      WLeaf{WDone{SOk{Met.empty([])}}}
    case 1n+f:
      match ts:
        case Nil{}:
          WLeaf{WDone{SOk{Met.empty([])}}}
        case Con{t, rest}:
          match rest:
            case Nil{}:
              t
            case Con{u, more}:
              wtree(f, wpairs(Con{t, Con{u, more}}))

# the rest of the pieces the fast path stopped in, read by add_lines,
# all at once
def work(t: WT) -> List<&2, Seg>:
  match t:
    case WLeaf{w}:
      match w:
        case WDone{x}:
          [x]
        case WLines{i, a, ls}:
          [seg_of(i, RD.add_lines(ls, a))]
    case WNode{l, r}:
      a b = work(l) work(r)
      runs(a, b)

# the lines of each piece the fast path stopped in, from the source
def fetch(ss: List<&2, Seg>) -> IO(List<&2, Work>):
  match ss:
    case Nil{}:
      IO.pure(List<&2, Work>, [])
    case Con{x, rest}:
      match x:
        case SRedo{+i, +j, a}:
          do IO<List<&2, Work>>:
            ls : List<&2, List<&2, U32>> <- Sys.Pieces.lines(i, j)
            ws : List<&2, Work> <- fetch(rest)
            return Con{WLines{i, a, ls}, ws}
        case SOk{a}:
          do IO<List<&2, Work>>:
            ws : List<&2, Work> <- fetch(rest)
            return Con{WDone{SOk{a}}, ws}
        case SBad{a, r, i}:
          do IO<List<&2, Work>>:
            ws : List<&2, Work> <- fetch(rest)
            return Con{WDone{SBad{a, r, i}}, ws}

# the batch: all of it read, or up to a record that failed (in the piece
# at index i): the metrics before it, and the input from it to the end
# of its piece
type Run is Data:
  ROk{acc: Met.Acc}
  RBad{acc: Met.Acc, rest: String, i: U32}

def settle(ss: List<&2, Seg>, +acc: Met.Acc) -> Run:
  match ss:
    case Nil{}:
      ROk{acc}
    case Con{x, rest}:
      match x:
        case SOk{a}:
          settle(rest, Met.merge(acc, a))
        case SRedo{i, j, a}:
          settle(rest, Met.merge(acc, a))
        case SBad{a, r, i}:
          RBad{Met.merge(acc, a), r, i}

# a batch of pieces after the input that waits (pend), decoded
def batch(+pend: String, ps: List<&2, List<&2, List<&2, U32>>>) -> List<&2, Seg>:
  match ps:
    case Nil{}:
      [seg_of(0, RD.add_all(pend, Met.empty([])))]
    case Con{p, rest}:
      run_tree(tree(64n, Con{PText{0, pend ++ Sys.Packed.text(p)}, leaves(rest, 1)}))

# the bytes of packed pieces, in order
def texts(ps: List<&2, List<&2, List<&2, U32>>>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, rest}:
      Sys.Packed.text(p) ++ texts(rest)

def piece_size() -> U32:
  65536

def batch_size() -> U32:
  16777216

# the batch decoded, when the computation runs (the bind puts it off, so
# it runs where the computation is forked)
def decode_io(+pend: String, ps: List<&2, List<&2, List<&2, U32>>>) -> IO(List<&2, Seg>):
  do IO<List<&2, Seg>>:
    u : Unit <- IO.pure(Unit, Unit{})
    return batch(pend, ps)

def open_src(stdin: Bool, +path: String) -> IO(Result<&1, &1, U32 & String, U32>):
  match stdin:
    case True{}:
      IO.pure(Result<&1, &1, U32 & String, U32>, Done{0})
    case False{}:
      Sys.Pieces.open(path)

def read(+fd: U32) -> IO(Result<&1, &1, U32 & String, List<&2, List<&2, List<&2, U32>>>>):
  Sys.Pieces.read(fd, batch_size(), piece_size())

# The steps: a source opened; a batch read, with no decoding going on;
# the decoding of the last batch going on, and the next batch read; that
# decoding done, and the next batch read; the last of a source decoded
type Rd is Type:
  Next{}
  Opened{r: Result<&1, &1, U32 & String, U32>}
  Read{r: Result<&1, &1, U32 & String, List<&2, List<&2, List<&2, U32>>>>}
  Both{c: Chan(List<&2, Seg>), r: Result<&1, &1, U32 & String, List<&2, List<&2, List<&2, U32>>>>}
  Joined{run: Run, r: Result<&1, &1, U32 & String, List<&2, List<&2, List<&2, U32>>>>}
  Last{m: RD.Res}

# reads every source in turn, a batch decoding while the next is read:
# pend is the input that waits for more, fd the source's descriptor, src
# its name
@unsafe def feed(m: Rd, +pend: String, +acc: Met.Acc, +fd: U32, +src: String, +files: List<&2, String>)
  -> IO(Result<&2, &2, String, Met.Acc>):
  match m:
    case Next{}:
      match files:
        case Nil{}:
          IO.pure(Result<&2, &2, String, Met.Acc>, Done{acc})
        case Con{+f, rest}:
          do IO<Result<&2, &2, String, Met.Acc>>:
            r : Result<&1, &1, U32 & String, U32> <- open_src(String.eq(f, "stdin"), f)
            feed(Opened{r}, "", acc, 0, f, rest)
    case Opened{r}:
      match r:
        case Fail{(code, msg)}:
          IO.pure(Result<&2, &2, String, Met.Acc>, Fail{"error: open " ++ src ++ ": " ++ msg})
        case Done{+d}:
          do IO<Result<&2, &2, String, Met.Acc>>:
            b : Result<&1, &1, U32 & String, List<&2, List<&2, List<&2, U32>>>> <- read(d)
            feed(Read{b}, "", acc, d, src, files)
    case Read{r}:
      match r:
        case Fail{(code, msg)}:
          IO.pure(Result<&2, &2, String, Met.Acc>, Fail{"error: open " ++ src ++ ": " ++ msg})
        case Done{ps}:
          match ps:
            case Nil{}:
              do IO<Result<&2, &2, String, Met.Acc>>:
                Sys.Pieces.close(fd)
                feed(Last{RD.add_all(pend, acc)}, "", Met.empty([]), fd, src, files)
            case Con{p, rest}:
              do IO<Result<&2, &2, String, Met.Acc>>:
                c : Chan(List<&2, Seg>) <- IO.fork(List<&2, Seg>, decode_io(pend, Con{p, rest}))
                b : Result<&1, &1, U32 & String, List<&2, List<&2, List<&2, U32>>>> <- read(fd)
                feed(Both{c, b}, "", acc, fd, src, files)
    case Both{c, b}:
      do IO<Result<&2, &2, String, Met.Acc>>:
        ss : List<&2, Seg> <- IO.join(List<&2, Seg>, c)
        ws : List<&2, Work> <- fetch(ss)
        feed(Joined{settle(work(wtree(64n, wleaves(ws))), Met.empty([])), b}, "", acc, fd, src, files)
    case Joined{run, b}:
      match run:
        case ROk{x}:
          feed(Read{b}, "", Met.merge(acc, x), fd, src, files)
        case RBad{x, rest, i}:
          do IO<Result<&2, &2, String, Met.Acc>>:
            after : List<&2, List<&2, List<&2, U32>>> <- Sys.Pieces.again((i + 1 : U32))
            feed(Read{b}, rest ++ texts(after), Met.merge(acc, x), fd, src, files)
    case Last{m}:
      match m:
        case RD.ABad{a, rest}:
          IO.pure(Result<&2, &2, String, Met.Acc>, Fail{"error: decode: " ++ src ++ ": not a result in CSV or JSON"})
        case RD.AOk{a}:
          feed(Next{}, "", a, fd, src, files)

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

# the span checked on the extremes alone (span_ok's reading), so that the
# accumulator is not shared: its latencies are walked once, by close
def go_ext(a: Met.Acc, +r: Flags.Report) -> IO(Unit):
  Met.Acc{bs, n, ok, codes, errs, lat, bin, bout, +x, t} = a
  go_span(Met.span_ok.of(x), r, Met.Acc{bs, n, ok, codes, errs, lat, bin, bout, x, t})

def go_acc(res: Result<&2, &2, String, Met.Acc>, +r: Flags.Report) -> IO(Unit):
  match res:
    case Fail{m}:
      die(m)
    case Done{acc}:
      go_ext(acc, r)

def go_flags(res: Result<&2, &2, String, Flags.Report>) -> IO(Unit):
  match res:
    case Fail{m}:
      die(m)
    case Done{+r}:
      do IO<Unit>:
        a : Result<&2, &2, String, Met.Acc> <- feed(Next{}, "", Met.empty(buckets(r_kind(r))), 0, "", r_files(r))
        go_acc(a, r)

def run(+args: List<&2, String>) -> IO(Unit):
  go_flags(Flags.parse_report(args))

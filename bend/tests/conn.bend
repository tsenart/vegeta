# The client machine driven by scripted timelines.
#
# First, the cases of scripts/gen-conn.go: the machine is fed what Go's
# client saw from the scripted server, and prints name|error|body as
# Vegeta's result records them (through Conn.to_hit), then the requests
# it sent as name>n|request, as Go's lines do.
#
# Then timelines: each line is the first commands, then every event and
# the commands it drew (Got shows its size; Send the request line).
import Base
import ../lib/hdr.bend as Hdr
import ../lib/target.bend as Tgt
import ../lib/http.bend as Http
import ../lib/dec.bend as Dec
import ../lib/civil.bend as Civil
import ../lib/hit.bend as Hit
import ../lib/conn.bend as Conn

def sel(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def esc(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      sel(String, U32.is_eq(code(c), 13), "\\r", sel(String, U32.is_eq(code(c), 10), "\\n", SCon{c, SNil{}})) ++ esc(rest)

def line1(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      sel(String, U32.is_eq(code(c), 13), "", SCon{c, line1(rest)})

def st_of(+r: Sigma<&2, &2, Conn.State, _ => List<&2, Conn.Cmd>>) -> Conn.State:
  (st, cs) = r
  st

def cs_of(+r: Sigma<&2, &2, Conn.State, _ => List<&2, Conn.Cmd>>) -> List<&2, Conn.Cmd>:
  (st, cs) = r
  cs

# ---------------------------------------------------------------------
# Showing
# ---------------------------------------------------------------------

def show_pb(+m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{b}:
      " partial=" ++ esc(b)

def show_out(+o: Conn.Out) -> String:
  match o:
    case Conn.Answered{r}:
      Http.Resp{c, st, hs, b, k} = r
      "ok " ++ st ++ " body=" ++ esc(b)
    case Conn.Failed{m, pb}:
      "fail " ++ m ++ show_pb(pb)

def show_cmd(+k: Conn.Cmd) -> String:
  match k:
    case Conn.Resolve{h}:
      "Resolve " ++ h
    case Conn.Open{ip, p}:
      "Open " ++ ip ++ ":" ++ Dec.show(p)
    case Conn.Send{d}:
      "Send " ++ line1(d)
    case Conn.Recv{}:
      "Recv"
    case Conn.Shut{}:
      "Shut"
    case Conn.Finish{o, keep}:
      "Finish " ++ show_out(o) ++ sel(String, keep, " (kept)", " (closed)")

def show_cmds(cs: List<&2, Conn.Cmd>) -> String:
  match cs:
    case Nil{}:
      "-"
    case Con{+k, +rest}:
      match rest:
        case Nil{}:
          show_cmd(k)
        case Con{+k2, +more}:
          show_cmd(k) ++ ", " ++ show_cmds(Con{k2, more})

def show_ev(+e: Conn.Ev) -> String:
  match e:
    case Conn.Opened{}:
      "Opened"
    case Conn.OpenFailed{m}:
      "OpenFailed"
    case Conn.Sent{}:
      "Sent"
    case Conn.SendFailed{m}:
      "SendFailed"
    case Conn.Got{d}:
      "Got" ++ Dec.show(String.length(d))
    case Conn.Eof{}:
      "Eof"
    case Conn.Late{}:
      "Late"
    case Conn.Resolved{ip}:
      "Resolved " ++ ip
    case Conn.ResolveFailed{m}:
      "ResolveFailed"

# ---------------------------------------------------------------------
# Driving
# ---------------------------------------------------------------------

def trace(evs: List<&2, Conn.Ev>, +c: Conn.Cfg, +s: Conn.State) -> String:
  match evs:
    case Nil{}:
      ""
    case Con{+e, +rest}:
      " | " ++ show_ev(e) ++ ": " ++ show_cmds(cs_of(Conn.step(c, s, e))) ++ trace(rest, c, st_of(Conn.step(c, s, e)))

def timeline.of(+r: Sigma<&2, &2, Conn.State, _ => List<&2, Conn.Cmd>>, +c: Conn.Cfg, +evs: List<&2, Conn.Ev>) -> String:
  show_cmds(cs_of(r)) ++ trace(evs, c, st_of(r))

def timeline(+name: String, +c: Conn.Cfg, +q: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>) -> String:
  name ++ ": " ++ timeline.of(Conn.start(c, q, open), c, evs)

def cmds(evs: List<&2, Conn.Ev>, +c: Conn.Cfg, +s: Conn.State) -> List<&2, Conn.Cmd>:
  match evs:
    case Nil{}:
      []
    case Con{+e, +rest}:
      List.append(&2, Conn.Cmd, cs_of(Conn.step(c, s, e)), cmds(rest, c, st_of(Conn.step(c, s, e))))

def all.of(+r: Sigma<&2, &2, Conn.State, _ => List<&2, Conn.Cmd>>, +c: Conn.Cfg, +evs: List<&2, Conn.Ev>) -> List<&2, Conn.Cmd>:
  List.append(&2, Conn.Cmd, cs_of(r), cmds(evs, c, st_of(r)))

def all(+c: Conn.Cfg, +q: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>) -> List<&2, Conn.Cmd>:
  all.of(Conn.start(c, q, open), c, evs)

def outcome(cs: List<&2, Conn.Cmd>) -> Maybe<&2, Conn.Out>:
  match cs:
    case Nil{}:
      None{}
    case Con{+k, +rest}:
      match k:
        case Conn.Finish{o, keep}:
          Some{o}
        case _:
          outcome(rest)

def sends(cs: List<&2, Conn.Cmd>) -> List<&2, String>:
  match cs:
    case Nil{}:
      []
    case Con{+k, +rest}:
      match k:
        case Conn.Send{d}:
          Con{d, sends(rest)}
        case _:
          sends(rest)

def n_recv(cs: List<&2, Conn.Cmd>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{+k, +rest}:
      match k:
        case Conn.Recv{}:
          1n+n_recv(rest)
        case _:
          n_recv(rest)

def t0() -> Civil.Time:
  Civil.Time{0n, 0n, 0n}

def hit_text(+name: String, +h: Hit.Hit) -> String:
  Hit.Hit{a, s, k, ts, lat, bo, bi, err, body, me, u, hs} = h
  name ++ "|" ++ esc(err) ++ "|" ++ esc(Maybe.default(&2, String, body, ""))

def hit_line(+name: String, +m: Maybe<&2, Conn.Out>) -> String:
  match m:
    case None{}:
      name ++ "|unfinished|"
    case Some{o}:
      hit_text(name, Conn.to_hit("", 0n, t0(), 0n, "GET", "u", 0n, o))

def req_lines(xs: List<&2, String>, +name: String, +i: Nat) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      Con{name ++ ">" ++ Dec.show(i) ++ "|" ++ esc(x), req_lines(rest, name, 1n+i)}

def lines(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      match rest:
        case Nil{}:
          x
        case Con{+y, +more}:
          x ++ "\n" ++ lines(Con{y, more})

# a Go case: the result line, and the requests when shown
def go_case(+name: String, +c: Conn.Cfg, +q: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>, +show: Bool) -> String:
  lines(Con{hit_line(name, outcome(all(c, q, open, evs))),
    sel(List<&2, String>, show, req_lines(sends(all(c, q, open, evs)), name, 0n), [])})

# the bytes in Got pieces of n
def pieces(fuel: Nat, +n: Nat, +s: String) -> List<&2, Conn.Ev>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      sel(List<&2, Conn.Ev>, String.is_empty(s), [], Con{Conn.Got{String.take(s, n)}, pieces(f, n, String.drop(s, n))})

# ---------------------------------------------------------------------
# Requests and configurations
# ---------------------------------------------------------------------

def cfg(+ka: Bool, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>) -> Conn.Cfg:
  Conn.CCfg{ka, 0n, mb, rd}

def dflt() -> Conn.Cfg:
  Conn.CCfg{True{}, 0n, None{}, Some{10n}}

def rd(+n: Maybe<&2, Nat>) -> Conn.Cfg:
  Conn.CCfg{True{}, 0n, None{}, n}

def req(+m: String, +path: String, +hs: List<&2, Hdr.Header>, +body: String) -> Conn.Req:
  Conn.Req{Tgt.Target{m, "http://h" ++ path, hs, None{}}, Tgt.Url{"http", "h", None{}, path}, "127.0.0.1", body, 0n, ""}

def get() -> Conn.Req:
  req("GET", "/", [], "")

def auth_ct() -> List<&2, Hdr.Header>:
  [Hdr.Header{"Authorization", ["t"]}, Hdr.Header{"Content-Type", ["text/plain"]}]

def ok5() -> String:
  "HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello"

def go_lines() -> String:
  lines([
    go_case("refused", dflt(), Conn.Req{Tgt.Target{"GET", "http://127.0.0.1:1/", [], None{}}, Tgt.Url{"http", "127.0.0.1", Some{1n}, "/"}, "127.0.0.1", "", 0n, ""},
      False{}, [Conn.OpenFailed{"Connection refused"}], False{}),
    go_case("eof-fresh", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Eof{}], False{}),
    go_case("eof-reused-post", dflt(), req("POST", "/", [], "x"), True{}, [Conn.Sent{}, Conn.Eof{}], True{}),
    go_case("eof-reused-get", dflt(), req("GET", "/r", [], ""), True{}, [Conn.Sent{}, Conn.Eof{}, Conn.Opened{}, Conn.Sent{}, Conn.Got{ok5()}], True{}),
    go_case("late-head", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Late{}], False{}),
    go_case("late-body", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nabc"}, Conn.Late{}], False{}),
    go_case("late-interim", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 103 Early Hints\r\nLink: x\r\n\r\n"}, Conn.Late{}], False{}),
    go_case("cut-body", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\nabc"}, Conn.Eof{}], False{}),
    go_case("cut-chunked", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n2\r\nd"}, Conn.Eof{}], False{}),
    go_case("cut-head", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nX: 1\r\n"}, Conn.Eof{}], False{}),
    go_case("cut-status", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 20"}, Conn.Eof{}], False{}),
    go_case("cut-name", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nContent-Le"}, Conn.Eof{}], False{}),
    go_case("garbage", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"garbage\r\n\r\n"}], False{}),
    go_case("bad-chunk", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabcXY"}], False{}),
    go_case("not-found", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 404 Not Found\r\nContent-Length: 4\r\n\r\nnope"}], False{}),
    go_case("max-body", Conn.CCfg{True{}, 0n, Some{2n}, Some{10n}}, get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nContent-Length: 8\r\n\r\n12345678"}], False{}),
    go_case("stop-0", rd(Some{0n}), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 0\r\n\r\n"}], False{}),
    go_case("stop-1", rd(Some{1n}), req("POST", "/a", [], "b"), False{},
      [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /b\r\nContent-Length: 0\r\n\r\n"}, Conn.Sent{},
       Conn.Got{"HTTP/1.1 301 Moved Permanently\r\nLocation: c?q=1\r\nContent-Length: 0\r\n\r\n"}], True{}),
    go_case("nofollow", rd(None{}), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 2\r\n\r\nmv"}], False{}),
    go_case("follow-303", dflt(), req("POST", "/a/b", auth_ct(), "data"), False{},
      [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 303 See Other\r\nLocation: ../c\r\nContent-Length: 3\r\n\r\nabc"}, Conn.Sent{}, Conn.Got{ok5()}], True{}),
    go_case("follow-307-other", dflt(), req("PUT", "/", auth_ct(), "data"), False{},
      [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 307 Temporary Redirect\r\nLocation: http://other:8080/z\r\nConnection: close\r\n\r\nclosed-body"}, Conn.Eof{},
       Conn.Resolved{"127.0.0.1"}, Conn.Opened{}, Conn.Sent{}, Conn.Got{ok5()}], True{}),
    go_case("late-redirect", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 10\r\n\r\nabc"}, Conn.Late{}], False{}),
    go_case("lf-redirect", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\nLocation: /x\nContent-Length: 0\n\n"}, Conn.Sent{}, Conn.Got{ok5()}], True{}),
    go_case("lf-close", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\n\nabc"}, Conn.Eof{}], False{}),
    go_case("two-spaces", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1  302 Found\r\nLocation: /x\r\nContent-Length: 0\r\n\r\n"}, Conn.Sent{}, Conn.Got{ok5()}], True{}),
    go_case("loc-space", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation : /x\r\nContent-Length: 2\r\n\r\nmv"}], False{}),
    go_case("empty-loc", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: \r\nContent-Length: 2\r\n\r\nmv"}], False{})])

def chunked() -> String:
  "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nX-A: 1\r\n\r\n5;ext=1\r\nhello\r\n6\r\n world\r\n0\r\nTrailer-X: y\r\n\r\n"

def big_body() -> String:
  String.join(["0123456789", "0123456789", "0123456789", "0123456789", "0123456789", "0123456789", "0123456789", "0123456789", "0123456789", "0123456789"], "")

def split_line(+name: String, +c: Conn.Cfg, +raw: String, +n: Nat) -> String:
  +cs = all(c, get(), True{}, Con{Conn.Sent{}, pieces(String.length(raw), n, raw)})
  name ++ ": " ++ Dec.show(n_recv(cs)) ++ " Recv, " ++ show_cmds(sel(List<&2, Conn.Cmd>, Maybe.is_some(&2, Conn.Out, outcome(cs)), List.drop(&2, Conn.Cmd, cs, Nat.sub(List.length(&2, Conn.Cmd, cs), 1n)), []))

# n copies of s, doubling
def times(fuel: Nat, +s: String) -> String:
  match fuel:
    case 0n:
      s
    case 1n+f:
      times(f, s ++ s)

def mib() -> String:
  times(20n, "x")

def body_len(+m: Maybe<&2, Conn.Out>) -> String:
  match m:
    case None{}:
      "unfinished"
    case Some{o}:
      match o:
        case Conn.Answered{r}:
          Http.Resp{c, st, hs, b, k} = r
          st ++ " " ++ Dec.show(String.length(b))
        case Conn.Failed{e, pb}:
          e

def last(cs: List<&2, Conn.Cmd>, +d: Conn.Cmd) -> Conn.Cmd:
  match cs:
    case Nil{}:
      d
    case Con{+k, +rest}:
      last(rest, k)

# the last command, a Finish shown by its body's length
def short(+k: Conn.Cmd) -> String:
  match k:
    case Conn.Finish{o, keep}:
      body_len(Some{o}) ++ sel(String, keep, " (kept)", " (closed)")
    case _:
      show_cmd(k)

# a 1 MiB body in 1 KiB pieces (then the events in tail): the Recv
# count and the last command
def big_line(+name: String, +c: Conn.Cfg, +raw: String, +tail: List<&2, Conn.Ev>) -> String:
  +cs = all(c, get(), True{}, Con{Conn.Sent{}, List.append(&2, Conn.Ev, pieces(String.length(raw), 1024n, raw), tail)})
  name ++ ": " ++ Dec.show(n_recv(cs)) ++ " Recv, " ++ short(last(cs, Conn.Recv{}))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(go_lines())
    IO.print("differs from Go: " ++ lines(req_lines(sends(all(dflt(), req("GET", "/", [Hdr.Header{"Host", ["custom"]}], ""), False{},
      [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: http://other/\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"},
       Conn.Resolved{"127.0.0.1"}, Conn.Opened{}])), "host-other", 0n)))
    IO.print(timeline("fresh", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhel"}, Conn.Got{"lo"}]))
    IO.print(timeline("reuse", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{ok5()}]))
    IO.print(timeline("server-close", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nConnection: close\r\nContent-Length: 2\r\n\r\nhi"}]))
    IO.print(timeline("http10", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.0 200 OK\r\nContent-Length: 2\r\n\r\nhi"}]))
    IO.print(timeline("no-keepalive", cfg(False{}, None{}, Some{10n}), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Got{ok5()}]))
    IO.print("no-keepalive sends close: " ++ Bool.show(String.contains(Maybe.default(&2, String, List.head(&2, String, sends(all(cfg(False{}, None{}, Some{10n}), get(), True{}, []))), ""), "Connection: close\r\n")))
    IO.print(timeline("extra-bytes", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{ok5() ++ "EXTRA"}]))
    IO.print(timeline("until-close", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\n\r\nab"}, Conn.Got{"c"}, Conn.Eof{}]))
    IO.print(timeline("head", dflt(), req("HEAD", "/", [], ""), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\n"}]))
    IO.print(timeline("interim", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 204 No Content\r\n\r\n"}]))
    IO.print(timeline("early-answer", dflt(), get(), True{}, [Conn.Got{ok5()}, Conn.Sent{}]))
    IO.print(split_line("chunked-by-1", dflt(), chunked(), 1n))
    IO.print(split_line("chunked-by-3", dflt(), chunked(), 3n))
    IO.print(split_line("length-by-7", dflt(), "HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\n" ++ big_body(), 7n))
    IO.print(split_line("max-body-by-5", cfg(True{}, Some{3n}, Some{10n}), "HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\n" ++ big_body(), 5n))
    IO.print(split_line("max-body-0", cfg(True{}, Some{0n}, Some{10n}), chunked(), 4n))
    IO.print(big_line("mib-length", dflt(), "HTTP/1.1 200 OK\r\nContent-Length: 1048576\r\n\r\n" ++ mib(), []))
    IO.print(big_line("mib-close", dflt(), "HTTP/1.1 200 OK\r\n\r\n" ++ mib(), [Conn.Eof{}]))
    IO.print(big_line("mib-max-body", cfg(True{}, Some{100n}, Some{10n}), "HTTP/1.1 200 OK\r\nContent-Length: 1048576\r\n\r\n" ++ mib(), []))
    IO.print(big_line("mib-redirect", dflt(), "HTTP/1.1 302 Found\r\nLocation: /b\r\n\r\n" ++ mib(), []))
    IO.print(timeline("late-before-send", dflt(), get(), False{}, [Conn.Late{}]))
    IO.print(timeline("send-failed", dflt(), get(), False{}, [Conn.Opened{}, Conn.SendFailed{"Broken pipe"}]))
    IO.print(timeline("send-failed-retry", dflt(), get(), True{}, [Conn.SendFailed{"Broken pipe"}, Conn.Opened{}, Conn.Sent{}, Conn.Got{ok5()}]))
    IO.print(timeline("retry-once", dflt(), get(), True{}, [Conn.Sent{}, Conn.Eof{}, Conn.Opened{}, Conn.Sent{}, Conn.Eof{}]))
    IO.print(timeline("retry-refused", dflt(), get(), True{}, [Conn.Sent{}, Conn.Eof{}, Conn.OpenFailed{"Connection refused"}]))
    IO.print(timeline("retry-idempotent", dflt(), req("POST", "/", [Hdr.Header{"idempotency-key", ["k"]}], "x"), True{}, [Conn.Sent{}, Conn.Eof{}]))
    IO.print(timeline("no-retry-fresh", dflt(), get(), False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Eof{}]))
    IO.print(timeline("no-retry-after-bytes", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 2"}, Conn.Eof{}]))
    IO.print(timeline("redirect-reuse", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /b\r\nContent-Length: 1\r\n\r\n"}, Conn.Got{"x"}, Conn.Sent{}, Conn.Got{ok5()}]))
    IO.print(timeline("redirect-closed", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 301 Moved Permanently\r\nLocation: /b\r\nConnection: close\r\nContent-Length: 0\r\n\r\n"}, Conn.Eof{}, Conn.Opened{}, Conn.Sent{}, Conn.Got{ok5()}]))
    IO.print(timeline("redirect-port", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: http://H:81/p\r\nContent-Length: 0\r\n\r\n"}, Conn.Opened{}]))
    IO.print(timeline("redirect-host", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: http://other/\r\nContent-Length: 0\r\n\r\n"}, Conn.Resolved{"10.0.0.2"}, Conn.Opened{}, Conn.Sent{}, Conn.Late{}]))
    IO.print(timeline("redirect-lookup-failed", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: http://other/\r\nContent-Length: 0\r\n\r\n"}, Conn.ResolveFailed{"No such host"}]))
    IO.print(timeline("redirect-big-body", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /b\r\nContent-Length: 5000\r\n\r\n"}, Conn.Opened{}]))
    IO.print(timeline("redirect-https", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: https://h/\r\nContent-Length: 0\r\n\r\n"}]))
    IO.print(timeline("redirect-late-at-limit", rd(Some{0n}), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 9\r\n\r\n"}, Conn.Late{}]))
    IO.print(timeline("redirect-empty-location", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: \r\nContent-Length: 0\r\n\r\n"}, Conn.Eof{}]))
    IO.print(timeline("redirect-hop-retry", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /b\r\nContent-Length: 0\r\n\r\n"}, Conn.Sent{}, Conn.Eof{}, Conn.Opened{}, Conn.Sent{}, Conn.Eof{}]))
    IO.print(timeline("stray-events", dflt(), get(), False{}, [Conn.Sent{}, Conn.Resolved{"9.9.9.9"}, Conn.Opened{}, Conn.Opened{}, Conn.Sent{}, Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /b\r\nConnection: close\r\n\r\n"}, Conn.Eof{}]))
    IO.print(timeline("after-finish", dflt(), get(), True{}, [Conn.Sent{}, Conn.Got{ok5()}, Conn.Late{}, Conn.Eof{}, Conn.Opened{}]))

#|refused|Get "http://127.0.0.1:1/": dial tcp 127.0.0.1:1: connect: connection refused|
#|eof-fresh|Get "http://h/": EOF|
#|eof-reused-post|Post "http://h/": EOF|
#|eof-reused-post>0|POST / HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nContent-Length: 1\r\nX-Vegeta-Seq: 0\r\n\r\nx
#|eof-reused-get||hello
#|eof-reused-get>0|GET /r HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nX-Vegeta-Seq: 0\r\n\r\n
#|eof-reused-get>1|GET /r HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nX-Vegeta-Seq: 0\r\n\r\n
#|late-head|Get "http://h/": context deadline exceeded (Client.Timeout exceeded while awaiting headers)|
#|late-body|context deadline exceeded (Client.Timeout or context cancellation while reading body)|abc
#|late-interim|Get "http://h/": context deadline exceeded (Client.Timeout exceeded while awaiting headers)|
#|cut-body|unexpected EOF|abc
#|cut-chunked|unexpected EOF|abcd
#|cut-head|Get "http://h/": net/http: HTTP/1.x transport connection broken: unexpected EOF|
#|cut-status|Get "http://h/": net/http: HTTP/1.x transport connection broken: malformed HTTP status code "20"|
#|cut-name|Get "http://h/": net/http: HTTP/1.x transport connection broken: malformed MIME header: missing colon: "Content-Le"|
#|garbage|Get "http://h/": net/http: HTTP/1.x transport connection broken: malformed HTTP response "garbage"|
#|bad-chunk|malformed chunked encoding|abc
#|not-found|404 Not Found|nope
#|max-body||12
#|stop-0|Get "/x": stopped after 0 redirects|
#|stop-1|Post "c?q=1": stopped after 1 redirects|
#|stop-1>0|POST /a HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nContent-Length: 1\r\nX-Vegeta-Seq: 0\r\n\r\nb
#|stop-1>1|GET /b HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nReferer: http://h/a\r\nX-Vegeta-Seq: 0\r\n\r\n
#|nofollow||mv
#|follow-303||hello
#|follow-303>0|POST /a/b HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nContent-Length: 4\r\nAuthorization: t\r\nContent-Type: text/plain\r\nX-Vegeta-Seq: 0\r\n\r\ndata
#|follow-303>1|GET /c HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nAuthorization: t\r\nReferer: http://h/a/b\r\nX-Vegeta-Seq: 0\r\n\r\n
#|follow-307-other||hello
#|follow-307-other>0|PUT / HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nContent-Length: 4\r\nAuthorization: t\r\nContent-Type: text/plain\r\nX-Vegeta-Seq: 0\r\n\r\ndata
#|follow-307-other>1|PUT /z HTTP/1.1\r\nHost: other:8080\r\nUser-Agent: Go-http-client/1.1\r\nContent-Length: 4\r\nContent-Type: text/plain\r\nReferer: http://h/\r\nX-Vegeta-Seq: 0\r\n\r\ndata
#|late-redirect|Get "http://h/x": context deadline exceeded (Client.Timeout exceeded while awaiting headers)|
#|lf-redirect||hello
#|lf-redirect>0|GET / HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nX-Vegeta-Seq: 0\r\n\r\n
#|lf-redirect>1|GET /x HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nReferer: http://h/\r\nX-Vegeta-Seq: 0\r\n\r\n
#|lf-close||abc
#|two-spaces||hello
#|two-spaces>0|GET / HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nX-Vegeta-Seq: 0\r\n\r\n
#|two-spaces>1|GET /x HTTP/1.1\r\nHost: h\r\nUser-Agent: Go-http-client/1.1\r\nReferer: http://h/\r\nX-Vegeta-Seq: 0\r\n\r\n
#|loc-space||mv
#|empty-loc||mv
#|differs from Go: host-other>0|GET / HTTP/1.1\r\nHost: custom\r\nUser-Agent: Go-http-client/1.1\r\nX-Vegeta-Seq: 0\r\n\r\n
#|host-other>1|GET / HTTP/1.1\r\nHost: custom\r\nUser-Agent: Go-http-client/1.1\r\nReferer: http://h/\r\nX-Vegeta-Seq: 0\r\n\r\n
#|fresh: Open 127.0.0.1:80 | Opened: Send GET / HTTP/1.1 | Sent: Recv | Got41: Recv | Got2: Finish ok 200 OK body=hello (kept)
#|reuse: Send GET / HTTP/1.1 | Sent: Recv | Got43: Finish ok 200 OK body=hello (kept)
#|server-close: Send GET / HTTP/1.1 | Sent: Recv | Got59: Finish ok 200 OK body=hi (closed)
#|http10: Send GET / HTTP/1.1 | Sent: Recv | Got40: Finish ok 200 OK body=hi (closed)
#|no-keepalive: Open 127.0.0.1:80 | Opened: Send GET / HTTP/1.1 | Sent: Recv | Got43: Finish ok 200 OK body=hello (closed)
#|no-keepalive sends close: True
#|extra-bytes: Send GET / HTTP/1.1 | Sent: Recv | Got48: Finish ok 200 OK body=hello (closed)
#|until-close: Send GET / HTTP/1.1 | Sent: Recv | Got21: Recv | Got1: Recv | Eof: Finish ok 200 OK body=abc (closed)
#|head: Send HEAD / HTTP/1.1 | Sent: Recv | Got39: Finish ok 200 OK body= (kept)
#|interim: Send GET / HTTP/1.1 | Sent: Recv | Got52: Finish ok 204 No Content body= (kept)
#|early-answer: Send GET / HTTP/1.1 | Got43: Finish ok 200 OK body=hello (kept) | Sent: -
#|chunked-by-1: 101 Recv, Finish ok 200 OK body=hello world (kept)
#|chunked-by-3: 34 Recv, Finish ok 200 OK body=hello world (kept)
#|length-by-7: 20 Recv, Finish ok 200 OK body=0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789 (kept)
#|max-body-by-5: 28 Recv, Finish ok 200 OK body=012 (kept)
#|max-body-0: 26 Recv, Finish ok 200 OK body= (kept)
#|mib-length: 1025 Recv, 200 OK 1048576 (kept)
#|mib-close: 1026 Recv, 200 OK 1048576 (closed)
#|mib-max-body: 1025 Recv, 200 OK 100 (kept)
#|mib-redirect: 3 Recv, Open 127.0.0.1:80
#|late-before-send: Open 127.0.0.1:80 | Late: Finish fail Get "http://h/": context deadline exceeded (Client.Timeout exceeded while awaiting headers) (closed)
#|send-failed: Open 127.0.0.1:80 | Opened: Send GET / HTTP/1.1 | SendFailed: Finish fail Get "http://h/": write tcp 127.0.0.1:80: write: broken pipe (closed)
#|send-failed-retry: Send GET / HTTP/1.1 | SendFailed: Open 127.0.0.1:80 | Opened: Send GET / HTTP/1.1 | Sent: Recv | Got43: Finish ok 200 OK body=hello (kept)
#|retry-once: Send GET / HTTP/1.1 | Sent: Recv | Eof: Open 127.0.0.1:80 | Opened: Send GET / HTTP/1.1 | Sent: Recv | Eof: Finish fail Get "http://h/": EOF (closed)
#|retry-refused: Send GET / HTTP/1.1 | Sent: Recv | Eof: Open 127.0.0.1:80 | OpenFailed: Finish fail Get "http://h/": dial tcp 127.0.0.1:80: connect: connection refused (closed)
#|retry-idempotent: Send POST / HTTP/1.1 | Sent: Recv | Eof: Open 127.0.0.1:80
#|no-retry-fresh: Open 127.0.0.1:80 | Opened: Send GET / HTTP/1.1 | Sent: Recv | Eof: Finish fail Get "http://h/": EOF (closed)
#|no-retry-after-bytes: Send GET / HTTP/1.1 | Sent: Recv | Got10: Recv | Eof: Finish fail Get "http://h/": net/http: HTTP/1.x transport connection broken: malformed HTTP status code "2" (closed)
#|redirect-reuse: Send GET / HTTP/1.1 | Sent: Recv | Got55: Recv | Got1: Send GET /b HTTP/1.1 | Sent: Recv | Got43: Finish ok 200 OK body=hello (kept)
#|redirect-closed: Send GET / HTTP/1.1 | Sent: Recv | Got86: Shut, Open 127.0.0.1:80 | Eof: - | Opened: Send GET /b HTTP/1.1 | Sent: Recv | Got43: Finish ok 200 OK body=hello (kept)
#|redirect-port: Send GET / HTTP/1.1 | Sent: Recv | Got66: Shut, Open 127.0.0.1:81 | Opened: Send GET /p HTTP/1.1
#|redirect-host: Send GET / HTTP/1.1 | Sent: Recv | Got66: Shut, Resolve other | Resolved 10.0.0.2: Open 10.0.0.2:80 | Opened: Send GET / HTTP/1.1 | Sent: Recv | Late: Finish fail Get "http://other/": context deadline exceeded (Client.Timeout exceeded while awaiting headers) (closed)
#|redirect-lookup-failed: Send GET / HTTP/1.1 | Sent: Recv | Got66: Shut, Resolve other | ResolveFailed: Finish fail Get "http://other/": dial tcp: lookup other: no such host (closed)
#|redirect-big-body: Send GET / HTTP/1.1 | Sent: Recv | Got58: Shut, Open 127.0.0.1:80 | Opened: Send GET /b HTTP/1.1
#|redirect-https: Send GET / HTTP/1.1 | Sent: Recv | Got63: Finish fail Get "https://h/": https is not supported (closed)
#|redirect-late-at-limit: Send GET / HTTP/1.1 | Sent: Recv | Got55: Recv | Late: Finish fail Get "/x": stopped after 0 redirects (closed)
#|redirect-empty-location: Send GET / HTTP/1.1 | Sent: Recv | Got53: Finish ok 302 Found body= (kept) | Eof: -
#|redirect-hop-retry: Send GET / HTTP/1.1 | Sent: Recv | Got55: Send GET /b HTTP/1.1 | Sent: Recv | Eof: Open 127.0.0.1:80 | Opened: Send GET /b HTTP/1.1 | Sent: Recv | Eof: Finish fail Get "http://h/b": EOF (closed)
#|stray-events: Open 127.0.0.1:80 | Sent: - | Resolved 9.9.9.9: - | Opened: Send GET / HTTP/1.1 | Opened: - | Sent: Recv | Got55: Recv | Eof: Shut, Open 9.9.9.9:80
#|after-finish: Send GET / HTTP/1.1 | Sent: Recv | Got43: Finish ok 200 OK body=hello (kept) | Late: - | Eof: - | Opened: -

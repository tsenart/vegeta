# The HTTP client of one worker, as a pure machine: the shell runs its
# commands and feeds back what happened. One machine per request; the
# connection may be carried over from the previous request.
#
# The contract with the shell (shell.bend):
# - Resolve, Open, Send and Recv each get exactly one event back: Resolve
#   gets Resolved or ResolveFailed, Open gets Opened or OpenFailed, Send
#   gets Sent or SendFailed, Recv gets Got, Eof or Late. Shut and Finish
#   get none.
# - Every batch this machine emits holds at most one command that is
#   answered, and it comes last; only Shut ever comes before it. Finish
#   is always alone. After Finish, the machine takes events in and
#   answers nothing.
# - The shell owns the deadline (the request's start plus CCfg.timeout ns,
#   0 for none) and delivers Late in place of a Got or Eof.
# - start(c, r, True): the worker's socket from its last request (whose
#   Finish said open) is still open, and the request goes out on it.
#   Finish{out, open}: whether the socket may carry the next request.
# - Req.ip is the target's address, resolved once by the attack. Resolve
#   is only for a redirect to another host; Shut then Open or Resolve is
#   a move to another connection (the shell closes a socket before an
#   Open anyway).
#
# Go's client (net/http Client.do and Transport, as lib/attack.go sets
# them up), step by step:
# - the request goes out on the carried connection or on a new one to
#   Req.ip at the URL's port;
# - the bytes since the request went out are parsed by Http (the parse
#   is kept incrementally); a complete final response is the answer, kept
#   when both sides keep the connection and nothing extra arrived;
# - a request Go may replay (isReplayable) that was lost on a reused
#   connection before any byte of an answer is sent once more on a new
#   connection (the reconnect happens at once);
# - under -redirects=n (Some{n}) a 301/302/303/307/308 with a Location is
#   followed once Go is done with its body (it is complete, 2048 bytes of
#   it are read, or its Content-Length is over 2048), with Go's method,
#   body and header rules; the n+1-th is Go's "stopped after n redirects";
#   None (-redirects=-1) answers with the redirect itself. A hop to another
#   host is looked up; one to the same host reuses the connection only
#   when it is kept and the port is the same;
# - failures carry Go's texts: timeouts, dials, closes, malformed
#   responses; a failure in the body keeps the body read so far.
#
# The machine mirrors what LAWS.bend's client checkers track: the
# connection's open flag, the bytes since the last Send, the close, the
# redirect acted on (met), the lookup's address, and the sends and bytes
# that decide a retry. Events arriving in any order are taken as the laws
# take them: bytes and closes always count; an answer to a command that is
# not outstanding is ignored.
#
# The bytes since the last Send are kept last byte first only until the
# final head has arrived for good (its blank line is in and its status
# code is read); from then on the head's facts (redirect, code, Location,
# a large Content-Length) cannot change, so they are kept instead and the
# bytes are dropped: the parse holds the body.
import Base
import ./http.bend as Http
import ./target.bend as Tgt
import ./civil.bend as Civil
import ./hit.bend as Hit
import ./hdr.bend as Hdr
import ./dec.bend as Dec

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
  Failed{msg: String, partial: Maybe<&2, String>}

type Cmd is Data:
  Resolve{host: String}
  Open{ip: String, port: Nat}
  Send{data: String}
  Recv{}
  Shut{}
  Finish{out: Out, open: Bool}

# the command whose answer the machine waits for
type Phase is Data:
  PResolve{}
  POpen{}
  PSend{}
  PRecv{}

# the final head: not in for good yet (its facts are read off the bytes),
# or in, with what matters of it: a redirect the client follows, its code
# and Location, and a Content-Length over 2048
type Head is Data:
  HOut{}
  HIn{redir: Bool, code: Nat, loc: String, big: Bool}

# the request in flight (the original, then each redirect hop): its text,
# the times it went out, whether a nonempty byte came back since it first
# went out (for the original: since the start), whether it went out on a
# reused connection, and the hops before it
type Cur is Data:
  Cur{req: Req, text: String, tries: Nat, got: Bool, reused: Bool, hops: Nat}

# since the last Send: the bytes (last first, while the head is out), the
# head, the parse (under -max-body), the parse without -max-body (kept
# only for a redirect: Go drains its body), and whether the redirect was
# acted on
type Rx is Data:
  Rx{buf: String, hd: Head, p: Http.Parse, p0: Http.Parse, met: Bool}

# req: the original request; open: the connection is open (as far as the
# events said); over: finished; cur: the request in flight; rx: what came
# back; ph: the command awaited; pend, ptext, hop: the request to send
# once a connection is open (a retry, or a redirect hop); ip: the last
# address a lookup gave (at first the request's); port: where to connect
# after the lookup
type State is Data:
  CState{req: Req, open: Bool, over: Bool, cur: Cur, rx: Rx, ph: Phase, pend: Req, ptext: String, hop: Bool, ip: String, port: Nat}

# ---------------------------------------------------------------------
# Bytes and small helpers
# ---------------------------------------------------------------------

# a strict choice: both branches are evaluated (keep loops out of them)
def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def digit(c: Char) -> Nat:
  U32.to_nat((code(c) - 48 : U32))

def digits_value.go(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      digits_value.go(rest, Nat.add(Nat.mul(acc, 10n), digit(c)))

def digits_value(s: String) -> Nat:
  digits_value.go(s, 0n)

def is_digit(c: Char) -> Bool:
  +k = code(c)
  Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57))

def all_digits.go(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(is_digit(c), all_digits.go(rest))

def all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.and(is_digit(c), all_digits.go(rest))

def join_str(+sep: String, xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      match rest:
        case Nil{}:
          x
        case Con{+y, +more}:
          x ++ sep ++ join_str(sep, Con{y, more})

# a blank line starts at the "\n" here: the end of a head (textproto's
# lines end in "\n", a "\r" before it dropped)
def blank.of(nl: Bool, +rest: String) -> Bool:
  match nl:
    case True{}:
      Bool.or(String.starts_with(rest, "\n"), String.starts_with(rest, "\r\n"))
    case False{}:
      False{}

def blank_at(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      blank.of(U32.is_eq(code(c), 10), rest)

def is_30x(+k: Nat) -> Bool:
  Bool.or(Bool.or(Nat.is_eq(k, 301n), Nat.is_eq(k, 302n)), Bool.or(Bool.or(Nat.is_eq(k, 303n), Nat.is_eq(k, 307n)), Nat.is_eq(k, 308n)))

# ---------------------------------------------------------------------
# Accessors
# ---------------------------------------------------------------------

def c_ka(+c: Cfg) -> Bool:
  CCfg{ka, to, mb, rd} = c
  ka

def c_mb(+c: Cfg) -> Maybe<&2, Nat>:
  CCfg{ka, to, mb, rd} = c
  mb

def c_rd(+c: Cfg) -> Maybe<&2, Nat>:
  CCfg{ka, to, mb, rd} = c
  rd

def rd_limit(+m: Maybe<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, m, 0n)

def q_target(+r: Req) -> Tgt.Target:
  Req{t, u, ip, b, s, n} = r
  t

def q_url(+r: Req) -> Tgt.Url:
  Req{t, u, ip, b, s, n} = r
  u

def q_ip(+r: Req) -> String:
  Req{t, u, ip, b, s, n} = r
  ip

def q_body(+r: Req) -> String:
  Req{t, u, ip, b, s, n} = r
  b

def q_seq(+r: Req) -> Nat:
  Req{t, u, ip, b, s, n} = r
  s

def q_name(+r: Req) -> String:
  Req{t, u, ip, b, s, n} = r
  n

def mk_req(+t: Tgt.Target, +u: Tgt.Url, +ip: String, +b: String, +s: Nat, +n: String) -> Req:
  Req{t, u, ip, b, s, n}

def with_ip(+r: Req, +ip: String) -> Req:
  Req{t, u, i, b, s, n} = r
  Req{t, u, ip, b, s, n}

def u_host(+u: Tgt.Url) -> String:
  Tgt.Url{sc, h, p, pa} = u
  h

def u_portm(+u: Tgt.Url) -> Maybe<&2, Nat>:
  Tgt.Url{sc, h, p, pa} = u
  p

def u_port(+u: Tgt.Url) -> Nat:
  Maybe.default(&2, Nat, u_portm(u), 80n)

def tgt_url(+t: Tgt.Target) -> String:
  Tgt.Target{m, u, hs, b} = t
  u

def tgt_method(+t: Tgt.Target) -> String:
  Tgt.Target{m, u, hs, b} = t
  m

def tgt_hdrs(+t: Tgt.Target) -> List<&2, Hdr.Header>:
  Tgt.Target{m, u, hs, b} = t
  hs

def tgt_body(+t: Tgt.Target) -> Maybe<&2, String>:
  Tgt.Target{m, u, hs, b} = t
  b

def hdr_key(+h: Hdr.Header) -> String:
  Hdr.Header{k, vs} = h
  k

def hdr_vals(+h: Hdr.Header) -> List<&2, String>:
  Hdr.Header{k, vs} = h
  vs

def r_code(+r: Http.Resp) -> Nat:
  Http.Resp{c, st, hs, b, k} = r
  c

def r_status(+r: Http.Resp) -> String:
  Http.Resp{c, st, hs, b, k} = r
  st

def r_hdrs(+r: Http.Resp) -> List<&2, Hdr.Header>:
  Http.Resp{c, st, hs, b, k} = r
  hs

def r_body(+r: Http.Resp) -> String:
  Http.Resp{c, st, hs, b, k} = r
  b

def r_keep(+r: Http.Resp) -> Bool:
  Http.Resp{c, st, hs, b, k} = r
  k

def p_head(+p: Http.Parse) -> Bool:
  Http.Parse{mb, head, closed, ph} = p
  head

def p_closed(+p: Http.Parse) -> Bool:
  Http.Parse{mb, head, closed, ph} = p
  closed

def cur_req(+k: Cur) -> Req:
  Cur{r, t, n, g, u, h} = k
  r

def cur_text(+k: Cur) -> String:
  Cur{r, t, n, g, u, h} = k
  t

def cur_tries(+k: Cur) -> Nat:
  Cur{r, t, n, g, u, h} = k
  n

def cur_got(+k: Cur) -> Bool:
  Cur{r, t, n, g, u, h} = k
  g

def cur_reused(+k: Cur) -> Bool:
  Cur{r, t, n, g, u, h} = k
  u

def cur_hops(+k: Cur) -> Nat:
  Cur{r, t, n, g, u, h} = k
  h

def rx_buf(+x: Rx) -> String:
  Rx{b, hd, p, p0, met} = x
  b

def rx_hd(+x: Rx) -> Head:
  Rx{b, hd, p, p0, met} = x
  hd

def rx_p(+x: Rx) -> Http.Parse:
  Rx{b, hd, p, p0, met} = x
  p

def rx_p0(+x: Rx) -> Http.Parse:
  Rx{b, hd, p, p0, met} = x
  p0

def rx_met(+x: Rx) -> Bool:
  Rx{b, hd, p, p0, met} = x
  met

def hd_code(+h: Head) -> Nat:
  match h:
    case HOut{}:
      0n
    case HIn{r, k, l, g}:
      k

def hd_loc(+h: Head) -> String:
  match h:
    case HOut{}:
      ""
    case HIn{r, k, l, g}:
      l

def hd_redir(+h: Head) -> Bool:
  match h:
    case HOut{}:
      False{}
    case HIn{r, k, l, g}:
      r

def hd_big(+h: Head) -> Bool:
  match h:
    case HOut{}:
      False{}
    case HIn{r, k, l, g}:
      g

def st_req(+s: State) -> Req:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  q

def st_open(+s: State) -> Bool:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  o

def st_over(+s: State) -> Bool:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  v

def st_cur(+s: State) -> Cur:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  k

def st_rx(+s: State) -> Rx:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  x

def st_ph(+s: State) -> Phase:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  ph

def st_pend(+s: State) -> Req:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  pd

def st_ptext(+s: State) -> String:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  pt

def st_hop(+s: State) -> Bool:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  hp

def st_ip(+s: State) -> String:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  ip

def st_port(+s: State) -> Nat:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  pr

def set_open(+s: State, +o: Bool) -> State:
  CState{q, o0, v, k, x, ph, pd, pt, hp, ip, pr} = s
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}

def set_over(+s: State) -> State:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr} = s
  CState{q, o, True{}, k, x, ph, pd, pt, hp, ip, pr}

def set_cur(+s: State, +k: Cur) -> State:
  CState{q, o, v, k0, x, ph, pd, pt, hp, ip, pr} = s
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}

def set_rx(+s: State, +x: Rx) -> State:
  CState{q, o, v, k, x0, ph, pd, pt, hp, ip, pr} = s
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}

def set_ph(+s: State, +ph: Phase) -> State:
  CState{q, o, v, k, x, ph0, pd, pt, hp, ip, pr} = s
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}

def set_ip(+s: State, +ip: String) -> State:
  CState{q, o, v, k, x, ph, pd, pt, hp, ip0, pr} = s
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}

# a connection is awaited (ph), then pend goes out as ptext (a hop or not)
def set_pend(+s: State, +ph: Phase, +pd: Req, +pt: String, +hp: Bool, +pr: Nat) -> State:
  CState{q, o, v, k, x, ph0, pd0, pt0, hp0, ip, pr0} = s
  CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}

def set_met(+x: Rx) -> Rx:
  Rx{b, hd, p, p0, met} = x
  Rx{b, hd, p, p0, True{}}

def set_got(+k: Cur, +d: String) -> Cur:
  Cur{r, t, n, g, u, h} = k
  Cur{r, t, n, Bool.or(g, Bool.not(String.is_empty(d))), u, h}

# ---------------------------------------------------------------------
# Parses
# ---------------------------------------------------------------------

def is_head(+text: String) -> Bool:
  String.starts_with(text, "HEAD ")

# the values of the first header named k (canonically), as a loop that
# stops at the hit (hit: the header before hs matched, with values v)
def hdr_get_ci.go(hs: List<&2, Hdr.Header>, hit: Bool, +k: String, +v: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match hs:
    case Nil{}:
      match hit:
        case True{}:
          Some{v}
        case False{}:
          None{}
    case Con{+h, +rest}:
      match hit:
        case True{}:
          Some{v}
        case False{}:
          hdr_get_ci.go(rest, String.eq(Http.canon(hdr_key(h)), k), k, hdr_vals(h))

def hdr_get_ci(+k: String, hs: List<&2, Hdr.Header>) -> Maybe<&2, List<&2, String>>:
  hdr_get_ci.go(hs, False{}, k, [])

# a redirect status with a Location (its name compared canonically, as
# LAWS.bend reads it; the parser's names are canonical anyway)
def is_redirect(+r: Http.Resp) -> Bool:
  Bool.and(is_30x(r_code(r)), Bool.not(String.is_empty(Http.first_of("", hdr_get_ci("Location", r_hdrs(r))))))

# a complete response the client answers with: not a redirect it follows
def final_of(+c: Cfg, m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          False{}
        case Done{pr}:
          (r0, lo) = pr
          +r = r0
          Bool.not(Bool.and(Maybe.is_some(&2, Nat, c_rd(c)), is_redirect(r)))

def is_done(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          False{}
        case Done{pr}:
          True{}

def is_fail(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          True{}
        case Done{pr}:
          False{}

def fail_msg(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> String:
  match m:
    case None{}:
      "unexpected EOF"
    case Some{res}:
      match res:
        case Fail{e}:
          e
        case Done{pr}:
          "unexpected EOF"

# the connection stays usable after a complete response: both sides
# keep it and nothing extra arrived
def kept_of(+ka: Bool, m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          False{}
        case Done{pr}:
          (r0, lo0) = pr
          +r = r0
          +lo = lo0
          Bool.and(Bool.and(r_keep(r), ka), String.is_empty(lo))

def ph_failed(ph: Http.Ph) -> Bool:
  match ph:
    case Http.HFail{m}:
      True{}
    case _:
      False{}

def p_failed(+p: Http.Parse) -> Bool:
  Http.Parse{mb, head, closed, ph} = p
  ph_failed(ph)

# the parse is in a body
def ph_body(ph: Http.Ph) -> Bool:
  match ph:
    case Http.HLen{r, left, body, kept}:
      True{}
    case Http.HChSize{r, line, body, kept}:
      True{}
    case Http.HChData{r, left, body, kept}:
      True{}
    case Http.HChCR{r, body, kept}:
      True{}
    case Http.HChLF{r, body, kept}:
      True{}
    case Http.HTrail{r, line, body}:
      True{}
    case Http.HClose{r, body, kept}:
      True{}
    case _:
      False{}

def p_body(+p: Http.Parse) -> Bool:
  Http.Parse{mb, head, closed, ph} = p
  ph_body(ph)

# the parse fed s up to the byte that fails it (the last good parse)
def upto(s: String, bad: Bool, +good: Http.Parse, +p: Http.Parse) -> Http.Parse:
  match s:
    case SNil{}:
      match bad:
        case True{}:
          good
        case False{}:
          p
    case SCon{+c, +rest}:
      match bad:
        case True{}:
          good
        case False{}:
          +q = Http.step(p, c)
          upto(rest, p_failed(q), p, q)

# ---------------------------------------------------------------------
# The final head, read off the bytes as LAWS.bend reads it
# ---------------------------------------------------------------------

# from the head's blank line on ("" when it has not arrived)
def after_head.go(fuel: Nat, found: Bool, +s: String) -> String:
  match fuel:
    case 0n:
      match found:
        case True{}:
          s
        case False{}:
          ""
    case 1n+f:
      match found:
        case True{}:
          s
        case False{}:
          +t = String.drop(s, 1n)
          after_head.go(f, blank_at(t), t)

def after_head(+s: String) -> String:
  after_head.go(String.length(s), blank_at(s), s)

# the head's blank line has arrived
def has_head(+s: String) -> Bool:
  Bool.not(String.is_empty(after_head(s)))

# the bytes after the head's blank line
def after_blank(+s: String) -> String:
  String.drop(after_head(s), pick(Nat, String.starts_with(after_head(s), "\n\n"), 2n, 3n))

# the status code as ReadResponse reads it: after "HTTP/1.x " and any
# more spaces
def code_at(+s: String) -> Nat:
  digits_value(String.take(Http.trim_sp_l(String.drop(s, 9n)), 3n))

def interim(+k: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_ge(k, 100n), Nat.is_le(k, 199n)), Bool.not(Nat.is_eq(k, 101n)))

def skip_head(+s: String) -> Bool:
  Bool.and(interim(code_at(s)), has_head(s))

# the bytes from the final head on: interim heads that fully arrived skipped
def final_from.go(fuel: Nat, skip: Bool, +s: String) -> String:
  match fuel:
    case 0n:
      s
    case 1n+f:
      match skip:
        case True{}:
          +t = after_blank(s)
          final_from.go(f, skip_head(t), t)
        case False{}:
          s

def final_from(+buf: String) -> String:
  final_from.go(String.length(buf), skip_head(buf), buf)

def first_head(+s: String) -> String:
  String.take(s, Nat.sub(String.length(s), String.length(after_head(s))))

def strip_cr(+l: String) -> String:
  pick(String, String.ends_with(l, "\r"), String.take(l, Nat.sub(String.length(l), 1n)), l)

def line_key(+l: String) -> String:
  Maybe.default(&2, String, List.head(&2, String, Http.split_on(58, strip_cr(l))), "")

def line_val(+l: String) -> String:
  Http.trim_ows(String.drop(strip_cr(l), 1n+String.length(line_key(l))))

def line_is(+k: String, +l: String) -> Bool:
  String.eq(Http.canon(line_key(l)), k)

# the value of the first line with key k (d when none): a loop that stops
# at the hit (hit: the line before rest had key k, and v is its value)
def first_line.go(ls: List<&2, String>, hit: Bool, +k: String, +v: String, +d: String) -> String:
  match ls:
    case Nil{}:
      match hit:
        case True{}:
          v
        case False{}:
          d
    case Con{+l, +rest}:
      match hit:
        case True{}:
          v
        case False{}:
          first_line.go(rest, line_is(k, l), k, line_val(l), d)

def head_loc_of(ls: List<&2, String>) -> String:
  first_line.go(ls, False{}, "Location", "", "")

# (a match, not a pick: the value of a long non-digit run passes 2^48)
def digits_of.of(ok: Bool, +v: String) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{digits_value(v)}
    case False{}:
      None{}

def digits_of(+v: String) -> Maybe<&2, Nat>:
  digits_of.of(all_digits(v), v)

# the first Content-Length line's value, if it is all digits: a loop that
# stops at the hit
def head_cl.go(ls: List<&2, String>, hit: Bool, +v: String) -> Maybe<&2, Nat>:
  match ls:
    case Nil{}:
      match hit:
        case True{}:
          digits_of(v)
        case False{}:
          None{}
    case Con{+l, +rest}:
      match hit:
        case True{}:
          digits_of(v)
        case False{}:
          head_cl.go(rest, line_is("Content-Length", l), line_val(l))

def head_cl(ls: List<&2, String>) -> Maybe<&2, Nat>:
  head_cl.go(ls, False{}, "")

def big_body(+m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      Nat.is_gt(n, 2048n)

# the head facts of a redirect the client may follow (its lines read)
def head_of.of(may: Bool, +k: Nat, +ff: String, +ah: String) -> Head:
  match may:
    case True{}:
      +lines = List.drop(&2, String, Http.split_on(10, String.take(ff, Nat.sub(String.length(ff), String.length(ah)))), 1n)
      +loc = head_loc_of(lines)
      HIn{Bool.not(String.is_empty(loc)), k, loc, big_body(head_cl(lines))}
    case False{}:
      HIn{False{}, k, "", False{}}

# the head facts of the final head ff (from final_from), its blank line
# in; its lines are read only for a code the client would follow
def head_of(+c: Cfg, +ff: String, +ah: String) -> Head:
  +k = code_at(ff)
  head_of.of(Bool.and(Maybe.is_some(&2, Nat, c_rd(c)), is_30x(k)), k, ff, ah)

def head_bytes.of(in: Bool, +c: Cfg, +ff: String, +ah: String) -> Head:
  match in:
    case True{}:
      head_of(c, ff, ah)
    case False{}:
      HOut{}

# the final head's facts read off the bytes (HOut while its blank line
# is not in)
def head_bytes(+c: Cfg, +buf: String) -> Head:
  +ff = final_from(buf)
  +ah = after_head(ff)
  head_bytes.of(Bool.not(String.is_empty(ah)), c, ff, ah)

# ---------------------------------------------------------------------
# Taking bytes in
# ---------------------------------------------------------------------

def feed_redir(r: Bool, +p0: Http.Parse, +d: String) -> Http.Parse:
  match r:
    case True{}:
      Http.feed(p0, d)
    case False{}:
      p0

# where the walk over the heads ends: the final head (from its first
# byte), whether it and every head skipped before it are in for good, and
# the bytes from its blank line on
type Walk is Data:
  Walk{ok: Bool, ff: String, ah: String}

def walk_ok(+w: Walk) -> Bool:
  Walk{ok, ff, ah} = w
  ok

def walk_ff(+w: Walk) -> String:
  Walk{ok, ff, ah} = w
  ff

# a head is in for good once its blank line is in, it has 9 bytes or
# more before it, and the 3 bytes its status code is read from are in:
# its status code is then read inside it (or runs into its blank line,
# and then it is no code the client acts on), and it reads the same
# however many bytes follow
def fixed(+s: String, +ah: String) -> Bool:
  Bool.and(Bool.and(Bool.not(String.is_empty(ah)), Nat.is_ge(Nat.sub(String.length(s), String.length(ah)), 9n)),
    Nat.is_eq(String.length(String.take(Http.trim_sp_l(String.drop(s, 9n)), 3n)), 3n))

def skip_of(+s: String, +ah: String) -> Bool:
  Bool.and(interim(code_at(s)), Bool.not(String.is_empty(ah)))

def blank_rest(+ah: String) -> String:
  String.drop(ah, pick(Nat, String.starts_with(ah, "\n\n"), 2n, 3n))

# final_from fused with the check that every head it walks is in for
# good: one search for the blank line per head (ah: from s's blank line)
def walk.go(fuel: Nat, skip: Bool, +ok: Bool, +s: String, +ah: String) -> Walk:
  match fuel:
    case 0n:
      Walk{Bool.and(ok, fixed(s, ah)), s, ah}
    case 1n+f:
      match skip:
        case True{}:
          +t = blank_rest(ah)
          +aht = after_head(t)
          walk.go(f, skip_of(t, aht), Bool.and(ok, fixed(s, ah)), t, aht)
        case False{}:
          Walk{Bool.and(ok, fixed(s, ah)), s, ah}

def walk.of(+buf: String, +ah: String) -> Walk:
  walk.go(String.length(buf), skip_of(buf, ah), True{}, buf, ah)

def walk(+buf: String) -> Walk:
  walk.of(buf, after_head(buf))

def walk_ah(+w: Walk) -> String:
  Walk{ok, ff, ah} = w
  ah

def rx_settle.of(st: Bool, +c: Cfg, +w: Walk, +buf: String, +rbuf: String, +p: Http.Parse, +p0: Http.Parse, +met: Bool) -> Rx:
  match st:
    case True{}:
      +h = head_of(c, walk_ff(w), walk_ah(w))
      Rx{"", h, p, feed_redir(hd_redir(h), Http.start(None{}, p_head(p)), buf), met}
    case False{}:
      Rx{rbuf, HOut{}, p, p0, met}

def rx_settle(+c: Cfg, +rbuf: String, +p: Http.Parse, +p0: Http.Parse, +met: Bool) -> Rx:
  +buf = String.reverse(rbuf)
  +w = walk(buf)
  rx_settle.of(walk_ok(w), c, w, buf, rbuf, p, p0, met)

# the bytes d taken in, the parse p2 already fed them
def rx_feed.hd(h: Head, +c: Cfg, +b: String, +p2: Http.Parse, +p0: Http.Parse, +met: Bool, +d: String) -> Rx:
  match h:
    case HOut{}:
      rx_settle(c, String.reverse(d) ++ b, p2, p0, met)
    case HIn{+r, k, l, g}:
      Rx{b, HIn{r, k, l, g}, p2, feed_redir(Bool.and(r, Bool.not(met)), p0, d), met}

# (the parse and met are set here, outside the head's match: every branch
# keeps them)
def rx_feed(+c: Cfg, +x: Rx, +p2: Http.Parse, +d: String) -> Rx:
  Rx{b, hd, p, p0, met} = x
  +t = rx_feed.hd(hd, c, b, p2, p0, met, d)
  Rx{rx_buf(t), rx_hd(t), p2, rx_p0(t), met}

def rx_eof(+x: Rx) -> Rx:
  Rx{b, hd, p, p0, met} = x
  Rx{b, hd, Http.eof(p), p0, met}

def rx_fresh(+c: Cfg, +text: String) -> Rx:
  Rx{"", HOut{}, Http.start(c_mb(c), is_head(text)), Http.start(None{}, False{}), False{}}

# what the bytes say, head in or out: the final head's blank line is in
def in_of(h: Head, +rbuf: String) -> Bool:
  match h:
    case HOut{}:
      has_head(final_from(String.reverse(rbuf)))
    case HIn{r, k, l, g}:
      True{}

# Go is done with a redirect's body
def drained(+x: Rx) -> Bool:
  Bool.or(Bool.or(hd_big(rx_hd(x)), p_closed(rx_p(x))),
    Bool.or(is_done(Http.done(rx_p0(x))), Nat.is_ge(String.length(Http.partial(rx_p0(x))), 2048n)))

def due.of(go: Bool, +x: Rx) -> Bool:
  match go:
    case True{}:
      drained(x)
    case False{}:
      False{}

# a redirect not acted on yet, and Go is done with its body
def due(+x: Rx) -> Bool:
  due.of(Bool.and(Bool.not(rx_met(x)), hd_redir(rx_hd(x))), x)

# ---------------------------------------------------------------------
# Go's texts
# ---------------------------------------------------------------------

# Go's url.Error op: "Get", "Post" (of the first request's method)
def op(+m: String) -> String:
  String.take(m, 1n) ++ String.to_lower(String.drop(m, 1n))

def named(+q: Req, +url: String) -> String:
  op(tgt_method(q_target(q))) ++ " \"" ++ url ++ "\": "

# the error prefix of the request in flight
def prefix(+s: State) -> String:
  named(st_req(s), tgt_url(q_target(cur_req(st_cur(s)))))

def broken(+s: State) -> String:
  prefix(s) ++ "net/http: HTTP/1.x transport connection broken: "

def awaiting() -> String:
  "context deadline exceeded (Client.Timeout exceeded while awaiting headers)"

def reading() -> String:
  "context deadline exceeded (Client.Timeout or context cancellation while reading body)"

def dial_text(+s: State, +m: String) -> String:
  +r = cur_req(st_cur(s))
  prefix(s) ++ "dial tcp " ++ q_ip(r) ++ ":" ++ Dec.show(u_port(q_url(r))) ++ ": connect: " ++ String.to_lower(m)

def write_text(+s: State, +m: String) -> String:
  +r = cur_req(st_cur(s))
  prefix(s) ++ "write tcp " ++ q_ip(r) ++ ":" ++ Dec.show(u_port(q_url(r))) ++ ": write: " ++ String.to_lower(m)

def lookup_text(+s: State, +m: String) -> String:
  named(st_req(s), tgt_url(q_target(st_pend(s)))) ++ "dial tcp: lookup " ++ u_host(q_url(st_pend(s))) ++ ": " ++ String.to_lower(m)

def stop_text(+q: Req, +loc: String, +n: Nat) -> String:
  op(tgt_method(q_target(q))) ++ " \"" ++ loc ++ "\": stopped after " ++ Dec.show(n) ++ " redirects"

# ---------------------------------------------------------------------
# Redirects (Go's Client.do, as LAWS.bend's hop_of_head)
# ---------------------------------------------------------------------

def last_slash(s: String, +acc: String, +cut: String) -> String:
  match s:
    case SNil{}:
      cut
    case SCon{+c, +rest}:
      +acc2 = acc ++ SCon{c, SNil{}}
      last_slash(rest, acc2, pick(String, U32.is_eq(code(c), 47), acc2, cut))

def dir_of(+p: String) -> String:
  last_slash(p, "", "/")

def rev_drop1(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      rest

# RFC 3986's remove_dot_segments over the segments of an absolute path,
# collected in reverse
def dots(segs: List<&2, String>, +out: List<&2, String>) -> List<&2, String>:
  match segs:
    case Nil{}:
      out
    case Con{+g, +rest}:
      +last = List.is_empty(&2, String, rest)
      +dot = String.eq(g, ".")
      +up = String.eq(g, "..")
      +out2 = pick(List<&2, String>, dot, out, pick(List<&2, String>, up, rev_drop1(out), Con{g, out}))
      dots(rest, pick(List<&2, String>, Bool.and(last, Bool.or(dot, up)), Con{"", out2}, out2))

def remove_dots(+p: String) -> String:
  "/" ++ join_str("/", List.reverse(&2, String, dots(List.drop(&2, String, Http.split_on(47, p), 1n), [])))

# a Location resolved against the request's URL, as Go's URL.ResolveReference
def loc_url(+u: Tgt.Url, +loc: String) -> String:
  +base = "http://" ++ u_host(u) ++ Http.port_text(u_portm(u))
  +bpath = Http.before_q(Http.url_path(u))
  +lpath = Http.before_q(loc)
  +lq = String.drop(loc, String.length(lpath))
  pick(String, Bool.or(String.starts_with(String.to_lower(loc), "http://"), String.starts_with(String.to_lower(loc), "https://")), loc,
  pick(String, String.starts_with(loc, "//"), "http:" ++ loc,
  pick(String, String.starts_with(loc, "/"), base ++ remove_dots(lpath) ++ lq,
  pick(String, String.is_empty(lpath), base ++ bpath ++ pick(String, String.is_empty(lq), String.drop(Http.url_path(u), String.length(bpath)), lq),
    base ++ remove_dots(dir_of(bpath) ++ lpath) ++ lq))))

def has_key_ci(+k: String, hs: List<&2, Hdr.Header>) -> Bool:
  Maybe.is_some(&2, List<&2, String>, hdr_get_ci(k, hs))

def drop_ci(+k: String, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      +r = drop_ci(k, rest)
      pick(List<&2, Hdr.Header>, String.eq(Http.canon(hdr_key(h)), k), r, Con{h, r})

def drop_all_ci(ks: List<&2, String>, +hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match ks:
    case Nil{}:
      hs
    case Con{+k, +rest}:
      drop_all_ci(rest, drop_ci(k, hs))

def sensitive() -> List<&2, String>:
  ["Authorization", "Www-Authenticate", "Cookie", "Cookie2", "Proxy-Authorization", "Proxy-Authenticate"]

def body_hdrs() -> List<&2, String>:
  ["Content-Type", "Content-Encoding", "Content-Language", "Content-Location"]

# Go's shouldCopyHeaderOnRedirect: the same host or a subdomain of it
def same_domain(+src: String, +dst: String) -> Bool:
  +a = String.to_lower(src)
  +b = String.to_lower(dst)
  Bool.or(String.eq(a, b), String.ends_with(b, "." ++ a))

def is_slash_q(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.or(U32.is_eq(code(c), 47), U32.is_eq(code(c), 63))

def is_colon(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), 58)

# the bytes before the first "/" or "?", as a loop that stops there (acc
# last byte first)
def before_slash.go(s: String, stop: Bool, +acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+c, +rest}:
      match stop:
        case True{}:
          String.reverse(acc)
        case False{}:
          before_slash.go(rest, is_slash_q(rest), SCon{c, acc})

def before_slash(+s: String) -> String:
  before_slash.go(s, is_slash_q(s), "")

def before_colon.go(s: String, stop: Bool, +acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{+c, +rest}:
      match stop:
        case True{}:
          String.reverse(acc)
        case False{}:
          before_colon.go(rest, is_colon(rest), SCon{c, acc})

def before_colon(+s: String) -> String:
  before_colon.go(s, is_colon(s), "")

def host_of_url(+s: String) -> String:
  +r = String.drop(s, pick(Nat, String.starts_with(String.to_lower(s), "https://"), 8n, 7n))
  before_colon(before_slash(r))

# Go's redirectBehavior: 301, 302 and 303 turn every method but GET and
# HEAD into GET and drop the body; 307 and 308 keep method and body
def redirect_method(+k: Nat, +m: String) -> String:
  pick(String, Bool.and(Bool.or(Bool.or(Nat.is_eq(k, 301n), Nat.is_eq(k, 302n)), Nat.is_eq(k, 303n)),
      Bool.not(Bool.or(String.eq(m, "GET"), String.eq(m, "HEAD")))), "GET", m)

def redirect_body(+k: Nat, +b: String) -> String:
  pick(String, Bool.or(Nat.is_eq(k, 307n), Nat.is_eq(k, 308n)), b, "")

# the next target: Go's method; the headers less credentials when the
# host leaves the first request's domain and less the body's headers when
# the body is dropped; a Referer naming the URL redirected from, unless
# the request set its own
def redirect_target(+orig: String, +t: Tgt.Target, +u: Tgt.Url, +k: Nat, +loc: String) -> Tgt.Target:
  +next = loc_url(u, loc)
  +keep_body = Bool.or(Nat.is_eq(k, 307n), Nat.is_eq(k, 308n))
  +hs1 = pick(List<&2, Hdr.Header>, same_domain(orig, host_of_url(next)), tgt_hdrs(t), drop_all_ci(sensitive(), tgt_hdrs(t)))
  +hs2 = pick(List<&2, Hdr.Header>, keep_body, hs1, drop_all_ci(body_hdrs(), hs1))
  +hs3 = pick(List<&2, Hdr.Header>, has_key_ci("Referer", hs2), hs2, List.append(&2, Hdr.Header, hs2, [Hdr.Header{"Referer", [tgt_url(t)]}]))
  Tgt.Target{redirect_method(k, tgt_method(t)), next, hs3, tgt_body(t)}

def url_or(+d: Tgt.Url, r: Result<&2, &2, String, Tgt.Url>) -> Tgt.Url:
  match r:
    case Done{u}:
      u
    case Fail{e}:
      d

def url_err(r: Result<&2, &2, String, Tgt.Url>) -> String:
  match r:
    case Done{u}:
      ""
    case Fail{e}:
      e

def same_host(+a: String, +b: String) -> Bool:
  String.eq(String.to_lower(a), String.to_lower(b))

# Go's isReplayable: a request it may send again on a new connection
def replayable(+t: Tgt.Target) -> Bool:
  +m = tgt_method(t)
  Bool.or(Bool.or(Bool.or(String.eq(m, "GET"), String.eq(m, "HEAD")), Bool.or(String.eq(m, "OPTIONS"), String.eq(m, "TRACE"))),
    Bool.or(has_key_ci("Idempotency-Key", tgt_hdrs(t)), has_key_ci("X-Idempotency-Key", tgt_hdrs(t))))

# ---------------------------------------------------------------------
# Moves
# ---------------------------------------------------------------------

def finish(+s: State, +o: Out, +keep: Bool) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  (set_over(s), [Finish{o, keep}])

def fail(+s: State, +m: String, +pb: Maybe<&2, String>) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  finish(s, Failed{m, pb}, False{})

def stay(+s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  (s, [])

# the request text goes out on the open connection, as the request k
def send_now(+c: Cfg, +s: State, +text: String, +k: Cur) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  (set_ph(set_rx(set_cur(s, k), rx_fresh(c, text)), PSend{}), [Send{text}])

# a redirect hop goes out: it is the request in flight from now on, one
# hop further
def hop_now(+c: Cfg, +s: State, +nq: Req, +text: String, +reused: Bool) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  send_now(c, s, text, Cur{nq, text, 1n, False{}, reused, 1n+cur_hops(st_cur(s))})

# the pending request goes out on the connection just opened
def send_pend(hop: Bool, +c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match hop:
    case True{}:
      hop_now(c, s, with_ip(st_pend(s), st_ip(s)), st_ptext(s), False{})
    case False{}:
      +k = st_cur(s)
      send_now(c, s, st_ptext(s), Cur{cur_req(k), cur_text(k), 1n+cur_tries(k), cur_got(k), cur_reused(k), cur_hops(k)})

# the request in flight was lost on a reused connection before any byte
# of an answer, and Go may send it again
def lost(+s: State) -> Bool:
  +k = st_cur(s)
  Bool.and(Bool.and(Bool.and(cur_reused(k), replayable(q_target(cur_req(k)))), Nat.is_eq(cur_tries(k), 1n)), Bool.not(cur_got(k)))

# send the request in flight once more, on a new connection
def retry(+s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  +k = st_cur(s)
  +r = cur_req(k)
  (set_pend(s, POpen{}, r, cur_text(k), False{}, st_port(s)), [Open{q_ip(r), u_port(q_url(r))}])

def answer(+c: Cfg, +s: State, m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match m:
    case None{}:
      stay(s)
    case Some{res}:
      match res:
        case Fail{e}:
          stay(s)
        case Done{pr}:
          (r0, lo0) = pr
          +r = r0
          +lo = lo0
          finish(s, Answered{r}, Bool.and(Bool.and(r_keep(r), c_ka(c)), String.is_empty(lo)))

# the next hop's connection: the connection kept (same host and port), a
# new one to the same host, or a lookup of another host
def follow.open(kept: Bool, +c: Cfg, +s: State, +nq: Req, +text: String, +hp: Nat) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match kept:
    case True{}:
      hop_now(c, s, with_ip(nq, q_ip(cur_req(st_cur(s)))), text, True{})
    case False{}:
      (set_rx(set_pend(set_open(s, False{}), POpen{}, nq, text, True{}, hp), set_met(st_rx(s))), [Shut{}, Open{st_ip(s), hp}])

def follow.host(same: Bool, +c: Cfg, +s: State, +nq: Req, +text: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match same:
    case True{}:
      +nu = q_url(nq)
      +cu = q_url(cur_req(st_cur(s)))
      follow.open(Bool.and(Bool.and(kept_of(c_ka(c), Http.done(rx_p0(st_rx(s)))), Nat.is_eq(u_port(nu), u_port(cu))), st_open(s)),
        c, s, nq, text, u_port(nu))
    case False{}:
      +nu = q_url(nq)
      (set_rx(set_pend(set_open(s, False{}), PResolve{}, nq, text, True{}, u_port(nu)), set_met(st_rx(s))), [Shut{}, Resolve{u_host(nu)}])

def follow.ok(ok: Bool, +c: Cfg, +s: State, +nt: Tgt.Target, +pu: Result<&2, &2, String, Tgt.Url>, +k: Nat) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match ok:
    case True{}:
      +q = st_req(s)
      +cr = cur_req(st_cur(s))
      +nq = mk_req(nt, url_or(q_url(cr), pu), "", redirect_body(k, q_body(cr)), q_seq(q), q_name(q))
      follow.host(same_host(u_host(q_url(nq)), u_host(q_url(cr))), c, s, nq,
        Http.request(q_target(nq), q_url(nq), q_body(nq), q_seq(q), q_name(q), c_ka(c)))
    case False{}:
      fail(s, named(st_req(s), tgt_url(nt)) ++ url_err(pu), None{})

# a redirect Go is done with: the next hop, or Go's stop at the limit
def redirect.of(stop: Bool, +c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match stop:
    case True{}:
      fail(s, stop_text(st_req(s), hd_loc(rx_hd(st_rx(s))), rd_limit(c_rd(c))), None{})
    case False{}:
      +q = st_req(s)
      +h = rx_hd(st_rx(s))
      +cr = cur_req(st_cur(s))
      +nt = redirect_target(u_host(q_url(q)), q_target(cr), q_url(cr), hd_code(h), hd_loc(h))
      follow.ok(Result.is_done(&2, &2, String, Tgt.Url, Tgt.parse_url(tgt_url(nt))), c, s, nt, Tgt.parse_url(tgt_url(nt)), hd_code(h))

def redirect(+c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  redirect.of(Nat.is_ge(cur_hops(st_cur(s)), rd_limit(c_rd(c))), c, s)

# a malformed response: in the head, the connection broke; in the body,
# the bare error and the body read up to it
def bad.of(body: Bool, +s: State, +good: Http.Parse, +m: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match body:
    case True{}:
      fail(s, m, Some{Http.partial(good)})
    case False{}:
      fail(s, broken(s) ++ m, None{})

# the parse is in the status line
def ph_stat(ph: Http.Ph) -> Bool:
  match ph:
    case Http.HStat{n, line}:
      True{}
    case _:
      False{}

def p_stat(+p: Http.Parse) -> Bool:
  Http.Parse{mb, head, closed, ph} = p
  ph_stat(ph)

# the parse is in the header lines
def ph_hdr(ph: Http.Ph) -> Bool:
  match ph:
    case Http.HHdr{k, st, mi, hs, pend, line}:
      True{}
    case _:
      False{}

def p_hdr(+p: Http.Parse) -> Bool:
  Http.Parse{mb, head, closed, ph} = p
  ph_hdr(ph)

def ph_msg(+d: String, ph: Http.Ph) -> String:
  match ph:
    case Http.HFail{m}:
      m
    case _:
      d

# Go reads the whole status line before it complains: the parse stops at
# the first byte that cannot start a response, so its complaint is
# redone on the whole line (as far as it arrived) when the bytes are at hand
def stat_msg(h: Head, +rbuf: String, +m: String) -> String:
  match h:
    case HOut{}:
      ph_msg(m, Http.status_of(strip_cr(Tgt.before(final_from(String.reverse(rbuf)), 10))))
    case HIn{r, k, l, g}:
      m

def bad.msg(stat: Bool, +s: State, +m: String) -> String:
  match stat:
    case True{}:
      stat_msg(rx_hd(st_rx(s)), rx_buf(st_rx(s)), m)
    case False{}:
      m

def bad(+s: State, +good: Http.Parse) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  bad.of(p_body(good), s, good, bad.msg(p_stat(good), s, fail_msg(Http.done(rx_p(st_rx(s))))))

# after bytes: answer a final response; act on a redirect Go is done with;
# fail on a malformed response; else read on
def got.more(ph: Phase, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match ph:
    case PRecv{}:
      (s, [Recv{}])
    case _:
      stay(s)

def got.bad(b: Bool, +s: State, +old: Http.Parse, +data: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match b:
    case True{}:
      bad(s, upto(data, False{}, old, old))
    case False{}:
      got.more(st_ph(s), s)

def got.due(d: Bool, +c: Cfg, +s: State, +old: Http.Parse, +data: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match d:
    case True{}:
      redirect(c, s)
    case False{}:
      got.bad(is_fail(Http.done(rx_p(st_rx(s)))), s, old, data)

def got.rest(+c: Cfg, +s: State, +old: Http.Parse, +data: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  got.due(due(st_rx(s)), c, s, old, data)

# a final response is answered at once (the bytes' other facts are not
# needed then); else the bytes are taken in and read
def got.fin(f: Bool, +c: Cfg, +s: State, +p2: Http.Parse, +data: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match f:
    case True{}:
      answer(c, s, Http.done(p2))
    case False{}:
      got.rest(c, set_rx(s, rx_feed(c, st_rx(s), p2, data)), rx_p(st_rx(s)), data)

def on_got(+c: Cfg, +s: State, +d: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  +s1 = set_cur(s, set_got(st_cur(s), d))
  +p2 = Http.feed(rx_p(st_rx(s)), d)
  got.fin(final_of(c, Http.done(p2)), c, s1, p2, d)

# after the close: answer; retry; ignore it while moving to a redirect
# hop; follow a redirect; or fail with Go's words
# a close in the middle of a header line: Go reads the half line as a line
def eof.cut(hdr: Bool, +p: Http.Parse) -> Http.Parse:
  match hdr:
    case True{}:
      Http.feed(p, "\n")
    case False{}:
      p

def eof.text.nl(nl: Bool, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match nl:
    case True{}:
      fail(s, broken(s) ++ "unexpected EOF", None{})
    case False{}:
      fail(s, broken(s) ++ fail_msg(Http.done(eof.cut(p_hdr(rx_p(st_rx(s))), rx_p(st_rx(s))))), None{})

def eof.text.empty(e: Bool, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match e:
    case True{}:
      fail(s, prefix(s) ++ "EOF", None{})
    case False{}:
      eof.text.nl(String.ends_with(final_from(String.reverse(rx_buf(st_rx(s)))), "\n"), s)

def eof.text(in: Bool, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match in:
    case True{}:
      fail(s, "unexpected EOF", Some{Http.partial(rx_p(st_rx(s)))})
    case False{}:
      eof.text.empty(String.is_empty(rx_buf(st_rx(s))), s)

def eof.redir(r: Bool, +c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match r:
    case True{}:
      redirect(c, s)
    case False{}:
      eof.text(in_of(rx_hd(st_rx(s)), rx_buf(st_rx(s))), s)

def eof.met(m: Bool, +c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match m:
    case True{}:
      stay(s)
    case False{}:
      eof.redir(hd_redir(rx_hd(st_rx(s))), c, s)

def eof.lost(l: Bool, +c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match l:
    case True{}:
      retry(s)
    case False{}:
      eof.met(rx_met(st_rx(s)), c, s)

def eof.fin(f: Bool, +c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match f:
    case True{}:
      answer(c, s, Http.done(rx_p(st_rx(s))))
    case False{}:
      eof.lost(lost(s), c, s)

def on_eof(+c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  +s2 = set_rx(set_open(s, False{}), rx_eof(st_rx(s)))
  eof.fin(final_of(c, Http.done(rx_p(st_rx(s2)))), c, s2)

# the deadline: while a redirect's head is in, Go is on the next hop (or
# stops at the limit); before the final head, awaiting headers; after it,
# reading the body (what was read is kept)
def late.in(in: Bool, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match in:
    case True{}:
      fail(s, reading(), Some{Http.partial(rx_p(st_rx(s)))})
    case False{}:
      fail(s, prefix(s) ++ awaiting(), None{})

def late.redir(r: Bool, +c: Cfg, +s: State, +h: Head) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match r:
    case True{}:
      +q = st_req(s)
      +n = rd_limit(c_rd(c))
      fail(s, pick(String, Nat.is_ge(cur_hops(st_cur(s)), n), stop_text(q, hd_loc(h), n),
        named(q, loc_url(q_url(cur_req(st_cur(s))), hd_loc(h))) ++ awaiting()), None{})
    case False{}:
      late.in(in_of(rx_hd(st_rx(s)), rx_buf(st_rx(s))), s)

# the head's facts: kept once it is in for good, else read off the bytes
def late.head(h: Head, +c: Cfg, +rbuf: String) -> Head:
  match h:
    case HOut{}:
      head_bytes(c, String.reverse(rbuf))
    case HIn{r, k, l, g}:
      HIn{r, k, l, g}

def late.of(+c: Cfg, +s: State, +h: Head) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  late.redir(hd_redir(h), c, s, h)

def on_late(+c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  late.of(c, s, late.head(rx_hd(st_rx(s)), c, rx_buf(st_rx(s))))

def on_opened(ph: Phase, +c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match ph:
    case POpen{}:
      send_pend(st_hop(s), c, s)
    case _:
      stay(s)

def on_sent(ph: Phase, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match ph:
    case PSend{}:
      (set_ph(s, PRecv{}), [Recv{}])
    case _:
      stay(s)

def on_send_failed(l: Bool, +s: State, +m: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match l:
    case True{}:
      retry(s)
    case False{}:
      fail(s, write_text(s, m), None{})

def on_resolved(ph: Phase, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match ph:
    case PResolve{}:
      (set_ph(s, POpen{}), [Open{st_ip(s), st_port(s)}])
    case _:
      stay(s)

def on_resolve_failed(ph: Phase, +s: State, +m: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match ph:
    case PResolve{}:
      fail(s, lookup_text(s, m), None{})
    case _:
      stay(s)

def step.ev(e: Ev, +c: Cfg, +s: State) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match e:
    case Opened{}:
      on_opened(st_ph(s), c, set_open(s, True{}))
    case OpenFailed{m}:
      fail(set_open(s, False{}), dial_text(s, m), None{})
    case Sent{}:
      on_sent(st_ph(s), s)
    case SendFailed{m}:
      on_send_failed(lost(s), set_open(s, False{}), m)
    case Got{d}:
      on_got(c, s, d)
    case Eof{}:
      on_eof(c, s)
    case Late{}:
      on_late(c, s)
    case Resolved{ip}:
      on_resolved(st_ph(s), set_ip(s, ip))
    case ResolveFailed{m}:
      on_resolve_failed(st_ph(s), s, m)

def step.over(over: Bool, +c: Cfg, +s: State, e: Ev) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match over:
    case True{}:
      (s, [])
    case False{}:
      step.ev(e, c, s)

# ---------------------------------------------------------------------
# The machine
# ---------------------------------------------------------------------

def start.of(open: Bool, +c: Cfg, +r: Req, +text: String) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  match open:
    case True{}:
      (CState{r, True{}, False{}, Cur{r, text, 1n, False{}, True{}, 0n}, rx_fresh(c, text), PSend{}, r, text, False{}, q_ip(r), u_port(q_url(r))},
       [Send{text}])
    case False{}:
      (CState{r, False{}, False{}, Cur{r, text, 0n, False{}, False{}, 0n}, Rx{"", HOut{}, Http.start(c_mb(c), False{}), Http.start(None{}, False{}), False{}}, POpen{}, r, text, False{}, q_ip(r), u_port(q_url(r))},
       [Open{q_ip(r), u_port(q_url(r))}])

# open: whether the worker's connection from its last request is still open
def start(+c: Cfg, +r: Req, open: Bool) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  start.of(open, c, r, Http.request(q_target(r), q_url(r), q_body(r), q_seq(r), q_name(r), c_ka(c)))

def step(+c: Cfg, +s: State, e: Ev) -> Sigma<&2, &2, State, _ => List<&2, Cmd>>:
  step.over(st_over(s), c, s, e)

# ---------------------------------------------------------------------
# Results
# ---------------------------------------------------------------------

def is_ok(+k: Nat) -> Bool:
  Bool.and(Nat.is_ge(k, 200n), Nat.is_lt(k, 400n))

# the result the shell records for a finished request: attack name, seq,
# start time, latency, the request's method, URL and body size, and the outcome
def to_hit(+name: String, +seq: Nat, +ts: Civil.Time, +lat: Nat, +method: String, +url: String, +out_bytes: Nat, +o: Out) -> Hit.Hit:
  match o:
    case Answered{r}:
      Hit.Hit{name, seq, r_code(r), ts, lat, out_bytes, String.length(r_body(r)), pick(String, is_ok(r_code(r)), "", r_status(r)),
        Some{r_body(r)}, method, url, Some{r_hdrs(r)}}
    case Failed{e, pb}:
      Hit.Hit{name, seq, 0n, ts, lat, 0n, 0n, e, pb, method, url, None{}}

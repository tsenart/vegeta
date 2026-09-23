# The parser reads bytes, not reads: a pipelined pair of chunked
# responses fed one byte at a time, three at a time, or cut in two at
# every point, parses as fed whole; what is left after the first is the
# second, which parses on its own (its "Connection: close" gone, as Go
# drops it). Then a 1 MiB body, framed by length
# and by chunks, fed in 1 KiB pieces.
import Base
import ../lib/hdr.bend as Hdr
import ../lib/target.bend as Tgt
import ../lib/http.bend as Http
import ../lib/dec.bend as Dec

def esc(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      Tgt.pick(String, U32.is_eq(Tgt.code(c), 13), "\\r", Tgt.pick(String, U32.is_eq(Tgt.code(c), 10), "\\n", SCon{c, SNil{}})) ++ esc(rest)

def kvs(hs: List<&2, Hdr.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      Hdr.Header{k, vs} = h
      k ++ "=" ++ String.join(vs, ",") ++ ";" ++ kvs(rest)

def show_resp(+r: Http.Resp, +rest: String) -> String:
  Http.Resp{c, st, hs, b, k} = r
  Dec.show(c) ++ "|" ++ st ++ "|" ++ kvs(hs) ++ "|" ++ b ++ "|" ++ Tgt.pick(String, k, "true", "false") ++ "|" ++ esc(rest)

def show(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> String:
  match m:
    case None{}:
      "none"
    case Some{res}:
      match res:
        case Fail{e}:
          "fail|" ++ e
        case Done{p}:
          (r, rest) = p
          show_resp(r, rest)

def rest_of(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> String:
  match m:
    case None{}:
      ""
    case Some{res}:
      match res:
        case Fail{e}:
          ""
        case Done{p}:
          (r, rest) = p
          rest

# the parse, its answer, and its answer after the close
def view(+p: Http.Parse) -> String:
  show(Http.done(p)) ++ "#" ++ show(Http.done(Http.eof(p))) ++ "#" ++ Http.partial(p)

def bytewise(s: String, p: Http.Parse) -> Http.Parse:
  match s:
    case SNil{}:
      p
    case SCon{+c, +rest}:
      bytewise(rest, Http.feed(p, SCon{c, SNil{}}))

def by3(+fuel: Nat, +s: String, +p: Http.Parse) -> Http.Parse:
  match fuel:
    case 0n:
      p
    case 1n+f:
      Tgt.pick(Http.Parse, String.is_empty(s), p, by3(f, String.drop(s, 3n), Http.feed(p, String.take(s, 3n))))

def cuts(+fuel: Nat, +k: Nat, +s: String, +want: String) -> Bool:
  match fuel:
    case 0n:
      True{}
    case 1n+f:
      Bool.and(String.eq(view(Http.feed(Http.feed(Http.start(None{}, False{}), String.take(s, k)), String.drop(s, k))), want),
        cuts(f, 1n+k, s, want))

def pipelined() -> String:
  "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nX-A: 1\r\n\r\n4\r\nWiki\r\n5;x=y\r\npedia\r\n0\r\nT: v\r\n\r\n"
    ++ "HTTP/1.1 201 Created\r\ntransfer-encoding: chunked\r\nConnection: close\r\n\r\n3\r\nabc\r\n0\r\n\r\n"

def big_body(+n: Nat, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      big_body(p, SCon{Chr{U32.from_nat(Nat.add(97n, Nat.mod(p, 26n)))}, acc})

def chunked(+fuel: Nat, +s: String) -> String:
  match fuel:
    case 0n:
      "0\r\n\r\n"
    case 1n+f:
      Tgt.pick(String, String.is_empty(s), "0\r\n\r\n", "1000\r\n" ++ String.take(s, 4096n) ++ "\r\n" ++ chunked(f, String.drop(s, 4096n)))

def pieces(+fuel: Nat, +s: String, +p: Http.Parse) -> Http.Parse:
  match fuel:
    case 0n:
      p
    case 1n+f:
      Tgt.pick(Http.Parse, String.is_empty(s), p, pieces(f, String.drop(s, 1024n), Http.feed(p, String.take(s, 1024n))))

def body_ok(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, +want: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          False{}
        case Done{p}:
          (r, rest) = p
          Http.Resp{c, st, hs, b, k} = r
          Bool.and(String.eq(b, want), String.is_empty(rest))

def whole(+s: String) -> String:
  view(Http.feed(Http.start(None{}, False{}), s))

def same(+s: String, +p: Http.Parse) -> String:
  Bool.show(String.eq(view(p), whole(s)))

def cl_ok(+b: String) -> String:
  +cl = "HTTP/1.1 200 OK\r\nContent-Length: 1048576\r\n\r\n" ++ b
  Bool.show(body_ok(Http.done(pieces(String.length(cl), cl, Http.start(None{}, False{}))), b))

def ch_ok(+b: String) -> String:
  +ch = "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n" ++ chunked(String.length(b), b)
  Bool.show(body_ok(Http.done(pieces(String.length(ch), ch, Http.start(None{}, False{}))), b))

def second(+s: String) -> String:
  show(Http.done(Http.feed(Http.start(None{}, False{}), rest_of(Http.done(Http.feed(Http.start(None{}, False{}), s))))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(esc(whole(pipelined())))
    IO.print(same(pipelined(), bytewise(pipelined(), Http.start(None{}, False{}))))
    IO.print(same(pipelined(), by3(String.length(pipelined()), pipelined(), Http.start(None{}, False{}))))
    IO.print(Bool.show(cuts(1n+String.length(pipelined()), 0n, pipelined(), whole(pipelined()))))
    IO.print(second(pipelined()))
    IO.print(cl_ok(big_body(1048576n, "")))
    IO.print(ch_ok(big_body(1048576n, "")))

#|200|200 OK|X-A=1;|Wikipedia|true|HTTP/1.1 201 Created\r\ntransfer-encoding: chunked\r\nConnection: close\r\n\r\n3\r\nabc\r\n0\r\n\r\n#200|200 OK|X-A=1;|Wikipedia|true|HTTP/1.1 201 Created\r\ntransfer-encoding: chunked\r\nConnection: close\r\n\r\n3\r\nabc\r\n0\r\n\r\n#Wikipedia
#|True
#|True
#|True
#|201|201 Created||abc|false|
#|True
#|True

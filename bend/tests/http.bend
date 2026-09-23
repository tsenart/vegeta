# HTTP/1.1 against Go: the request text Go's transport writes for a
# target (expected lines from scripts/gen-http-request.go), then
# responses as Go's transport reads them (scripts/gen-http-resp.go):
# code|status|headers|body|len|keep|rest, or fail|text. \r and \n are
# written as \r and \n. A response not complete at the end of its bytes
# is read again after the close.
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

def url_or(r: Result<&2, &2, String, Tgt.Url>) -> Tgt.Url:
  match r:
    case Done{u}:
      u
    case Fail{e}:
      Tgt.Url{"http", e, None{}, "/"}

def req(+m: String, +u: String, +hs: List<&2, Hdr.Header>, +body: String, +seq: Nat, +name: String, ka: Bool) -> String:
  esc(Http.request(Tgt.Target{m, u, hs, None{}}, url_or(Tgt.parse_url(u)), body, seq, name, ka))

def hkey(+h: Hdr.Header) -> String:
  Hdr.Header{k, vs} = h
  k

def ins(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [h]
    case Con{+x, +rest}:
      Tgt.pick(List<&2, Hdr.Header>, String.is_lt(hkey(h), hkey(x)), Con{h, Con{x, rest}}, Con{x, ins(h, rest)})

def sorted(hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      ins(h, sorted(rest))

def kvs(hs: List<&2, Hdr.Header>) -> List<&2, String>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      Hdr.Header{k, vs} = h
      Con{k ++ "=" ++ String.join(vs, ","), kvs(rest)}

def show_resp(+r: Http.Resp, +rest: String) -> String:
  Http.Resp{c, st, hs, b, k} = r
  Dec.show(c) ++ "|" ++ st ++ "|" ++ String.join(kvs(sorted(hs)), ";") ++ "|" ++ esc(b) ++ "|" ++ Dec.show(String.length(b))
    ++ "|" ++ Tgt.pick(String, k, "true", "false") ++ "|" ++ esc(rest)

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

def resp.of(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, +p: Http.Parse) -> String:
  match m:
    case None{}:
      show(Http.done(Http.eof(p)))
    case Some{x}:
      show(Some{x})

def resp(+raw: String, +head: Bool, +mb: Maybe<&2, Nat>) -> String:
  +p = Http.feed(Http.start(mb, head), raw)
  resp.of(Http.done(p), p)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(req("GET", "http://example.com:8080/a?b=c", [Hdr.Header{"X-A", ["1", "2"]}, Hdr.Header{"Accept", ["*/*"]}], "", 7n, "atk", True{}))
    IO.print(req("POST", "http://example.com/p", [Hdr.Header{"Content-Type", ["text/plain"]}, Hdr.Header{"Host", ["h.example"]}, Hdr.Header{"User-Agent", ["ua/1"]}], "hello", 0n, "", False{}))
    IO.print(req("PUT", "http://example.com/a b/c", [], "", 1n, "", True{}))
    IO.print(req("DELETE", "http://example.com/x/%7e;p?q=%zz", [Hdr.Header{"Content-Length", ["99"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}, Hdr.Header{"Trailer", ["X"]}, Hdr.Header{"Connection", ["keep-alive"]}], "", 2n, "n", False{}))
    IO.print(req("PATCH", "http://example.com/%41%2f", [Hdr.Header{"x-lower", ["v"]}], "", 3n, "", True{}))
    IO.print(req("GET", "http://example.com/", [Hdr.Header{"host", ["lower"]}, Hdr.Header{"user-agent", ["lower"]}], "", 4n, "", True{}))
    IO.print(req("GET", "http://example.com/", [Hdr.Header{"X-Vegeta-Seq", ["9"]}, Hdr.Header{"X-Vegeta-Attack", ["old"]}, Hdr.Header{"Host", ["a", "b"]}], "", 5n, "new", True{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nContent-Length: 5\r\n\r\nhelloEXTRA", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nX-A: 1\r\n\r\n5;ext=1\r\nhello\r\n6\r\n world\r\n0\r\nTrailer-X: y\r\n\r\nNEXT", False{}, None{}))
    IO.print(resp("HTTP/1.1 500 Internal Server Error\r\nX: y\r\n\r\noops", False{}, None{}))
    IO.print(resp("HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 103 Early Hints\r\nLink: </a>\r\n\r\nHTTP/1.1 204 No Content\r\nX: 1\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nContent-Length: 8\r\n\r\n12345678", False{}, Some{2n}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n3\r\nabc\r\n3\r\ndef\r\n0\r\n\r\n", False{}, Some{4n}))
    IO.print(resp("HTTP/1.0 200 OK\r\nConnection: keep-alive\r\nContent-Length: 2\r\n\r\nhi", False{}, None{}))
    IO.print(resp("HTTP/1.0 200 OK\r\nContent-Length: 2\r\n\r\nhi", False{}, None{}))
    IO.print(resp("HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhi", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\n", True{}, None{}))
    IO.print(resp("HTTP/1.1 304 Not Modified\r\nContent-Length: 10\r\n\r\nrest", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\ncontent-length: 2\r\nx-multi:  a \t\r\nx-multi: b\r\nX-Fold: a\r\n  b\r\nx-odd name: v\r\n\r\nok", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\nContent-Length: 1\n\nz", False{}, None{}))
    IO.print(resp("HTTP/1.1  201 Created\r\nContent-Length: 0\r\nContent-Length: 0\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200\r\nContent-Length: 0\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 abc OK\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nBad Header\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\n Folded: x\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nBad@Name: x\r\n\r\n", False{}, None{}))
    IO.print(resp(("HTTP/1.1 200 OK\r\nX: a" ++ SCon{Chr{1}, SNil{}} ++ "b\r\n\r\n"), False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nContent-Length: x\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nContent-Length: \r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nContent-Length: 1\r\nContent-Length: 2\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nzz\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\nab\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nabX\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nabc", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nX: 1\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: CHUNKED\r\nContent-Length: 99\r\n\r\n1 ; x\r\na\r\n0\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nConnection: keep-alive, Close\r\nX: 1\r\nContent-Length: 1\r\n\r\na", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nConnection: Upgrade\r\nContent-Length: 1\r\n\r\na", False{}, None{}))
    IO.print(resp("HTTP/1.0 200 OK\r\nConnection: foo , Keep-Alive\r\nContent-Length: 1\r\n\r\na", False{}, None{}))
    IO.print(resp("HTTP/1.0 200 OK\r\nConnection: keep-alive\r\nConnection: close\r\nContent-Length: 1\r\n\r\na", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nPragma: no-cache\r\nContent-Length: 0\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nPragma: no-cache\r\nCache-Control: max-age=1\r\nContent-Length: 0\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nPragma: No-Cache\r\nContent-Length: 0\r\n\r\n", False{}, None{}))
    IO.print(resp("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n1\r\na\r\n0\r\n\r\n", False{}, None{}))

#|GET /a?b=c HTTP/1.1\r\nHost: example.com:8080\r\nUser-Agent: Go-http-client/1.1\r\nAccept: */*\r\nX-A: 1\r\nX-A: 2\r\nX-Vegeta-Attack: atk\r\nX-Vegeta-Seq: 7\r\n\r\n
#|POST /p HTTP/1.1\r\nHost: h.example\r\nUser-Agent: ua/1\r\nContent-Length: 5\r\nContent-Type: text/plain\r\nX-Vegeta-Seq: 0\r\nConnection: close\r\n\r\nhello
#|PUT /a%20b/c HTTP/1.1\r\nHost: example.com\r\nUser-Agent: Go-http-client/1.1\r\nContent-Length: 0\r\nX-Vegeta-Seq: 1\r\n\r\n
#|DELETE /x/%7e;p?q=%zz HTTP/1.1\r\nHost: example.com\r\nUser-Agent: Go-http-client/1.1\r\nConnection: keep-alive\r\nX-Vegeta-Attack: n\r\nX-Vegeta-Seq: 2\r\nConnection: close\r\n\r\n
#|PATCH /%41%2f HTTP/1.1\r\nHost: example.com\r\nUser-Agent: Go-http-client/1.1\r\nContent-Length: 0\r\nX-Vegeta-Seq: 3\r\nx-lower: v\r\n\r\n
#|GET / HTTP/1.1\r\nHost: example.com\r\nUser-Agent: Go-http-client/1.1\r\nX-Vegeta-Seq: 4\r\nhost: lower\r\nuser-agent: lower\r\n\r\n
#|GET / HTTP/1.1\r\nHost: a\r\nUser-Agent: Go-http-client/1.1\r\nX-Vegeta-Attack: new\r\nX-Vegeta-Seq: 5\r\n\r\n
#|200|200 OK|Content-Length=5;Content-Type=text/plain|hello|5|true|EXTRA
#|200|200 OK|X-A=1|hello world|11|true|NEXT
#|500|500 Internal Server Error|X=y|oops|4|false|
#|204|204 No Content|X=1||0|true|
#|200|200 OK|Content-Length=8|12|2|true|
#|200|200 OK||abcd|4|true|
#|200|200 OK|Connection=keep-alive;Content-Length=2|hi|2|true|
#|200|200 OK|Content-Length=2|hi|2|false|
#|200|200 OK||2\r\nhi|5|false|
#|200|200 OK|Content-Length=10||0|true|
#|304|304 Not Modified|Content-Length=10||0|true|rest
#|200|200 OK|Content-Length=2;X-Fold=a b;X-Multi=a,b;x-odd name=v|ok|2|true|
#|200|200 OK|Content-Length=1|z|1|true|
#|201|201 Created|Content-Length=0||0|true|
#|200|200|Content-Length=0||0|true|
#|fail|malformed HTTP status code "abc"
#|fail|malformed MIME header: missing colon: "Bad Header"
#|fail|malformed MIME header initial line: " Folded: x"
#|fail|malformed MIME header line: "Bad@Name: x"
#|fail|malformed MIME header line: "X: a\x01b"
#|fail|bad Content-Length "x"
#|fail|invalid empty Content-Length ""
#|fail|http: message cannot contain multiple Content-Length headers; got ["1" "2"]
#|fail|unsupported transfer encoding: "gzip"
#|fail|too many transfer encodings: ["chunked" "chunked"]
#|fail|invalid byte in chunk length
#|fail|empty hex number for chunk length
#|fail|chunked line ends with bare LF
#|fail|malformed chunked encoding
#|fail|unexpected EOF
#|fail|unexpected EOF
#|fail|invalid byte in chunk length
#|200|200 OK|Content-Length=1;X=1|a|1|false|
#|200|200 OK|Connection=Upgrade;Content-Length=1|a|1|true|
#|200|200 OK|Connection=foo , Keep-Alive;Content-Length=1|a|1|true|
#|200|200 OK|Connection=keep-alive,close;Content-Length=1|a|1|false|
#|200|200 OK|Cache-Control=no-cache;Content-Length=0;Pragma=no-cache||0|true|
#|200|200 OK|Cache-Control=max-age=1;Content-Length=0;Pragma=no-cache||0|true|
#|200|200 OK|Content-Length=0;Pragma=No-Cache||0|true|
#|200|200 OK||a|1|false|

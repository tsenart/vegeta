import Base
import ../.build/laws_helpers.bend as L
import ../lib/target.bend as Tgt
import ../lib/hdr.bend as Hdr
import ../lib/http.bend as Http
import ../lib/conn.bend as Conn

def big(hi: Nat, lo: Nat) -> Nat:
  Nat.add(Nat.mul(hi, 1000000n), lo)

def rounds(xs: List<&2, Nat>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      Con{Nat.show(L.round_go(x)), rounds(rest)}

def oks(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      L.pick(String, L.dur_ok(x), "T", "F") ++ oks(rest)

def spaces(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      L.pick(String, L.first_space(x), "T", "F") ++ spaces(rest)

def uris(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      L.request_uri(x) ++ " " ++ uris(rest)

def base() -> Tgt.Url:
  Tgt.Url{"http", "h", None{}, "/a/b/c?x=1"}

def locs(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      L.loc_url(base(), x) ++ " " ++ locs(rest)

def w0() -> L.Wait:
  L.Wait{False{}, False{}, False{}, False{}, False{}, False{}}

# Go's retry after a stale keep-alive close, then an answer
def retry() -> List<&2, L.CItem>:
  [L.CICmd{Conn.Send{"GET / HTTP/1.1"}}, L.CIEv{Conn.Sent{}}, L.CICmd{Conn.Recv{}}, L.CIEv{Conn.Eof{}},
   L.CICmd{Conn.Open{"127.0.0.1", 80n}}, L.CIEv{Conn.Opened{}}, L.CICmd{Conn.Send{"GET / HTTP/1.1"}}, L.CIEv{Conn.Sent{}},
   L.CICmd{Conn.Recv{}}, L.CIEv{Conn.Got{"x"}}, L.CICmd{Conn.Recv{}}]

# a client that connects and then asks for nothing
def stall() -> List<&2, L.CItem>:
  [L.CICmd{Conn.Open{"127.0.0.1", 80n}}, L.CIEv{Conn.Opened{}}, L.CIEv{Conn.Late{}}]

def req0() -> Conn.Req:
  Conn.Req{Tgt.Target{"GET", "http://h/", [], None{}}, Tgt.Url{"http", "h", None{}, "/"}, "127.0.0.1", "", 0n, ""}

def cfg0() -> Conn.Cfg:
  Conn.CCfg{True{}, 0n, None{}, Some{0n}}

# -redirects=0: a 302, Go's stop error, then the server closes (the
# request sent is the target's own: conn_redirect pins it)
def stop_then_eof() -> List<&2, L.CItem>:
  [L.CICmd{Conn.Send{L.q_text(cfg0(), req0())}}, L.CIEv{Conn.Sent{}}, L.CICmd{Conn.Recv{}},
   L.CIEv{Conn.Got{"HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 5000\r\n\r\n"}},
   L.CICmd{Conn.Finish{Conn.Failed{"Get \"/x\": stopped after 0 redirects", None{}}, False{}}}, L.CIEv{Conn.Eof{}}]

def spurious() -> List<&2, L.CItem>:
  [L.CICmd{Conn.Resolve{"h"}}, L.CIEv{Conn.Resolved{"127.0.0.1"}}, L.CICmd{Conn.Finish{Conn.Failed{"x", None{}}, False{}}}]

def dial_fail() -> List<&2, L.CItem>:
  [L.CICmd{Conn.Open{"127.0.0.1", 80n}}, L.CIEv{Conn.OpenFailed{"Connection refused"}}, L.CICmd{Conn.Finish{Conn.Failed{"x", None{}}, False{}}}]

def rd(+xs: List<&2, L.CItem>) -> String:
  L.pick(String, L.chk_redirect(xs, cfg0(), req0(), L.q_target(req0()), L.q_url(req0()), "", Some{L.q_text(cfg0(), req0())}, 0n, False{}, "", False{}, False{}, False{}, False{}, "127.0.0.1", None{}), "T", "F")

def hints_then(+e: Conn.Ev, +msg: String) -> List<&2, L.CItem>:
  [L.CICmd{Conn.Send{"GET / HTTP/1.1"}}, L.CIEv{Conn.Sent{}}, L.CICmd{Conn.Recv{}},
   L.CIEv{Conn.Got{"HTTP/1.1 103 Early Hints\r\nLink: x\r\n\r\n"}}, L.CICmd{Conn.Recv{}}, L.CIEv{e},
   L.CICmd{Conn.Finish{Conn.Failed{msg, None{}}, False{}}}]

def cut(+bytes: String, +msg: String) -> List<&2, L.CItem>:
  [L.CICmd{Conn.Send{"GET / HTTP/1.1"}}, L.CIEv{Conn.Sent{}}, L.CICmd{Conn.Recv{}},
   L.CIEv{Conn.Got{bytes}}, L.CICmd{Conn.Recv{}}, L.CIEv{Conn.Eof{}},
   L.CICmd{Conn.Finish{Conn.Failed{msg, None{}}, False{}}}]

def cf(+xs: List<&2, L.CItem>) -> String:
  L.pick(String, L.chk_fail(xs, cfg0(), req0(), False{}, False{}, False{}, ""), "T", "F")

def dst(+hh: String, +kept: Bool, +k: Conn.Cmd) -> String:
  L.pick(String, L.dest_ok(hh, 80n, "h", 80n, "1.1.1.1", kept, Some{k}), "T", "F")

def keys(hs: List<&2, Hdr.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      L.hdr_key(h) ++ "=" ++ L.join_str(",", L.hdr_vals(h)) ++ ";" ++ keys(rest)

def u8(k: U32) -> String:
  L.str1(k)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(L.join_str(" ", rounds([0n, 999n, 1000n, 1499n, 1500n, 1500000n, 1500499n, 1999999999n, big(59500n, 0n), big(3629999n, 999999n), big(3630000n, 0n), big(5400000n, 0n)])))
    IO.print(oks(["0", "-0", "+5s", "5x", "5sec", "1.5", "1.5s", ".5s", "5.s", "1h30m", "", "1", "1us", "1" ++ L.micro() ++ "s", "1" ++ L.greek_mu() ++ "s", "+-5s", "1.s5m"]))
    IO.print(spaces([" x", u8(227) ++ u8(128) ++ u8(128) ++ "y", u8(194) ++ u8(160) ++ "z", "x", u8(194) ++ u8(133) ++ "a", u8(226) ++ u8(128) ++ u8(168) ++ "b", u8(226) ++ u8(128) ++ u8(139) ++ "c"]))
    IO.print(uris(["/a|b", "/{x}?q={y}", "/a(b)", "/a%20b", "/a%7cb"]))
    IO.print(locs(["/x", "x", "../x", "./x", "?q", "//o/p", "http://o/p", "", "../../../x", "y/./z/.."]))
    IO.print(L.rjson_str("a" ++ u8(8) ++ "b" ++ u8(12) ++ "c<" ++ u8(1)))
    IO.print(L.pick(String, L.same_domain("example.com", "api.example.com"), "T", "F") ++ L.pick(String, L.same_domain("example.com", "evilexample.com"), "T", "F") ++ L.pick(String, L.same_domain("A.com", "a.com"), "T", "F"))
    IO.print(Nat.show(L.head_code("HTTP/1.1 302 Found\r\nlocation:  /x \r\nX: y\r\n\r\nbo")) ++ " " ++ L.head_location("HTTP/1.1 302 Found\r\nlocation:  /x \r\nX: y\r\n\r\nbo"))
    IO.print(L.request_uri("/a[1]") ++ " " ++ L.request_uri("/a[1]|"))
    IO.print(keys(L.tgt_hdrs(L.redirect_target("mine", Tgt.Target{"POST", "http://mine/", [Hdr.Header{"Authorization", ["x"]}, Hdr.Header{"Content-Type", ["t"]}, Hdr.Header{"X-Other", ["o"]}], None{}},
      Tgt.Url{"http", "mine", None{}, "/"}, Http.Resp{302n, "302 Found", [Hdr.Header{"Location", ["http://other/"]}], "", True{}}))))
    IO.print(keys(L.tgt_hdrs(L.redirect_target("a.test", Tgt.Target{"GET", "http://x.a.test/r2", [Hdr.Header{"Authorization", ["secret"]}], None{}},
      Tgt.Url{"http", "x.a.test", None{}, "/r2"}, Http.Resp{302n, "302 Found", [Hdr.Header{"Location", ["http://y.a.test/"]}], "", True{}}))))
    IO.print(L.pick(String, L.chk_pending(retry(), w0()), "T", "F") ++ L.pick(String, L.chk_pending(stall(), w0()), "T", "F"))
    IO.print(L.pick(String, L.drained(Conn.CCfg{True{}, 0n, None{}, Some{10n}}, False{}, "HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 5000\r\n\r\nabc", False{}), "T", "F")
      ++ L.pick(String, L.drained(Conn.CCfg{True{}, 0n, None{}, Some{10n}}, False{}, "HTTP/1.1 302 Found\r\nLocation: /x\r\nContent-Length: 10\r\n\r\nabc", False{}), "T", "F"))
    IO.print(rd(stop_then_eof()) ++ rd(spurious()) ++ rd(dial_fail()))
    IO.print(Nat.show(L.head_code("HTTP/1.1 103 Early Hints\r\nLink: x\r\n\r\nHTTP/1.1 302 Found\r\nLocation: /x\r\n\r\n")) ++ " "
      ++ L.head_location("HTTP/1.1 103 Early Hints\r\nLink: x\r\n\r\nHTTP/1.1 302 Found\r\nLocation: /x\r\n\r\n"))
    IO.print(cf(hints_then(Conn.Late{}, "Get \"http://h/\": context deadline exceeded (Client.Timeout exceeded while awaiting headers)"))
      ++ cf(hints_then(Conn.Eof{}, "Get \"http://h/\": net/http: HTTP/1.x transport connection broken: unexpected EOF"))
      ++ cf(hints_then(Conn.Late{}, "context deadline exceeded (Client.Timeout or context cancellation while reading body)"))
      ++ cf(cut("HTTP/1.1 20", "Get \"http://h/\": net/http: HTTP/1.x transport connection broken: malformed HTTP status code \"20\""))
      ++ cf(cut("HTTP/1.1 200 OK\r\nContent-Le", "Get \"http://h/\": net/http: HTTP/1.x transport connection broken: malformed MIME header: missing colon: \"Content-Le\""))
      ++ cf(cut("HTTP/1.1 200 OK\r\n", "Get \"http://h/\": net/http: HTTP/1.x transport connection broken: unexpected EOF"))
      ++ cf(cut("HTTP/1.1 200 OK\r\n", "Get \"http://h/\": net/http: HTTP/1.x transport connection broken: something else")))
    IO.print(dst("other", False{}, Conn.Resolve{"other"}) ++ dst("other", False{}, Conn.Open{"1.1.1.1", 80n}) ++ dst("other", True{}, Conn.Send{"x"})
      ++ dst("H", False{}, Conn.Open{"1.1.1.1", 80n}) ++ dst("h", False{}, Conn.Open{"2.2.2.2", 80n}) ++ dst("h", False{}, Conn.Send{"x"}) ++ dst("h", True{}, Conn.Send{"x"}))
    IO.print(L.pick(String, L.awaited_open("9.9.9.9", Some{80n}, [L.CICmd{Conn.Open{"9.9.9.9", 80n}}]), "T", "F")
      ++ L.pick(String, L.awaited_open("9.9.9.9", Some{80n}, [L.CICmd{Conn.Open{"1.1.1.1", 80n}}]), "T", "F"))
    IO.print(L.redirect_method(302n, "PUT") ++ " " ++ L.redirect_method(301n, "DELETE") ++ " " ++ L.redirect_method(302n, "HEAD") ++ " " ++ L.redirect_method(308n, "PUT"))

#|0 999 1000 1499 1500 1500000 1500000 2000000000 59500000000 3600000000000 3660000000000 5400000000000
#|TTTFFFTTTTFFTTTFT
#|TTTFTTF
#|/a%7Cb /%7Bx%7D?q={y} /a(b) /a%20b /a%7cb 
#|http://h/x http://h/a/b/x http://h/a/x http://h/a/b/x http://h/a/b/c?q http://o/p http://o/p http://h/a/b/c?x=1 http://h/x http://h/a/b/y/ 
#|"a\bb\fc\u003c\u0001"
#|TFT
#|302 /x
#|/a[1] /a%5B1%5D%7C
#|X-Other=o;Referer=http://mine/;
#|Authorization=secret;Referer=http://x.a.test/r2;
#|TF
#|TF
#|TFT
#|302 /x
#|TTFTTTF
#|TFFTFFT
#|TF
#|GET GET HEAD PUT

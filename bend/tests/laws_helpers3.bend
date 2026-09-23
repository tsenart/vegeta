import Base
import ../.build/laws_helpers.bend as L
import ../lib/target.bend as Tgt
import ../lib/hdr.bend as Hdr
import ../lib/http.bend as Http

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
    IO.print(keys(L.tgt_hdrs(L.redirect_target(Tgt.Target{"POST", "http://mine/", [Hdr.Header{"Authorization", ["x"]}, Hdr.Header{"Content-Type", ["t"]}, Hdr.Header{"X-Other", ["o"]}], None{}},
      Tgt.Url{"http", "mine", None{}, "/"}, Http.Resp{302n, "302 Found", [Hdr.Header{"Location", ["http://other/"]}], "", True{}}))))
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
#|GET GET HEAD PUT

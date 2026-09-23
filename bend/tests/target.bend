# The http targets format, against Go's NewHTTPTargeter (the expected
# lines up to the parse_url ones come from scripts/gen-http-targets.go),
# then parse_url, then apply.
import Base
import ../lib/hdr.bend as Hdr
import ../lib/target.bend as Tgt
import ../lib/dec.bend as Dec

def kv(+k: String, vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{+v, +rest}:
      Con{k ++ "=" ++ v, kv(k, rest)}

def hvals(+h: Hdr.Header) -> List<&2, String>:
  Hdr.Header{k, vs} = h
  vs

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
      List.append(&2, String, kv(hkey(h), hvals(h)), kvs(rest))

def body(+b: Maybe<&2, String>) -> String:
  match b:
    case None{}:
      ""
    case Some{p}:
      "@" ++ p

def show_t(+t: Tgt.Target) -> String:
  Tgt.Target{m, u, hs, b} = t
  m ++ " " ++ u ++ "|" ++ String.join(kvs(sorted(hs)), ",") ++ "|" ++ body(b)

def show_ts(ts: List<&2, Tgt.Target>) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{+t, +rest}:
      "\n" ++ show_t(t) ++ show_ts(rest)

def show(r: Result<&2, &2, String, List<&2, Tgt.Target>>) -> String:
  match r:
    case Fail{e}:
      "1\n" ++ e
    case Done{+ts}:
      Nat.show(List.length(&2, Tgt.Target, ts)) ++ show_ts(ts)

def port(+p: Maybe<&2, Nat>) -> String:
  match p:
    case None{}:
      "None"
    case Some{n}:
      "Some " ++ Dec.show(n)

def show_url(+u: Tgt.Url) -> String:
  Tgt.Url{s, h, p, pa} = u
  "Done " ++ s ++ " " ++ h ++ " " ++ port(p) ++ " " ++ pa

def show_u(r: Result<&2, &2, String, Tgt.Url>) -> String:
  match r:
    case Fail{e}:
      "Fail " ++ e
    case Done{u}:
      show_url(u)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show(Tgt.parse_all("GET http://127.0.0.1:8080/a?b=c\nX-A: 1\nX-A: 2\n\n# comment\nPOST http://localhost/x\n@tests/golden/body.txt\nPUT http://h:1/\n")))
    IO.print(show(Tgt.parse_all("get http://x/\n")))
    IO.print(show(Tgt.parse_all("GET\n")))
    IO.print(show(Tgt.parse_all("GET foo\n")))
    IO.print(show(Tgt.parse_all("GET :foo\n")))
    IO.print(show(Tgt.parse_all("GET http://x/%zz\n")))
    IO.print(show(Tgt.parse_all("GET http://x/\nX-A\n")))
    IO.print(show(Tgt.parse_all("GET http://x/\nX-A:  \n")))
    IO.print(show(Tgt.parse_all("GET http://x/\n: v\n")))
    IO.print(show(Tgt.parse_all("  GET http://x/  \r\n  X-B :  v : w \r\n\r\n")))
    IO.print(show(Tgt.parse_all("GET http://x/\n# c\nX-A: 1\n# d\nX-B: 2\nPOST http://y/\n")))
    IO.print(show(Tgt.parse_all("GET http://x/\nPOST http://y/\n@tests/golden/body.txt\nX-A: 1\n")))
    IO.print(show(Tgt.parse_all("GET http://x/\n@tests/golden/body.txt\n\n\n\nHEAD http://z/")))
    IO.print(show(Tgt.parse_all("GET\thttp://x/ y\n")))
    IO.print(show(Tgt.parse_all("G1T http://x/\n")))
    IO.print(show(Tgt.parse_all("\n\n# only comments\n   \n")))
    IO.print(show(Tgt.parse_all("")))
    IO.print(show(Tgt.parse_all("GET /relative\n")))
    IO.print(show(Tgt.parse_all("GET mailto:x\n")))
    IO.print(show(Tgt.parse_all("GET http://x/\nx-a: 1\nX-A: 2\nx-a: 3\n")))
    IO.print(show_u(Tgt.parse_url("http://h")))
    IO.print(show_u(Tgt.parse_url("http://h:8080/a/b?c=d#frag")))
    IO.print(show_u(Tgt.parse_url("http://127.0.0.1:80?x")))
    IO.print(show_u(Tgt.parse_url("http://h:/p")))
    IO.print(show_u(Tgt.parse_url("https://h/")))
    IO.print(show_u(Tgt.parse_url("ftp://h/")))
    IO.print(show_u(Tgt.parse_url("h/x")))
    IO.print(show_u(Tgt.parse_url("http:///x")))
    IO.print(show_u(Tgt.parse_url("http://a b/")))
    IO.print(show_u(Tgt.parse_url("http://h:0/")))
    IO.print(show_u(Tgt.parse_url("http://h:65536/")))
    IO.print(show_u(Tgt.parse_url("http://h:8x/")))
    IO.print(show_u(Tgt.parse_url("http://h/%4")))
    IO.print(show_u(Tgt.parse_url("http://h/a%41?%zz")))
    IO.print(show_u(Tgt.parse_url(("http://h/a" ++ SCon{Chr{1}, SNil{}} ++ ""))))
    IO.print(show_t(Tgt.apply(Tgt.Target{"GET", "http://h/", [Hdr.Header{"X-A", ["t"]}, Hdr.Header{"Y", ["y"]}], None{}}, [Hdr.Header{"X-A", ["g"]}, Hdr.Header{"Z", ["z"]}], Some{"gb"})))
    IO.print(show_t(Tgt.apply(Tgt.Target{"GET", "http://h/", [], Some{"own"}}, [], Some{"gb"})))

#|3
#|GET http://127.0.0.1:8080/a?b=c|X-A=1,X-A=2|
#|POST http://localhost/x||@tests/golden/body.txt
#|PUT http://h:1/||
#|1
#|bad method: get
#|1
#|bad target: GET
#|1
#|bad URL: foo, parse "foo": invalid URI for request
#|1
#|bad URL: :foo, parse ":foo": missing protocol scheme
#|1
#|bad URL: http://x/%zz, parse "http://x/%zz": invalid URL escape "%zz"
#|1
#|bad header: X-A
#|1
#|bad header: X-A:
#|1
#|bad header: : v
#|1
#|GET http://x/|X-B=v : w|
#|1
#|GET http://x/|POST http=//y/,X-A=1,X-B=2|
#|1
#|bad method: X-A:
#|2
#|GET http://x/||@tests/golden/body.txt
#|HEAD http://z/||
#|1
#|bad URL: y, parse "y": invalid URI for request
#|1
#|bad method: G1T
#|0
#|0
#|1
#|GET /relative||
#|1
#|GET mailto:x||
#|1
#|GET http://x/|X-A=2,x-a=1,x-a=3|
#|Done http h None /
#|Done http h Some 8080 /a/b?c=d
#|Done http 127.0.0.1 Some 80 /?x
#|Done http h None /p
#|Fail https is not supported
#|Fail unsupported protocol scheme "ftp"
#|Fail unsupported protocol scheme ""
#|Fail http: no Host in request URL
#|Fail invalid host "a b"
#|Fail invalid port ":0" after host
#|Fail invalid port ":65536" after host
#|Fail invalid port ":8x" after host
#|Fail invalid URL escape "%4"
#|Done http h None /a%41?%zz
#|Fail net/url: invalid control character in URL
#|GET http://h/|X-A=g,X-A=t,Y=y,Z=z|@gb
#|GET http://h/||@own

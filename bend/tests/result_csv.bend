# Results in CSV against Go (golden/results.csv, from scripts/gen/results):
# every record decodes, and re-encoding them gives Go's bytes back; then
# records Go (NewCSVDecoder) rejects or reads specially, with its verdicts.
import Base
import ../lib/hit.bend as Hit
import ../lib/sys.bend as Sys
import ../lib/b64.bend as B64

def encode_all(hs: List<&2, Hit.Hit>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, rest}:
      Hit.to_csv(h) ++ encode_all(rest)

def seqs(hs: List<&2, Hit.Hit>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{h, rest}:
      Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
      Nat.show(seq) ++ " " ++ Nat.show(code) ++ "\n" ++ seqs(rest)

def check(+golden: String, m: Maybe<&2, List<&2, Hit.Hit>>) -> String:
  match m:
    case None{}:
      "None\n"
    case Some{+hs}:
      Bool.show(String.eq(encode_all(hs), golden)) ++ "\n" ++ seqs(hs)

def run(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{+s}:
      check(s, Hit.decode_all(s))
    case Fail{e}:
      "no golden\n"

# a record decoded: seq, code, and the headers as JSON; or None
def brief(m: Maybe<&1, Hit.Hit & String>) -> String:
  match m:
    case None{}:
      "None"
    case Some{(h, r)}:
      Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
      Nat.show(seq) ++ " " ++ Nat.show(code) ++ " " ++ Hit.json_hdrs_of(hdrs)

# a record whose header column is the base64 of hb
def with_hdrs(+hb: String) -> String:
  brief(Hit.decode("1,200,3,4,5,,,a,7,GET,http://x/," ++ B64.encode(hb) ++ "\n"))

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/results.csv")
    Sys.Out.write(run(r))
    IO.print(brief(Hit.decode("1,2,3,4,5,e,,a,6,GET,http://x/\n")))
    IO.print(brief(Hit.decode("1,2,3,4,5,e,,a,6,GET,http://x/,,\n")))
    IO.print(brief(Hit.decode("1,2,3,4,5,e,,a,281474976710654,GET,http://x/,\n")))
    IO.print(brief(Hit.decode("1,2,3,4,5,e,,a,281474976710655,GET,http://x/,\n")))
    IO.print(brief(Hit.decode("1,2,3,4,5,e,,a,281474976710656,GET,http://x/,\n")))
    IO.print(brief(Hit.decode("1,2,3,4,5,e,,a,99999999999999999999,GET,http://x/,\n")))
    IO.print(brief(Hit.decode("1,2,3,4,5,e,,a,0000000000000000000001,GET,http://x/,\n")))
    IO.print(brief(Hit.decode("1,65536,3,4,5,e,,a,6,GET,http://x/,\n")))
    IO.print(brief(Hit.decode("-5,200,3,4,5,e,,a,6,GET,http://x/,\n")))
    IO.print(brief(Hit.decode("1,200,3,4,5,e,@@@@,a,6,GET,http://x/,\n")))
    IO.print(brief(Hit.decode("1, 200, 3,4,5, e,,a,6,GET,http://x/,\n")))
    IO.print(with_hdrs("B: 3\r\nA: 1\r\na: 2\r\n\r\n"))
    IO.print(with_hdrs("A: 1\r\n  2 \r\n\t3\r\n\r\n"))
    IO.print(with_hdrs("x y: 1\r\n\r\n"))
    IO.print(with_hdrs("A:1\n\nignored"))
    IO.print(with_hdrs("A: 1\r\n"))
    IO.print(with_hdrs(" A: 1\r\n\r\n"))
    IO.print(with_hdrs("A 1\r\n\r\n"))
    IO.print(with_hdrs("A: 1\r2\r\n\r\n"))
    IO.print(with_hdrs(": 1\r\n\r\n"))
    IO.print(with_hdrs("A(: 1\r\n\r\n"))

#|True
#|0 200
#|1 0
#|2 500
#|3 200
#|4294967296 404
#|5 302
#|None
#|None
#|281474976710654 2 null
#|None
#|None
#|None
#|1 2 null
#|None
#|None
#|None
#|6 200 null
#|7 200 {"A":["1","2"],"B":["3"]}
#|7 200 {"A":["1 2 3"]}
#|7 200 {"x y":["1"]}
#|7 200 {"A":["1"]}
#|None
#|None
#|None
#|None
#|None
#|None

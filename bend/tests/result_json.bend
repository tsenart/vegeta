# Results in JSON against Go (golden/results.json, from scripts/gen/results):
# every record decodes, and re-encoding them gives Go's bytes back; then
# lines Go (NewJSONDecoder) reads or rejects, with its verdicts (a missing
# timestamp is the Unix epoch here, Go's zero time there).
import Base
import ../lib/hit.bend as Hit
import ../lib/sys.bend as Sys
import ../lib/civil.bend as Civil

def encode_all(hs: List<&2, Hit.Hit>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, rest}:
      Hit.to_json(h) ++ encode_all(rest)

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

# a record decoded: seq, code, timestamp, body and headers; or None
def brief(m: Maybe<&1, Hit.Hit & String>) -> String:
  match m:
    case None{}:
      "None"
    case Some{(h, r)}:
      Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
      Nat.show(seq) ++ " " ++ Nat.show(code) ++ " " ++ Civil.rfc3339(ts) ++ " " ++ Hit.json_body(body) ++ " " ++ url ++ " " ++ Hit.json_hdrs_of(hdrs)

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/results.json")
    Sys.Out.write(run(r))
    IO.print(brief(Hit.decode("{\"url\":\"u\",\"seq\":3,\"x\":{\"a\":[1,\"}]\",{\"b\":null}],\"c\":true},\"code\":200,\"y\":-1.5e3,\"body\":null,\"attack\":null,\"timestamp\":\"2020-01-02T03:04:05.5+05:30\",\"headers\":{\"b\":[\"1\"],\"b\":[\"2\",\"3\"]}}\n")))
    IO.print(brief(Hit.decode("{ \"seq\" : 1 , \"body\" : \"\" } \r\n")))
    IO.print(brief(Hit.decode("{\"seq\":1} x\n")))
    IO.print(brief(Hit.decode("{\"seq\":1,}\n")))
    IO.print(brief(Hit.decode("{\"seq\":1.5}\n")))
    IO.print(brief(Hit.decode("{\"code\":70000}\n")))
    IO.print(brief(Hit.decode("{\"seq\":\"1\"}\n")))
    IO.print(brief(Hit.decode("{\"body\":\"@\"}\n")))
    IO.print(brief(Hit.decode("{\"timestamp\":\"bad\"}\n")))
    IO.print(brief(Hit.decode("{\"headers\":{\"a\":[\"x\",]}}\n")))

#|True
#|0 200
#|1 0
#|2 500
#|3 200
#|4294967296 404
#|5 302
#|3 200 2020-01-02T03:04:05.5+05:30 null u {"b":["2","3"]}
#|1 0 1970-01-01T00:00:00Z ""  null
#|None
#|None
#|None
#|None
#|None
#|None
#|None
#|None

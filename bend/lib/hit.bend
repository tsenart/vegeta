# A Vegeta result (Go's vegeta.Result) and its CSV/JSON codecs. STUB.
import Base
import ./civil.bend as Civil
import ./hdr.bend as Hdr

type Hit is Data:
  Hit{attack: String, seq: Nat, code: Nat, ts: Civil.Time, latency: Nat,
      bytes_out: Nat, bytes_in: Nat, error: String, body: Maybe<&2, String>,
      method: String, url: String, headers: Maybe<&2, List<&2, Hdr.Header>>}

def to_csv(+h: Hit) -> String:
  ""

def to_json(+h: Hit) -> String:
  ""

def of_csv(s: String) -> Maybe<&1, Hit & String>:
  None{}

def of_json(s: String) -> Maybe<&1, Hit & String>:
  None{}

# picks JSON when the first non-blank character is '{', CSV otherwise
def decode(s: String) -> Maybe<&1, Hit & String>:
  None{}

def decode_all(s: String) -> Maybe<&2, List<&2, Hit>>:
  None{}

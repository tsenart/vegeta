# HTTP/1.1: request text and an incremental response parser. STUB.
import Base
import ./hdr.bend as Hdr
import ./target.bend as Tgt

type Resp is Data:
  Resp{code: Nat, status: String, headers: List<&2, Hdr.Header>, body: String, body_len: Nat, keep: Bool}

type Parse is Data:
  Parse{seen: String, max_body: Maybe<&2, Nat>, head: Bool, closed: Bool}

def start(mb: Maybe<&2, Nat>, head: Bool) -> Parse:
  Parse{"", mb, head, False{}}

def feed(+p: Parse, s: String) -> Parse:
  p

def eof(+p: Parse) -> Parse:
  p

def done(+p: Parse) -> Maybe<&1, Result<&1, &1, String, Resp & String>>:
  None{}

def request(+t: Tgt.Target, +u: Tgt.Url, +body: String, +seq: Nat, +name: String, ka: Bool) -> String:
  ""

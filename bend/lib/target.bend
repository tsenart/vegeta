# URLs and the http targets format. STUB.
import Base
import ./hdr.bend as Hdr

type Url is Data:
  Url{scheme: String, host: String, port: Nat, path: String}

type Target is Data:
  Target{method: String, url: String, headers: List<&2, Hdr.Header>, body: Maybe<&2, String>}

def parse_url(s: String) -> Result<&2, &2, String, Url>:
  Fail{"stub"}

def show_url(+u: Url) -> String:
  ""

def parse_all(s: String) -> Result<&2, &2, String, List<&2, Target>>:
  Fail{"stub"}

def show_all(+ts: List<&2, Target>) -> String:
  ""

# the target as attacked: the global headers first, then the target's own
# (same name: values appended), and the global body unless the target has @file
def apply(+t: Target, +hs: List<&2, Hdr.Header>, +body: Maybe<&2, String>) -> Target:
  t

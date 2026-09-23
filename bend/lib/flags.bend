# Command-line flags for attack and report, with Go Vegeta's names and defaults.
# A timeout of None is Go's default (30s), applied by the shell: 30s is a
# closed number too big for the checker to state. STUB.
import Base
import ./pacer.bend as Pace
import ./hdr.bend as Hdr

type Attack is Data:
  Attack{rate: Pace.Rate, duration: Nat, targets: String, format: String, output: String,
         name: String, workers: Nat, max_workers: Maybe<&2, Nat>, timeout: Maybe<&2, Nat>,
         headers: List<&2, Hdr.Header>, body: Maybe<&2, String>, keepalive: Bool,
         max_body: Maybe<&2, Nat>, redirects: Maybe<&2, Nat>, encoding: String}

type RKind is Data:
  AsText{}
  AsJson{buckets: List<&2, Nat>}
  AsHist{buckets: List<&2, Nat>}

type Report is Data:
  Report{kind: RKind, output: String, files: List<&2, String>}

def parse_attack(args: List<&2, String>) -> Result<&2, &2, String, Attack>:
  Fail{"stub"}

def parse_report(args: List<&2, String>) -> Result<&2, &2, String, Report>:
  Fail{"stub"}

# Report metrics: an accumulator of hits, mergeable, closed into a Summary. STUB.
import Base
import ./big.bend as Big
import ./f64.bend as F64
import ./civil.bend as Civil
import ./hit.bend as Hit

type Acc is Data:
  Acc{buckets: List<&2, Nat>, hits: List<&2, Hit.Hit>}

type Summary is Data:
  Summary{requests: Nat, success: Nat,
          codes: List<&2, Sigma<&2, &2, Nat, _ => Nat>>, errors: List<&2, String>,
          lat_total: Big.Big, lat_mean: Nat, lat_min: Nat, lat_max: Nat,
          p50: Nat, p90: Nat, p95: Nat, p99: Nat,
          bytes_in: Big.Big, bytes_out: Big.Big, in_mean: F64.F64, out_mean: F64.F64,
          rate: F64.F64, throughput: F64.F64, ratio: F64.F64,
          earliest: Maybe<&2, Civil.Time>, latest: Maybe<&2, Civil.Time>, end: Maybe<&2, Civil.Time>,
          duration: Nat, wait: Nat, buckets: List<&2, Nat>, hist: List<&2, Nat>}

def empty(bs: List<&2, Nat>) -> Acc:
  Acc{bs, []}

def add(+a: Acc, +h: Hit.Hit) -> Acc:
  a

def merge(+a: Acc, +b: Acc) -> Acc:
  a

def close(+a: Acc) -> Summary:
  Summary{0n, 0n, [], [], Big.of(0n), 0n, 0n, 0n, 0n, 0n, 0n, 0n,
          Big.of(0n), Big.of(0n), F64.zero(), F64.zero(), F64.zero(), F64.zero(), F64.zero(),
          None{}, None{}, None{}, 0n, 0n, [], []}

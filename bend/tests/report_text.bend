# Rep.text against Go's NewTextReporter (golden/report-<case>.text, from
# scripts/gen/report, TZ=UTC, read back through Hit.decode_all), with Go's percentile estimates and error
# order put in our summary (Go's are t-digest estimates and first-seen
# order); then our exact nearest-rank percentiles (golden/report-<case>.pct)
# and sorted error set on their own.
import Base
import ../lib/dec.bend as Dec
import ../lib/big.bend as Big
import ../lib/f64.bend as F64
import ../lib/civil.bend as Civil
import ../lib/hit.bend as Hit
import ../lib/metrics.bend as Met
import ../lib/report.bend as Rep
import ../lib/sys.bend as Sys

def ms(+n: Nat) -> Nat:
  Nat.mul(n, 1000000n)

def h70() -> Nat:
  Nat.mul(252000n, 1000000000n)

def path(+c: String) -> String:
  "../../tests/golden/report-" ++ c ++ ".csv"

def or_fail(~f: List<&2, Hit.Hit> -> String, m: Maybe<&2, List<&2, Hit.Hit>>) -> String:
  match m:
    case None{}:
      "decode failed\n"
    case Some{hs}:
      f(hs)

# golden/report-<c>.csv, decoded (as Go's report reads it), then reported
def with(~f: List<&2, Hit.Hit> -> String, +c: String) -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, String> <- Sys.Files.read(path(c))
    Sys.Out.write(or_fail(~f, Hit.decode_all(Result.default(&1, &1, U32 & String, String, r, ""))))

def adds(hs: List<&2, Hit.Hit>, +a: Met.Acc) -> Met.Acc:
  match hs:
    case Nil{}:
      a
    case Con{+h, +rest}:
      adds(rest, Met.add(a, h))

def summary(+bs: List<&2, Nat>, +hs: List<&2, Hit.Hit>) -> Met.Summary:
  Met.close(adds(hs, Met.empty(bs)))

# Go's t-digest percentile estimates and first-seen error order in place
# of our exact ones and sorted set (they are checked on their own)
def as_go(+s: Met.Summary, +q50: Nat, +q90: Nat, +q95: Nat, +q99: Nat, +ges: List<&2, String>) -> Met.Summary:
  Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} = s
  Met.Summary{req, ok, cs, ges, lt, lm, lmin, lmax, q50, q90, q95, q99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h}

def ours(+name: String, +s: Met.Summary) -> String:
  Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} = s
  name ++ " " ++ Dec.show(p50) ++ " " ++ Dec.show(p90) ++ " " ++ Dec.show(p95) ++ " " ++ Dec.show(p99) ++ " [" ++ String.join(es, "|") ++ "]\n"

def go_errs() -> List<&2, String>:
  ["500 Internal Server Error", "Get \"http://h/\": EOF", "503 Service Unavailable"]


def main() -> IO(Unit):
  do IO<Unit>:
    with(~(hs => Rep.text(as_go(summary([], hs), 0n, 0n, 0n, 0n, []))), "empty")
    with(~(hs => Rep.text(as_go(summary([], hs), ms(3n), ms(3n), ms(3n), ms(3n), []))), "single")
    with(~(hs => Rep.text(as_go(summary([], hs), Nat.add(ms(50n), 500000n), Nat.add(ms(90n), 500000n), Nat.add(ms(95n), 500000n), Nat.add(ms(99n), 500000n), go_errs()))), "mixed")
    with(~(hs => Rep.text(as_go(summary([], hs), h70(), h70(), h70(), h70(), []))), "huge-sums")
    with(~(hs => Rep.text(as_go(summary([], hs), 1500000n, ms(2n), ms(2n), ms(2n), []))), "two-zones")
    with(~(hs => ours("empty", summary([], hs))), "empty")
    with(~(hs => ours("single", summary([], hs))), "single")
    with(~(hs => ours("mixed", summary([], hs))), "mixed")
    with(~(hs => ours("huge-sums", summary([], hs))), "huge-sums")
    with(~(hs => ours("two-zones", summary([], hs))), "two-zones")
#|Requests      [total, rate, throughput]         0, 0.00, 0.00
#|Duration      [total, attack, wait]             0s, 0s, 0s
#|Latencies     [min, mean, 50, 90, 95, 99, max]  0s, 0s, 0s, 0s, 0s, 0s, 0s
#|Bytes In      [total, mean]                     0, 0.00
#|Bytes Out     [total, mean]                     0, 0.00
#|Success       [ratio]                           0.00%
#|Status Codes  [code:count]                      
#|Error Set:
#|Requests      [total, rate, throughput]         1, 1.00, 1.00
#|Duration      [total, attack, wait]             3ms, 0s, 3ms
#|Latencies     [min, mean, 50, 90, 95, 99, max]  3ms, 3ms, 3ms, 3ms, 3ms, 3ms, 3ms
#|Bytes In      [total, mean]                     10, 10.00
#|Bytes Out     [total, mean]                     5, 5.00
#|Success       [ratio]                           100.00%
#|Status Codes  [code:count]                      200:1  
#|Error Set:
#|Requests      [total, rate, throughput]         100, 101.01, 36.70
#|Duration      [total, attack, wait]             1.09s, 990ms, 100ms
#|Latencies     [min, mean, 50, 90, 95, 99, max]  1ms, 50.5ms, 50.5ms, 90.5ms, 95.5ms, 99.5ms, 100ms
#|Bytes In      [total, mean]                     14850, 148.50
#|Bytes Out     [total, mean]                     700, 7.00
#|Success       [ratio]                           40.00%
#|Status Codes  [code:count]                      0:20  200:40  500:20  503:20  
#|Error Set:
#|500 Internal Server Error
#|Get "http://h/": EOF
#|503 Service Unavailable
#|Requests      [total, rate, throughput]         3, 1.50, 0.00
#|Duration      [total, attack, wait]             70h0m0s, 2s, 70h0m0s
#|Latencies     [min, mean, 50, 90, 95, 99, max]  70h0m0s, 70h0m0s, 70h0m0s, 70h0m0s, 70h0m0s, 70h0m0s, 70h0m0s
#|Bytes In      [total, mean]                     422212465065984, 140737488355328.00
#|Bytes Out     [total, mean]                     422212465065984, 140737488355328.00
#|Success       [ratio]                           100.00%
#|Status Codes  [code:count]                      200:3  
#|Error Set:
#|Requests      [total, rate, throughput]         2, 1.33, 1.33
#|Duration      [total, attack, wait]             1.502s, 1.5s, 2ms
#|Latencies     [min, mean, 50, 90, 95, 99, max]  1ms, 1.5ms, 1.5ms, 2ms, 2ms, 2ms, 2ms
#|Bytes In      [total, mean]                     0, 0.00
#|Bytes Out     [total, mean]                     0, 0.00
#|Success       [ratio]                           100.00%
#|Status Codes  [code:count]                      200:1  204:1  
#|Error Set:
#|empty 0 0 0 0 []
#|single 3000000 3000000 3000000 3000000 []
#|mixed 50000000 90000000 95000000 99000000 [500 Internal Server Error|503 Service Unavailable|Get "http://h/": EOF]
#|huge-sums 252000000000000 252000000000000 252000000000000 252000000000000 []
#|two-zones 1000000 2000000 2000000 2000000 []

# Rep.hist against Go's NewHistogramReporter (golden/report-<case>.hist,
# from scripts/gen/report: buckets 0, 1ms, 10ms, 100ms; the results read
# back through Hit.decode_all), then more bucket
# layouts over the mixed case's latencies against Go (Go 1.26, run by
# hand): a first bound above 0 (lower latencies fall in the last bucket),
# one bucket, bounds out of order, a bound in hours.
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
def bs() -> List<&2, Nat>:
  [0n, ms(1n), ms(10n), ms(100n)]

def main() -> IO(Unit):
  do IO<Unit>:
    with(~(hs => Rep.hist(summary(bs(), hs))), "single")
    with(~(hs => Rep.hist(summary(bs(), hs))), "mixed")
    with(~(hs => Rep.hist(summary(bs(), hs))), "huge-sums")
    with(~(hs => Rep.hist(summary(bs(), hs))), "two-zones")
    with(~(hs => Rep.hist(summary([ms(5n), ms(20n), ms(50n)], hs))), "mixed")
    with(~(hs => Rep.hist(summary([0n], hs))), "mixed")
    with(~(hs => Rep.hist(summary([ms(10n), ms(1n)], hs))), "mixed")
    with(~(hs => Rep.hist(summary([0n, 1500000n, Nat.mul(7200n, 1000000000n)], hs))), "mixed")
#|Bucket           #  %        Histogram
#|[0s,     1ms]    0  0.00%    
#|[1ms,    10ms]   1  100.00%  ###########################################################################
#|[10ms,   100ms]  0  0.00%    
#|[100ms,  +Inf]   0  0.00%    
#|Bucket           #   %       Histogram
#|[0s,     1ms]    0   0.00%   
#|[1ms,    10ms]   9   9.00%   ######
#|[10ms,   100ms]  90  90.00%  ###################################################################
#|[100ms,  +Inf]   1   1.00%   
#|Bucket           #  %        Histogram
#|[0s,     1ms]    0  0.00%    
#|[1ms,    10ms]   0  0.00%    
#|[10ms,   100ms]  0  0.00%    
#|[100ms,  +Inf]   3  100.00%  ###########################################################################
#|Bucket           #  %        Histogram
#|[0s,     1ms]    0  0.00%    
#|[1ms,    10ms]   2  100.00%  ###########################################################################
#|[10ms,   100ms]  0  0.00%    
#|[100ms,  +Inf]   0  0.00%    
#|Bucket         #   %       Histogram
#|[5ms,   20ms]  15  15.00%  ###########
#|[20ms,  50ms]  30  30.00%  ######################
#|[50ms,  +Inf]  55  55.00%  #########################################
#|Bucket         #    %        Histogram
#|[0s,    +Inf]  100  100.00%  ###########################################################################
#|Bucket         #    %        Histogram
#|[10ms,  1ms]   0    0.00%    
#|[1ms,   +Inf]  100  100.00%  ###########################################################################
#|Bucket             #   %       Histogram
#|[0s,      1.5ms]   1   1.00%   
#|[1.5ms,   2h0m0s]  99  99.00%  ##########################################################################
#|[2h0m0s,  +Inf]    0   0.00%   

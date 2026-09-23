# Rep.json against Go's NewJSONReporter (golden/report-<case>.json, from
# scripts/gen/report, TZ=UTC, read back through Hit.decode_all), with Go's percentile estimates and error
# order put in our summary (Go's are t-digest estimates and first-seen
# order); then our exact nearest-rank percentiles (golden/report-<case>.pct)
# and sorted error set on their own; then buckets, zones and escapes,
# against Go's reporter with a histogram and results in other zones
# (Go 1.26, run by hand).
import Base
import ../lib/dec.bend as Dec
import ../lib/big.bend as Big
import ../lib/f64.bend as F64
import ../lib/civil.bend as Civil
import ../lib/hit.bend as Hit
import ../lib/metrics.bend as Met
import ../lib/report.bend as Rep
import ../lib/sys.bend as Sys

def t0() -> Nat:
  1790157600n

def hit(+code: Nat, +s: Nat, +ns: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +err: String) -> Hit.Hit:
  Hit.Hit{"", 0n, code, Civil.Time{s, ns, 86400n}, lat, bo, bi, err, Some{""}, "GET", "http://h/", None{}}

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


def str1(+k: U32) -> String:
  SCon{Chr{k}, SNil{}}

def esc_err() -> String:
  "a" ++ str1(8) ++ "b" ++ str1(12) ++ "c<d>&e" ++ str1(226) ++ str1(128) ++ str1(168) ++ "f" ++ str1(255) ++ "g\th\n\"\\"

def zoned() -> List<&2, Hit.Hit>:
  [hit(200n, t0(), 0n, 1500000n, 0n, 0n, esc_err()), hit(301n, t0(), 250000000n, ms(3n), 0n, 0n, str1(1))]

def zoned_json(+off: Nat) -> String:
  Rep.json(as_go(summary([], zoned()), 2250000n, ms(3n), ms(3n), ms(3n), [esc_err(), str1(1)]), Rep.Zones{off, off, off})

def main() -> IO(Unit):
  do IO<Unit>:
    with(~(hs => Rep.json(as_go(summary([], hs), 0n, 0n, 0n, 0n, []), Rep.Zones{86400n, 86400n, 86400n})), "empty")
    with(~(hs => Rep.json(as_go(summary([], hs), ms(3n), ms(3n), ms(3n), ms(3n), []), Rep.Zones{86400n, 86400n, 86400n})), "single")
    with(~(hs => Rep.json(as_go(summary([], hs), Nat.add(ms(50n), 500000n), Nat.add(ms(90n), 500000n), Nat.add(ms(95n), 500000n), Nat.add(ms(99n), 500000n), go_errs()), Rep.Zones{86400n, 86400n, 86400n})), "mixed")
    with(~(hs => Rep.json(as_go(summary([], hs), h70(), h70(), h70(), h70(), []), Rep.Zones{86400n, 86400n, 86400n})), "huge-sums")
    with(~(hs => Rep.json(as_go(summary([], hs), 1500000n, ms(2n), ms(2n), ms(2n), []), Rep.Zones{86400n, 86400n, 86400n})), "two-zones")
    with(~(hs => ours("empty", summary([], hs))), "empty")
    with(~(hs => ours("single", summary([], hs))), "single")
    with(~(hs => ours("mixed", summary([], hs))), "mixed")
    with(~(hs => ours("huge-sums", summary([], hs))), "huge-sums")
    with(~(hs => ours("two-zones", summary([], hs))), "two-zones")
    with(~(hs => Rep.json(as_go(summary([0n, ms(1n), ms(10n), ms(100n)], hs), Nat.add(ms(50n), 500000n), Nat.add(ms(90n), 500000n), Nat.add(ms(95n), 500000n), Nat.add(ms(99n), 500000n), go_errs()), Rep.Zones{86400n, 86400n, 86400n})), "mixed")
    Sys.Out.write(zoned_json(93600n))
    Sys.Out.write(zoned_json(66600n))
#|{"latencies":{"total":0,"mean":0,"50th":0,"90th":0,"95th":0,"99th":0,"max":0,"min":0},"bytes_in":{"total":0,"mean":0},"bytes_out":{"total":0,"mean":0},"earliest":"0001-01-01T00:00:00Z","latest":"0001-01-01T00:00:00Z","end":"0001-01-01T00:00:00Z","duration":0,"wait":0,"requests":0,"rate":0,"throughput":0,"success":0,"status_codes":{},"errors":[]}
#|{"latencies":{"total":3000000,"mean":3000000,"50th":3000000,"90th":3000000,"95th":3000000,"99th":3000000,"max":3000000,"min":3000000},"bytes_in":{"total":10,"mean":10},"bytes_out":{"total":5,"mean":5},"earliest":"2026-09-23T10:00:00Z","latest":"2026-09-23T10:00:00Z","end":"2026-09-23T10:00:00.003Z","duration":0,"wait":3000000,"requests":1,"rate":1,"throughput":1,"success":1,"status_codes":{"200":1},"errors":[]}
#|{"latencies":{"total":5050000000,"mean":50500000,"50th":50500000,"90th":90500000,"95th":95500000,"99th":99500000,"max":100000000,"min":1000000},"bytes_in":{"total":14850,"mean":148.5},"bytes_out":{"total":700,"mean":7},"earliest":"2026-09-23T10:00:00Z","latest":"2026-09-23T10:00:00.99Z","end":"2026-09-23T10:00:01.09Z","duration":990000000,"wait":100000000,"requests":100,"rate":101.01010101010101,"throughput":36.69724770642202,"success":0.4,"status_codes":{"0":20,"200":40,"500":20,"503":20},"errors":["500 Internal Server Error","Get \"http://h/\": EOF","503 Service Unavailable"]}
#|{"latencies":{"total":756000000000000,"mean":252000000000000,"50th":252000000000000,"90th":252000000000000,"95th":252000000000000,"99th":252000000000000,"max":252000000000000,"min":252000000000000},"bytes_in":{"total":422212465065984,"mean":140737488355328},"bytes_out":{"total":422212465065984,"mean":140737488355328},"earliest":"2026-09-23T10:00:00Z","latest":"2026-09-23T10:00:02Z","end":"2026-09-26T08:00:02Z","duration":2000000000,"wait":252000000000000,"requests":3,"rate":1.5,"throughput":0.000011904667423274418,"success":1,"status_codes":{"200":3},"errors":[]}
#|{"latencies":{"total":3000000,"mean":1500000,"50th":1500000,"90th":2000000,"95th":2000000,"99th":2000000,"max":2000000,"min":1000000},"bytes_in":{"total":0,"mean":0},"bytes_out":{"total":0,"mean":0},"earliest":"2026-09-23T10:00:00Z","latest":"2026-09-23T10:00:01.5Z","end":"2026-09-23T10:00:01.502Z","duration":1500000000,"wait":2000000,"requests":2,"rate":1.3333333333333333,"throughput":1.3315579227696406,"success":1,"status_codes":{"200":1,"204":1},"errors":[]}
#|empty 0 0 0 0 []
#|single 3000000 3000000 3000000 3000000 []
#|mixed 50000000 90000000 95000000 99000000 [500 Internal Server Error|503 Service Unavailable|Get "http://h/": EOF]
#|huge-sums 252000000000000 252000000000000 252000000000000 252000000000000 []
#|two-zones 1000000 2000000 2000000 2000000 []
#|{"latencies":{"total":5050000000,"mean":50500000,"50th":50500000,"90th":90500000,"95th":95500000,"99th":99500000,"max":100000000,"min":1000000},"buckets":{"0":0,"1000000":9,"10000000":90,"100000000":1},"bytes_in":{"total":14850,"mean":148.5},"bytes_out":{"total":700,"mean":7},"earliest":"2026-09-23T10:00:00Z","latest":"2026-09-23T10:00:00.99Z","end":"2026-09-23T10:00:01.09Z","duration":990000000,"wait":100000000,"requests":100,"rate":101.01010101010101,"throughput":36.69724770642202,"success":0.4,"status_codes":{"0":20,"200":40,"500":20,"503":20},"errors":["500 Internal Server Error","Get \"http://h/\": EOF","503 Service Unavailable"]}
#|{"latencies":{"total":4500000,"mean":2250000,"50th":2250000,"90th":3000000,"95th":3000000,"99th":3000000,"max":3000000,"min":1500000},"bytes_in":{"total":0,"mean":0},"bytes_out":{"total":0,"mean":0},"earliest":"2026-09-23T12:00:00+02:00","latest":"2026-09-23T12:00:00.25+02:00","end":"2026-09-23T12:00:00.253+02:00","duration":250000000,"wait":3000000,"requests":2,"rate":8,"throughput":7.905138339920948,"success":1,"status_codes":{"200":1,"301":1},"errors":["a\bb\fc\u003cd\u003e\u0026e\u2028f\ufffdg\th\n\"\\","\u0001"]}
#|{"latencies":{"total":4500000,"mean":2250000,"50th":2250000,"90th":3000000,"95th":3000000,"99th":3000000,"max":3000000,"min":1500000},"bytes_in":{"total":0,"mean":0},"bytes_out":{"total":0,"mean":0},"earliest":"2026-09-23T04:30:00-05:30","latest":"2026-09-23T04:30:00.25-05:30","end":"2026-09-23T04:30:00.253-05:30","duration":250000000,"wait":3000000,"requests":2,"rate":8,"throughput":7.905138339920948,"success":1,"status_codes":{"200":1,"301":1},"errors":["a\bb\fc\u003cd\u003e\u0026e\u2028f\ufffdg\th\n\"\\","\u0001"]}

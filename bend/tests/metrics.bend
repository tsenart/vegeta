# Metrics against Go (golden/results.metrics, from scripts/gen/results:
# Go's Metrics over golden/results.csv, buckets [0, 1ms, 10ms], with p50
# as exact nearest rank), then the accumulator built in other shapes
# (met_build), sums past 2^48 (met_totals) and 200,000 results (to catch
# anything quadratic).
#
# The results are those of golden/results.csv, built here rather than
# decoded: the sixth one's timestamp, 999ns after the epoch, makes the
# attack span 56 years, past what a runtime Nat (Summary.duration) holds,
# so close would abort. Here it is 999ns into the first one's second;
# nothing results.metrics prints depends on it.
import Base
import ../lib/big.bend as Big
import ../lib/dec.bend as Dec
import ../lib/f64.bend as F64
import ../lib/civil.bend as Civil
import ../lib/hit.bend as Hit
import ../lib/metrics.bend as Met

def hit(+code: Nat, +s: Nat, +ns: Nat, +lat: Nat, +bo: Nat, +bi: Nat, +err: String) -> Hit.Hit:
  Hit.Hit{"a", 0n, code, Civil.Time{s, ns, 86400n}, lat, bo, bi, err, None{}, "GET", "http://h/", None{}}

def golden() -> List<&2, Hit.Hit>:
  [hit(200n, 1790129387n, 935870875n, 1500000n, 0n, 2n, ""),
   hit(0n, 1790129387n, 936870875n, 300000n, 0n, 0n, "Get \"http://127.0.0.1:1/\": dial tcp 127.0.0.1:1: connect: connection refused"),
   hit(500n, 1790129387n, 937870875n, 25000000n, 3n, 4n, "500 Internal Server Error"),
   hit(200n, 1790129387n, 938870875n, 7000000n, 0n, 0n, ""),
   hit(404n, 1790129387n, 939870875n, 999000n, 0n, 0n, "404 Not Found"),
   hit(302n, 1790129387n, 999n, 1n, 0n, 0n, "")]

def bs() -> List<&2, Nat>:
  [0n, 1000000n, 10000000n]

def codes(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{+p, +rest}:
      (k, v) = p
      "code " ++ Dec.show(k) ++ " " ++ Dec.show(v) ++ "\n" ++ codes(rest)

def errors(es: List<&2, String>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{+e, +rest}:
      "error " ++ e ++ "\n" ++ errors(rest)

def buckets(cs: List<&2, Nat>, +i: Nat) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{+c, +rest}:
      "bucket " ++ Dec.show(i) ++ " " ++ Dec.show(c) ++ "\n" ++ buckets(rest, 1n+i)

# the lines of golden/results.metrics
def go_lines(+s: Met.Summary) -> String:
  Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} = s
  "requests " ++ Dec.show(req) ++ "\nsuccess " ++ Dec.show(ok) ++ "\n" ++ codes(cs) ++ errors(es)
  ++ "p50 " ++ Dec.show(p50) ++ "\nmax " ++ Dec.show(lmax) ++ "\nmin " ++ Dec.show(lmin) ++ "\n" ++ buckets(h, 0n)

def time(+m: Maybe<&2, Civil.Time>) -> String:
  match m:
    case None{}:
      "-"
    case Some{t}:
      Civil.Time{s, ns, off} = t
      Dec.show(s) ++ "." ++ Dec.pad(9n, ns) ++ "@" ++ Dec.show(off)

def nats(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      Dec.show(x) ++ " " ++ nats(rest)

# every field
def all(+s: Met.Summary) -> String:
  Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} = s
  Dec.show(req) ++ " " ++ Dec.show(ok) ++ " [" ++ codes(cs) ++ "] [" ++ errors(es) ++ "] " ++ Big.show(lt) ++ " " ++ Dec.show(lm)
  ++ " " ++ Dec.show(lmin) ++ " " ++ Dec.show(lmax) ++ " " ++ Dec.show(p50) ++ " " ++ Dec.show(p90) ++ " " ++ Dec.show(p95) ++ " " ++ Dec.show(p99)
  ++ " " ++ Big.show(bi) ++ " " ++ Big.show(bo) ++ " " ++ F64.json(im) ++ " " ++ F64.json(om) ++ " " ++ F64.json(rate) ++ " " ++ F64.json(thr)
  ++ " " ++ F64.json(ratio) ++ " " ++ time(e) ++ " " ++ time(l) ++ " " ++ time(n) ++ " " ++ Dec.show(du) ++ " " ++ Dec.show(w)
  ++ " [" ++ nats(b) ++ "] [" ++ nats(h) ++ "]"

def adds(hs: List<&2, Hit.Hit>, +a: Met.Acc) -> Met.Acc:
  match hs:
    case Nil{}:
      a
    case Con{+h, +rest}:
      adds(rest, Met.add(a, h))

# every result on its own, merged from the right: merge(h1, merge(h2, ...))
def rmerge(hs: List<&2, Hit.Hit>, +bs: List<&2, Nat>) -> Met.Acc:
  match hs:
    case Nil{}:
      Met.empty(bs)
    case Con{+h, +rest}:
      Met.merge(Met.add(Met.empty(bs), h), rmerge(rest, bs))

def one_by_one(+hs: List<&2, Hit.Hit>) -> String:
  all(Met.close(adds(hs, Met.empty(bs()))))

def pick_code(+p: Nat) -> Nat:
  Met.pick(Nat, Nat.is_eq(Nat.mod(p, 4n), 0n), 500n, 200n)

# n results with latencies n, n-1, ..., 1 ms
def many(n: Nat, +acc: Met.Acc) -> Met.Acc:
  match n:
    case 0n:
      acc
    case 1n+(+p):
      many(p, Met.add(acc, hit(pick_code(p), 1790157600n, Nat.mul(p, 1000n), Nat.mul(1n+p, 1000000n), 1n, 3n, "")))

def big.of(+s: Met.Summary) -> String:
  Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, nn, du, w, b, h} = s
  Dec.show(req) ++ " " ++ Dec.show(ok) ++ " " ++ codes(cs) ++ Big.show(lt) ++ " " ++ Dec.show(lmin) ++ " " ++ Dec.show(lmax)
  ++ " " ++ Dec.show(p50) ++ " " ++ Dec.show(p99) ++ " " ++ nats(h)

def big(+n: Nat) -> String:
  big.of(Met.close(many(n, Met.empty(bs()))))

def huge() -> List<&2, Hit.Hit>:
  [hit(200n, 1790157600n, 0n, Nat.mul(252000n, 1000000000n), Nat.mul(131072n, 1073741824n), Nat.mul(131072n, 1073741824n), ""),
   hit(200n, 1790157601n, 0n, Nat.mul(252000n, 1000000000n), Nat.mul(131072n, 1073741824n), Nat.mul(131072n, 1073741824n), ""),
   hit(200n, 1790157602n, 0n, Nat.mul(252000n, 1000000000n), Nat.mul(131072n, 1073741824n), Nat.mul(131072n, 1073741824n), "")]

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(go_lines(Met.close(adds(golden(), Met.empty(bs())))))
    IO.print(one_by_one(golden()))
    IO.print(all(Met.close(rmerge(golden(), bs()))))
    IO.print(all(Met.close(Met.merge(adds(List.drop(&2, Hit.Hit, golden(), 3n), Met.empty(bs())), adds(List.take(&2, Hit.Hit, golden(), 3n), Met.empty(bs()))))))
    IO.print(one_by_one(List.reverse(&2, Hit.Hit, golden())))
    IO.print(all(Met.close(Met.merge(Met.empty(bs()), Met.merge(adds(golden(), Met.empty(bs())), Met.empty(bs()))))))
    IO.print(all(Met.close(Met.empty(bs()))))
    IO.print(one_by_one([hit(200n, 5n, 1500000000n, 10n, 0n, 0n, "")]))
    IO.print(all(Met.close(adds(huge(), Met.empty([])))))
    IO.print(big(200000n))
#|requests 6
#|success 3
#|code 0 1
#|code 200 2
#|code 302 1
#|code 404 1
#|code 500 1
#|error 404 Not Found
#|error 500 Internal Server Error
#|error Get "http://127.0.0.1:1/": dial tcp 127.0.0.1:1: connect: connection refused
#|p50 999000
#|max 25000000
#|min 1
#|bucket 0 3
#|bucket 1 2
#|bucket 2 1
#|
#|6 3 [code 0 1
#|code 200 2
#|code 302 1
#|code 404 1
#|code 500 1
#|] [error 404 Not Found
#|error 500 Internal Server Error
#|error Get "http://127.0.0.1:1/": dial tcp 127.0.0.1:1: connect: connection refused
#|] 34799001 5799833 1 25000000 999000 25000000 25000000 25000000 6 3 1 0.5 6.383862440123573 3.1156858001028587 0.5 1790129387.000000999@86400 1790129387.939870875@86400 1790129387.962870875@86400 939869876 23000000 [0 1000000 10000000 ] [3 2 1 ]
#|6 3 [code 0 1
#|code 200 2
#|code 302 1
#|code 404 1
#|code 500 1
#|] [error 404 Not Found
#|error 500 Internal Server Error
#|error Get "http://127.0.0.1:1/": dial tcp 127.0.0.1:1: connect: connection refused
#|] 34799001 5799833 1 25000000 999000 25000000 25000000 25000000 6 3 1 0.5 6.383862440123573 3.1156858001028587 0.5 1790129387.000000999@86400 1790129387.939870875@86400 1790129387.962870875@86400 939869876 23000000 [0 1000000 10000000 ] [3 2 1 ]
#|6 3 [code 0 1
#|code 200 2
#|code 302 1
#|code 404 1
#|code 500 1
#|] [error 404 Not Found
#|error 500 Internal Server Error
#|error Get "http://127.0.0.1:1/": dial tcp 127.0.0.1:1: connect: connection refused
#|] 34799001 5799833 1 25000000 999000 25000000 25000000 25000000 6 3 1 0.5 6.383862440123573 3.1156858001028587 0.5 1790129387.000000999@86400 1790129387.939870875@86400 1790129387.962870875@86400 939869876 23000000 [0 1000000 10000000 ] [3 2 1 ]
#|6 3 [code 0 1
#|code 200 2
#|code 302 1
#|code 404 1
#|code 500 1
#|] [error 404 Not Found
#|error 500 Internal Server Error
#|error Get "http://127.0.0.1:1/": dial tcp 127.0.0.1:1: connect: connection refused
#|] 34799001 5799833 1 25000000 999000 25000000 25000000 25000000 6 3 1 0.5 6.383862440123573 3.1156858001028587 0.5 1790129387.000000999@86400 1790129387.939870875@86400 1790129387.962870875@86400 939869876 23000000 [0 1000000 10000000 ] [3 2 1 ]
#|6 3 [code 0 1
#|code 200 2
#|code 302 1
#|code 404 1
#|code 500 1
#|] [error 404 Not Found
#|error 500 Internal Server Error
#|error Get "http://127.0.0.1:1/": dial tcp 127.0.0.1:1: connect: connection refused
#|] 34799001 5799833 1 25000000 999000 25000000 25000000 25000000 6 3 1 0.5 6.383862440123573 3.1156858001028587 0.5 1790129387.000000999@86400 1790129387.939870875@86400 1790129387.962870875@86400 939869876 23000000 [0 1000000 10000000 ] [3 2 1 ]
#|0 0 [] [] 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 - - - 0 0 [0 1000000 10000000 ] [0 0 0 ]
#|1 1 [code 200 1
#|] [] 10 10 10 10 10 10 10 10 0 0 0 0 1 1 1 6.500000000@86400 6.500000000@86400 6.500000010@86400 0 10 [0 1000000 10000000 ] [1 0 0 ]
#|3 3 [code 200 3
#|] [] 756000000000000 252000000000000 252000000000000 252000000000000 252000000000000 252000000000000 252000000000000 252000000000000 422212465065984 422212465065984 140737488355328 140737488355328 1.5 0.000011904667423274418 1 1790157600.000000000@86400 1790157602.000000000@86400 1790409602.000000000@86400 2000000000 252000000000000 [] []
#|200000 150000 code 200 150000
#|code 500 50000
#|20000100000000000 1000000 200000000000 100000000000 198000000000 0 9 199991 

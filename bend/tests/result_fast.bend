# The report's fast decoder (lib/rdec.bend) against Hit.decode_all: on
# the goldens and on records in and just out of its fast shapes, the same
# hits (every field) or the same None, and the same metrics
# as folding Met.add over Hit.decode_all (compared as the text and
# histogram reports), also read as the report reads a piece (its lines:
# add_lines, and the fast path alone then add_lines from where it
# stopped). Each check prints ok, or both sides. Then whether
# the fast path itself reads a few records (Go's shapes) or leaves them.
# check2: a record cut by the end of a piece (at a raw LF in it) is read
# whole once the next piece comes, as in the input as one (a piece ends
# with a LF, but for the last).
import Base
import ../lib/sys.bend as Sys
import ../lib/hit.bend as Hit
import ../lib/metrics.bend as Met
import ../lib/report.bend as Rep
import ../lib/rdec.bend as RD
import ../lib/hdr.bend as Hdr
import ../lib/civil.bend as Civil

def raw(ks: List<&2, U32>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{k, rest}:
      SCon{Chr{k}, raw(rest)}

def vals(vs: List<&2, String>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{v, rest}:
      "[" ++ v ++ "]" ++ vals(rest)

def hdrs(hs: List<&2, Hdr.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{h, rest}:
      Hdr.Header{k, vs} = h
      k ++ "=" ++ vals(vs) ++ ";" ++ hdrs(rest)

def hdrs_of(m: Maybe<&2, List<&2, Hdr.Header>>) -> String:
  match m:
    case None{}:
      "null"
    case Some{hs}:
      "{" ++ hdrs(hs) ++ "}"

def body_of(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "null"
    case Some{x}:
      "<" ++ x ++ ">"

# every field of a hit
def dump(h: Hit.Hit) -> String:
  Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hs} = h
  Civil.Time{sec, ns, off} = ts
  attack ++ "|" ++ Nat.show(seq) ++ "|" ++ Nat.show(code) ++ "|" ++ Nat.show(sec) ++ "|" ++ Nat.show(ns) ++ "|" ++ Nat.show(off)
    ++ "|" ++ Nat.show(lat) ++ "|" ++ Nat.show(bout) ++ "|" ++ Nat.show(bin) ++ "|" ++ err ++ "|" ++ body_of(body)
    ++ "|" ++ method ++ "|" ++ url ++ "|" ++ hdrs_of(hs) ++ "\n"

def hits(hs: List<&2, Hit.Hit>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{h, rest}:
      dump(h) ++ hits(rest)

def hits_of(m: Maybe<&2, List<&2, Hit.Hit>>) -> String:
  match m:
    case None{}:
      "None\n"
    case Some{hs}:
      hits(hs)

def fold(hs: List<&2, Hit.Hit>, +acc: Met.Acc) -> Met.Acc:
  match hs:
    case Nil{}:
      acc
    case Con{h, rest}:
      fold(rest, Met.add(acc, h))

def folded(m: Maybe<&2, List<&2, Hit.Hit>>) -> Maybe<&2, Met.Acc>:
  match m:
    case None{}:
      None{}
    case Some{hs}:
      Some{fold(hs, Met.empty([0n, 1000000n, 5000000n]))}

def report.of(ok: Bool, +a: Met.Acc) -> String:
  match ok:
    case True{}:
      Rep.text(Met.close(a)) ++ Rep.hist(Met.close(a))
    case False{}:
      "span past the port's durations\n"

def report(m: Maybe<&2, Met.Acc>) -> String:
  match m:
    case None{}:
      "None\n"
    case Some{+a}:
      report.of(Met.span_ok(a), a)

def verdict(same: Bool, +i: String, +a: String, +b: String) -> String:
  match same:
    case True{}:
      "ok"
    case False{}:
      "DIFF " ++ i ++ "\n" ++ a ++ "----\n" ++ b

def res_acc(r: RD.Res) -> Maybe<&2, Met.Acc>:
  match r:
    case RD.AOk{a}:
      Some{a}
    case RD.ABad{a, rest}:
      None{}

# decoding s, and then t after what s failed on
def resume(r: RD.Res, +t: String) -> RD.Res:
  match r:
    case RD.AOk{a}:
      RD.add_all(t, a)
    case RD.ABad{a, rest}:
      RD.add_all(rest ++ t, a)

# s then t, as the report reads two pieces: the same metrics as s ++ t
def check2(+i: Nat, +s: String, +t: String) -> String:
  +ra = report(res_acc(resume(RD.add_all(s, Met.empty([0n, 1000000n, 5000000n])), t)))
  +rb = report(folded(Hit.decode_all(s ++ t)))
  verdict(String.eq(ra, rb), Nat.show(i), ra, rb)

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# s as Sys.Pieces.read hands a piece out: its lines, each packed
def byte(c: Char, +n: Nat) -> U32:
  Chr{k} = c
  (k << n : U32)

def pack.go(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SNil{}:
      acc
    case SCon{a, r1}:
      match r1:
        case SNil{}:
          Con{byte(a, 0n), acc}
        case SCon{b, r2}:
          match r2:
            case SNil{}:
              Con{(byte(a, 0n) .|. byte(b, 8n) : U32), acc}
            case SCon{c, r3}:
              match r3:
                case SNil{}:
                  Con{(byte(a, 0n) .|. byte(b, 8n) .|. byte(c, 16n) : U32), acc}
                case SCon{d, r4}:
                  pack.go(r4, Con{(byte(a, 0n) .|. byte(b, 8n) .|. byte(c, 16n) .|. byte(d, 24n) : U32), acc})

def last_count(+n: Nat) -> U32:
  U32.from_nat(pick(Nat, Nat.is_eq(n, 0n), 0n, pick(Nat, Nat.is_eq(Nat.mod(n, 4n), 0n), 4n, Nat.mod(n, 4n))))

def pack(+s: String) -> List<&2, U32>:
  Con{last_count(String.length(s)), pack.go(s, [])}

# the lines of s, each with its LF (the last maybe without; none empty)
def lines.of(ps: List<&2, String>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      match rest:
        case Nil{}:
          pick(List<&2, List<&2, U32>>, String.is_empty(p), [], [pack(p)])
        case Con{q, more}:
          Con{pack(p ++ "\n"), lines.of(Con{q, more})}

def lines(+s: String) -> List<&2, List<&2, U32>>:
  lines.of(String.split(s, '\n'))

def drop_lines(j: Nat, ls: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match j:
    case 0n:
      ls
    case 1n+k:
      match ls:
        case Nil{}:
          []
        case Con{l, rest}:
          drop_lines(k, rest)

# a result of the report's decoding, in full
def res_text(r: RD.Res) -> String:
  match r:
    case RD.AOk{a}:
      report(Some{a})
    case RD.ABad{a, rest}:
      "failed at [" ++ rest ++ "]\n" ++ report(Some{a})

# the fast path over the lines, then add_lines from where it stopped
def two_pass(+s: String, f: RD.Fast) -> RD.Res:
  match f:
    case RD.FAll{a}:
      RD.AOk{a}
    case RD.FStop{a, j}:
      RD.add_lines(drop_lines(U32.to_nat(j), lines(s)), a)

def check.hits(+i: String, +a: String, +b: String, +s: String) -> String:
  +ra = report(res_acc(RD.add_all(s, Met.empty([0n, 1000000n, 5000000n]))))
  +rb = report(folded(Hit.decode_all(s)))
  +ta = res_text(RD.add_all(s, Met.empty([0n, 1000000n, 5000000n])))
  +tl = res_text(RD.add_lines(lines(s), Met.empty([0n, 1000000n, 5000000n])))
  +tf = res_text(two_pass(s, RD.add_fast(lines(s), Met.empty([0n, 1000000n, 5000000n]))))
  verdict(Bool.and(Bool.and(String.eq(a, b), String.eq(ra, rb)), Bool.and(String.eq(ta, tl), String.eq(ta, tf))),
    i, a ++ ra, b ++ rb ++ "----\n" ++ ta ++ "----\n" ++ tl ++ "----\n" ++ tf)

def check(+i: Nat, +s: String) -> String:
  check.hits(Nat.show(i), hits_of(RD.decode_all(s)), hits_of(Hit.decode_all(s)), s)

def golden(+name: String, r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{e}:
      "no golden " ++ name
    case Done{+s}:
      check.hits(name, hits_of(RD.decode_all(s)), hits_of(Hit.decode_all(s)), s)

# whether s starts with '{' (the fast path to try)
def first(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Chr{k} = c
      U32.is_eq(k, 123)

def main() -> IO(Unit):
  do IO<Unit>:
    results_csv : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/results.csv")
    IO.print(golden("results.csv", results_csv))
    results_json : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/results.json")
    IO.print(golden("results.json", results_json))
    report_empty_csv : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/report-empty.csv")
    IO.print(golden("report-empty.csv", report_empty_csv))
    report_huge_sums_csv : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/report-huge-sums.csv")
    IO.print(golden("report-huge-sums.csv", report_huge_sums_csv))
    report_mixed_csv : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/report-mixed.csv")
    IO.print(golden("report-mixed.csv", report_mixed_csv))
    report_single_csv : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/report-single.csv")
    IO.print(golden("report-single.csv", report_single_csv))
    report_two_zones_csv : Result<&1, &1, U32 & String, String> <- Sys.Files.read("../../tests/golden/report-two-zones.csv")
    IO.print(golden("report-two-zones.csv", report_two_zones_csv))
    IO.print(check(0n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(1n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(2n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732503000,200,3686083,0,3,,b2sK,,1,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,QTogMQ0KQjogMg0KDQo=\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(3n, "1790160129732228000,200,3686083,0,3,,b2s,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(4n, "1790160129732228000,200,3686083,0,3,,b2s=,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(5n, "1790160129732228000,200,3686083,0,3,,,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(6n, "1790160129732228000,200,3686083,0,3,,@@@@,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(7n, "1,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(8n, "12345678,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(9n, "123456789,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(10n, "1234567890,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(11n, "12345678901234567890123,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(12n, "123456789012345678901234,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(13n, "000000000000000000001,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(14n, "99999999999999999999999,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(15n, "28147497671065500000000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(16n, "28147497671065400000000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(17n, "1790160129732228000,200,99999999999999,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(18n, "1790160129732228000,200,100000000000000,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(19n, "1790160129732228000,200,281474976710654,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(20n, "1790160129732228000,200,281474976710655,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(21n, "1790160129732228000,200,00000000000000000000007,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(22n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(23n, "1790160129732228000,200,3686083,0,3,,b2sK,,,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(24n, "1790160129732228000,200,,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(25n, "1790160129732228000,65535,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(26n, "1790160129732228000,65536,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(27n, "1790160129732228000,0,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(28n, "1790160129732228000,0000000000065535,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(29n, "1790160129732228000,200,3686083,0,3, x,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(30n, "1790160129732228000,200,3686083,0,3,\tx,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(31n, "1790160129732228000,200,3686083,0,3,a b,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(32n, "1790160129732228000,200,3686083,0,3,x\ry,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(33n, "1790160129732228000,200,3686083,0,3,a\"b,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(34n, "1790160129732228000,200,3686083,0,3,\"quoted, with comma\",b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(35n, "1790160129732228000,200,3686083,0,3,\"with \"\"quote\"\"\",b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(36n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\r\n"))
    IO.print(check(37n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K"))
    IO.print(check(38n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n\n\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(39n, "\n\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(40n, "  1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(41n, "1790160129732228000,200,3686083,0,3,,b2sK,{x,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(42n, "{1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(43n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://h/,x,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(44n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K,extra\n"))
    IO.print(check(45n, "1,1,1,1,1,1,1,1,1,1,1\n"))
    IO.print(check(46n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K,\n"))
    IO.print(check(47n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,\n"))
    IO.print(check(48n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,!!!!\n"))
    IO.print(check(49n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,QSAxDQoNCg==\n"))
    IO.print(check(50n, "1790160129732228000,200,3686083,0,3,caf" ++ raw([195]) ++ raw([169]) ++ ",b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(51n, "1790160129732228000,200,3686083,0,3," ++ raw([194]) ++ raw([160]) ++ "x,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(52n, "1790160129732228000,200,3686083,0,3," ++ raw([226]) ++ raw([128]) ++ raw([128]) ++ "x,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(53n, "1790160129732228000,200,3686083,0,3,,b2sK," ++ raw([128]) ++ ",0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(54n, "1790160129732228000,200,3686083,0,3,-,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(55n, "1790160129732228000,200,3686083,0,3,e1,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,e1,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,e2,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(56n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,POST,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://x/,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,a,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,b,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(57n, "1790160129732228000,200,-5,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(58n, "1790160129732228000,200,5a,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(59n, "1790160129732228000,200,+5,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(60n, "1790160129732228000,200,3686083,1.5,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(61n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(62n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(63n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":1,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"],\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"]}}\n{\"attack\":\"\",\"seq\":2,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:10 GMT\"],\"Content-Length\":[\"3\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"],\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"]}}\n"))
    IO.print(check(64n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{}}\n"))
    IO.print(check(65n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"A\":[]}}\n"))
    IO.print(check(66n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"A\":[\"1\",\"2\"],\"B\":[\"3\"]}}\n"))
    IO.print(check(67n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"A\":[\"1\"],\"A\":[\"2\"]}}\n"))
    IO.print(check(68n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"B\":[\"1\"],\"A\":[\"2\"],\"C\":[]}}\n"))
    IO.print(check(69n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":null}\n"))
    IO.print(check(70n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"A\":null}}\n"))
    IO.print(check(71n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"A\":[\"x\\\"y\"]}}\n"))
    IO.print(check(72n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{ \"A\":[\"1\"]}}\n"))
    IO.print(check(73n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"A\":[\"1\"] }}\n"))
    IO.print(check(74n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"A\" :[\"1\"]}}\n"))
    IO.print(check(75n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"A\":\"1\"}}\n"))
    IO.print(check(76n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(77n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.5Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(78n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09,5Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(79n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.123456789123+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(80n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(81n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09-05:30\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(82n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-02-30T12:42:09Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(83n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T24:42:09Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(84n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09+25:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(85n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09+24:60\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(86n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23t12:42:09Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(87n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"1969-12-31T23:59:59Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(88n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"1970-01-01T00:00:00+01:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(89n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"1970-01-01T01:00:00+01:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(90n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.1+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.2+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.3Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.4-01:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.5-01:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.6+02:00x\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(91n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:0\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(92n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(93n, "{\"attack\":\"\",\"seq\":0,\"code\":65536,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(94n, "{\"attack\":\"\",\"seq\":0,\"code\":65535,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(95n, "{\"attack\":\"\",\"seq\":281474976710654,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(96n, "{\"attack\":\"\",\"seq\":99999999999999,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(97n, "{\"attack\":\"\",\"seq\":100000000000000,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(98n, "{\"attack\":\"\",\"seq\":007,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(99n, "{\"attack\":\"\",\"seq\":-1,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(100n, "{\"attack\":\"\",\"seq\":1.0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(101n, "{\"attack\":\"\",\"seq\":1e3,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(102n, "{\"attack\":\"\",\"seq\":,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(103n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"x\\\"y\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(104n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\\u00e9\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(105n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"caf" ++ raw([195]) ++ raw([169]) ++ "\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(106n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"" ++ raw([1]) ++ "\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(107n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"" ++ raw([127]) ++ "\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(108n, "{\"attack\":\"a/b\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(109n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2s\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(110n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(111n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"@@@@\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(112n, "{\"attack\":\"\",\"code\":200,\"seq\":0,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(113n, "{\"attack\":\"\",\"extra\":[1,{\"a\":\"}\"}],\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(114n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":null,\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(115n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\": \"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(116n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}  \n"))
    IO.print(check(117n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\r\n"))
    IO.print(check(118n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}"))
    IO.print(check(119n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}} x\n"))
    IO.print(check(120n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(121n, "  {\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(122n, "\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n\n\n"))
    IO.print(check(123n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n{\"attack\":\"\",\"seq\":5,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n1790160129732228000,200,3686083,0,3,,b2sK,,6,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check(124n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"URL\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check(125n, "{\"Attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))

    IO.print(check2(0n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3,4,5,\"multi\n", "line\",b2sK,,0,GET,http://h/,\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check2(1n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3,4,5,\"multi\r\n", "\r\nline\",b2sK,,0,GET,http://h/,\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check2(2n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\n", "\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check2(3n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n{\n", "\"seq\":1}\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check2(4n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\ngarbage\n", "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print(check2(5n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n", "garbage\n"))
    IO.print(check2(6n, "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n", "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K"))
    IO.print(check2(7n, "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}", "\n{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"))
    IO.print(check2(8n, "", ""))
    IO.print(check2(9n, "\n\n", "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"), "1790160129732228000,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("1,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,\n"), "1,200,3686083,0,3,,b2sK,,0,GET,http://127.0.0.1:18322/ok,\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"), "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{}}\n"), "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{}}\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"), "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09Z\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("1790160129732228000,200,3686083,0,3, x,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"), "1790160129732228000,200,3686083,0,3, x,b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("1790160129732228000,200,3686083,0,3,\"q\",b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n"), "1790160129732228000,200,3686083,0,3,\"q\",b2sK,,0,GET,http://127.0.0.1:18322/ok,Q29udGVudC1MZW5ndGg6IDMNCkNvbnRlbnQtVHlwZTogdGV4dC9wbGFpbjsgY2hhcnNldD11dGYtOA0KRGF0ZTogV2VkLCAyMyBTZXAgMjAyNiAxMDo0MjowOSBHTVQNCg0K\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"x\\\"y\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"), "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"x\\\"y\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("{\"attack\":\"\",\"code\":200,\"seq\":0,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n"), "{\"attack\":\"\",\"code\":200,\"seq\":0,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\n", RD.memo0()))))
    IO.print("fast " ++ Bool.show(Maybe.is_some(&2, RD.Got, RD.fast(first("{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\r\n"), "{\"attack\":\"\",\"seq\":0,\"code\":200,\"timestamp\":\"2026-09-23T12:42:09.732228+02:00\",\"latency\":3686083,\"bytes_out\":0,\"bytes_in\":3,\"error\":\"\",\"body\":\"b2sK\",\"method\":\"GET\",\"url\":\"http://127.0.0.1:18322/ok\",\"headers\":{\"Content-Length\":[\"3\"],\"Content-Type\":[\"text/plain; charset=utf-8\"],\"Date\":[\"Wed, 23 Sep 2026 10:42:09 GMT\"]}}\r\n", RD.memo0()))))
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|ok
#|fast True
#|fast True
#|fast True
#|fast True
#|fast True
#|fast False
#|fast False
#|fast False
#|fast False
#|fast False

# The text, JSON and histogram reports: Go Vegeta's NewTextReporter,
# NewJSONReporter (encoding/json of Metrics) and NewHistogramReporter.
import Base
import ./dec.bend as Dec
import ./big.bend as Big
import ./f64.bend as F64
import ./dur.bend as Dur
import ./civil.bend as Civil
import ./json.bend as Json
import ./tab.bend as Tab
import ./metrics.bend as Met

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def has_char(s: String, +k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.or(U32.is_eq(code(c), k), has_char(rest, k))

def join_str(+sep: String, xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      match rest:
        case Nil{}:
          x
        case Con{+y, +more}:
          x ++ sep ++ join_str(sep, Con{y, more})

def head_or(+d: Nat, +xs: List<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, List.head(&2, Nat, xs), d)

def dur(+n: Nat) -> String:
  Dur.show(Dur.round(n))

def fixed2(+x: F64.F64) -> String:
  F64.fixed(2n, x)

# ---------------------------------------------------------------------
# Text
# ---------------------------------------------------------------------

def code_of(+p: Sigma<&2, &2, Nat, _ => Nat>) -> Nat:
  (k, v) = p
  k

def insert_code(+p: Sigma<&2, &2, Nat, _ => Nat>, cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> List<&2, Sigma<&2, &2, Nat, _ => Nat>>:
  match cs:
    case Nil{}:
      [p]
    case Con{+q, +rest}:
      pick(List<&2, Sigma<&2, &2, Nat, _ => Nat>>, String.is_lt(Dec.show(code_of(p)), Dec.show(code_of(q))),
        Con{p, Con{q, rest}}, Con{q, insert_code(p, rest)})

# status codes as Go orders them: as strings ("0" < "200" < "503")
def codes_by_text(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> List<&2, Sigma<&2, &2, Nat, _ => Nat>>:
  match cs:
    case Nil{}:
      []
    case Con{+p, +rest}:
      insert_code(p, codes_by_text(rest))

def code_items(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{+p, +rest}:
      (k, v) = p
      Dec.show(k) ++ ":" ++ Dec.show(v) ++ "  " ++ code_items(rest)

def error_lines(es: List<&2, String>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{+e, +rest}:
      e ++ "\n" ++ error_lines(rest)

# Go's NewTextReporter format string, filled in
def text_src(+s: Met.Summary) -> String:
  Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} = s
  "Requests\t[total, rate, throughput]\t" ++ Dec.show(req) ++ ", " ++ fixed2(rate) ++ ", " ++ fixed2(thr) ++ "\n"
  ++ "Duration\t[total, attack, wait]\t" ++ dur(Nat.add(du, w)) ++ ", " ++ dur(du) ++ ", " ++ dur(w) ++ "\n"
  ++ "Latencies\t[min, mean, 50, 90, 95, 99, max]\t" ++ dur(lmin) ++ ", " ++ dur(lm) ++ ", " ++ dur(p50) ++ ", "
     ++ dur(p90) ++ ", " ++ dur(p95) ++ ", " ++ dur(p99) ++ ", " ++ dur(lmax) ++ "\n"
  ++ "Bytes In\t[total, mean]\t" ++ Big.show(bi) ++ ", " ++ fixed2(im) ++ "\n"
  ++ "Bytes Out\t[total, mean]\t" ++ Big.show(bo) ++ ", " ++ fixed2(om) ++ "\n"
  ++ "Success\t[ratio]\t" ++ fixed2(F64.mul(ratio, F64.of_nat(100n))) ++ "%\n"
  ++ "Status Codes\t[code:count]\t" ++ code_items(codes_by_text(cs)) ++ "\nError Set:\n" ++ error_lines(es)

def text(+s: Met.Summary) -> String:
  Tab.render(text_src(s))

# ---------------------------------------------------------------------
# JSON
# ---------------------------------------------------------------------

# the local UTC offsets (plus 86400) of the earliest, latest and end times
type Zones is Data:
  Zones{earliest: Nat, latest: Nat, end: Nat}

# a time as Go's JSON writes it; Go's zero time when there is none
def json_time(+m: Maybe<&2, Civil.Time>, +off: Nat) -> String:
  match m:
    case None{}:
      "\"0001-01-01T00:00:00Z\""
    case Some{t}:
      Civil.Time{s, ns, o} = t
      "\"" ++ Civil.rfc3339(Civil.Time{s, ns, off}) ++ "\""

def json_codes(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> List<&2, String>:
  match cs:
    case Nil{}:
      []
    case Con{+p, +rest}:
      (k, v) = p
      Con{"\"" ++ Dec.show(k) ++ "\":" ++ Dec.show(v), json_codes(rest)}

# Go's Histogram.MarshalJSON, compacted: each bound in ns and its count
def json_buckets(bs: List<&2, Nat>, +cs: List<&2, Nat>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{+b, +rest}:
      Con{"\"" ++ Dec.show(b) ++ "\":" ++ Dec.show(head_or(0n, cs)), json_buckets(rest, List.drop(&2, Nat, cs, 1n))}

def rjesc_ff(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, +rest}:
      match rest:
        case Nil{}:
          Json.esc(p)
        case Con{+q, +more}:
          Json.esc(p) ++ "\\f" ++ rjesc_ff(Con{q, more})

def rjesc_parts(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{+p, +rest}:
      match rest:
        case Nil{}:
          rjesc_ff(Tab.split_on(12, p))
        case Con{+q, +more}:
          rjesc_ff(Tab.split_on(12, p)) ++ "\\b" ++ rjesc_parts(Con{q, more})

def rjesc_of(both: Bool, +s: String) -> String:
  match both:
    case True{}:
      rjesc_parts(Tab.split_on(8, s))
    case False{}:
      Json.esc(s)

# escape run by run: control bytes 8 and 12 short, the rest as easyjson
def rjesc_str(+s: String) -> String:
  rjesc_of(Bool.or(has_char(s, 8), has_char(s, 12)), s)

# encoding/json's string: easyjson's, but \b and \f are short escapes
def rjson_str(+s: String) -> String:
  "\"" ++ rjesc_str(s) ++ "\""

def rjson_strs(vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{+v, +rest}:
      Con{rjson_str(v), rjson_strs(rest)}

def json_hist(+bs: List<&2, Nat>, +h: List<&2, Nat>) -> String:
  pick(String, List.is_empty(&2, Nat, bs), "", ",\"buckets\":{" ++ join_str(",", json_buckets(bs, h)) ++ "}")

# Go's JSON reporter: encoding/json of Metrics, fields in struct order,
# status codes sorted as strings, times in the local zone
def json(+s: Met.Summary, +z: Zones) -> String:
  Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} = s
  Zones{ze, zl, zn} = z
  "{\"latencies\":{\"total\":" ++ Big.show(lt) ++ ",\"mean\":" ++ Dec.show(lm)
  ++ ",\"50th\":" ++ Dec.show(p50) ++ ",\"90th\":" ++ Dec.show(p90) ++ ",\"95th\":" ++ Dec.show(p95)
  ++ ",\"99th\":" ++ Dec.show(p99) ++ ",\"max\":" ++ Dec.show(lmax) ++ ",\"min\":" ++ Dec.show(lmin) ++ "}"
  ++ json_hist(b, h)
  ++ ",\"bytes_in\":{\"total\":" ++ Big.show(bi) ++ ",\"mean\":" ++ F64.json(im) ++ "}"
  ++ ",\"bytes_out\":{\"total\":" ++ Big.show(bo) ++ ",\"mean\":" ++ F64.json(om) ++ "}"
  ++ ",\"earliest\":" ++ json_time(e, ze) ++ ",\"latest\":" ++ json_time(l, zl)
  ++ ",\"end\":" ++ json_time(n, zn)
  ++ ",\"duration\":" ++ Dec.show(du) ++ ",\"wait\":" ++ Dec.show(w)
  ++ ",\"requests\":" ++ Dec.show(req) ++ ",\"rate\":" ++ F64.json(rate)
  ++ ",\"throughput\":" ++ F64.json(thr) ++ ",\"success\":" ++ F64.json(ratio)
  ++ ",\"status_codes\":{" ++ join_str(",", json_codes(codes_by_text(cs))) ++ "}"
  ++ ",\"errors\":[" ++ join_str(",", rjson_strs(es)) ++ "]}\n"

# ---------------------------------------------------------------------
# Histogram
# ---------------------------------------------------------------------

# a bucket's upper bound: the next bucket's lower one, or +Inf
def upper_bound(+bs: List<&2, Nat>) -> String:
  match bs:
    case Nil{}:
      "+Inf"
    case Con{+b, +rest}:
      Dur.show(b)

def hist_rows(bs: List<&2, Nat>, +cs: List<&2, Nat>, +total: Nat) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{+b, +rest}:
      +n = head_or(0n, cs)
      +ratio = F64.div(F64.of_nat(n), F64.of_nat(total))
      "[" ++ Dur.show(b) ++ ",\t" ++ upper_bound(rest) ++ "]\t"
        ++ Dec.show(n) ++ "\t" ++ fixed2(F64.mul(ratio, F64.of_nat(100n))) ++ "%\t"
        ++ String.repeat("#", F64.trunc(F64.mul(ratio, F64.of_nat(75n)))) ++ "\n"
        ++ hist_rows(rest, List.drop(&2, Nat, cs, 1n), total)

# Go's NewHistogramReporter (it divides by the total: for no results Go
# prints NaN%, and this 0.00%, F64.div by zero being zero)
def hist(+s: Met.Summary) -> String:
  Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} = s
  Tab.render("Bucket\t\t#\t%\tHistogram\n" ++ hist_rows(b, h, req))

# A Vegeta result (Go's vegeta.Result) and its CSV/JSON codecs.
#
# The writers build their text front to back (each *_into(..., t) is the
# LAWS helper's text ++ t, so every byte is written once), and the
# base64 CSV fields are encoded in place (base64 never needs quotes).
#
# The readers never measure or copy the input past the record they read:
# a stream can hold a million records, so every scan of it is a loop with
# a stop flag (fuel is the input itself), and every choice that would
# read further is a match on a computed flag (a `pick` evaluates both
# sides). Only bounded pieces (a field, a key, a header block) are
# scanned with plain recursion.
#
# CSV (Go's NewCSVDecoder): 12 fields; the timestamp is Unix nanoseconds
# (split as seconds and the last 9 digits, never read as one number) and
# comes back in UTC; the other numbers must stay below 2^48 - 1 (the runtime
# Nat); body and headers are base64, headers read as textproto's
# ReadMIMEHeader reads them ("" is no headers).
#
# JSON (easyjson's decoder): one object, members in any order, unknown
# ones skipped, null leaves a field at its default; after the object,
# spaces up to the end of the line.
import Base
import ./civil.bend as Civil
import ./hdr.bend as Hdr
import ./dec.bend as Dec
import ./csv.bend as Csv
import ./json.bend as Json
import ./b64.bend as B64

type Hit is Data:
  Hit{attack: String, seq: Nat, code: Nat, ts: Civil.Time, latency: Nat,
      bytes_out: Nat, bytes_in: Nat, error: String, body: Maybe<&2, String>,
      method: String, url: String, headers: Maybe<&2, List<&2, Hdr.Header>>}

# ---------------------------------------------------------------------
# Bytes
# ---------------------------------------------------------------------

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def in_range32(+k: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(k, lo), U32.is_le(k, hi))

def is_alnum(+k: U32) -> Bool:
  Bool.or(in_range32(k, 48, 57), Bool.or(in_range32(k, 65, 90), in_range32(k, 97, 122)))

def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

# Scans stop where they can: a loop carries the verdict on the byte it is
# at (a flag it matches itself), since a `pick` would evaluate the
# recursive call on both sides and walk the whole string.

# hit: s starts with k
def has_char.go(s: String, +k: U32, hit: Bool) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      match hit:
        case True{}:
          True{}
        case False{}:
          has_char.go(rest, k, first_is(rest, k))

def has_char(+s: String, +k: U32) -> Bool:
  has_char.go(s, k, first_is(s, k))

# ---------------------------------------------------------------------
# Headers (the LAWS "Headers" helpers)
# ---------------------------------------------------------------------

# one of !#$%&'*+-.^_`|~ (LAWS' has_char on that text, unrolled)
def token_punct(+k: U32) -> Bool:
  Bool.or(U32.is_eq(33, k), Bool.or(U32.is_eq(35, k), Bool.or(U32.is_eq(36, k), Bool.or(U32.is_eq(37, k),
  Bool.or(U32.is_eq(38, k), Bool.or(U32.is_eq(39, k), Bool.or(U32.is_eq(42, k), Bool.or(U32.is_eq(43, k),
  Bool.or(U32.is_eq(45, k), Bool.or(U32.is_eq(46, k), Bool.or(U32.is_eq(94, k), Bool.or(U32.is_eq(95, k),
  Bool.or(U32.is_eq(96, k), Bool.or(U32.is_eq(124, k), Bool.or(U32.is_eq(126, k), False{})))))))))))))))

# the punctuation is looked at only when k is not alphanumeric
def token_byte.of(a: Bool, +k: U32) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      token_punct(k)

def token_byte(+k: U32) -> Bool:
  token_byte.of(is_alnum(k), k)

def all_token(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(token_byte(code(c)), all_token(rest))

def token(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), all_token(s))

def canon.go(s: String, +up: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      +k = code(c)
      +k2 = pick(U32, Bool.and(up, in_range32(k, 97, 122)), (k - 32 : U32),
             pick(U32, Bool.and(Bool.not(up), in_range32(k, 65, 90)), (k + 32 : U32), k))
      SCon{Chr{k2}, canon.go(rest, U32.is_eq(k, 45))}

# Go's CanonicalMIMEHeaderKey
def canon(+s: String) -> String:
  pick(String, token(s), canon.go(s, True{}), s)

def hdr_key(+h: Hdr.Header) -> String:
  Hdr.Header{k, vs} = h
  k

def hdr_vals(+h: Hdr.Header) -> List<&2, String>:
  Hdr.Header{k, vs} = h
  vs

def is_ows(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), U32.is_eq(k, 9))

def first_ows(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      is_ows(code(c))

# ws: s starts with a space or a tab
def trim_ows_l.go(s: String, ws: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match ws:
        case True{}:
          trim_ows_l.go(rest, first_ows(rest))
        case False{}:
          SCon{c, rest}

def trim_ows_l(+s: String) -> String:
  trim_ows_l.go(s, first_ows(s))

def trim_ows_r.of(+t: String, +c: Char) -> String:
  pick(String, Bool.and(String.is_empty(t), is_ows(code(c))), SNil{}, SCon{c, t})

# spaces and tabs at the end dropped, in one pass
def trim_ows_r(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      trim_ows_r.of(trim_ows_r(rest), c)

# trims spaces and tabs at both ends (textproto.TrimString)
def trim_ows(+s: String) -> String:
  trim_ows_r(trim_ows_l(s))

def nl_char(+c: Char) -> Char:
  Chr{pick(U32, Bool.or(U32.is_eq(code(c), 10), U32.is_eq(code(c), 13)), 32, code(c))}

def nl_to_space(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      SCon{nl_char(c), nl_to_space(rest)}

# String.is_lt(a, b) without rebuilding the strings (String.cmp hands
# both back): lt.st is the verdict on the heads, 0 less, 1 not less, 2
# equal so far
def lt.st(+a: String, +b: String) -> Nat:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          1n
        case SCon{+cb, +rb}:
          0n
    case SCon{+ca, +ra}:
      match b:
        case SNil{}:
          1n
        case SCon{+cb, +rb}:
          pick(Nat, U32.is_lt(code(ca), code(cb)), 0n, pick(Nat, U32.is_eq(code(ca), code(cb)), 2n, 1n))

def lt.go(a: String, b: String, st: Nat) -> Bool:
  match a:
    case SNil{}:
      Nat.is_eq(st, 0n)
    case SCon{+ca, +ra}:
      match b:
        case SNil{}:
          Nat.is_eq(st, 0n)
        case SCon{+cb, +rb}:
          match st:
            case 0n:
              True{}
            case 1n+x:
              match x:
                case 0n:
                  False{}
                case 1n+y:
                  lt.go(ra, rb, lt.st(ra, rb))

def str_lt(+a: String, +b: String) -> Bool:
  lt.go(a, b, lt.st(a, b))

# h goes before the head of hs
def key_lt(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Con{+x, +rest}:
      str_lt(hdr_key(h), hdr_key(x))

def insert_hdr.go(hs: List<&2, Hdr.Header>, +h: Hdr.Header, lt: Bool) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [h]
    case Con{+x, +rest}:
      match lt:
        case True{}:
          Con{h, Con{x, rest}}
        case False{}:
          Con{x, insert_hdr.go(rest, h, key_lt(h, rest))}

def insert_hdr(+h: Hdr.Header, +hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  insert_hdr.go(hs, h, key_lt(h, hs))

# headers ordered by name
def sort_hdrs(hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      insert_hdr(h, sort_hdrs(rest))

# The writers build front to back onto the text t that follows, so that
# every byte is written once (a ++ copies its left side).

# A header value as written, trim_ows(nl_to_space(v)), in one copy: skip
# the blanks it starts with (CR and LF count, as they become spaces), then
# copy up to the blanks it ends with (keep counts the bytes before them).
def vblank(+k: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(k, 10), U32.is_eq(k, 13)), is_ows(k))

def first_vblank(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      vblank(code(c))

# bl: s starts with a blank
def skip_bl.go(s: String, bl: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match bl:
        case True{}:
          skip_bl.go(rest, first_vblank(rest))
        case False{}:
          SCon{c, rest}

def skip_bl(+s: String) -> String:
  skip_bl.go(s, first_vblank(s))

def keep.of(+m: Nat, b: Bool) -> Nat:
  pick(Nat, Bool.and(Nat.is_eq(m, 0n), b), 0n, 1n+m)

def keep(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{+c, +rest}:
      keep.of(keep(rest), vblank(code(c)))

# the first n bytes of s, CR and LF as spaces, then t
def copy_nl(n: Nat, s: String, t: String) -> String:
  match n:
    case 0n:
      t
    case 1n+m:
      match s:
        case SNil{}:
          t
        case SCon{+c, +rest}:
          SCon{nl_char(c), copy_nl(m, rest, t)}

# trim_ows(nl_to_space(v)) ++ t
def val_into(+v: String, t: String) -> String:
  +u = skip_bl(v)
  copy_nl(keep(u), u, t)

# hdr_lines(k, vs) ++ t
def lines_into(+k: String, vs: List<&2, String>, t: String) -> String:
  match vs:
    case Nil{}:
      t
    case Con{+v, +rest}:
      k ++ SCon{':', SCon{' ', val_into(v, SCon{'\r', SCon{'\n', lines_into(k, rest, t)}})}}

def text_into(tok: Bool, +k: String, vs: List<&2, String>, t: String) -> String:
  match tok:
    case True{}:
      lines_into(k, vs, t)
    case False{}:
      t

# hdrs_text(hs) ++ t
def hdrs_into(hs: List<&2, Hdr.Header>, t: String) -> String:
  match hs:
    case Nil{}:
      t
    case Con{+h, +rest}:
      text_into(token(hdr_key(h)), hdr_key(h), hdr_vals(h), hdrs_into(rest, t))

# Go's headerBytes: http.Header.Write, then a blank line; nothing for nil
def hdr_block(+m: Maybe<&2, List<&2, Hdr.Header>>) -> String:
  match m:
    case None{}:
      ""
    case Some{hs}:
      hdrs_into(sort_hdrs(hs), "\r\n")

# ---------------------------------------------------------------------
# Writing (the LAWS "Results" helpers)
# ---------------------------------------------------------------------

def body_or_empty(+m: Maybe<&2, String>) -> String:
  Maybe.default(&2, String, m, "")

# the fields, each followed by a comma, then t
def csv_into(fs: List<&2, String>, t: String) -> String:
  match fs:
    case Nil{}:
      t
    case Con{+f, +rest}:
      Csv.field_into(f, SCon{',', csv_into(rest, t)})

# the field B64.encode(x), then t: base64 text never needs quotes (a
# letter, digit, + or / is not a comma, quote, CR, LF or space), so it is
# encoded in place
def b64_field_into(x: String, t: String) -> String:
  B64.encode_into(x, t)

# the CSV record Go's NewCSVEncoder writes (Csv.row of its 12 fields)
def to_csv(+h: Hit) -> String:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  csv_into([Civil.unix_nanos(ts), Dec.show(code), Dec.show(lat), Dec.show(bout), Dec.show(bin), err],
    b64_field_into(body_or_empty(body), SCon{',', csv_into([attack, Dec.show(seq), method, url],
      b64_field_into(hdr_block(hdrs), "\n"))}))

# JSON, front to back: json_list(vs) ++ t, json_hdrs(hs) ++ t, ...
def json_list_into(vs: List<&2, String>, t: String) -> String:
  match vs:
    case Nil{}:
      t
    case Con{+v, +rest}:
      match rest:
        case Nil{}:
          Json.str_into(v, t)
        case Con{+w, +more}:
          Json.str_into(v, SCon{',', json_list_into(Con{w, more}, t)})

def json_item_into(+h: Hdr.Header, t: String) -> String:
  Json.str_into(hdr_key(h), SCon{':', SCon{'[', json_list_into(hdr_vals(h), SCon{']', t})}})

def json_items_into(hs: List<&2, Hdr.Header>, t: String) -> String:
  match hs:
    case Nil{}:
      t
    case Con{+h, +rest}:
      match rest:
        case Nil{}:
          json_item_into(h, t)
        case Con{+g, +more}:
          json_item_into(h, SCon{',', json_items_into(Con{g, more}, t)})

def json_body_into(+m: Maybe<&2, String>, t: String) -> String:
  match m:
    case None{}:
      "null" ++ t
    case Some{x}:
      SCon{'"', B64.encode_into(x, SCon{'"', t})}

def json_hdrs_into(+m: Maybe<&2, List<&2, Hdr.Header>>, t: String) -> String:
  match m:
    case None{}:
      "null" ++ t
    case Some{hs}:
      SCon{'{', json_items_into(sort_hdrs(hs), SCon{'}', t})}

def json_body(+m: Maybe<&2, String>) -> String:
  json_body_into(m, "")

def json_hdrs_of(+m: Maybe<&2, List<&2, Hdr.Header>>) -> String:
  json_hdrs_into(m, "")

# The JSON keys, each as a chain of bytes before t: a literal ++ t walks a
# shared constant byte by byte (several times slower than building it).

# "{\"attack\":" ++ t
def jk_attack(t: String) -> String:
  SCon{'{', SCon{'"', SCon{'a', SCon{'t', SCon{'t', SCon{'a', SCon{'c', SCon{'k', SCon{'"', SCon{':', t}}}}}}}}}}

# ",\"seq\":" ++ t
def jk_seq(t: String) -> String:
  SCon{',', SCon{'"', SCon{'s', SCon{'e', SCon{'q', SCon{'"', SCon{':', t}}}}}}}

# ",\"code\":" ++ t
def jk_code(t: String) -> String:
  SCon{',', SCon{'"', SCon{'c', SCon{'o', SCon{'d', SCon{'e', SCon{'"', SCon{':', t}}}}}}}}

# ",\"timestamp\":\"" ++ t
def jk_ts(t: String) -> String:
  SCon{',', SCon{'"', SCon{'t', SCon{'i', SCon{'m', SCon{'e', SCon{'s', SCon{'t', SCon{'a', SCon{'m', SCon{'p', SCon{'"', SCon{':', SCon{'"', t}}}}}}}}}}}}}}

# "\",\"latency\":" ++ t
def jk_lat(t: String) -> String:
  SCon{'"', SCon{',', SCon{'"', SCon{'l', SCon{'a', SCon{'t', SCon{'e', SCon{'n', SCon{'c', SCon{'y', SCon{'"', SCon{':', t}}}}}}}}}}}}

# ",\"bytes_out\":" ++ t
def jk_bout(t: String) -> String:
  SCon{',', SCon{'"', SCon{'b', SCon{'y', SCon{'t', SCon{'e', SCon{'s', SCon{'_', SCon{'o', SCon{'u', SCon{'t', SCon{'"', SCon{':', t}}}}}}}}}}}}}

# ",\"bytes_in\":" ++ t
def jk_bin(t: String) -> String:
  SCon{',', SCon{'"', SCon{'b', SCon{'y', SCon{'t', SCon{'e', SCon{'s', SCon{'_', SCon{'i', SCon{'n', SCon{'"', SCon{':', t}}}}}}}}}}}}

# ",\"error\":" ++ t
def jk_err(t: String) -> String:
  SCon{',', SCon{'"', SCon{'e', SCon{'r', SCon{'r', SCon{'o', SCon{'r', SCon{'"', SCon{':', t}}}}}}}}}

# ",\"body\":" ++ t
def jk_body(t: String) -> String:
  SCon{',', SCon{'"', SCon{'b', SCon{'o', SCon{'d', SCon{'y', SCon{'"', SCon{':', t}}}}}}}}

# ",\"method\":" ++ t
def jk_method(t: String) -> String:
  SCon{',', SCon{'"', SCon{'m', SCon{'e', SCon{'t', SCon{'h', SCon{'o', SCon{'d', SCon{'"', SCon{':', t}}}}}}}}}}

# ",\"url\":" ++ t
def jk_url(t: String) -> String:
  SCon{',', SCon{'"', SCon{'u', SCon{'r', SCon{'l', SCon{'"', SCon{':', t}}}}}}}

# ",\"headers\":" ++ t
def jk_hdrs(t: String) -> String:
  SCon{',', SCon{'"', SCon{'h', SCon{'e', SCon{'a', SCon{'d', SCon{'e', SCon{'r', SCon{'s', SCon{'"', SCon{':', t}}}}}}}}}}}

# Dec.show(n) ++ t (show.go prepends the digits to what it is given)
def show_into(+n: Nat, t: String) -> String:
  Dec.show.go(1n+n, False{}, n, t)

# the JSON line Go's NewJSONEncoder writes (header names sorted)
def to_json(+h: Hit) -> String:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  jk_attack(Json.str_into(attack, jk_seq(show_into(seq, jk_code(show_into(code,
    jk_ts(Civil.rfc3339(ts) ++ jk_lat(show_into(lat, jk_bout(show_into(bout, jk_bin(show_into(bin,
    jk_err(Json.str_into(err, jk_body(json_body_into(body, jk_method(Json.str_into(method,
    jk_url(Json.str_into(url, jk_hdrs(json_hdrs_into(hdrs, SCon{'}', SCon{'\n', SNil{}}})))))))))))))))))))))))

# ---------------------------------------------------------------------
# Scanning the stream (stop-flag loops)
# ---------------------------------------------------------------------

# a blank byte: space, tab, CR, and LF when nl
def blank(+nl: Bool, +k: U32) -> Bool:
  Bool.or(Bool.or(U32.is_eq(k, 32), U32.is_eq(k, 9)), Bool.or(U32.is_eq(k, 13), Bool.and(nl, U32.is_eq(k, 10))))

def first_blank(+nl: Bool, +s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      blank(nl, code(c))

def skip.go(fuel: String, stop: Bool, +nl: Bool, +s: String) -> String:
  match fuel:
    case SNil{}:
      s
    case SCon{c, f}:
      match stop:
        case True{}:
          s
        case False{}:
          +b = first_blank(nl, s)
          skip.go(f, Bool.not(b), nl, String.drop(s, pick(Nat, b, 1n, 0n)))

# s without the blanks it starts with
def skip_ws(+s: String) -> String:
  skip.go(SCon{Chr{0}, s}, False{}, True{}, s)

# s without the spaces, tabs and CRs it starts with
def skip_sp(+s: String) -> String:
  skip.go(SCon{Chr{0}, s}, False{}, False{}, s)

def is_digit(+k: U32) -> Bool:
  in_range32(k, 48, 57)

# a byte of a JSON literal (number, true, false, null)
def lit_byte(+k: U32) -> Bool:
  Bool.or(is_alnum(k), Bool.or(Bool.or(U32.is_eq(k, 43), U32.is_eq(k, 45)), U32.is_eq(k, 46)))

def first_digit(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      is_digit(code(c))

def first_lit(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      lit_byte(code(c))

# how many digits (lit: literal bytes) s starts with, plus n
def count.go(fuel: String, stop: Bool, +lit: Bool, s: String, +n: Nat) -> Nat:
  match fuel:
    case SNil{}:
      n
    case SCon{c, f}:
      match stop:
        case True{}:
          n
        case False{}:
          match s:
            case SNil{}:
              n
            case SCon{+d, +rest}:
              +more = pick(Bool, lit, lit_byte(code(d)), is_digit(code(d)))
              count.go(f, Bool.not(more), lit, pick(String, more, rest, ""), pick(Nat, more, Nat.add(n, 1n), n))

def count_digits(+s: String) -> Nat:
  count.go(SCon{Chr{0}, s}, False{}, False{}, s, 0n)

def count_lit(+s: String) -> Nat:
  count.go(SCon{Chr{0}, s}, False{}, True{}, s, 0n)

# ---------------------------------------------------------------------
# Numbers (below 2^48, the runtime Nat)
# ---------------------------------------------------------------------

def strip0.go(s: String, z: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match z:
        case True{}:
          strip0.go(rest, first_is(rest, 48))
        case False{}:
          SCon{c, rest}

def strip0(+s: String) -> String:
  strip0.go(s, first_is(s, 48))

# digits without leading zeros, below 2^48 - 1 = 281474976710655 (Dec.show
# runs n + 1 steps, so 2^48 - 1 itself would abort re-encoding)
def fits48(+t: String) -> Bool:
  +n = String.length(t)
  Bool.or(Nat.is_lt(n, 15n), Bool.and(Nat.is_eq(n, 15n), String.is_lt(t, "281474976710655")))

def nat_ok(+s: String) -> Bool:
  Bool.and(Dec.all_digits(s), fits48(strip0(s)))

# the value of s, 0 when it is not nat_ok (so nothing ever overflows)
def nat_val(+s: String) -> Nat:
  Dec.value(pick(String, nat_ok(s), s, ""))

def code_ok(+s: String) -> Bool:
  Bool.and(nat_ok(s), Nat.is_lt(nat_val(s), 65536n))

# ---------------------------------------------------------------------
# CSV
# ---------------------------------------------------------------------

# the timestamp column: the seconds are all but the last 9 digits
def ts_sec(+s: String) -> String:
  String.take(s, Nat.sub(String.length(s), 9n))

def ts_nsec(+s: String) -> String:
  String.drop(s, Nat.sub(String.length(s), 9n))

def ts_ok(+s: String) -> Bool:
  Bool.and(Dec.all_digits(s), fits48(strip0(ts_sec(s))))

def ts_val(+s: String) -> Civil.Time:
  +ok = ts_ok(s)
  Civil.Time{Dec.value(pick(String, ok, ts_sec(s), "")), Dec.value(pick(String, ok, ts_nsec(s), "")), 86400n}

# the header column, read: ok, and the headers
type HCol is Data:
  HCol{ok: Bool, hs: Maybe<&2, List<&2, Hdr.Header>>}

def hcol_ok(+c: HCol) -> Bool:
  HCol{ok, hs} = c
  ok

def hcol_hs(+c: HCol) -> Maybe<&2, List<&2, Hdr.Header>>:
  HCol{ok, hs} = c
  hs

# the segments of s between LFs: the head is the first one
type Segs is Data:
  Segs{head: String, rest: List<&2, String>}

def segs_head(+p: Segs) -> String:
  Segs{h, r} = p
  h

def segs_rest(+p: Segs) -> List<&2, String>:
  Segs{h, r} = p
  r

def segs.go(s: String) -> Segs:
  match s:
    case SNil{}:
      Segs{"", []}
    case SCon{+c, +rest}:
      +r = segs.go(rest)
      pick(Segs, U32.is_eq(code(c), 10), Segs{"", Con{segs_head(r), segs_rest(r)}}, Segs{SCon{c, segs_head(r)}, segs_rest(r)})

def segs_all(+p: Segs) -> List<&2, String>:
  Con{segs_head(p), segs_rest(p)}

# s is "\r"
def lone_cr(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.and(U32.is_eq(code(c), 13), String.is_empty(rest))

# s without its final CR
def drop_cr.go(s: String, lone: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match lone:
        case True{}:
          SNil{}
        case False{}:
          SCon{c, drop_cr.go(rest, lone_cr(rest))}

# a line without its final CR (bufio's ReadLine), then trimmed
def line_trim(+s: String) -> String:
  trim_ows_l(trim_ows_r(drop_cr.go(s, lone_cr(s))))

# a blank line: nothing but its final CR
def line_blank(+s: String) -> Bool:
  Bool.or(String.is_empty(s), String.eq(s, "\r"))

# the logical lines of a header block (textproto's continued lines):
# the one being built, whether there is one, those done (last first),
# a syntax error, and whether the blank line was seen
type MF is Data:
  MF{cur: String, has: Bool, kvs: List<&2, String>, bad: Bool, end: Bool}

def mf_kvs(+m: MF) -> List<&2, String>:
  MF{cur, has, kvs, bad, end} = m
  kvs

def mf_ok(+m: MF) -> Bool:
  MF{cur, has, kvs, bad, end} = m
  Bool.and(end, Bool.not(bad))

def mf.step(+line: String, st: MF) -> MF:
  match st:
    case MF{+cur, +has, +kvs, +bad, +end}:
      +t = line_trim(line)
      +pushed = pick(List<&2, String>, has, Con{cur, kvs}, kvs)
      +cont = Bool.or(first_is(line, 32), first_is(line, 9))
      pick(MF, Bool.or(bad, end), MF{cur, has, kvs, bad, end},
      pick(MF, line_blank(line), MF{cur, False{}, pushed, False{}, True{}},
      pick(MF, cont,
        pick(MF, has, MF{cur ++ " " ++ t, True{}, kvs, False{}, False{}}, MF{cur, has, kvs, True{}, False{}}),
        pick(MF, has_char(line, 58), MF{t, True{}, pushed, False{}, False{}}, MF{cur, has, kvs, True{}, False{}}))))

# every segment but the last (the bytes after the last LF are no line)
def mf.fold(ls: List<&2, String>, st: MF) -> MF:
  match ls:
    case Nil{}:
      st
    case Con{+l, +rest}:
      match rest:
        case Nil{}:
          st
        case Con{+y, +more}:
          mf.fold(Con{y, more}, mf.step(l, st))

def before_colon.go(s: String, hit: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match hit:
        case True{}:
          SNil{}
        case False{}:
          SCon{c, before_colon.go(rest, first_is(rest, 58))}

def before_colon(+s: String) -> String:
  before_colon.go(s, first_is(s, 58))

def after_colon.go(s: String, hit: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match hit:
        case True{}:
          rest
        case False{}:
          after_colon.go(rest, first_is(rest, 58))

def after_colon(+s: String) -> String:
  after_colon.go(s, first_is(s, 58))

# a header name as textproto takes it: token bytes and spaces
def all_key(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.or(token_byte(code(c)), U32.is_eq(code(c), 32)), all_key(rest))

def key_ok(+k: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(k)), all_key(k))

# textproto's validHeaderValueByte: no control byte but tab
def val_ok(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.or(U32.is_eq(code(c), 9), Bool.and(U32.is_ge(code(c), 32), Bool.not(U32.is_eq(code(c), 127)))), val_ok(rest))

# v added under k, in a list ordered by name
def hadd(+k: String, +v: String, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [Hdr.Header{k, [v]}]
    case Con{+x, +rest}:
      pick(List<&2, Hdr.Header>, String.eq(k, hdr_key(x)), Con{Hdr.Header{k, List.append(&2, String, hdr_vals(x), [v])}, rest},
      pick(List<&2, Hdr.Header>, String.is_lt(k, hdr_key(x)), Con{Hdr.Header{k, [v]}, Con{x, rest}},
        Con{x, hadd(k, v, rest)}))

type KF is Data:
  KF{hs: List<&2, Hdr.Header>, bad: Bool}

def kf.step(+kv: String, st: KF) -> KF:
  match st:
    case KF{+hs, +bad}:
      +k = before_colon(kv)
      +v = after_colon(kv)
      pick(KF, Bool.and(Bool.not(bad), Bool.and(key_ok(k), val_ok(v))), KF{hadd(canon(k), trim_ows_l(v), hs), False{}}, KF{hs, True{}})

def kf.fold(kvs: List<&2, String>, st: KF) -> KF:
  match kvs:
    case Nil{}:
      st
    case Con{+kv, +rest}:
      kf.fold(rest, kf.step(kv, st))

def kf_col(+k: KF) -> HCol:
  KF{hs, bad} = k
  HCol{Bool.not(bad), Some{hs}}

def mime.of(ok: Bool, kvs: List<&2, String>) -> HCol:
  match ok:
    case True{}:
      kf_col(kf.fold(kvs, KF{[], False{}}))
    case False{}:
      HCol{False{}, None{}}

# textproto's ReadMIMEHeader over a whole header block
def mime.fin(+m: MF) -> HCol:
  mime.of(mf_ok(m), List.reverse(&2, String, mf_kvs(m)))

def mime(+b: String) -> HCol:
  mime.fin(mf.fold(segs_all(segs.go(b)), MF{"", False{}, [], False{}, False{}}))

def hcol.b64(m: Maybe<&2, String>) -> HCol:
  match m:
    case None{}:
      HCol{False{}, None{}}
    case Some{b}:
      mime(b)

def hcol.of(empty: Bool, +s: String) -> HCol:
  match empty:
    case True{}:
      HCol{True{}, None{}}
    case False{}:
      hcol.b64(B64.decode(s))

def hcol(+s: String) -> HCol:
  hcol.of(String.is_empty(s), s)

def csv.rec.of(ok: Bool, +hc: HCol, +bm: Maybe<&2, String>, +f0: String, +f1: String, +f2: String, +f3: String,
  +f4: String, +f5: String, +f7: String, +f8: String, +f9: String, +f10: String, rest: String) -> Maybe<&1, Hit & String>:
  match ok:
    case True{}:
      Some{(Hit{f7, nat_val(f8), nat_val(f1), ts_val(f0), nat_val(f2), nat_val(f3), nat_val(f4), f5,
        Some{Maybe.default(&2, String, bm, "")}, f9, f10, hcol_hs(hc)}, rest)}
    case False{}:
      None{}

def csv.rec(+f0: String, +f1: String, +f2: String, +f3: String, +f4: String, +f5: String, +f6: String,
  +f7: String, +f8: String, +f9: String, +f10: String, +f11: String, rest: String) -> Maybe<&1, Hit & String>:
  +hc = hcol(f11)
  +bm = B64.decode(f6)
  +ok = Bool.and(Bool.and(Bool.and(ts_ok(f0), code_ok(f1)), Bool.and(nat_ok(f2), nat_ok(f3))),
    Bool.and(Bool.and(nat_ok(f4), Maybe.is_some(&2, String, bm)), Bool.and(nat_ok(f8), hcol_ok(hc))))
  csv.rec.of(ok, hc, bm, f0, f1, f2, f3, f4, f5, f7, f8, f9, f10, rest)

# exactly 12 fields (Go's FieldsPerRecord)
def csv.fields(fs: List<&2, String>, rest: String) -> Maybe<&1, Hit & String>:
  match fs:
    case Nil{}:
      None{}
    case Con{f0, r0}:
      match r0:
        case Nil{}:
          None{}
        case Con{f1, r1}:
          match r1:
            case Nil{}:
              None{}
            case Con{f2, r2}:
              match r2:
                case Nil{}:
                  None{}
                case Con{f3, r3}:
                  match r3:
                    case Nil{}:
                      None{}
                    case Con{f4, r4}:
                      match r4:
                        case Nil{}:
                          None{}
                        case Con{f5, r5}:
                          match r5:
                            case Nil{}:
                              None{}
                            case Con{f6, r6}:
                              match r6:
                                case Nil{}:
                                  None{}
                                case Con{f7, r7}:
                                  match r7:
                                    case Nil{}:
                                      None{}
                                    case Con{f8, r8}:
                                      match r8:
                                        case Nil{}:
                                          None{}
                                        case Con{f9, r9}:
                                          match r9:
                                            case Nil{}:
                                              None{}
                                            case Con{f10, r10}:
                                              match r10:
                                                case Nil{}:
                                                  None{}
                                                case Con{f11, r11}:
                                                  match r11:
                                                    case Nil{}:
                                                      csv.rec(f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, rest)
                                                    case Con{f12, r12}:
                                                      None{}

def csv.row(m: Maybe<&1, List<&2, String> & String>) -> Maybe<&1, Hit & String>:
  match m:
    case None{}:
      None{}
    case Some{(fs, rest)}:
      csv.fields(fs, rest)

def of_csv(s: String) -> Maybe<&1, Hit & String>:
  csv.row(Csv.parse_row(s))

# ---------------------------------------------------------------------
# JSON
# ---------------------------------------------------------------------

def zero_hit() -> Hit:
  Hit{"", 0n, 0n, Civil.Time{0n, 0n, 86400n}, 0n, 0n, 0n, "", None{}, "", "", None{}}

def set_attack(+h: Hit, x: String) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{x, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs}

def set_seq(+h: Hit, x: Nat) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, x, code, ts, lat, bout, bin, err, body, method, url, hdrs}

def set_code(+h: Hit, x: Nat) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, x, ts, lat, bout, bin, err, body, method, url, hdrs}

def set_ts(+h: Hit, x: Civil.Time) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, x, lat, bout, bin, err, body, method, url, hdrs}

def set_lat(+h: Hit, x: Nat) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, ts, x, bout, bin, err, body, method, url, hdrs}

def set_bout(+h: Hit, x: Nat) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, ts, lat, x, bin, err, body, method, url, hdrs}

def set_bin(+h: Hit, x: Nat) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, ts, lat, bout, x, err, body, method, url, hdrs}

def set_err(+h: Hit, x: String) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, ts, lat, bout, bin, x, body, method, url, hdrs}

def set_body(+h: Hit, x: String) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, ts, lat, bout, bin, err, Some{x}, method, url, hdrs}

def set_method(+h: Hit, x: String) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, x, url, hdrs}

def set_url(+h: Hit, x: String) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, x, hdrs}

def set_hdrs(+h: Hit, x: List<&2, Hdr.Header>) -> Hit:
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} = h
  Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, Some{x}}

# where a JSON reader is: expecting a member or an element (JKey), a
# comma or the close (JNext), done (JEnd), failed (JBad)
type JCut is Data:
  JKey{}
  JNext{}
  JEnd{}
  JBad{}

# the result object being read
type JObj is Data:
  JObj{h: Hit, rest: String, cut: JCut}

# a JSON number: digits only, below 2^48 - 1
def read_nat.of(ok: Bool, +ds: String, rest: String) -> Maybe<&1, Nat & String>:
  match ok:
    case True{}:
      Some{(Dec.value(ds), rest)}
    case False{}:
      None{}

def read_nat.go(+s: String, +n: Nat) -> Maybe<&1, Nat & String>:
  +ds = String.take(s, n)
  read_nat.of(nat_ok(ds), ds, String.drop(s, n))

def read_nat(+s: String) -> Maybe<&1, Nat & String>:
  read_nat.go(s, count_digits(s))

def is_null(+s: String) -> Bool:
  String.starts_with(s, "null")

# a JSON value skipped (easyjson's SkipRecursive): a string, a literal,
# or brackets up to the matching close (strings inside skipped whole)
type Skip is Data:
  Skip{depth: Nat, rest: String, cut: JCut}

def skip.str(+d: Nat, m: Maybe<&1, String & String>) -> Skip:
  match m:
    case None{}:
      Skip{d, "", JBad{}}
    case Some{(x, r)}:
      Skip{d, r, pick(JCut, Nat.is_eq(d, 0n), JEnd{}, JKey{})}

def skip.byte(+d: Nat, +s: String) -> Skip:
  +open = Bool.or(first_is(s, 123), first_is(s, 91))
  +close = Bool.or(first_is(s, 125), first_is(s, 93))
  +r = String.drop(s, 1n)
  pick(Skip, String.is_empty(s), Skip{d, s, JBad{}},
  pick(Skip, open, Skip{Nat.add(d, 1n), r, JKey{}},
  pick(Skip, close, pick(Skip, Nat.is_eq(d, 1n), Skip{0n, r, JEnd{}}, Skip{Nat.sub(d, 1n), r, JKey{}}),
    Skip{d, r, JKey{}})))

def skip.step(quote: Bool, +d: Nat, +s: String) -> Skip:
  match quote:
    case True{}:
      skip.str(d, Json.read_str(s))
    case False{}:
      skip.byte(d, s)

def skip.loop(fuel: String, st: Skip) -> Maybe<&2, String>:
  match fuel:
    case SNil{}:
      None{}
    case SCon{c, f}:
      match st:
        case Skip{+d, +rest, cut}:
          match cut:
            case JKey{}:
              skip.loop(f, skip.step(first_is(rest, 34), d, rest))
            case JNext{}:
              None{}
            case JEnd{}:
              Some{rest}
            case JBad{}:
              None{}

def skip_lit(+s: String, +n: Nat) -> Maybe<&2, String>:
  pick(Maybe<&2, String>, Nat.is_eq(n, 0n), None{}, Some{String.drop(s, n)})

def skip_value.of(kind: Nat, +s: String) -> Maybe<&2, String>:
  match kind:
    case 0n:
      skip.loop(SCon{Chr{0}, s}, Skip{0n, s, JKey{}})
    case 1n+k:
      skip_lit(s, count_lit(s))

def skip_value(+s: String) -> Maybe<&2, String>:
  skip_value.of(pick(Nat, Bool.or(first_is(s, 34), Bool.or(first_is(s, 123), first_is(s, 91))), 0n, 1n), s)

# an array of strings: the elements so far (last first)
type JArr is Data:
  JArr{vs: List<&2, String>, rest: String, cut: JCut}

def arr.elem(vs: List<&2, String>, m: Maybe<&1, String & String>) -> JArr:
  match m:
    case None{}:
      JArr{vs, "", JBad{}}
    case Some{(x, r)}:
      JArr{Con{x, vs}, r, JNext{}}

def arr.next(+vs: List<&2, String>, +s: String) -> JArr:
  pick(JArr, first_is(s, 44), JArr{vs, skip_ws(String.drop(s, 1n)), JKey{}},
  pick(JArr, first_is(s, 93), JArr{vs, String.drop(s, 1n), JEnd{}}, JArr{vs, s, JBad{}}))

def arr.loop(fuel: String, st: JArr) -> Maybe<&1, List<&2, String> & String>:
  match fuel:
    case SNil{}:
      None{}
    case SCon{c, f}:
      match st:
        case JArr{vs, rest, cut}:
          match cut:
            case JKey{}:
              arr.loop(f, arr.elem(vs, Json.read_str(rest)))
            case JNext{}:
              arr.loop(f, arr.next(vs, skip_ws(rest)))
            case JEnd{}:
              Some{(List.reverse(&2, String, vs), rest)}
            case JBad{}:
              None{}

def arr.start(+s: String) -> JArr:
  pick(JArr, first_is(s, 93), JArr{[], String.drop(s, 1n), JEnd{}}, JArr{[], s, JKey{}})

def read_arr.of(open: Bool, +s: String) -> Maybe<&1, List<&2, String> & String>:
  match open:
    case True{}:
      arr.loop(SCon{Chr{0}, s}, arr.start(skip_ws(String.drop(s, 1n))))
    case False{}:
      None{}

def read_arr(+s: String) -> Maybe<&1, List<&2, String> & String>:
  read_arr.of(first_is(s, 91), s)

# vs under k in a list ordered by name (a repeated name: the last wins)
def hput(+k: String, +vs: List<&2, String>, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [Hdr.Header{k, vs}]
    case Con{+x, +rest}:
      pick(List<&2, Hdr.Header>, String.eq(k, hdr_key(x)), Con{Hdr.Header{k, vs}, rest},
      pick(List<&2, Hdr.Header>, String.is_lt(k, hdr_key(x)), Con{Hdr.Header{k, vs}, Con{x, rest}},
        Con{x, hput(k, vs, rest)}))

# the headers object: names to arrays of strings (or null)
type JHdrs is Data:
  JHdrs{hs: List<&2, Hdr.Header>, rest: String, cut: JCut}

def hobj.arr(hs: List<&2, Hdr.Header>, +k: String, m: Maybe<&1, List<&2, String> & String>) -> JHdrs:
  match m:
    case None{}:
      JHdrs{hs, "", JBad{}}
    case Some{(vs, r)}:
      JHdrs{hput(k, vs, hs), r, JNext{}}

def hobj.val(null: Bool, hs: List<&2, Hdr.Header>, +k: String, +s: String) -> JHdrs:
  match null:
    case True{}:
      JHdrs{hput(k, [], hs), String.drop(s, 4n), JNext{}}
    case False{}:
      hobj.arr(hs, k, read_arr(s))

def hobj.colon(ok: Bool, hs: List<&2, Hdr.Header>, +k: String, +s: String) -> JHdrs:
  match ok:
    case True{}:
      hobj.val(is_null(skip_ws(String.drop(s, 1n))), hs, k, skip_ws(String.drop(s, 1n)))
    case False{}:
      JHdrs{hs, "", JBad{}}

def hobj.member(hs: List<&2, Hdr.Header>, m: Maybe<&1, String & String>) -> JHdrs:
  match m:
    case None{}:
      JHdrs{hs, "", JBad{}}
    case Some{(+k, +r)}:
      hobj.colon(first_is(skip_ws(r), 58), hs, k, skip_ws(r))

def hobj.next(+hs: List<&2, Hdr.Header>, +s: String) -> JHdrs:
  pick(JHdrs, first_is(s, 44), JHdrs{hs, skip_ws(String.drop(s, 1n)), JKey{}},
  pick(JHdrs, first_is(s, 125), JHdrs{hs, String.drop(s, 1n), JEnd{}}, JHdrs{hs, s, JBad{}}))

def hobj.loop(fuel: String, st: JHdrs) -> Maybe<&1, List<&2, Hdr.Header> & String>:
  match fuel:
    case SNil{}:
      None{}
    case SCon{c, f}:
      match st:
        case JHdrs{hs, rest, cut}:
          match cut:
            case JKey{}:
              hobj.loop(f, hobj.member(hs, Json.read_str(rest)))
            case JNext{}:
              hobj.loop(f, hobj.next(hs, skip_ws(rest)))
            case JEnd{}:
              Some{(hs, rest)}
            case JBad{}:
              None{}

def hobj.start(+s: String) -> JHdrs:
  pick(JHdrs, first_is(s, 125), JHdrs{[], String.drop(s, 1n), JEnd{}}, JHdrs{[], s, JKey{}})

def read_hdrs.of(open: Bool, +s: String) -> Maybe<&1, List<&2, Hdr.Header> & String>:
  match open:
    case True{}:
      hobj.loop(SCon{Chr{0}, s}, hobj.start(skip_ws(String.drop(s, 1n))))
    case False{}:
      None{}

def read_hdrs(+s: String) -> Maybe<&1, List<&2, Hdr.Header> & String>:
  read_hdrs.of(first_is(s, 123), s)

# the member's index: 0 attack, 1 seq, 2 code, 3 timestamp, 4 latency,
# 5 bytes_out, 6 bytes_in, 7 error, 8 body, 9 method, 10 url, 11 headers,
# 12 any other
def key_idx(+k: String) -> Nat:
  pick(Nat, String.eq(k, "attack"), 0n, pick(Nat, String.eq(k, "seq"), 1n,
  pick(Nat, String.eq(k, "code"), 2n, pick(Nat, String.eq(k, "timestamp"), 3n,
  pick(Nat, String.eq(k, "latency"), 4n, pick(Nat, String.eq(k, "bytes_out"), 5n,
  pick(Nat, String.eq(k, "bytes_in"), 6n, pick(Nat, String.eq(k, "error"), 7n,
  pick(Nat, String.eq(k, "body"), 8n, pick(Nat, String.eq(k, "method"), 9n,
  pick(Nat, String.eq(k, "url"), 10n, pick(Nat, String.eq(k, "headers"), 11n, 12n))))))))))))

def bad(+h: Hit) -> JObj:
  JObj{h, "", JBad{}}

def jv.set_str(i: Nat, +h: Hit, x: String, r: String) -> JObj:
  match i:
    case 0n:
      JObj{set_attack(h, x), r, JNext{}}
    case 1n+a:
      match a:
        case 0n:
          JObj{set_err(h, x), r, JNext{}}
        case 1n+b:
          match b:
            case 0n:
              JObj{set_method(h, x), r, JNext{}}
            case 1n+c:
              JObj{set_url(h, x), r, JNext{}}

# a string member (i: 0 attack, 1 error, 2 method, 3 url)
def jv.str(i: Nat, +h: Hit, m: Maybe<&1, String & String>) -> JObj:
  match m:
    case None{}:
      bad(h)
    case Some{(x, r)}:
      jv.set_str(i, h, x, r)

def jv.set_num(i: Nat, +h: Hit, +x: Nat, r: String) -> JObj:
  match i:
    case 0n:
      JObj{set_seq(h, x), r, JNext{}}
    case 1n+a:
      match a:
        case 0n:
          JObj{set_code(h, x), r, pick(JCut, Nat.is_lt(x, 65536n), JNext{}, JBad{})}
        case 1n+b:
          match b:
            case 0n:
              JObj{set_lat(h, x), r, JNext{}}
            case 1n+c:
              match c:
                case 0n:
                  JObj{set_bout(h, x), r, JNext{}}
                case 1n+d:
                  JObj{set_bin(h, x), r, JNext{}}

# a number member (i: 0 seq, 1 code, 2 latency, 3 bytes_out, 4 bytes_in)
def jv.num(i: Nat, +h: Hit, m: Maybe<&1, Nat & String>) -> JObj:
  match m:
    case None{}:
      bad(h)
    case Some{(x, r)}:
      jv.set_num(i, h, x, r)

def jv.ts2(+h: Hit, t: Maybe<&2, Civil.Time>, r: String) -> JObj:
  match t:
    case None{}:
      bad(h)
    case Some{x}:
      JObj{set_ts(h, x), r, JNext{}}

def jv.ts(+h: Hit, m: Maybe<&1, String & String>) -> JObj:
  match m:
    case None{}:
      bad(h)
    case Some{(x, r)}:
      jv.ts2(h, Civil.parse_rfc3339(x), r)

def jv.body2(+h: Hit, b: Maybe<&2, String>, r: String) -> JObj:
  match b:
    case None{}:
      bad(h)
    case Some{x}:
      JObj{set_body(h, x), r, JNext{}}

def jv.body(+h: Hit, m: Maybe<&1, String & String>) -> JObj:
  match m:
    case None{}:
      bad(h)
    case Some{(x, r)}:
      jv.body2(h, B64.decode(x), r)

def jv.hdrs(+h: Hit, m: Maybe<&1, List<&2, Hdr.Header> & String>) -> JObj:
  match m:
    case None{}:
      bad(h)
    case Some{(hs, r)}:
      JObj{set_hdrs(h, hs), r, JNext{}}

def jv.skip(+h: Hit, m: Maybe<&2, String>) -> JObj:
  match m:
    case None{}:
      bad(h)
    case Some{r}:
      JObj{h, r, JNext{}}

# the value of member i at s
def jv.of(i: Nat, +h: Hit, +s: String) -> JObj:
  match i:
    case 0n:
      jv.str(0n, h, Json.read_str(s))
    case 1n+i1:
      match i1:
        case 0n:
          jv.num(0n, h, read_nat(s))
        case 1n+i2:
          match i2:
            case 0n:
              jv.num(1n, h, read_nat(s))
            case 1n+i3:
              match i3:
                case 0n:
                  jv.ts(h, Json.read_str(s))
                case 1n+i4:
                  match i4:
                    case 0n:
                      jv.num(2n, h, read_nat(s))
                    case 1n+i5:
                      match i5:
                        case 0n:
                          jv.num(3n, h, read_nat(s))
                        case 1n+i6:
                          match i6:
                            case 0n:
                              jv.num(4n, h, read_nat(s))
                            case 1n+i7:
                              match i7:
                                case 0n:
                                  jv.str(1n, h, Json.read_str(s))
                                case 1n+i8:
                                  match i8:
                                    case 0n:
                                      jv.body(h, Json.read_str(s))
                                    case 1n+i9:
                                      match i9:
                                        case 0n:
                                          jv.str(2n, h, Json.read_str(s))
                                        case 1n+i10:
                                          match i10:
                                            case 0n:
                                              jv.str(3n, h, Json.read_str(s))
                                            case 1n+i11:
                                              match i11:
                                                case 0n:
                                                  jv.hdrs(h, read_hdrs(s))
                                                case 1n+i12:
                                                  jv.skip(h, skip_value(s))

# null leaves the member's field as it is (easyjson)
def jv.val(null: Bool, i: Nat, +h: Hit, +s: String) -> JObj:
  match null:
    case True{}:
      JObj{h, String.drop(s, 4n), JNext{}}
    case False{}:
      jv.of(i, h, s)

def obj.colon(ok: Bool, +h: Hit, +k: String, +s: String) -> JObj:
  match ok:
    case True{}:
      jv.val(is_null(skip_ws(String.drop(s, 1n))), key_idx(k), h, skip_ws(String.drop(s, 1n)))
    case False{}:
      bad(h)

def obj.member(+h: Hit, m: Maybe<&1, String & String>) -> JObj:
  match m:
    case None{}:
      bad(h)
    case Some{(+k, +r)}:
      obj.colon(first_is(skip_ws(r), 58), h, k, skip_ws(r))

def obj.next(+h: Hit, +s: String) -> JObj:
  pick(JObj, first_is(s, 44), JObj{h, skip_ws(String.drop(s, 1n)), JKey{}},
  pick(JObj, first_is(s, 125), JObj{h, String.drop(s, 1n), JEnd{}}, bad(h)))

# after the object: spaces, then the end of the line or of the input
def obj.fin.end(end: Bool, h: Hit, t: String) -> Maybe<&1, Hit & String>:
  match end:
    case True{}:
      Some{(h, t)}
    case False{}:
      None{}

def obj.fin.of(nl: Bool, h: Hit, +t: String) -> Maybe<&1, Hit & String>:
  match nl:
    case True{}:
      Some{(h, String.drop(t, 1n))}
    case False{}:
      obj.fin.end(String.is_empty(t), h, t)

def obj.fin(h: Hit, +s: String) -> Maybe<&1, Hit & String>:
  +t = skip_sp(s)
  obj.fin.of(first_is(t, 10), h, t)

def obj.loop(fuel: String, st: JObj) -> Maybe<&1, Hit & String>:
  match fuel:
    case SNil{}:
      None{}
    case SCon{c, f}:
      match st:
        case JObj{h, rest, cut}:
          match cut:
            case JKey{}:
              obj.loop(f, obj.member(h, Json.read_str(rest)))
            case JNext{}:
              obj.loop(f, obj.next(h, skip_ws(rest)))
            case JEnd{}:
              obj.fin(h, rest)
            case JBad{}:
              None{}

def obj.start(+s: String) -> JObj:
  pick(JObj, first_is(s, 125), JObj{zero_hit(), String.drop(s, 1n), JEnd{}}, JObj{zero_hit(), s, JKey{}})

def of_json.of(open: Bool, +t: String) -> Maybe<&1, Hit & String>:
  match open:
    case True{}:
      obj.loop(SCon{Chr{0}, t}, obj.start(skip_ws(String.drop(t, 1n))))
    case False{}:
      None{}

def of_json.go(+t: String) -> Maybe<&1, Hit & String>:
  of_json.of(first_is(t, 123), t)

def of_json(s: String) -> Maybe<&1, Hit & String>:
  of_json.go(skip_ws(s))

# ---------------------------------------------------------------------
# Streams
# ---------------------------------------------------------------------

def decode.of(json: Bool, s: String) -> Maybe<&1, Hit & String>:
  match json:
    case True{}:
      of_json(s)
    case False{}:
      of_csv(s)

def decode.go(+s: String) -> Maybe<&1, Hit & String>:
  decode.of(first_is(skip_ws(s), 123), s)

# picks JSON when the first non-blank character is '{', CSV otherwise
def decode(s: String) -> Maybe<&1, Hit & String>:
  decode.go(s)

# the results so far (last first), what is left, and whether to go on
type DAll is Data:
  DAll{acc: List<&2, Hit>, rest: String, cut: JCut}

def all.rec(acc: List<&2, Hit>, m: Maybe<&1, Hit & String>) -> DAll:
  match m:
    case None{}:
      DAll{acc, "", JBad{}}
    case Some{(h, r)}:
      DAll{Con{h, acc}, r, JKey{}}

def all.step(done: Bool, acc: List<&2, Hit>, s: String) -> DAll:
  match done:
    case True{}:
      DAll{acc, "", JEnd{}}
    case False{}:
      all.rec(acc, decode(s))

def all.loop(fuel: String, st: DAll) -> Maybe<&2, List<&2, Hit>>:
  match fuel:
    case SNil{}:
      None{}
    case SCon{c, f}:
      match st:
        case DAll{acc, +rest, cut}:
          match cut:
            case JKey{}:
              all.loop(f, all.step(String.is_empty(skip_ws(rest)), acc, rest))
            case JNext{}:
              None{}
            case JEnd{}:
              Some{List.reverse(&2, Hit, acc)}
            case JBad{}:
              None{}

def decode_all.go(+s: String) -> Maybe<&2, List<&2, Hit>>:
  all.loop(SCon{Chr{0}, SCon{Chr{0}, s}}, DAll{[], s, JKey{}})

def decode_all(s: String) -> Maybe<&2, List<&2, Hit>>:
  decode_all.go(s)

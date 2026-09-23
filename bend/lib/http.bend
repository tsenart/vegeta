# HTTP/1.1: request text and an incremental response parser.
#
# The parser is a machine over bytes: feed folds step over the input, one
# byte at a time, so feeding in pieces is feeding once (http_split). Its
# phases follow Go's net/http reader (response.go, transfer.go,
# internal/chunked.go, textproto): the status line (its first 7 bytes
# must be "HTTP/1.", so garbage fails at once), the header lines, then a
# body framed by Content-Length, by chunks, or by the close. Lines and
# bodies are kept last byte first and flipped once, when they end, so a
# body of n bytes costs O(n). Past a complete response, the bytes that
# follow are kept for the next one.
import Base
import ./hdr.bend as Hdr
import ./target.bend as Tgt
import ./dec.bend as Dec

type Resp is Data:
  Resp{code: Nat, status: String, headers: List<&2, Hdr.Header>, body: String, keep: Bool}

# where the parser is; a body's bytes and the line being read are kept
# last byte first, kept counting the body bytes held (at most -max-body)
type Ph is Data:
  # the status line: n bytes of it (up to 7) checked against "HTTP/1."
  HStat{n: Nat, line: String}
  # header lines; pend is the logical line not yet stored (a line that
  # starts with a space or a tab continues it)
  HHdr{code: Nat, status: String, minor: Nat, hs: List<&2, Hdr.Header>, pend: Maybe<&2, String>, line: String}
  # a body of left more bytes (Content-Length)
  HLen{r: Resp, left: Nat, body: String, kept: Nat}
  # a chunk-size line
  HChSize{r: Resp, line: String, body: String, kept: Nat}
  # left more bytes of chunk data
  HChData{r: Resp, left: Nat, body: String, kept: Nat}
  # the CR, then the LF, after chunk data
  HChCR{r: Resp, body: String, kept: Nat}
  HChLF{r: Resp, body: String, kept: Nat}
  # trailer lines, up to a blank one
  HTrail{r: Resp, line: String, body: String}
  # a body that ends at the close
  HClose{r: Resp, body: String, kept: Nat}
  # a complete response; rest: the bytes after it
  HDone{r: Resp, rest: String}
  HFail{msg: String}

type Parse is Data:
  Parse{max_body: Maybe<&2, Nat>, head: Bool, closed: Bool, ph: Ph}

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

# string equality byte by byte (Base's String.eq rebuilds both strings
# as it compares them, which the header lookups could not afford)
def seq.go(a: String, b: String, ok: Bool) -> Bool:
  match a:
    case SNil{}:
      Bool.and(ok, String.is_empty(b))
    case SCon{c, at}:
      match b:
        case SNil{}:
          False{}
        case SCon{d, bt}:
          match ok:
            case False{}:
              False{}
            case True{}:
              seq.go(at, bt, U32.is_eq(code(c), code(d)))

def seq(a: String, b: String) -> Bool:
  seq.go(a, b, True{})

def in_range32(+k: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(k, lo), U32.is_le(k, hi))

def is_alnum(+k: U32) -> Bool:
  Bool.or(in_range32(k, 48, 57), Bool.or(in_range32(k, 65, 90), in_range32(k, 97, 122)))

def has_char(s: String, +k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.or(U32.is_eq(code(c), k), has_char(rest, k))

def str1(k: U32) -> String:
  SCon{Chr{k}, SNil{}}

def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

# the first byte is k
def first_k(+s: String, +k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

# the byte at index i, or 0 past the end
def byte_at(s: String, i: Nat) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{+c, +rest}:
      match i:
        case 0n:
          code(c)
        case 1n+j:
          byte_at(rest, j)

def is_ows(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), U32.is_eq(k, 9))

# the first byte is a space or a tab
def first_ws(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.or(U32.is_eq(code(c), 32), U32.is_eq(code(c), 9))

# leading spaces and tabs dropped; ws says whether s starts with one (the
# loop stops at the first other byte)
def trim_ows_l.go(s: String, ws: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match ws:
        case True{}:
          trim_ows_l.go(rest, first_ws(rest))
        case False{}:
          SCon{c, rest}

def trim_ows_l(+s: String) -> String:
  trim_ows_l.go(s, first_ws(s))

def rtrim.one(w: Bool, +c: Char) -> String:
  match w:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, SNil{}}

def rtrim.of(t: String, +c: Char) -> String:
  match t:
    case SNil{}:
      rtrim.one(Bool.or(U32.is_eq(code(c), 32), U32.is_eq(code(c), 9)), c)
    case SCon{+d, +r}:
      SCon{c, SCon{d, r}}

# trailing spaces and tabs dropped, in one pass (no reversing)
def rtrim(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      rtrim.of(rtrim(rest), c)

# trims spaces and tabs at both ends (textproto.TrimString)
def trim_ows(+s: String) -> String:
  rtrim(trim_ows_l(s))

# leading spaces dropped; sp says whether s starts with one
def trim_sp_l.go(s: String, sp: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match sp:
        case True{}:
          trim_sp_l.go(rest, first_k(rest, 32))
        case False{}:
          SCon{c, rest}

def trim_sp_l(+s: String) -> String:
  trim_sp_l.go(s, first_k(s, 32))

# the line, its '\r' at the end dropped (textproto's ReadLine), from the
# line kept last byte first
def line_of(cur: String) -> String:
  match cur:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      String.reverse(pick(String, U32.is_eq(code(c), 13), rest, SCon{c, rest}))

# the bytes before the first k (all of s when there is none), as
# Tgt.before, but the loop stops at the k (hit: s starts with k)
def before.go(s: String, +k: U32, hit: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match hit:
        case True{}:
          SNil{}
        case False{}:
          SCon{c, before.go(rest, k, first_k(rest, k))}

def before(+s: String, +k: U32) -> String:
  before.go(s, k, first_k(s, k))

# the bytes after the first k ("" when there is none), as Tgt.after
def after.go(s: String, +k: U32, hit: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match hit:
        case True{}:
          rest
        case False{}:
          after.go(rest, k, first_k(rest, k))

def after(+s: String, +k: U32) -> String:
  after.go(s, k, first_k(s, k))

# s has the byte k (the loop stops at it; hit: s starts with k)
def has_byte.go(s: String, +k: U32, hit: Bool) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      match hit:
        case True{}:
          True{}
        case False{}:
          has_byte.go(rest, k, first_k(rest, k))

def has_byte(+s: String, +k: U32) -> Bool:
  has_byte.go(s, k, first_k(s, k))

def all_digits.go(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(in_range32(code(c), 48, 57), all_digits.go(rest))

def eq_ci(+a: String, +b: String) -> Bool:
  seq(String.to_lower(a), String.to_lower(b))

# Go's %q of a []string: ["a" "b"]
def quote_list.go(vs: List<&2, String>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{+v, +rest}:
      " " ++ Tgt.quote(v) ++ quote_list.go(rest)

def quote_list(vs: List<&2, String>) -> String:
  match vs:
    case Nil{}:
      "[]"
    case Con{+v, +rest}:
      "[" ++ Tgt.quote(v) ++ quote_list.go(rest) ++ "]"

# ---------------------------------------------------------------------
# Headers
# ---------------------------------------------------------------------

def hdr_key(+h: Hdr.Header) -> String:
  Hdr.Header{k, vs} = h
  k

def hdr_vals(+h: Hdr.Header) -> List<&2, String>:
  Hdr.Header{k, vs} = h
  vs

# a byte allowed in a header name (an RFC 7230 token character)
# one of !#$%&'*+-.^_`|~ (has_char on that string, spelled out)
def tok_punct(+k: U32) -> Bool:
  Bool.or(U32.is_eq(33, k), Bool.or(U32.is_eq(35, k), Bool.or(U32.is_eq(36, k), Bool.or(U32.is_eq(37, k), Bool.or(U32.is_eq(38, k),
  Bool.or(U32.is_eq(39, k), Bool.or(U32.is_eq(42, k), Bool.or(U32.is_eq(43, k), Bool.or(U32.is_eq(45, k), Bool.or(U32.is_eq(46, k),
  Bool.or(U32.is_eq(94, k), Bool.or(U32.is_eq(95, k), Bool.or(U32.is_eq(96, k), Bool.or(U32.is_eq(124, k), Bool.or(U32.is_eq(126, k), False{})))))))))))))))

def tb.of(al: Bool, +k: U32) -> Bool:
  match al:
    case True{}:
      True{}
    case False{}:
      tok_punct(k)

# a letter or digit, or one of the punctuation above (checked only then)
def token_byte(+k: U32) -> Bool:
  tb.of(is_alnum(k), k)

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

# Go's CanonicalMIMEHeaderKey: "content-type" is "Content-Type"; a name
# with a byte outside the token set stays as it is
def canon(+s: String) -> String:
  pick(String, token(s), canon.go(s, True{}), s)

# the values of header k (exact name), if any
def hdr_get(+k: String, hs: List<&2, Hdr.Header>) -> Maybe<&2, List<&2, String>>:
  match hs:
    case Nil{}:
      None{}
    case Con{+h, +rest}:
      pick(Maybe<&2, List<&2, String>>, seq(hdr_key(h), k), Some{hdr_vals(h)}, hdr_get(k, rest))

def hdr_del(+k: String, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      +r = hdr_del(k, rest)
      pick(List<&2, Hdr.Header>, seq(hdr_key(h), k), r, Con{h, r})

def hdr_set(+k: String, +vs: List<&2, String>, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      +r = hdr_set(k, vs, rest)
      pick(List<&2, Hdr.Header>, seq(hdr_key(h), k), Con{Hdr.Header{k, vs}, r}, Con{h, r})

# value v added to name k: after its values, or as a new name at the end
def hdr_add(+k: String, +v: String, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [Hdr.Header{k, [v]}]
    case Con{+h, +rest}:
      pick(List<&2, Hdr.Header>, seq(hdr_key(h), k),
        Con{Hdr.Header{k, List.append(&2, String, hdr_vals(h), [v])}, rest}, Con{h, hdr_add(k, v, rest)})

def any_ci(+v: String, vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case Con{+x, +rest}:
      Bool.or(eq_ci(x, v), any_ci(v, rest))

def is_digit(+k: U32) -> Bool:
  in_range32(k, 48, 57)

def st_version(ok: Bool, +proto: String, +status: String, +cs: String) -> Ph:
  match ok:
    case False{}:
      HFail{"malformed HTTP version " ++ Tgt.quote(proto)}
    case True{}:
      HHdr{Dec.value(cs), status, U32.to_nat((byte_at(proto, 7n) - 48 : U32)), [], None{}, ""}

def st_code(ok: Bool, +proto: String, +status: String, +cs: String) -> Ph:
  match ok:
    case False{}:
      HFail{"malformed HTTP status code " ++ Tgt.quote(cs)}
    case True{}:
      st_version(Bool.and(Nat.is_eq(String.length(proto), 8n), Bool.and(String.starts_with(proto, "HTTP/1."), is_digit(byte_at(proto, 7n)))),
        proto, status, cs)

def st_status(+proto: String, +status: String) -> Ph:
  +cs = before(status, 32)
  st_code(Bool.and(Nat.is_eq(String.length(cs), 3n), all_digits.go(cs)), proto, status, cs)

# a status line (ReadResponse): "HTTP/1.x", a space, a 3-digit code
def status_line(sp: Bool, +line: String) -> Ph:
  match sp:
    case False{}:
      HFail{"malformed HTTP response " ++ Tgt.quote(line)}
    case True{}:
      st_status(before(line, 32), trim_sp_l(after(line, 32)))

def status_of(+line: String) -> Ph:
  status_line(has_byte(line, 32), line)

def stat_byte(ok: Bool, nl: Bool, +n: Nat, +c: Char, +line: String) -> Ph:
  match ok:
    case False{}:
      HFail{"malformed HTTP response " ++ Tgt.quote(String.reverse(SCon{c, line}))}
    case True{}:
      match nl:
        case True{}:
          status_of(line_of(line))
        case False{}:
          HStat{Nat.min(1n+n, 7n), SCon{c, line}}

# past the first 7 bytes: the line so far, or its end
def stat_byte7(nl: Bool, +c: Char, +line: String) -> Ph:
  match nl:
    case True{}:
      status_of(line_of(line))
    case False{}:
      HStat{7n, SCon{c, line}}

def stat_step.of(ge: Bool, +n: Nat, +line: String, +c: Char) -> Ph:
  match ge:
    case True{}:
      stat_byte7(U32.is_eq(code(c), 10), c, line)
    case False{}:
      stat_byte(U32.is_eq(code(c), byte_at("HTTP/1.", n)), U32.is_eq(code(c), 10), n, c, line)

def stat_step(+n: Nat, +line: String, +c: Char) -> Ph:
  stat_step.of(Nat.is_ge(n, 7n), n, line, c)

# ---------------------------------------------------------------------
# Framing (transfer.go: readTransfer, fixLength, shouldClose)
# ---------------------------------------------------------------------

def split_cons(+c: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{c, SNil{}}]
    case Con{+p, +rest}:
      Con{SCon{c, p}, rest}

def split_on(+k: U32, s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [""]
    case SCon{+c, +rest}:
      +r = split_on(k, rest)
      pick(List<&2, String>, U32.is_eq(code(c), k), Con{"", r}, split_cons(c, r))

def trim_all(vs: List<&2, String>) -> List<&2, String>:
  match vs:
    case Nil{}:
      []
    case Con{+v, +rest}:
      Con{trim_ows(v), trim_all(rest)}

# the comma-separated tokens of a header value, trimmed
def token_list(+v: String) -> List<&2, String>:
  trim_all(split_on(44, v))

def any_token(+t: String, vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case Con{+v, +rest}:
      Bool.or(any_ci(t, token_list(v)), any_token(t, rest))

def some_token(+t: String, +m: Maybe<&2, List<&2, String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{vs}:
      any_token(t, vs)

# some Connection value has the token t (Go's HeaderValuesContainsToken)
def conn_token(+t: String, +hs: List<&2, Hdr.Header>) -> Bool:
  some_token(t, hdr_get("Connection", hs))

# the connection stays usable (Go's shouldClose): HTTP/1.1 unless it
# says close; HTTP/1.0 only when it says keep-alive (and not close)
def keep_of.of(ten: Bool, +close: Bool, +hs: List<&2, Hdr.Header>) -> Bool:
  match ten:
    case True{}:
      Bool.and(conn_token("keep-alive", hs), Bool.not(close))
    case False{}:
      Bool.not(close)

def keep_of(+minor: Nat, +hs: List<&2, Hdr.Header>) -> Bool:
  keep_of.of(Nat.is_eq(minor, 0n), conn_token("close", hs), hs)

# HTTP/1.1 drops the Connection header that says close (shouldClose)
def conn_fix.of(drop: Bool, +hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match drop:
    case True{}:
      hdr_del("Connection", hs)
    case False{}:
      hs

def conn_fix(+minor: Nat, +hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  conn_fix.of(Bool.and(Bool.not(Nat.is_eq(minor, 0n)), conn_token("close", hs)), hs)

def first_no_cache(+m: Maybe<&2, List<&2, String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{vs}:
      match vs:
        case Nil{}:
          False{}
        case Con{+v, +rest}:
          seq(v, "no-cache")

# "Pragma: no-cache" without Cache-Control gains "Cache-Control:
# no-cache" (fixPragmaCacheControl)
def pragma_fix.cc(none: Bool, +hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match none:
    case True{}:
      List.append(&2, Hdr.Header, hs, [Hdr.Header{"Cache-Control", ["no-cache"]}])
    case False{}:
      hs

def pragma_fix.of(nc: Bool, +hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match nc:
    case True{}:
      pragma_fix.cc(Maybe.is_none(&2, List<&2, String>, hdr_get("Cache-Control", hs)), hs)
    case False{}:
      hs

def pragma_fix(+hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  pragma_fix.of(first_no_cache(hdr_get("Pragma", hs)), hs)

def interim(+c: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n)))

# no body whatever the headers say: to HEAD, 1xx, 204, 304
def no_body(+head: Bool, +c: Nat) -> Bool:
  Bool.or(head, Bool.or(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))))

def fr_len(m: Maybe<&2, Nat>, +r: Resp) -> Ph:
  match m:
    case None{}:
      Resp{c, st, hs, b, k} = r
      HClose{Resp{c, st, hs, b, False{}}, "", 0n}
    case Some{n}:
      match n:
        case 0n:
          HDone{r, ""}
        case 1n+p:
          HLen{r, 1n+p, "", 0n}

def fr_cl_read(ok: Bool, +v: String, +r: Resp) -> Ph:
  match ok:
    case False{}:
      pick(Ph, String.is_empty(v), HFail{"invalid empty Content-Length \"\""}, HFail{"bad Content-Length " ++ Tgt.quote(v)})
    case True{}:
      fr_len(Some{Dec.value(v)}, r)

def all_eq(+v: String, vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(seq(x, v), all_eq(v, rest))

def fr_cl_one(ok: Bool, +vs: List<&2, String>, +v: String, +r: Resp) -> Ph:
  match ok:
    case False{}:
      HFail{"http: message cannot contain multiple Content-Length headers; got " ++ quote_list(vs)}
    case True{}:
      Resp{c, st, hs, b, k} = r
      fr_cl_read(Bool.and(Bool.not(String.is_empty(v)), all_digits.go(v)), v,
        Resp{c, st, hdr_set("Content-Length", [v], hs), b, k})

def fr_cl_vals(vs: List<&2, String>, +r: Resp) -> Ph:
  match vs:
    case Nil{}:
      fr_len(None{}, r)
    case Con{+v, +rest}:
      fr_cl_one(all_eq(v, rest), Con{v, rest}, v, r)

def fr_cl(m: Maybe<&2, List<&2, String>>, +r: Resp) -> Ph:
  match m:
    case None{}:
      fr_len(None{}, r)
    case Some{vs}:
      fr_cl_vals(vs, r)

def fr_chunked(chunked: Bool, +r: Resp) -> Ph:
  match chunked:
    case True{}:
      Resp{c, st, hs, b, k} = r
      HChSize{Resp{c, st, hdr_del("Content-Length", hs), b, k}, "", "", 0n}
    case False{}:
      Resp{c, st, hs, b, k} = r
      fr_cl(hdr_get("Content-Length", hs), Resp{c, st, hs, b, k})

def fr_te_one(ch: Bool, +v: String, +r: Resp) -> Ph:
  match ch:
    case True{}:
      fr_chunked(True{}, r)
    case False{}:
      HFail{"unsupported transfer encoding: " ++ Tgt.quote(v)}

def fr_te_many(many: Bool, +v: String, +rest: List<&2, String>, +r: Resp) -> Ph:
  match many:
    case True{}:
      HFail{"too many transfer encodings: " ++ quote_list(Con{v, rest})}
    case False{}:
      fr_te_one(eq_ci(v, "chunked"), v, r)

def fr_te_vals(vs: List<&2, String>, +r: Resp) -> Ph:
  match vs:
    case Nil{}:
      fr_chunked(False{}, r)
    case Con{+v, +rest}:
      fr_te_many(Bool.not(List.is_empty(&2, String, rest)), v, rest, r)

# Transfer-Encoding counts from HTTP/1.1 on (and is never kept)
def fr_te_some(ten: Bool, +vs: List<&2, String>, +r: Resp) -> Ph:
  match ten:
    case True{}:
      fr_chunked(False{}, r)
    case False{}:
      fr_te_vals(vs, r)

def fr_te(m: Maybe<&2, List<&2, String>>, +minor: Nat, +r: Resp) -> Ph:
  match m:
    case None{}:
      fr_chunked(False{}, r)
    case Some{+vs}:
      fr_te_some(Nat.is_eq(minor, 0n), vs, r)

def fr_body(nb: Bool, +code: Nat, +minor: Nat, +te: Maybe<&2, List<&2, String>>, +r: Resp) -> Ph:
  match nb:
    case True{}:
      pick(Ph, interim(code), HStat{0n, ""}, HDone{r, ""})
    case False{}:
      fr_te(te, minor, r)

# the end of the head: an interim response starts over; a response with
# no body is complete; otherwise the body's framing
def framing(+code: Nat, +status: String, +minor: Nat, +hs0: List<&2, Hdr.Header>, +head: Bool) -> Ph:
  +hs = pragma_fix(hs0)
  fr_body(no_body(head, code), code, minor, hdr_get("Transfer-Encoding", hs),
    Resp{code, status, conn_fix(minor, hdr_del("Transfer-Encoding", hs)), "", Bool.and(keep_of(minor, hs), Bool.not(Nat.is_eq(code, 101n)))})

# ---------------------------------------------------------------------
# Header lines
# ---------------------------------------------------------------------

def name_byte(+k: U32) -> Bool:
  Bool.or(token_byte(k), U32.is_eq(k, 32))

def all_name(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(name_byte(code(c)), all_name(rest))

# a byte allowed in a value: tab, space, visible ASCII, or past 0x7f
def value_byte(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 9), Bool.and(U32.is_ge(k, 32), Bool.not(U32.is_eq(k, 127))))

def all_value(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(value_byte(code(c)), all_value(rest))

def store_of(ok: Bool, +k: String, +v: String, +p: String, +hs: List<&2, Hdr.Header>) -> Result<&2, &2, String, List<&2, Hdr.Header>>:
  match ok:
    case False{}:
      Fail{"malformed MIME header line: " ++ Tgt.quote(p)}
    case True{}:
      Done{hdr_add(pick(String, has_byte(k, 32), k, canon(k)), trim_ows(v), hs)}

def store.kv(+k: String, +v: String, +p: String, +hs: List<&2, Hdr.Header>) -> Result<&2, &2, String, List<&2, Hdr.Header>>:
  store_of(Bool.and(Bool.and(Bool.not(String.is_empty(k)), all_name(k)), all_value(v)), k, v, p, hs)

# a logical header line stored: the name canonical (kept as written when
# it has a space), the value trimmed, grouped under its name
def store(+p: String, +hs: List<&2, Hdr.Header>) -> Result<&2, &2, String, List<&2, Hdr.Header>>:
  store.kv(before(p, 58), after(p, 58), p, hs)

def store_pend(+pend: Maybe<&2, String>, +hs: List<&2, Hdr.Header>) -> Result<&2, &2, String, List<&2, Hdr.Header>>:
  match pend:
    case None{}:
      Done{hs}
    case Some{p}:
      store(p, hs)

def hdr_next(r: Result<&2, &2, String, List<&2, Hdr.Header>>, +code: Nat, +status: String, +minor: Nat, +line: String) -> Ph:
  match r:
    case Fail{e}:
      HFail{e}
    case Done{hs}:
      HHdr{code, status, minor, hs, Some{trim_ows(line)}, ""}

def hdr_fold(+code: Nat, +status: String, +minor: Nat, +hs: List<&2, Hdr.Header>, +pend: Maybe<&2, String>, +line: String) -> Ph:
  match pend:
    case None{}:
      HFail{"malformed MIME header initial line: " ++ Tgt.quote(line)}
    case Some{p}:
      HHdr{code, status, minor, hs, Some{p ++ " " ++ trim_ows(line)}, ""}

def hdr_new(colon: Bool, +code: Nat, +status: String, +minor: Nat, +hs: List<&2, Hdr.Header>, +pend: Maybe<&2, String>, +line: String) -> Ph:
  match colon:
    case False{}:
      HFail{"malformed MIME header: missing colon: " ++ Tgt.quote(line)}
    case True{}:
      hdr_next(store_pend(pend, hs), code, status, minor, line)

def hdr_cont(cont: Bool, +code: Nat, +status: String, +minor: Nat, +hs: List<&2, Hdr.Header>, +pend: Maybe<&2, String>, +line: String) -> Ph:
  match cont:
    case True{}:
      hdr_fold(code, status, minor, hs, pend, line)
    case False{}:
      hdr_new(has_byte(line, 58), code, status, minor, hs, pend, line)

def hdr_end(r: Result<&2, &2, String, List<&2, Hdr.Header>>, +code: Nat, +status: String, +minor: Nat, +mb: Maybe<&2, Nat>, +head: Bool) -> Ph:
  match r:
    case Fail{e}:
      HFail{e}
    case Done{hs}:
      framing(code, status, minor, hs, head)

def hdr_line(blank: Bool, +code: Nat, +status: String, +minor: Nat, +hs: List<&2, Hdr.Header>, +pend: Maybe<&2, String>, +line: String, +mb: Maybe<&2, Nat>, +head: Bool) -> Ph:
  match blank:
    case True{}:
      hdr_end(store_pend(pend, hs), code, status, minor, mb, head)
    case False{}:
      hdr_cont(Bool.or(first_is(line, 32), first_is(line, 9)), code, status, minor, hs, pend, line)

def hdr_byte(nl: Bool, +code: Nat, +status: String, +minor: Nat, +hs: List<&2, Hdr.Header>, +pend: Maybe<&2, String>, +cur: String, +c: Char, +mb: Maybe<&2, Nat>, +head: Bool) -> Ph:
  match nl:
    case True{}:
      +line = line_of(cur)
      hdr_line(String.is_empty(line), code, status, minor, hs, pend, line, mb, head)
    case False{}:
      HHdr{code, status, minor, hs, pend, SCon{c, cur}}

# ---------------------------------------------------------------------
# Bodies
# ---------------------------------------------------------------------

def with_body(+r: Resp, +b: String) -> Resp:
  Resp{c, st, hs, x, k} = r
  Resp{c, st, hs, b, k}

# there is room for one more body byte under -max-body
def room(+mb: Maybe<&2, Nat>, +kept: Nat) -> Bool:
  match mb:
    case None{}:
      True{}
    case Some{m}:
      Nat.is_lt(kept, m)

def len_next(last: Bool, +r: Resp, +left: Nat, +body: String, +kept: Nat) -> Ph:
  match last:
    case True{}:
      HDone{with_body(r, String.reverse(body)), ""}
    case False{}:
      HLen{r, left, body, kept}

def len_step(+mb: Maybe<&2, Nat>, +r: Resp, +left: Nat, +body: String, +kept: Nat, +c: Char) -> Ph:
  +ok = room(mb, kept)
  len_next(Nat.is_eq(left, 1n), r, Nat.sub(left, 1n), pick(String, ok, SCon{c, body}, body), pick(Nat, ok, 1n+kept, kept))

def hex_val(+k: U32) -> Nat:
  U32.to_nat(pick(U32, in_range32(k, 48, 57), (k - 48 : U32), pick(U32, in_range32(k, 65, 70), (k - 55 : U32), (k - 87 : U32))))

def all_hex(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Tgt.is_hex(code(c)), all_hex(rest))

def hex_value(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      hex_value(rest, Nat.add(Nat.mul(acc, 16n), hex_val(code(c))))

def trim_ows_r(+s: String) -> String:
  rtrim(s)

def chunk_size(n: Nat, +r: Resp, +body: String, +kept: Nat) -> Ph:
  match n:
    case 0n:
      HTrail{r, "", body}
    case 1n+p:
      HChData{r, 1n+p, body, kept}

def chunk_hex(+h: String, +r: Resp, +body: String, +kept: Nat) -> Ph:
  pick(Ph, String.is_empty(h), HFail{"empty hex number for chunk length"},
    pick(Ph, all_hex(h), chunk_size(hex_value(h, 0n), r, body, kept), HFail{"invalid byte in chunk length"}))

def chunk_line(crlf: Bool, +line: String, +r: Resp, +body: String, +kept: Nat) -> Ph:
  match crlf:
    case False{}:
      HFail{"chunked line ends with bare LF"}
    case True{}:
      pick(Ph, has_byte(line, 13), HFail{"invalid CR in chunked line"},
        chunk_hex(before(trim_ows_r(line), 59), r, body, kept))

# a chunk-size line ends: CRLF (no other CR), extensions dropped, hex
def chunk_end(cur: String, +r: Resp, +body: String, +kept: Nat) -> Ph:
  match cur:
    case SNil{}:
      HFail{"chunked line ends with bare LF"}
    case SCon{+c, +rest}:
      chunk_line(U32.is_eq(code(c), 13), String.reverse(rest), r, body, kept)

def size_byte(nl: Bool, +r: Resp, +cur: String, +body: String, +kept: Nat, +c: Char) -> Ph:
  match nl:
    case True{}:
      chunk_end(cur, r, body, kept)
    case False{}:
      HChSize{r, SCon{c, cur}, body, kept}

def data_next(last: Bool, +r: Resp, +left: Nat, +body: String, +kept: Nat) -> Ph:
  match last:
    case True{}:
      HChCR{r, body, kept}
    case False{}:
      HChData{r, left, body, kept}

def data_step(+mb: Maybe<&2, Nat>, +r: Resp, +left: Nat, +body: String, +kept: Nat, +c: Char) -> Ph:
  +ok = room(mb, kept)
  data_next(Nat.is_eq(left, 1n), r, Nat.sub(left, 1n), pick(String, ok, SCon{c, body}, body), pick(Nat, ok, 1n+kept, kept))

def trail_line(blank: Bool, +r: Resp, +body: String) -> Ph:
  match blank:
    case True{}:
      HDone{with_body(r, String.reverse(body)), ""}
    case False{}:
      HTrail{r, "", body}

def trail_byte(nl: Bool, +r: Resp, +cur: String, +body: String, +c: Char) -> Ph:
  match nl:
    case True{}:
      trail_line(String.is_empty(line_of(cur)), r, body)
    case False{}:
      HTrail{r, SCon{c, cur}, body}

def close_step(+mb: Maybe<&2, Nat>, +r: Resp, +body: String, +kept: Nat, +c: Char) -> Ph:
  +ok = room(mb, kept)
  HClose{r, pick(String, ok, SCon{c, body}, body), pick(Nat, ok, 1n+kept, kept)}

# ---------------------------------------------------------------------
# The machine
# ---------------------------------------------------------------------

def step_ph(ph: Ph, +mb: Maybe<&2, Nat>, +head: Bool, +c: Char) -> Ph:
  match ph:
    case HStat{n, line}:
      stat_step(n, line, c)
    case HHdr{code, status, minor, hs, pend, line}:
      hdr_byte(U32.is_eq(Tgt.code(c), 10), code, status, minor, hs, pend, line, c, mb, head)
    case HLen{r, left, body, kept}:
      len_step(mb, r, left, body, kept, c)
    case HChSize{r, line, body, kept}:
      size_byte(U32.is_eq(Tgt.code(c), 10), r, line, body, kept, c)
    case HChData{r, left, body, kept}:
      data_step(mb, r, left, body, kept, c)
    case HChCR{r, body, kept}:
      pick(Ph, U32.is_eq(Tgt.code(c), 13), HChLF{r, body, kept}, HFail{"malformed chunked encoding"})
    case HChLF{r, body, kept}:
      pick(Ph, U32.is_eq(Tgt.code(c), 10), HChSize{r, "", body, kept}, HFail{"malformed chunked encoding"})
    case HTrail{r, line, body}:
      trail_byte(U32.is_eq(Tgt.code(c), 10), r, line, body, c)
    case HClose{r, body, kept}:
      close_step(mb, r, body, kept, c)
    case HDone{r, rest}:
      HDone{r, SCon{c, rest}}
    case HFail{m}:
      HFail{m}

def step(+p: Parse, +c: Char) -> Parse:
  Parse{mb, head, closed, ph} = p
  Parse{mb, head, closed, step_ph(ph, mb, head, c)}

def feed.go(s: String, p: Parse) -> Parse:
  match s:
    case SNil{}:
      p
    case SCon{+c, +rest}:
      feed.go(rest, step(p, c))

def start(mb: Maybe<&2, Nat>, head: Bool) -> Parse:
  Parse{mb, head, False{}, HStat{0n, ""}}

def feed(+p: Parse, s: String) -> Parse:
  feed.go(s, p)

def eof(+p: Parse) -> Parse:
  Parse{mb, head, closed, ph} = p
  Parse{mb, head, True{}, ph}

def done_open(ph: Ph) -> Maybe<&1, Result<&1, &1, String, Resp & String>>:
  match ph:
    case HDone{r, rest}:
      Some{Done{(r, String.reverse(rest))}}
    case HFail{m}:
      Some{Fail{m}}
    case _:
      None{}

def eof_stat(ph: Ph) -> String:
  match ph:
    case HFail{m}:
      m
    case _:
      "unexpected EOF"

# after the close: a complete response, a body that ends at the close, a
# half status line's complaint, or else "unexpected EOF"
def done_eof(ph: Ph) -> Maybe<&1, Result<&1, &1, String, Resp & String>>:
  match ph:
    case HDone{r, rest}:
      Some{Done{(r, String.reverse(rest))}}
    case HFail{m}:
      Some{Fail{m}}
    case HClose{r, body, kept}:
      Some{Done{(with_body(r, String.reverse(body)), "")}}
    case HStat{n, +line}:
      Some{Fail{pick(String, String.is_empty(line), "unexpected EOF", eof_stat(status_of(line_of(line))))}}
    case _:
      Some{Fail{"unexpected EOF"}}

def done.of(closed: Bool, ph: Ph) -> Maybe<&1, Result<&1, &1, String, Resp & String>>:
  match closed:
    case True{}:
      done_eof(ph)
    case False{}:
      done_open(ph)

def done(+p: Parse) -> Maybe<&1, Result<&1, &1, String, Resp & String>>:
  Parse{mb, head, closed, ph} = p
  done.of(closed, ph)

def partial_of(ph: Ph) -> String:
  match ph:
    case HLen{r, left, body, kept}:
      String.reverse(body)
    case HChSize{r, line, body, kept}:
      String.reverse(body)
    case HChData{r, left, body, kept}:
      String.reverse(body)
    case HChCR{r, body, kept}:
      String.reverse(body)
    case HChLF{r, body, kept}:
      String.reverse(body)
    case HTrail{r, line, body}:
      String.reverse(body)
    case HClose{r, body, kept}:
      String.reverse(body)
    case HDone{r, rest}:
      Resp{c, st, hs, b, k} = r
      b
    case _:
      ""

# the body read so far (after de-chunking, within max-body)
def partial(+p: Parse) -> String:
  Parse{mb, head, closed, ph} = p
  partial_of(ph)

# ---------------------------------------------------------------------
# Requests (the LAWS helper wire_request, def for def)
# ---------------------------------------------------------------------

def nl_to_space(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, Bool.or(U32.is_eq(code(c), 10), U32.is_eq(code(c), 13)), " ", SCon{c, SNil{}}) ++ nl_to_space(rest)

def insert_hdr(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [h]
    case Con{+x, +rest}:
      pick(List<&2, Hdr.Header>, String.is_lt(hdr_key(h), hdr_key(x)), Con{h, Con{x, rest}}, Con{x, insert_hdr(h, rest)})

# headers ordered by name (Go writes http.Header in sorted key order)
def sort_hdrs(hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      insert_hdr(h, sort_hdrs(rest))

def hdr_lines(+k: String, vs: List<&2, String>) -> String:
  match vs:
    case Nil{}:
      ""
    case Con{+v, +rest}:
      k ++ ": " ++ trim_ows(nl_to_space(v)) ++ "\r\n" ++ hdr_lines(k, rest)

def hdrs_text(hs: List<&2, Hdr.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{+h, +rest}:
      pick(String, token(hdr_key(h)), hdr_lines(hdr_key(h), hdr_vals(h)), "") ++ hdrs_text(rest)

def port_text(+p: Maybe<&2, Nat>) -> String:
  match p:
    case None{}:
      ""
    case Some{n}:
      ":" ++ Dec.show(n)

def url_host(+u: Tgt.Url) -> String:
  Tgt.Url{sc, host, port, path} = u
  host ++ port_text(port)

def url_path(+u: Tgt.Url) -> String:
  Tgt.Url{sc, host, port, path} = u
  path

def hexu(+n: U32) -> String:
  str1(pick(U32, U32.is_lt(n, 10), (48 + n : U32), (55 + n : U32)))

def hex_val32(+k: U32) -> U32:
  pick(U32, in_range32(k, 48, 57), (k - 48 : U32), pick(U32, in_range32(k, 65, 70), (k - 55 : U32), (k - 87 : U32)))

def unreserved(+k: U32) -> Bool:
  Bool.or(is_alnum(k), has_char("-._~", k))

# Go's validEncoded: a path Go sends as written
def valid_encoded(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.or(unreserved(code(c)), has_char("!$&'()*+,;=:@/%[]", code(c))), valid_encoded(rest))

# %XX sequences decoded
def unescape.go(+fuel: Nat, +s: String) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      +pct = Bool.and(first_is(s, 37), Nat.is_ge(String.length(s), 3n))
      +v = pick(U32, pct, ((hex_val32(byte_at(s, 1n)) * 16 + hex_val32(byte_at(s, 2n))) .&. 255 : U32), byte_at(s, 0n))
      pick(String, String.is_empty(s), "", str1(v) ++ unescape.go(f, String.drop(s, pick(Nat, pct, 3n, 1n))))

def unescape(+s: String) -> String:
  unescape.go(String.length(s), s)

# Go's escape(s, encodePath): all but unreserved and $&+,/:;=@ as %XX
def escape_path(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      +k = code(c)
      pick(String, Bool.or(unreserved(k), has_char("$&+,/:;=@", k)), str1(k), "%" ++ hexu((k >> 4n : U32)) ++ hexu((k .&. 15 : U32)))
        ++ escape_path(rest)

def before_q(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 63), "", SCon{c, before_q(rest)})

# the request target Go writes: the path as EscapedPath gives it (as
# written when validly encoded, else re-escaped), then the raw query
def request_uri(+path: String) -> String:
  +p = before_q(path)
  +q = String.drop(path, String.length(p))
  pick(String, valid_encoded(p), p, escape_path(unescape(p))) ++ q

def first_of(+d: String, +m: Maybe<&2, List<&2, String>>) -> String:
  match m:
    case None{}:
      d
    case Some{vs}:
      Maybe.default(&2, String, List.head(&2, String, vs), d)

def needs_length(+m: String, +body: String) -> Bool:
  Bool.or(Bool.not(String.is_empty(body)), Bool.or(String.eq(m, "POST"), Bool.or(String.eq(m, "PUT"), String.eq(m, "PATCH"))))

# the headers without name k, compared exactly (Go's Header map is keyed
# by the name as written)
def drop_exact(+k: String, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      +r = drop_exact(k, rest)
      pick(List<&2, Hdr.Header>, String.eq(hdr_key(h), k), r, Con{h, r})

# Header.Set: every value under k replaced by v
def set_hdr(+k: String, +v: String, +hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  List.append(&2, Hdr.Header, drop_exact(k, hs), [Hdr.Header{k, [v]}])

def tgt_method(+t: Tgt.Target) -> String:
  Tgt.Target{m, u, hs, b} = t
  m

def tgt_hdrs(+t: Tgt.Target) -> List<&2, Hdr.Header>:
  Tgt.Target{m, u, hs, b} = t
  hs

# the request text Go's transport writes for a target (Accept-Encoding
# left out: bodies arrive as the server sent them): the request line;
# Host and User-Agent from the target's "Host" and "User-Agent" headers
# when it has them (exact names); the length; X-Vegeta-Attack (when
# named) and X-Vegeta-Seq set as Header.Set does; every other header
# sorted by name, less the framing headers Go never takes from the user
# (exact names); and Connection: close last
def request(+t: Tgt.Target, +u: Tgt.Url, +body: String, +seq: Nat, +name: String, ka: Bool) -> String:
  +hs = tgt_hdrs(t)
  +named = pick(List<&2, Hdr.Header>, String.is_empty(name), hs, set_hdr("X-Vegeta-Attack", name, hs))
  +rest = drop_exact("Host", drop_exact("User-Agent", drop_exact("Content-Length", drop_exact("Transfer-Encoding", drop_exact("Trailer",
            set_hdr("X-Vegeta-Seq", Dec.show(seq), named))))))
  tgt_method(t) ++ " " ++ request_uri(url_path(u)) ++ " HTTP/1.1\r\n"
    ++ "Host: " ++ first_of(url_host(u), hdr_get("Host", hs)) ++ "\r\n"
    ++ "User-Agent: " ++ first_of("Go-http-client/1.1", hdr_get("User-Agent", hs)) ++ "\r\n"
    ++ pick(String, needs_length(tgt_method(t), body), "Content-Length: " ++ Dec.show(String.length(body)) ++ "\r\n", "")
    ++ hdrs_text(sort_hdrs(rest))
    ++ pick(String, ka, "", "Connection: close\r\n") ++ "\r\n" ++ body

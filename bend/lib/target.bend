# URLs and the http targets format.
#
# parse_url reads an http URL the way the attack uses it: a host of name
# characters, a port as written (None when there is none), and the path
# with its query (the fragment dropped; "/" when there is none).
#
# parse_all reads Go's http targets format (lib/targets.go,
# NewHTTPTargeter): the text is cut into lines, and each line moves a
# small state machine (looking for a target, just after its request line,
# in its headers), so the parse is one pass over the lines.
import Base
import ./hdr.bend as Hdr
import ./dec.bend as Dec

type Url is Data:
  Url{scheme: String, host: String, port: Maybe<&2, Nat>, path: String}

type Target is Data:
  Target{method: String, url: String, headers: List<&2, Hdr.Header>, body: Maybe<&2, String>}

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

def is_letter(+k: U32) -> Bool:
  Bool.or(in_range32(k, 65, 90), in_range32(k, 97, 122))

def is_upper(+k: U32) -> Bool:
  in_range32(k, 65, 90)

def is_hex(+k: U32) -> Bool:
  Bool.or(in_range32(k, 48, 57), Bool.or(in_range32(k, 65, 70), in_range32(k, 97, 102)))

def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

# Every scan below stops where it can: a loop carries the verdict on the
# byte it is at (a flag it matches itself), since a `pick` would evaluate
# the recursive call on both sides and walk the whole string.

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

def str1(k: U32) -> String:
  SCon{Chr{k}, SNil{}}

# Go's ASCII white space (strings.TrimSpace, for the bytes below 0x80)
def is_ws(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), Bool.and(U32.is_ge(k, 9), U32.is_le(k, 13)))

def first_ws(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      is_ws(code(c))

# ws: s starts with white space
def trim_ws_l.go(s: String, ws: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match ws:
        case True{}:
          trim_ws_l.go(rest, first_ws(rest))
        case False{}:
          SCon{c, rest}

def trim_ws_l(+s: String) -> String:
  trim_ws_l.go(s, first_ws(s))

def trim_ws_r.of(+t: String, +c: Char) -> String:
  pick(String, Bool.and(String.is_empty(t), is_ws(code(c))), SNil{}, SCon{c, t})

# white space at the end dropped, in one pass
def trim_ws_r(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      trim_ws_r.of(trim_ws_r(rest), c)

# strings.TrimSpace (ASCII white space)
def trim_ws(+s: String) -> String:
  trim_ws_r(trim_ws_l(s))

def is_ctl(+k: U32) -> Bool:
  Bool.or(U32.is_lt(k, 32), U32.is_eq(k, 127))

def has_ctl(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.or(is_ctl(code(c)), has_ctl(rest))

# the bytes before the first k (all of s when there is none)
def before.go(s: String, +k: U32, hit: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match hit:
        case True{}:
          SNil{}
        case False{}:
          SCon{c, before.go(rest, k, first_is(rest, k))}

def before(+s: String, +k: U32) -> String:
  before.go(s, k, first_is(s, k))

# the bytes after the first k ("" when there is none)
def after.go(s: String, +k: U32, hit: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match hit:
        case True{}:
          rest
        case False{}:
          after.go(rest, k, first_is(rest, k))

def after(+s: String, +k: U32) -> String:
  after.go(s, k, first_is(s, k))

def hexd(+n: U32) -> String:
  str1(pick(U32, U32.is_lt(n, 10), (48 + n : U32), (87 + n : U32)))

def quote_byte(+k: U32) -> String:
  pick(String, U32.is_eq(k, 34), "\\\"",
  pick(String, U32.is_eq(k, 92), "\\\\",
  pick(String, U32.is_eq(k, 10), "\\n",
  pick(String, U32.is_eq(k, 13), "\\r",
  pick(String, U32.is_eq(k, 9), "\\t",
  pick(String, U32.is_eq(k, 7), "\\a",
  pick(String, U32.is_eq(k, 8), "\\b",
  pick(String, U32.is_eq(k, 12), "\\f",
  pick(String, U32.is_eq(k, 11), "\\v",
  pick(String, in_range32(k, 32, 126), str1(k),
    "\\x" ++ hexd((k >> 4n : U32)) ++ hexd((k .&. 15 : U32))))))))))))

def quote.go(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      quote_byte(code(c)) ++ quote.go(rest)

# Go's %q for ASCII text (bytes past 0x7e are written as \xHH)
def quote(+s: String) -> String:
  "\"" ++ quote.go(s) ++ "\""

# ---------------------------------------------------------------------
# URLs
# ---------------------------------------------------------------------

def is_host_char(+k: U32) -> Bool:
  Bool.or(is_alnum(k), Bool.or(U32.is_eq(k, 46), Bool.or(U32.is_eq(k, 45), U32.is_eq(k, 95))))

def all_host(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(is_host_char(code(c)), all_host(rest))

def ends_auth(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 47), Bool.or(U32.is_eq(k, 63), U32.is_eq(k, 35)))

# the authority: the bytes up to the first '/', '?' or '#'
def first_ends_auth(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      ends_auth(code(c))

def auth_of.go(s: String, end: Bool) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      match end:
        case True{}:
          SNil{}
        case False{}:
          SCon{c, auth_of.go(rest, first_ends_auth(rest))}

def auth_of(+s: String) -> String:
  auth_of.go(s, first_ends_auth(s))

# the path as the request uses it: the fragment dropped, "/" when empty
def path_of(+p: String) -> String:
  +q = before(p, 35)
  pick(String, String.is_empty(q), "/", pick(String, first_is(q, 63), "/" ++ q, q))

# the first malformed %XX escape (Go's EscapeError text), if any
# s starts with a malformed escape
def first_bad(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.and(U32.is_eq(code(c), 37), Bool.not(Bool.and(is_hex(byte_at(rest, 0n)), is_hex(byte_at(rest, 1n)))))

def bad_escape.go(s: String, bad: Bool) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +rest}:
      match bad:
        case True{}:
          Some{SCon{c, String.take(rest, 2n)}}
        case False{}:
          bad_escape.go(rest, first_bad(rest))

def bad_escape(+s: String) -> Maybe<&2, String>:
  bad_escape.go(s, first_bad(s))

def url_port.of(ok: Bool, +host: String, +v: Nat, +p: String, +path: String) -> Result<&2, &2, String, Url>:
  match ok:
    case True{}:
      Done{Url{"http", host, Some{v}, path}}
    case False{}:
      Fail{"invalid port " ++ quote(":" ++ p) ++ " after host"}

def url_port.read(m: Maybe<&2, Nat>, +host: String, +p: String, +path: String) -> Result<&2, &2, String, Url>:
  match m:
    case None{}:
      Fail{"invalid port " ++ quote(":" ++ p) ++ " after host"}
    case Some{+v}:
      url_port.of(Bool.and(Nat.is_ge(v, 1n), Nat.is_le(v, 65535n)), host, v, p, path)

# host[:port] (an empty port is no port, as in Go)
def url_port(has: Bool, +host: String, +p: String, +path: String) -> Result<&2, &2, String, Url>:
  match has:
    case False{}:
      Done{Url{"http", host, None{}, path}}
    case True{}:
      url_port.read(pick(Maybe<&2, Nat>, String.is_empty(p), Some{80n}, Dec.read(p)), host, p, path)

def url_esc(m: Maybe<&2, String>, +host: String, +auth: String, +path: String) -> Result<&2, &2, String, Url>:
  match m:
    case Some{e}:
      Fail{"invalid URL escape " ++ quote(e)}
    case None{}:
      url_port(Bool.and(has_char(auth, 58), Bool.not(String.is_empty(after(auth, 58)))), host, after(auth, 58), path)

def url_path(ctl: Bool, +host: String, +auth: String, +path: String) -> Result<&2, &2, String, Url>:
  match ctl:
    case True{}:
      Fail{"net/url: invalid control character in URL"}
    case False{}:
      url_esc(bad_escape(before(path, 63)), host, auth, path)

def url_host(ok: Bool, +host: String, +auth: String, +path: String) -> Result<&2, &2, String, Url>:
  match ok:
    case False{}:
      pick(Result<&2, &2, String, Url>, String.is_empty(host), Fail{"http: no Host in request URL"},
        Fail{"invalid host " ++ quote(auth)})
    case True{}:
      url_path(has_ctl(path), host, auth, path)

# after "http://"
def url_rest(+r: String) -> Result<&2, &2, String, Url>:
  +auth = auth_of(r)
  +host = before(auth, 58)
  url_host(Bool.and(Bool.not(String.is_empty(host)), all_host(host)), host, auth,
    path_of(String.drop(r, String.length(auth))))

def scheme_char(+k: U32) -> Bool:
  Bool.or(is_alnum(k), Bool.or(U32.is_eq(k, 43), Bool.or(U32.is_eq(k, 45), U32.is_eq(k, 46))))

def all_scheme(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(scheme_char(code(c)), all_scheme(rest))

# the scheme Go reads off s ("" when there is none)
def scheme_of(+s: String) -> String:
  +sc = before(s, 58)
  pick(String, Bool.and(Bool.and(has_char(s, 58), is_letter(byte_at(sc, 0n))), all_scheme(sc)), sc, "")

def parse_url.of(http: Bool, https: Bool, +s: String) -> Result<&2, &2, String, Url>:
  match http:
    case True{}:
      url_rest(String.drop(s, 7n))
    case False{}:
      match https:
        case True{}:
          Fail{"https is not supported"}
        case False{}:
          Fail{"unsupported protocol scheme " ++ quote(String.to_lower(scheme_of(s)))}

def parse_url(s: String) -> Result<&2, &2, String, Url>:
  +t = s
  parse_url.of(String.starts_with(t, "http://"), String.starts_with(t, "https://"), t)

# ---------------------------------------------------------------------
# Headers of a target
# ---------------------------------------------------------------------

def hdr_key(+h: Hdr.Header) -> String:
  Hdr.Header{k, vs} = h
  k

def hdr_vals(+h: Hdr.Header) -> List<&2, String>:
  Hdr.Header{k, vs} = h
  vs

# append a header's values to the same name in a list, or add it at the end
def add_hdr(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [h]
    case Con{+g, +rest}:
      pick(List<&2, Hdr.Header>, String.eq(hdr_key(g), hdr_key(h)),
        Con{Hdr.Header{hdr_key(g), List.append(&2, String, hdr_vals(g), hdr_vals(h))}, rest}, Con{g, add_hdr(h, rest)})

def add_hdrs(hs: List<&2, Hdr.Header>, base: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      base
    case Con{+h, +rest}:
      add_hdrs(rest, add_hdr(h, base))

# the target as attacked: the global headers first, then the target's own
# (same name: values appended), and the global body unless the target has @file
def apply(+t: Target, +hs: List<&2, Hdr.Header>, +body: Maybe<&2, String>) -> Target:
  Target{m, u, ths, b} = t
  Target{m, u, add_hdrs(ths, hs), Maybe.or(&2, String, b, body)}

# ---------------------------------------------------------------------
# The targets format
# ---------------------------------------------------------------------

# upper-case letters then white space: Go's startsWithHTTPMethod (^[A-Z]+\s)
def first_upper(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      is_upper(code(c))

def upper_run.go(s: String, up: Bool) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{+c, +rest}:
      match up:
        case True{}:
          1n+upper_run.go(rest, first_upper(rest))
        case False{}:
          0n

def upper_run(+s: String) -> Nat:
  upper_run.go(s, first_upper(s))

def is_re_space(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), Bool.or(U32.is_eq(k, 9), Bool.or(U32.is_eq(k, 10), Bool.or(U32.is_eq(k, 12), U32.is_eq(k, 13)))))

def starts_method.of(+n: Nat, +l: String) -> Bool:
  Bool.and(Nat.is_gt(n, 0n), Bool.and(Nat.is_lt(n, String.length(l)), is_re_space(byte_at(l, n))))

def starts_method(+l: String) -> Bool:
  starts_method.of(upper_run(l), l)

# where the parse is: looking for a target, on the line after its request
# line (a blank line or another request line ends it there), or in its
# headers; acc holds the targets read so far, last first
type St is Data:
  SSeek{acc: List<&2, Target>}
  SPeek{t: Target, acc: List<&2, Target>}
  SHdr{t: Target, acc: List<&2, Target>}
  SFail{msg: String}

def with_hdr(+t: Target, +k: String, +v: String) -> Target:
  Target{m, u, hs, b} = t
  Target{m, u, add_hdr(Hdr.Header{k, [v]}, hs), b}

def with_body(+t: Target, +p: String) -> Target:
  Target{m, u, hs, b} = t
  Target{m, u, hs, Some{p}}

# Go's url.ParseRequestURI, for the errors a targets line can make
def req_uri.esc(m: Maybe<&2, String>, +u: String) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{"parse " ++ quote(u) ++ ": invalid URL escape " ++ quote(e)}

def req_uri.path(+u: String, +path: String) -> Maybe<&2, String>:
  req_uri.esc(bad_escape(path), u)

def req_uri.fail(+u: String, +e: String) -> Maybe<&2, String>:
  Some{"parse " ++ quote(u) ++ ": " ++ e}

def req_uri.auth(auth: Bool, +u: String, +r: String) -> Maybe<&2, String>:
  match auth:
    case True{}:
      +a = String.drop(r, 2n)
      req_uri.path(u, String.drop(a, String.length(before(a, 47))))
    case False{}:
      req_uri.path(u, r)

def req_uri.opaque(bare: Bool, +u: String) -> Maybe<&2, String>:
  match bare:
    case True{}:
      req_uri.fail(u, "invalid URI for request")
    case False{}:
      None{}

def req_uri.slash(slash: Bool, +u: String, +sc: String, +r: String) -> Maybe<&2, String>:
  match slash:
    case True{}:
      req_uri.auth(Bool.and(Bool.not(String.is_empty(sc)), String.starts_with(r, "//")), u, r)
    case False{}:
      req_uri.opaque(String.is_empty(sc), u)

def req_uri.rest(+u: String, +sc: String, +rest: String) -> Maybe<&2, String>:
  +r = before(rest, 63)
  req_uri.slash(first_is(r, 47), u, sc, r)

def req_uri.sc(+u: String, +sc: String) -> Maybe<&2, String>:
  req_uri.rest(u, sc, pick(String, String.is_empty(sc), u, String.drop(u, 1n+String.length(sc))))

def req_uri.colon(colon: Bool, +u: String) -> Maybe<&2, String>:
  match colon:
    case True{}:
      req_uri.fail(u, "missing protocol scheme")
    case False{}:
      req_uri.sc(u, scheme_of(u))

def req_uri.star(star: Bool, +u: String) -> Maybe<&2, String>:
  match star:
    case True{}:
      None{}
    case False{}:
      req_uri.colon(first_is(u, 58), u)

def req_uri.ctl(ctl: Bool, +u: String) -> Maybe<&2, String>:
  match ctl:
    case True{}:
      req_uri.fail(u, "net/url: invalid control character in URL")
    case False{}:
      req_uri.star(String.eq(u, "*"), u)

def req_uri_err(+u: String) -> Maybe<&2, String>:
  req_uri.ctl(has_ctl(u), u)

def req_line.url(m: Maybe<&2, String>, +meth: String, +u: String, +acc: List<&2, Target>) -> St:
  match m:
    case Some{e}:
      SFail{"bad URL: " ++ u ++ ", " ++ e}
    case None{}:
      SPeek{Target{meth, u, [], None{}}, acc}

def req_line.meth(ok: Bool, +l: String, +acc: List<&2, Target>) -> St:
  match ok:
    case False{}:
      SFail{"bad method: " ++ before(l, 32)}
    case True{}:
      req_line.url(req_uri_err(after(l, 32)), before(l, 32), after(l, 32), acc)

# a request line (trimmed, not blank, not a comment)
def req_line(sp: Bool, +l: String, +acc: List<&2, Target>) -> St:
  match sp:
    case False{}:
      SFail{"bad target: " ++ l}
    case True{}:
      req_line.meth(starts_method(l), l, acc)

def seek.of(skip: Bool, +l: String, +acc: List<&2, Target>) -> St:
  match skip:
    case True{}:
      SSeek{acc}
    case False{}:
      req_line(has_char(l, 32), l, acc)

# a (trimmed) line while looking for a target: blank lines and comments
# are skipped
def seek(+tl: String, +acc: List<&2, Target>) -> St:
  seek.of(Bool.or(String.is_empty(tl), first_is(tl, 35)), tl, acc)

def hdr.kv(ok: Bool, +l: String, +k: String, +v: String, +t: Target, +acc: List<&2, Target>) -> St:
  match ok:
    case False{}:
      SFail{"bad header: " ++ l}
    case True{}:
      SHdr{with_hdr(t, k, v), acc}

def hdr.colon(ok: Bool, +l: String, +t: Target, +acc: List<&2, Target>) -> St:
  match ok:
    case False{}:
      SFail{"bad header: " ++ l}
    case True{}:
      +k = trim_ws(before(l, 58))
      +v = trim_ws(after(l, 58))
      hdr.kv(Bool.and(Bool.not(String.is_empty(k)), Bool.not(String.is_empty(v))), l, k, v, t, acc)

def hdr.body(at: Bool, +l: String, +t: Target, +acc: List<&2, Target>) -> St:
  match at:
    case True{}:
      SSeek{Con{with_body(t, String.drop(l, 1n)), acc}}
    case False{}:
      hdr.colon(has_char(l, 58), l, t, acc)

def hdr.comment(c: Bool, +l: String, +t: Target, +acc: List<&2, Target>) -> St:
  match c:
    case True{}:
      SHdr{t, acc}
    case False{}:
      hdr.body(first_is(l, 64), l, t, acc)

def hdr.blank(b: Bool, +l: String, +t: Target, +acc: List<&2, Target>) -> St:
  match b:
    case True{}:
      SSeek{Con{t, acc}}
    case False{}:
      hdr.comment(first_is(l, 35), l, t, acc)

# a (trimmed) line in a target's headers: a blank line ends the target,
# a comment is skipped, @path is the body (and ends it), anything else a
# header
def hdr(+tl: String, +t: Target, +acc: List<&2, Target>) -> St:
  hdr.blank(String.is_empty(tl), tl, t, acc)

def peek.of(ends: Bool, +l: String, +t: Target, +acc: List<&2, Target>) -> St:
  match ends:
    case True{}:
      seek(l, Con{t, acc})
    case False{}:
      hdr(l, t, acc)

# the (trimmed) line after a request line: blank or another request line
# ends the target there (and is read again as the start of the next one)
def peek(+tl: String, +t: Target, +acc: List<&2, Target>) -> St:
  peek.of(Bool.or(String.is_empty(tl), starts_method(tl)), tl, t, acc)

# a line (trimmed) moves the state
def step(st: St, +l: String) -> St:
  match st:
    case SSeek{acc}:
      seek(l, acc)
    case SPeek{t, acc}:
      peek(l, t, acc)
    case SHdr{t, acc}:
      hdr(l, t, acc)
    case SFail{m}:
      SFail{m}

def finish(st: St) -> Result<&2, &2, String, List<&2, Target>>:
  match st:
    case SSeek{acc}:
      Done{List.reverse(&2, Target, acc)}
    case SPeek{t, acc}:
      Done{List.reverse(&2, Target, Con{t, acc})}
    case SHdr{t, acc}:
      Done{List.reverse(&2, Target, Con{t, acc})}
    case SFail{m}:
      Fail{m}

# a line read so far (last byte first), and the state
type Ln is Data:
  Ln{cur: String, st: St}

# the line, its '\r' at the end dropped (bufio.ScanLines), trimmed
# (every use of a line trims it first)
def line_of(cur: String) -> String:
  trim_ws_l(String.reverse(trim_ws_l(cur)))

def adv(nl: Bool, +c: Char, r: Ln) -> Ln:
  match nl:
    case True{}:
      Ln{cur, st} = r
      Ln{SNil{}, step(st, line_of(cur))}
    case False{}:
      Ln{cur, st} = r
      Ln{SCon{c, cur}, st}

def ln_end(r: Ln) -> St:
  Ln{cur, st} = r
  step(st, line_of(cur))

# the lines of s, each moving the state
def run(s: String, r: Ln) -> St:
  match s:
    case SNil{}:
      ln_end(r)
    case SCon{+c, +rest}:
      run(rest, adv(U32.is_eq(code(c), 10), c, r))

def parse_all(s: String) -> Result<&2, &2, String, List<&2, Target>>:
  finish(run(s, Ln{SNil{}, SSeek{[]}}))

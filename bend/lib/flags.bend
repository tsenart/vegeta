# Command-line flags for attack and report, with Go Vegeta's names and defaults.
# A timeout of None is Go's default (30s), applied by the shell: 30s is a
# closed number too big for the checker to state.
#
# Parsing follows Go's flag package: "-k=v", "-k v", "--k=v" and "--k v"
# are one; a bool flag takes no separate value; parsing stops at the first
# argument that is not a flag (or after "--"); errors are Go's texts. Go
# Vegeta's flags the port lacks are refused by name. After the flags, the
# checks Go's attack makes before it starts: -rate=0 needs -max-workers,
# the targets format is http (the port has no json targets).
import Base
import ./dec.bend as Dec
import ./dur.bend as Dur
import ./pacer.bend as Pace
import ./hdr.bend as Hdr

type Attack is Data:
  Attack{rate: Pace.Rate, duration: Nat, targets: String, format: String, output: String,
         name: String, workers: Nat, max_workers: Maybe<&2, Nat>, timeout: Maybe<&2, Nat>,
         headers: List<&2, Hdr.Header>, body: Maybe<&2, String>, keepalive: Bool,
         max_body: Maybe<&2, Nat>, redirects: Maybe<&2, Nat>, encoding: String}

type RKind is Data:
  AsText{}
  AsJson{buckets: List<&2, Nat>}
  AsHist{buckets: List<&2, Nat>}

type Report is Data:
  Report{kind: RKind, output: String, files: List<&2, String>}

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

def has_str(+x: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+y, +rest}:
      Bool.or(String.eq(x, y), has_str(x, rest))

# Go's %q for the texts at hand
def quote(+s: String) -> String:
  Pace.quote(s)

# ---------------------------------------------------------------------
# Reading one argument as Go's flag package does
# ---------------------------------------------------------------------

# s cut at its first byte k: before, and after (None without a k)
type Cut is Data:
  Cut{head: String, tail: Maybe<&2, String>}

def cut_head(+c: Cut) -> String:
  Cut{h, t} = c
  h

def cut_tail(+c: Cut) -> Maybe<&2, String>:
  Cut{h, t} = c
  t

def cut_cons(+c: Char, +r: Cut) -> Cut:
  Cut{h, t} = r
  Cut{SCon{c, h}, t}

def cut(+k: U32, s: String) -> Cut:
  match s:
    case SNil{}:
      Cut{"", None{}}
    case SCon{+c, +rest}:
      pick(Cut, U32.is_eq(code(c), k), Cut{"", Some{rest}}, cut_cons(c, cut(k, rest)))

# what an argument is
type Arg is Data:
  AStop{}
  AEnd{}
  ABad{}
  AFlag{name: String, val: Maybe<&2, String>}

# "-name" or "--name", then "=value" or not
def arg_of(+s: String) -> Arg:
  +dashes = pick(Nat, String.starts_with(s, "--"), 2n, 1n)
  +name = String.drop(s, dashes)
  pick(Arg, Bool.or(Nat.is_lt(String.length(s), 2n), Bool.not(first_is(s, 45))), AStop{},
  pick(Arg, String.eq(s, "--"), AEnd{},
  pick(Arg, Bool.or(String.is_empty(name), Bool.or(first_is(name, 45), first_is(name, 61))), ABad{},
    AFlag{cut_head(cut(61, name)), cut_tail(cut(61, name))})))

# a step of the loop: the result so far, the arguments left, and whether
# it is over
type St is Data:
  St{res: Result<&2, &2, String, Attack>, rest: List<&2, String>, stop: Bool}

def st_res(+s: St) -> Result<&2, &2, String, Attack>:
  St{r, a, t} = s
  r

def st_rest(+s: St) -> List<&2, String>:
  St{r, a, t} = s
  a

def st_stop(+s: St) -> Bool:
  St{r, a, t} = s
  t

def fail(+e: String) -> St:
  St{Fail{e}, [], True{}}

def invalid(+name: String, +v: String, +why: String) -> String:
  "invalid value " ++ quote(v) ++ " for flag -" ++ name ++ ": " ++ why

# ---------------------------------------------------------------------
# attack
# ---------------------------------------------------------------------

def attack_defaults() -> Attack:
  Attack{Pace.Rate{50n, 1000000000n}, 0n, "stdin", "http", "stdout", "", 10n, None{}, None{},
    [], None{}, True{}, None{}, Some{10n}, "csv"}

# Go Vegeta's attack flags this port does not implement
def unsupported() -> List<&2, String>:
  ["http2", "h2c", "insecure", "lazy", "cert", "key", "root-certs", "chunked", "laddr", "unix-socket",
   "prometheus-addr", "dns-ttl", "session-tickets", "connect-to", "proxy-header", "resolvers",
   "connections", "max-connections"]

type VFlag is Data:
  VRate{}
  VDuration{}
  VTargets{}
  VFormat{}
  VOutput{}
  VName{}
  VWorkers{}
  VMaxWorkers{}
  VTimeout{}
  VHeader{}
  VBody{}
  VMaxBody{}
  VRedirects{}
  VEncoding{}

type FKind is Data:
  KValue{f: VFlag}
  KKeepalive{}
  KHelp{}
  KRefused{}
  KUnknown{}

def kind_of(+n: String) -> FKind:
  pick(FKind, String.eq(n, "rate"), KValue{VRate{}},
  pick(FKind, String.eq(n, "duration"), KValue{VDuration{}},
  pick(FKind, String.eq(n, "targets"), KValue{VTargets{}},
  pick(FKind, String.eq(n, "format"), KValue{VFormat{}},
  pick(FKind, String.eq(n, "output"), KValue{VOutput{}},
  pick(FKind, String.eq(n, "name"), KValue{VName{}},
  pick(FKind, String.eq(n, "workers"), KValue{VWorkers{}},
  pick(FKind, String.eq(n, "max-workers"), KValue{VMaxWorkers{}},
  pick(FKind, String.eq(n, "timeout"), KValue{VTimeout{}},
  pick(FKind, String.eq(n, "header"), KValue{VHeader{}},
  pick(FKind, String.eq(n, "body"), KValue{VBody{}},
  pick(FKind, String.eq(n, "max-body"), KValue{VMaxBody{}},
  pick(FKind, String.eq(n, "redirects"), KValue{VRedirects{}},
  pick(FKind, String.eq(n, "encoding"), KValue{VEncoding{}},
  pick(FKind, String.eq(n, "keepalive"), KKeepalive{},
  pick(FKind, Bool.or(String.eq(n, "h"), String.eq(n, "help")), KHelp{},
  pick(FKind, has_str(n, unsupported()), KRefused{}, KUnknown{})))))))))))))))))

# setters
def set_rate(+a: Attack, +x: Pace.Rate) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{x, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc}

def set_duration(+a: Attack, +x: Nat) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, x, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc}

def set_targets(+a: Attack, +x: String) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, x, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc}

def set_format(+a: Attack, +x: String) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, x, out, name, w, mw, to, hs, body, ka, mb, rd, enc}

def set_output(+a: Attack, +x: String) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, x, name, w, mw, to, hs, body, ka, mb, rd, enc}

def set_name(+a: Attack, +x: String) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, x, w, mw, to, hs, body, ka, mb, rd, enc}

def set_workers(+a: Attack, +x: Nat) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, x, mw, to, hs, body, ka, mb, rd, enc}

def set_max_workers(+a: Attack, +x: Maybe<&2, Nat>) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, w, x, to, hs, body, ka, mb, rd, enc}

def set_timeout(+a: Attack, +x: Maybe<&2, Nat>) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, w, mw, x, hs, body, ka, mb, rd, enc}

def set_headers(+a: Attack, +x: List<&2, Hdr.Header>) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, w, mw, to, x, body, ka, mb, rd, enc}

def set_body(+a: Attack, +x: Maybe<&2, String>) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, x, ka, mb, rd, enc}

def set_keepalive(+a: Attack, +x: Bool) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, x, mb, rd, enc}

def set_max_body(+a: Attack, +x: Maybe<&2, Nat>) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, x, rd, enc}

def set_redirects(+a: Attack, +x: Maybe<&2, Nat>) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, x, enc}

def set_encoding(+a: Attack, +x: String) -> Attack:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, x}

def headers_of(+a: Attack) -> List<&2, Hdr.Header>:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  hs

# values

def with_rate(r: Result<&2, &2, String, Pace.Rate>, +v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  match r:
    case Fail{e}:
      Fail{invalid("rate", v, e)}
    case Done{x}:
      Done{set_rate(a, x)}

# "infinity" is no rate to Go's flag: the default stays
def rate_val(inf: Bool, +v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  match inf:
    case True{}:
      Done{a}
    case False{}:
      with_rate(Pace.parse_rate(v), v, a)

def nat_val(m: Maybe<&2, Nat>, +name: String, +v: String) -> Result<&2, &2, String, Nat>:
  match m:
    case None{}:
      Fail{invalid(name, v, "parse error")}
    case Some{n}:
      Done{n}

def set_nat(w: VFlag, +n: Nat, +a: Attack) -> Attack:
  match w:
    case VRate{}:
      a
    case VDuration{}:
      set_duration(a, n)
    case VTargets{}:
      a
    case VFormat{}:
      a
    case VOutput{}:
      a
    case VName{}:
      a
    case VWorkers{}:
      set_workers(a, n)
    case VMaxWorkers{}:
      set_max_workers(a, Some{n})
    case VTimeout{}:
      set_timeout(a, Some{n})
    case VHeader{}:
      a
    case VBody{}:
      a
    case VMaxBody{}:
      set_max_body(a, Some{n})
    case VRedirects{}:
      set_redirects(a, Some{n})
    case VEncoding{}:
      a

def with_nat(r: Result<&2, &2, String, Nat>, +which: VFlag, +a: Attack) -> Result<&2, &2, String, Attack>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{n}:
      Done{set_nat(which, n, a)}

def is_space(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), Bool.and(U32.is_ge(k, 9), U32.is_le(k, 13)))

def trim_l(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, is_space(code(c)), trim_l(rest), SCon{c, rest})

# strings.TrimSpace, for ASCII white space
def trim(+s: String) -> String:
  String.reverse(trim_l(String.reverse(trim_l(s))))

# the value under the name, appended; a new name goes last
def hdr_add(hs: List<&2, Hdr.Header>, +k: String, +v: String) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      [Hdr.Header{k, [v]}]
    case Con{+h, +rest}:
      Hdr.Header{hk, hv} = h
      pick(List<&2, Hdr.Header>, String.eq(hk, k), Con{Hdr.Header{hk, List.append(&2, String, hv, [v])}, rest},
        Con{Hdr.Header{hk, hv}, hdr_add(rest, k, v)})

def hdr_of(ok: Bool, +k: String, +val: String, +v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  match ok:
    case True{}:
      Done{set_headers(a, hdr_add(headers_of(a), k, val))}
    case False{}:
      Fail{invalid("header", v, "header '" ++ v ++ "' has a wrong format")}

# Go's headers.Set: split at the first colon, both sides trimmed and non-empty
def hdr_val(+v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  +c = cut(58, v)
  +k = trim(cut_head(c))
  +val = trim(Maybe.default(&2, String, cut_tail(c), ""))
  hdr_of(Bool.and(Maybe.is_some(&2, String, cut_tail(c)), Bool.and(Bool.not(String.is_empty(k)), Bool.not(String.is_empty(val)))),
    k, val, v, a)

# datasize.ByteSize's text: digits and a unit (b, kb, mb, ... or k, m, ...)
def size_unit(+u: String) -> Nat:
  +l = String.to_lower(u)
  pick(Nat, Bool.or(String.eq(l, ""), String.eq(l, "b")), 1n,
  pick(Nat, Bool.or(String.eq(l, "k"), String.eq(l, "kb")), 1024n,
  pick(Nat, Bool.or(String.eq(l, "m"), String.eq(l, "mb")), 1048576n,
  pick(Nat, Bool.or(String.eq(l, "g"), String.eq(l, "gb")), 1073741824n,
  pick(Nat, Bool.or(String.eq(l, "t"), String.eq(l, "tb")), Nat.mul(1024n, 1073741824n), 0n)))))

def size_of(ok: Bool, +digits: String, +mult: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{Nat.mul(Dec.value(digits), mult)}
    case False{}:
      None{}

def size(+v: String) -> Maybe<&2, Nat>:
  +p = Dur.span_digits(v)
  +mult = size_unit(Dur.SS.b(p))
  size_of(Bool.and(Bool.not(String.is_empty(Dur.SS.a(p))), Nat.is_gt(mult, 0n)), Dur.SS.a(p), mult)

def max_body_of(m: Maybe<&2, Nat>, +v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  match m:
    case None{}:
      Fail{invalid("max-body", v, "strconv.UnmarshalText: parsing " ++ quote(v) ++ ": invalid syntax")}
    case Some{n}:
      Done{set_max_body(a, Some{n})}

def max_body_val(neg: Bool, +v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  match neg:
    case True{}:
      Done{set_max_body(a, None{})}
    case False{}:
      max_body_of(size(v), v, a)

# -redirects: any negative count reads as -1, Go's "do not follow"
def redirects_val(neg: Bool, +v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  match neg:
    case True{}:
      Done{set_redirects(a, None{})}
    case False{}:
      with_nat(nat_val(Dec.read(v), "redirects", v), VRedirects{}, a)

def neg_int(+v: String) -> Bool:
  Bool.and(first_is(v, 45), Dec.all_digits(String.drop(v, 1n)))

def encoding_val(+v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  pick(Result<&2, &2, String, Attack>, Bool.or(String.eq(v, "csv"), String.eq(v, "json")), Done{set_encoding(a, v)},
    Fail{invalid("encoding", v, "want csv or json" ++ pick(String, String.eq(v, "gob"), " (gob is not supported in the Bend port)", ""))})

def apply(f: VFlag, +v: String, +a: Attack) -> Result<&2, &2, String, Attack>:
  match f:
    case VRate{}:
      rate_val(String.eq(v, "infinity"), v, a)
    case VDuration{}:
      with_nat(nat_val(Dur.parse(v), "duration", v), VDuration{}, a)
    case VTargets{}:
      Done{set_targets(a, v)}
    case VFormat{}:
      Done{set_format(a, v)}
    case VOutput{}:
      Done{set_output(a, v)}
    case VName{}:
      Done{set_name(a, v)}
    case VWorkers{}:
      with_nat(nat_val(Dec.read(v), "workers", v), VWorkers{}, a)
    case VMaxWorkers{}:
      with_nat(nat_val(Dec.read(v), "max-workers", v), VMaxWorkers{}, a)
    case VTimeout{}:
      with_nat(nat_val(Dur.parse(v), "timeout", v), VTimeout{}, a)
    case VHeader{}:
      hdr_val(v, a)
    case VBody{}:
      Done{set_body(a, pick(Maybe<&2, String>, String.is_empty(v), None{}, Some{v}))}
    case VMaxBody{}:
      max_body_val(String.eq(v, "-1"), v, a)
    case VRedirects{}:
      redirects_val(neg_int(v), v, a)
    case VEncoding{}:
      encoding_val(v, a)

def st_of(r: Result<&2, &2, String, Attack>, +rest: List<&2, String>) -> St:
  match r:
    case Fail{e}:
      fail(e)
    case Done{a}:
      St{Done{a}, rest, False{}}

# a flag that takes a value: after "=", or the next argument
def valued(v: Maybe<&2, String>, +f: VFlag, +name: String, rest: List<&2, String>, +a: Attack) -> St:
  match v:
    case Some{x}:
      st_of(apply(f, x, a), rest)
    case None{}:
      match rest:
        case Nil{}:
          fail("flag needs an argument: -" ++ name)
        case Con{+x, +more}:
          st_of(apply(f, x, a), more)

def bool_of(+v: String) -> Maybe<&2, Bool>:
  pick(Maybe<&2, Bool>, has_str(v, ["1", "t", "T", "TRUE", "true", "True"]), Some{True{}},
    pick(Maybe<&2, Bool>, has_str(v, ["0", "f", "F", "FALSE", "false", "False"]), Some{False{}}, None{}))

def keepalive_of(b: Maybe<&2, Bool>, +v: String, +rest: List<&2, String>, +a: Attack) -> St:
  match b:
    case None{}:
      fail("invalid boolean value " ++ quote(v) ++ " for -keepalive: parse error")
    case Some{x}:
      St{Done{set_keepalive(a, x)}, rest, False{}}

def keepalive(v: Maybe<&2, String>, +rest: List<&2, String>, +a: Attack) -> St:
  match v:
    case None{}:
      St{Done{set_keepalive(a, True{})}, rest, False{}}
    case Some{+x}:
      keepalive_of(bool_of(x), x, rest, a)

def flag_step(k: FKind, +name: String, +v: Maybe<&2, String>, +rest: List<&2, String>, +a: Attack) -> St:
  match k:
    case KValue{f}:
      valued(v, f, name, rest, a)
    case KKeepalive{}:
      keepalive(v, rest, a)
    case KHelp{}:
      fail("flag: help requested")
    case KRefused{}:
      fail("flag not supported in the Bend port: -" ++ name)
    case KUnknown{}:
      fail("flag provided but not defined: -" ++ name)

def arg_step(x: Arg, +s: String, +rest: List<&2, String>, +a: Attack) -> St:
  match x:
    case AStop{}:
      St{Done{a}, Con{s, rest}, True{}}
    case AEnd{}:
      St{Done{a}, rest, True{}}
    case ABad{}:
      fail("bad flag syntax: " ++ s)
    case AFlag{+name, +v}:
      flag_step(kind_of(name), name, v, rest, a)

def step(args: List<&2, String>, +a: Attack) -> St:
  match args:
    case Nil{}:
      St{Done{a}, [], True{}}
    case Con{+s, +rest}:
      arg_step(arg_of(s), s, rest, a)

def attack_of(+r: Result<&2, &2, String, Attack>) -> Attack:
  match r:
    case Fail{e}:
      attack_defaults()
    case Done{a}:
      a

def attack_loop(fuel: Nat, stop: Bool, +args: List<&2, String>, +r: Result<&2, &2, String, Attack>) -> Result<&2, &2, String, Attack>:
  match fuel:
    case 0n:
      r
    case 1n+f:
      match stop:
        case True{}:
          r
        case False{}:
          +st = step(args, attack_of(r))
          attack_loop(f, st_stop(st), st_rest(st), st_res(st))

# Go's attack checks, once the flags are read
def attack_check(+a: Attack) -> Result<&2, &2, String, Attack>:
  Attack{rate, du, tg, fm, out, name, w, mw, to, hs, body, ka, mb, rd, enc} = a
  Pace.Rate{f, p} = rate
  pick(Result<&2, &2, String, Attack>, Bool.and(Nat.is_eq(f, 0n), Maybe.is_none(&2, Nat, mw)), Fail{"-rate=0 requires setting -max-workers"},
  pick(Result<&2, &2, String, Attack>, String.eq(fm, "json"), Fail{"target format not supported in the Bend port: json"},
  pick(Result<&2, &2, String, Attack>, Bool.not(String.eq(fm, "http")), Fail{"format " ++ quote(fm) ++ " isn't one of [http, json]"},
    Done{a})))

def attack_fin(r: Result<&2, &2, String, Attack>) -> Result<&2, &2, String, Attack>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      attack_check(a)

def parse_attack.go(+args: List<&2, String>) -> Result<&2, &2, String, Attack>:
  attack_fin(attack_loop(1n+List.length(&2, String, args), False{}, args, Done{attack_defaults()}))

def parse_attack(args: List<&2, String>) -> Result<&2, &2, String, Attack>:
  parse_attack.go(args)

# ---------------------------------------------------------------------
# report
# ---------------------------------------------------------------------

# the flags as read: -type, -output, -buckets ("" when not given), files
type RSt is Data:
  RSt{res: Maybe<&2, String>, typ: String, out: String, buckets: String, files: List<&2, String>, rest: List<&2, String>, stop: Bool}

def rst_res(+s: RSt) -> Maybe<&2, String>:
  RSt{res, typ, out, bs, files, rest, stop} = s
  res

def rst_typ(+s: RSt) -> String:
  RSt{res, typ, out, bs, files, rest, stop} = s
  typ

def rst_out(+s: RSt) -> String:
  RSt{res, typ, out, bs, files, rest, stop} = s
  out

def rst_bs(+s: RSt) -> String:
  RSt{res, typ, out, bs, files, rest, stop} = s
  bs

def rst_files(+s: RSt) -> List<&2, String>:
  RSt{res, typ, out, bs, files, rest, stop} = s
  files

def rst_rest(+s: RSt) -> List<&2, String>:
  RSt{res, typ, out, bs, files, rest, stop} = s
  rest

def rst_stop(+s: RSt) -> Bool:
  RSt{res, typ, out, bs, files, rest, stop} = s
  stop

type RFlag is Data:
  RType{}
  ROutput{}
  RBuckets{}
  REvery{}
  RHelp{}
  RUnknown{}

def rflag_of(+n: String) -> RFlag:
  pick(RFlag, String.eq(n, "type"), RType{},
  pick(RFlag, String.eq(n, "output"), ROutput{},
  pick(RFlag, String.eq(n, "buckets"), RBuckets{},
  pick(RFlag, String.eq(n, "every"), REvery{},
  pick(RFlag, Bool.or(String.eq(n, "h"), String.eq(n, "help")), RHelp{}, RUnknown{})))))

def rfail(+e: String) -> RSt:
  RSt{Some{e}, "", "", "", [], [], True{}}

def rset(f: RFlag, +x: String, +typ: String, +out: String, +bs: String, +rest: List<&2, String>) -> RSt:
  match f:
    case RType{}:
      RSt{None{}, x, out, bs, [], rest, False{}}
    case ROutput{}:
      RSt{None{}, typ, x, bs, [], rest, False{}}
    case RBuckets{}:
      RSt{None{}, typ, out, x, [], rest, False{}}
    case REvery{}:
      rfail("flag not supported in the Bend port: -every")
    case RHelp{}:
      rfail("flag: help requested")
    case RUnknown{}:
      rfail("flag provided but not defined")

def rvalued(v: Maybe<&2, String>, +f: RFlag, +name: String, rest: List<&2, String>, +typ: String, +out: String, +bs: String) -> RSt:
  match v:
    case Some{x}:
      rset(f, x, typ, out, bs, rest)
    case None{}:
      match rest:
        case Nil{}:
          rfail("flag needs an argument: -" ++ name)
        case Con{+x, +more}:
          rset(f, x, typ, out, bs, more)

def rflag_step(f: RFlag, +name: String, +v: Maybe<&2, String>, +rest: List<&2, String>, +typ: String, +out: String, +bs: String) -> RSt:
  match f:
    case RType{}:
      rvalued(v, RType{}, name, rest, typ, out, bs)
    case ROutput{}:
      rvalued(v, ROutput{}, name, rest, typ, out, bs)
    case RBuckets{}:
      rvalued(v, RBuckets{}, name, rest, typ, out, bs)
    case REvery{}:
      rfail("flag not supported in the Bend port: -every")
    case RHelp{}:
      rfail("flag: help requested")
    case RUnknown{}:
      rfail("flag provided but not defined: -" ++ name)

def rarg_step(x: Arg, +s: String, +rest: List<&2, String>, +typ: String, +out: String, +bs: String) -> RSt:
  match x:
    case AStop{}:
      RSt{None{}, typ, out, bs, Con{s, rest}, [], True{}}
    case AEnd{}:
      RSt{None{}, typ, out, bs, rest, [], True{}}
    case ABad{}:
      rfail("bad flag syntax: " ++ s)
    case AFlag{+name, +v}:
      rflag_step(rflag_of(name), name, v, rest, typ, out, bs)

def rstep(args: List<&2, String>, +typ: String, +out: String, +bs: String) -> RSt:
  match args:
    case Nil{}:
      RSt{None{}, typ, out, bs, [], [], True{}}
    case Con{+s, +rest}:
      rarg_step(arg_of(s), s, rest, typ, out, bs)

def report_loop.go(fuel: Nat, stop: Bool, +res: Maybe<&2, String>, +typ: String, +out: String, +bs: String, +files: List<&2, String>, +rest: List<&2, String>) -> RSt:
  match fuel:
    case 0n:
      RSt{res, typ, out, bs, files, rest, stop}
    case 1n+f:
      match stop:
        case True{}:
          RSt{res, typ, out, bs, files, rest, stop}
        case False{}:
          +st = rstep(rest, typ, out, bs)
          report_loop.go(f, rst_stop(st), rst_res(st), rst_typ(st), rst_out(st), rst_bs(st), rst_files(st), rst_rest(st))

# Go's Buckets.UnmarshalText: "[d1,d2,...]", each trimmed and parsed; a
# 0 bucket is added in front of a positive first bound
def bucket_cons.of(+n: Nat, r: Result<&2, &2, String, List<&2, Nat>>) -> Result<&2, &2, String, List<&2, Nat>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bs}:
      Done{Con{n, bs}}

def bucket_cons(d: Maybe<&2, Nat>, +text: String, +r: Result<&2, &2, String, List<&2, Nat>>) -> Result<&2, &2, String, List<&2, Nat>>:
  match d:
    case None{}:
      Fail{Pace.dur_error(text)}
    case Some{n}:
      bucket_cons.of(n, r)

def bucket_list(ps: List<&2, String>) -> Result<&2, &2, String, List<&2, Nat>>:
  match ps:
    case Nil{}:
      Done{[]}
    case Con{+p, +rest}:
      bucket_cons(Dur.parse(trim(p)), trim(p), bucket_list(rest))

def split_cons(+c: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{c, SNil{}}]
    case Con{+p, +rest}:
      Con{SCon{c, p}, rest}

def split_commas(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [""]
    case SCon{+c, +rest}:
      +r = split_commas(rest)
      pick(List<&2, String>, U32.is_eq(code(c), 44), Con{"", r}, split_cons(c, r))

def with_zero(bs: List<&2, Nat>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      []
    case Con{+b, +rest}:
      pick(List<&2, Nat>, Nat.is_gt(b, 0n), Con{0n, Con{b, rest}}, Con{b, rest})

def zeroed(r: Result<&2, &2, String, List<&2, Nat>>) -> Result<&2, &2, String, List<&2, Nat>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bs}:
      Done{with_zero(bs)}

def buckets_of(ok: Bool, +s: String) -> Result<&2, &2, String, List<&2, Nat>>:
  match ok:
    case False{}:
      Fail{"bad buckets: " ++ s}
    case True{}:
      zeroed(bucket_list(split_commas(String.take(String.drop(s, 1n), Nat.sub(String.length(s), 2n)))))

def buckets(+s: String) -> Result<&2, &2, String, List<&2, Nat>>:
  buckets_of(Bool.and(Nat.is_ge(String.length(s), 2n), Bool.and(String.starts_with(s, "["), String.ends_with(s, "]"))), s)

def kind_with(r: Result<&2, &2, String, List<&2, Nat>>, json: Bool, +out: String, +files: List<&2, String>) -> Result<&2, &2, String, Report>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bs}:
      match json:
        case True{}:
          Done{Report{AsJson{bs}, out, files}}
        case False{}:
          Done{Report{AsHist{bs}, out, files}}

def json_kind(given: Bool, +bs: String, +out: String, +files: List<&2, String>) -> Result<&2, &2, String, Report>:
  match given:
    case False{}:
      Done{Report{AsJson{[]}, out, files}}
    case True{}:
      kind_with(buckets(bs), True{}, out, files)

def hist_kind(short: Bool, +s: String, +out: String, +files: List<&2, String>) -> Result<&2, &2, String, Report>:
  match short:
    case True{}:
      Fail{"bad buckets: '" ++ s ++ "'"}
    case False{}:
      kind_with(buckets(s), False{}, out, files)

type RType is Data:
  TText{}
  TJson{}
  THist{}
  TNo{text: String}

def rtype_of(+t: String) -> RType:
  pick(RType, Nat.is_lt(String.length(t), 4n), TNo{"invalid report type: " ++ t},
  pick(RType, String.eq(t, "text"), TText{},
  pick(RType, String.eq(t, "json"), TJson{},
  pick(RType, String.eq(t, "plot"), TNo{"The plot reporter has been deprecated and succeeded by the vegeta plot command"},
  pick(RType, String.eq(t, "hdrplot"), TNo{"report type not supported in the Bend port: hdrplot"},
  pick(RType, String.starts_with(t, "hist"), THist{}, TNo{"unknown report type: " ++ quote(t)}))))))

def report_of(k: RType, +typ: String, +out: String, +bs: String, +files: List<&2, String>) -> Result<&2, &2, String, Report>:
  match k:
    case TText{}:
      Done{Report{AsText{}, out, files}}
    case TJson{}:
      json_kind(Bool.not(String.is_empty(bs)), bs, out, files)
    case THist{}:
      hist_kind(Bool.and(String.is_empty(bs), Nat.is_lt(String.length(typ), 6n)),
        pick(String, String.is_empty(bs), String.drop(typ, 4n), bs), out, files)
    case TNo{e}:
      Fail{e}

def report_fin(res: Maybe<&2, String>, +typ: String, +out: String, +bs: String, +files: List<&2, String>) -> Result<&2, &2, String, Report>:
  match res:
    case Some{e}:
      Fail{e}
    case None{}:
      report_of(rtype_of(typ), typ, out, bs, files)

def parse_report.of(+st: RSt) -> Result<&2, &2, String, Report>:
  report_fin(rst_res(st), rst_typ(st), rst_out(st), rst_bs(st), rst_files(st))

def parse_report.go(+args: List<&2, String>) -> Result<&2, &2, String, Report>:
  parse_report.of(report_loop.go(1n+List.length(&2, String, args), False{}, None{}, "text", "stdout", "", [], args))

def parse_report(args: List<&2, String>) -> Result<&2, &2, String, Report>:
  parse_report.go(args)

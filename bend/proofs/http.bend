# Proofs of the HTTP laws (http_*).
import Base
import ../LAWS.bend as L
import ../lib/http.bend as Http
import ../lib/hdr.bend as Hdr
import ../lib/target.bend as Tgt
import ../lib/dec.bend as Dec
import ./nat.bend as N
import ./dec.bend as PDec

# ---------------------------------------------------------------------
# feed folds step over the bytes
# ---------------------------------------------------------------------

def split_go(a: String, +b: String, +p: Http.Parse)
  -> {Http.feed.go(b, Http.feed.go(a, p)) == Http.feed.go(a ++ b, p) : Http.Parse}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      split_go(rest, b, Http.step(p, c))

def L.http_split(p, a, b):
  split_go(a, b, p)

def eof_ph(ph: Http.Ph) -> {Maybe.is_some(&1, Result<&1, &1, String, Http.Resp & String>, Http.done_eof(ph)) == True{} : Bool}:
  match ph:
    case Http.HStat{n, line}:
      {==}
    case Http.HHdr{code, status, minor, hs, pend, line}:
      {==}
    case Http.HLen{r, left, body, kept}:
      {==}
    case Http.HChSize{r, line, body, kept}:
      {==}
    case Http.HChData{r, left, body, kept}:
      {==}
    case Http.HChCR{r, body, kept}:
      {==}
    case Http.HChLF{r, body, kept}:
      {==}
    case Http.HTrail{r, line, body}:
      {==}
    case Http.HClose{r, body, kept}:
      {==}
    case Http.HDone{r, rest}:
      {==}
    case Http.HFail{m}:
      {==}

def L.http_eof_decides(p):
  match p:
    case Http.Parse{mb, head, closed, ph}:
      eof_ph(ph)

# ---------------------------------------------------------------------
# Generic facts
# ---------------------------------------------------------------------

def bool_t(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def no_ft(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_t(_)
  Unit{}

def no_tf(e: {True{} == False{} : Bool}) -> Empty:
  no_ft(Equal.sym(Bool, True{}, False{}, e))

# Word.cmp decides equality (as in proofs/codec.bend)
def fin_eq_t(t: Cmp, -ah: Bool, -bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, no_ft(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, no_ft(h))

def fin_eq_h(t: Cmp, ah: Bool, bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {ah == bh : Bool}:
  match t:
    case LT{}:
      Empty.absurd({ah == bh : Bool}, no_ft(h))
    case GT{}:
      Empty.absurd({ah == bh : Bool}, no_ft(h))
    case EQ{}:
      match ah bh:
        case False{} False{}:
          {==}
        case True{} True{}:
          {==}
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, no_ft(h))
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, no_ft(h))

def weq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          %weq(p, at, bt, Equal.cong(Cmp, Bool, Cmp.is_eq, Word.cmp(p, at, bt), EQ{}, fin_eq_t(Word.cmp(p, at, bt), ah, bh, h)))
            : {WCon{ah, at} == WCon{bh, _} : Word(1n+p)}
          %fin_eq_h(Word.cmp(p, at, bt), ah, bh, h) : {WCon{ah, at} == WCon{_, at} : Word(1n+p)}
          {==}

def u32_eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %weq(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

# ---------------------------------------------------------------------
# http_garbage: the first 7 bytes are checked against "HTTP/1."
# ---------------------------------------------------------------------

def G(+n: Nat, +line: String, +s: String) -> Type:
  {L.is_fail(Http.done(Http.feed.go(s, Http.Parse{None{}, False{}, False{}, Http.HStat{n, line}}))) == True{} : Bool}

def fails(s: String, +m: String) -> {L.is_fail(Http.done(Http.feed.go(s, Http.Parse{None{}, False{}, False{}, Http.HFail{m}}))) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      fails(rest, m)

def stat_bad(ok: Bool, +nl: Bool, +n: Nat, +c: Char, +line: String, +s1: String, e: {ok == False{} : Bool})
  -> {L.is_fail(Http.done(Http.feed.go(s1, Http.Parse{None{}, False{}, False{}, Http.stat_byte(ok, nl, n, c, line)}))) == True{} : Bool}:
  match ok:
    case False{}:
      fails(s1, "malformed HTTP response " ++ Tgt.quote(String.reverse(SCon{c, line})))
    case True{}:
      Empty.absurd({L.is_fail(Http.done(Http.feed.go(s1, Http.Parse{None{}, False{}, False{}, Http.stat_byte(True{}, nl, n, c, line)}))) == True{} : Bool}, no_tf(e))

def lvl(b: Bool, +n: Nat, +lit: U32, +k: U32, +line: String, +s1: String, +pat: String, +m: Nat,
        +e: {U32.is_eq(k, lit) == b : Bool},
        h: {Bool.and(Nat.is_ge(String.length(s1), m), Bool.not(String.starts_with.if(s1, pat, b))) == True{} : Bool},
        +ok: {Http.stat_step(n, line, Chr{k}) == Http.stat_byte(U32.is_eq(k, lit), U32.is_eq(k, 10), n, Chr{k}, line) : Http.Ph},
        +nl: {U32.is_eq(lit, 10) == False{} : Bool},
        rec: {Bool.and(Nat.is_ge(String.length(s1), m), Bool.not(String.starts_with(s1, pat))) == True{} : Bool} -> G(Nat.min(1n+n, 7n), SCon{Chr{lit}, line}, s1))
  -> G(n, line, SCon{Chr{k}, s1}):
  match b:
    case False{}:
      %Equal.sym(Http.Ph, Http.stat_step(n, line, Chr{k}), Http.stat_byte(U32.is_eq(k, lit), U32.is_eq(k, 10), n, Chr{k}, line), ok)
        : {L.is_fail(Http.done(Http.feed.go(s1, Http.Parse{None{}, False{}, False{}, _}))) == True{} : Bool}
      stat_bad(U32.is_eq(k, lit), U32.is_eq(k, 10), n, Chr{k}, line, s1, e)
    case True{}:
      %Equal.sym(Http.Ph, Http.stat_step(n, line, Chr{k}), Http.stat_byte(U32.is_eq(k, lit), U32.is_eq(k, 10), n, Chr{k}, line), ok)
        : {L.is_fail(Http.done(Http.feed.go(s1, Http.Parse{None{}, False{}, False{}, _}))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(k, lit), True{}, e) : {L.is_fail(Http.done(Http.feed.go(s1, Http.Parse{None{}, False{}, False{}, Http.stat_byte(_, U32.is_eq(k, 10), n, Chr{k}, line)}))) == True{} : Bool}
      %Equal.sym(U32, k, lit, u32_eq(k, lit, e))
        : {L.is_fail(Http.done(Http.feed.go(s1, Http.Parse{None{}, False{}, False{}, Http.stat_byte(True{}, U32.is_eq(_, 10), n, Chr{_}, line)}))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(lit, 10), False{}, nl) : {L.is_fail(Http.done(Http.feed.go(s1, Http.Parse{None{}, False{}, False{}, Http.stat_byte(True{}, _, n, Chr{lit}, line)}))) == True{} : Bool}
      rec(h)

def g7(s: String, +line: String, h: {Bool.and(Nat.is_ge(String.length(s), 0n), Bool.not(String.starts_with(s, ""))) == True{} : Bool}) -> G(7n, line, s):
  match s:
    case SNil{}:
      Empty.absurd(G(7n, line, SNil{}), no_ft(h))
    case SCon{c, rest}:
      Empty.absurd(G(7n, line, SCon{c, rest}), no_ft(h))

def g6(s: String, +line: String, h: {Bool.and(Nat.is_ge(String.length(s), 1n), Bool.not(String.starts_with(s, "."))) == True{} : Bool}) -> G(6n, line, s):
  match s:
    case SNil{}:
      Empty.absurd(G(6n, line, SNil{}), no_ft(h))
    case SCon{c, +s1}:
      match c:
        case Chr{+k}:
          lvl(U32.is_eq(k, 46), 6n, 46, k, line, s1, "", 0n, {==}, h, {==}, {==}, hh => g7(s1, SCon{Chr{46}, line}, hh))

def g5(s: String, +line: String, h: {Bool.and(Nat.is_ge(String.length(s), 2n), Bool.not(String.starts_with(s, "1."))) == True{} : Bool}) -> G(5n, line, s):
  match s:
    case SNil{}:
      Empty.absurd(G(5n, line, SNil{}), no_ft(h))
    case SCon{c, +s1}:
      match c:
        case Chr{+k}:
          lvl(U32.is_eq(k, 49), 5n, 49, k, line, s1, ".", 1n, {==}, h, {==}, {==}, hh => g6(s1, SCon{Chr{49}, line}, hh))

def g4(s: String, +line: String, h: {Bool.and(Nat.is_ge(String.length(s), 3n), Bool.not(String.starts_with(s, "/1."))) == True{} : Bool}) -> G(4n, line, s):
  match s:
    case SNil{}:
      Empty.absurd(G(4n, line, SNil{}), no_ft(h))
    case SCon{c, +s1}:
      match c:
        case Chr{+k}:
          lvl(U32.is_eq(k, 47), 4n, 47, k, line, s1, "1.", 2n, {==}, h, {==}, {==}, hh => g5(s1, SCon{Chr{47}, line}, hh))

def g3(s: String, +line: String, h: {Bool.and(Nat.is_ge(String.length(s), 4n), Bool.not(String.starts_with(s, "P/1."))) == True{} : Bool}) -> G(3n, line, s):
  match s:
    case SNil{}:
      Empty.absurd(G(3n, line, SNil{}), no_ft(h))
    case SCon{c, +s1}:
      match c:
        case Chr{+k}:
          lvl(U32.is_eq(k, 80), 3n, 80, k, line, s1, "/1.", 3n, {==}, h, {==}, {==}, hh => g4(s1, SCon{Chr{80}, line}, hh))

def g2(s: String, +line: String, h: {Bool.and(Nat.is_ge(String.length(s), 5n), Bool.not(String.starts_with(s, "TP/1."))) == True{} : Bool}) -> G(2n, line, s):
  match s:
    case SNil{}:
      Empty.absurd(G(2n, line, SNil{}), no_ft(h))
    case SCon{c, +s1}:
      match c:
        case Chr{+k}:
          lvl(U32.is_eq(k, 84), 2n, 84, k, line, s1, "P/1.", 4n, {==}, h, {==}, {==}, hh => g3(s1, SCon{Chr{84}, line}, hh))

def g1(s: String, +line: String, h: {Bool.and(Nat.is_ge(String.length(s), 6n), Bool.not(String.starts_with(s, "TTP/1."))) == True{} : Bool}) -> G(1n, line, s):
  match s:
    case SNil{}:
      Empty.absurd(G(1n, line, SNil{}), no_ft(h))
    case SCon{c, +s1}:
      match c:
        case Chr{+k}:
          lvl(U32.is_eq(k, 84), 1n, 84, k, line, s1, "TP/1.", 5n, {==}, h, {==}, {==}, hh => g2(s1, SCon{Chr{84}, line}, hh))

def L.http_garbage(s, h):
  match s:
    case SNil{}:
      Empty.absurd(G(0n, "", SNil{}), no_ft(h))
    case SCon{c, +s1}:
      match c:
        case Chr{+k}:
          lvl(U32.is_eq(k, 72), 0n, 72, k, "", s1, "TTP/1.", 6n, {==}, h, {==}, {==}, hh => g1(s1, SCon{Chr{72}, ""}, hh))

# ---------------------------------------------------------------------
# Order and division facts: a status code in [100, 999] shows in 3 digits
# ---------------------------------------------------------------------

def lt_ge(r: Nat, a: Nat, -x: Nat, hr: {Nat.is_lt(r, a) == True{} : Bool}, h: {Nat.is_ge(r, Nat.add(a, x)) == True{} : Bool}) -> Empty:
  match r:
    case 0n:
      match a:
        case 0n:
          N.lt_zero(0n, hr)
        case 1n+ap:
          no_ft(h)
    case 1n+rp:
      match a:
        case 0n:
          N.lt_zero(1n+rp, hr)
        case 1n+ap:
          lt_ge(rp, ap, x, hr, h)

def divlb(q: Nat, +r: Nat, k: Nat, +hr: {Nat.is_lt(r, 10n) == True{} : Bool},
          h: {Nat.is_ge(Nat.add(Nat.mul(q, 10n), r), Nat.mul(k, 10n)) == True{} : Bool}) -> {Nat.is_ge(q, k) == True{} : Bool}:
  match q:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+kp:
          Empty.absurd({Nat.is_ge(0n, 1n+kp) == True{} : Bool}, lt_ge(r, 10n, Nat.mul(kp, 10n), hr, h))
    case 1n+qp:
      match k:
        case 0n:
          {==}
        case 1n+kp:
          divlb(qp, r, kp, hr, h)

def divub(q: Nat, +r: Nat, k: Nat, h: {Nat.is_lt(Nat.add(Nat.mul(q, 10n), r), Nat.mul(k, 10n)) == True{} : Bool}) -> {Nat.is_lt(q, k) == True{} : Bool}:
  match q:
    case 0n:
      match k:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.lt_zero(r, h))
        case 1n+kp:
          {==}
    case 1n+qp:
      match k:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+qp, 0n) == True{} : Bool}, N.lt_zero(Nat.add(Nat.add(10n, Nat.mul(qp, 10n)), r), h))
        case 1n+kp:
          divub(qp, r, kp, h)

# c >= a and b <= a: c < b is false
def lt0f(c: Nat) -> {Nat.is_lt(c, 0n) == False{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+cp:
      {==}

def ge_lt(b: Nat, ua: Nat, c: Nat, hab: {Nat.is_le(b, ua) == True{} : Bool}, h: {Nat.is_ge(c, ua) == True{} : Bool}) -> {Nat.is_lt(c, b) == False{} : Bool}:
  match b:
    case 0n:
      lt0f(c)
    case 1n+bp:
      match ua:
        case 0n:
          Empty.absurd({Nat.is_lt(c, 1n+bp) == False{} : Bool}, no_ft(hab))
        case 1n+uap:
          match c:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 1n+bp) == False{} : Bool}, no_ft(h))
            case 1n+cp:
              ge_lt(bp, uap, cp, hab, h)

def le_lt(c: Nat, n: Nat, h: {Nat.is_le(c, n) == True{} : Bool}) -> {Nat.is_lt(c, 1n+n) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+cp:
      match n:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+cp, 1n) == True{} : Bool}, no_ft(h))
        case 1n+np:
          le_lt(cp, np, h)

def lt_mono(x: Nat, a: Nat, b: Nat, h: {Nat.is_lt(x, a) == True{} : Bool}, hab: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(x, b) == True{} : Bool}:
  match x:
    case 0n:
      match a:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, b) == True{} : Bool}, no_ft(h))
        case 1n+ap:
          match b:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, no_ft(hab))
            case 1n+bp:
              {==}
    case 1n+xp:
      match a:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+xp, b) == True{} : Bool}, no_ft(h))
        case 1n+ap:
          match b:
            case 0n:
              Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, no_ft(hab))
            case 1n+bp:
              lt_mono(xp, ap, bp, h, hab)

# n's quotient by 10 is at least k when n is at least 10k
def q_ge(+n: Nat, +k: Nat, h: {Nat.is_ge(n, Nat.mul(k, 10n)) == True{} : Bool}) -> {Nat.is_ge(Nat.div(n, 10n), k) == True{} : Bool}:
  divlb(Nat.div(n, 10n), Nat.mod(n, 10n), k, N.mod_lt(n, 9n),
    Equal.trans(Bool, Nat.is_ge(Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), Nat.mul(k, 10n)), Nat.is_ge(n, Nat.mul(k, 10n)), True{},
      Equal.cong(Nat, Bool, x => Nat.is_ge(x, Nat.mul(k, 10n)), Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), n, Equal.sym(Nat, n, Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), N.div_mod_eq(n, 9n))), h))

def q_lt(+n: Nat, +k: Nat, h: {Nat.is_lt(n, Nat.mul(k, 10n)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(n, 10n), k) == True{} : Bool}:
  divub(Nat.div(n, 10n), Nat.mod(n, 10n), k,
    Equal.trans(Bool, Nat.is_lt(Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), Nat.mul(k, 10n)), Nat.is_lt(n, Nat.mul(k, 10n)), True{},
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, Nat.mul(k, 10n)), Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), n, Equal.sym(Nat, n, Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), N.div_mod_eq(n, 9n))), h))

# ---------------------------------------------------------------------
# Strings and Bools
# ---------------------------------------------------------------------

def and_l(p: Bool, -q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {p == True{} : Bool}:
  match p:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case True{}:
      {==}

def and_r(p: Bool, -q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case False{}:
      Empty.absurd({q == True{} : Bool}, no_ft(h))
    case True{}:
      h

def not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, no_ft(h))

def or_f_l(p: Bool, -q: Bool, h: {Bool.or(p, q) == False{} : Bool}) -> {p == False{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(h))

def or_f_r(p: Bool, -q: Bool, h: {Bool.or(p, q) == False{} : Bool}) -> {q == False{} : Bool}:
  match p:
    case False{}:
      h
    case True{}:
      Empty.absurd({q == False{} : Bool}, no_tf(h))

def neq(b: Bool, +k: U32, +lit: U32, -f: U32 -> Bool, +e: {U32.is_eq(k, lit) == b : Bool}, +hk: {f(k) == True{} : Bool}, hl: {f(lit) == False{} : Bool})
  -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        no_tf(Equal.trans(Bool, True{}, f(lit), False{},
          Equal.trans(Bool, True{}, f(k), f(lit), Equal.sym(Bool, f(k), True{}, hk), Equal.cong(U32, Bool, f, k, lit, u32_eq(k, lit, e))), hl)))

def app_nil(s: String) -> {s ++ "" == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %app_nil(rest) : {SCon{c, rest ++ ""} == SCon{c, _} : String}
      {==}

def app_assoc(a: String, +b: String, +c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +rest}:
      %app_assoc(rest, b, c) : {SCon{x, (rest ++ b) ++ c} == SCon{x, _} : String}
      {==}

def rr(s: String, +a: String, +b: String) -> {String.reverse.go(String.reverse.go(s, a), b) == String.reverse.go(a, s ++ b) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      rr(rest, SCon{c, a}, b)

# ---------------------------------------------------------------------
# The status line
# ---------------------------------------------------------------------

def stat_run(s: String, +line: String, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool, +h: {L.printable(s) == True{} : Bool})
  -> {Http.feed.go(s, Http.Parse{mb, hd, cl, Http.HStat{7n, line}}) == Http.Parse{mb, hd, cl, Http.HStat{7n, String.reverse.go(s, line)}} : Http.Parse}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, 10), False{}, neq(U32.is_eq(k, 10), k, 10, x => L.in_range32(x, 32, 126), {==}, and_l(L.in_range32(k, 32, 126), L.printable(rest), h), {==}))
            : {Http.feed.go(rest, Http.Parse{mb, hd, cl, Http.stat_byte7(_, Chr{k}, line)}) == Http.Parse{mb, hd, cl, Http.HStat{7n, String.reverse.go(rest, SCon{Chr{k}, line})}} : Http.Parse}
          stat_run(rest, SCon{Chr{k}, line}, mb, hd, cl, and_r(L.in_range32(k, 32, 126), L.printable(rest), h))

def stat_line(+s: String, +w: String, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool, +line0: String, +h: {L.printable(s) == True{} : Bool})
  -> {Http.feed.go(s ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HStat{7n, line0}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.status_of(String.reverse.go(line0, s))}) : Http.Parse}:
  %split_go(s, "\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HStat{7n, line0}})
    : {_ == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.status_of(String.reverse.go(line0, s))}) : Http.Parse}
  %Equal.sym(Http.Parse, Http.feed.go(s, Http.Parse{mb, hd, cl, Http.HStat{7n, line0}}), Http.Parse{mb, hd, cl, Http.HStat{7n, String.reverse.go(s, line0)}}, stat_run(s, line0, mb, hd, cl, h))
    : {Http.feed.go("\r\n" ++ w, _) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.status_of(String.reverse.go(line0, s))}) : Http.Parse}
  %Equal.sym(String, String.reverse.go(String.reverse.go(s, line0), ""), String.reverse.go(line0, s ++ ""), rr(s, line0, "")) : {Http.feed.go(w, Http.Parse{mb, hd, cl, Http.status_of(_)}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.status_of(String.reverse.go(line0, s))}) : Http.Parse}
  %app_nil(s) : {Http.feed.go(w, Http.Parse{mb, hd, cl, Http.status_of(String.reverse.go(line0, s ++ ""))}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.status_of(String.reverse.go(line0, _))}) : Http.Parse}
  {==}

# every digit character is printable
def pdig(+d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {L.printable(SCon{Dec.digit_chr(d), SNil{}}) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+d1:
      match d1:
        case 0n:
          {==}
        case 1n+d2:
          match d2:
            case 0n:
              {==}
            case 1n+d3:
              match d3:
                case 0n:
                  {==}
                case 1n+d4:
                  match d4:
                    case 0n:
                      {==}
                    case 1n+d5:
                      match d5:
                        case 0n:
                          {==}
                        case 1n+d6:
                          match d6:
                            case 0n:
                              {==}
                            case 1n+d7:
                              match d7:
                                case 0n:
                                  {==}
                                case 1n+d8:
                                  match d8:
                                    case 0n:
                                      {==}
                                    case 1n+d9:
                                      match d9:
                                        case 0n:
                                          {==}
                                        case 1n+j:
                                          Empty.absurd({L.printable(SCon{Dec.digit_chr(10n+j), SNil{}}) == True{} : Bool}, N.lt_zero(j, h))

def d3(+c: Nat) -> String:
  SCon{Dec.digit_chr(Nat.mod(Nat.div(Nat.div(c, 10n), 10n), 10n)), SCon{Dec.digit_chr(Nat.mod(Nat.div(c, 10n), 10n)), SCon{Dec.digit_chr(Nat.mod(c, 10n)), SNil{}}}}

def and3(x: Bool, y: Bool, z: Bool, hx: {Bool.and(x, True{}) == True{} : Bool}, hy: {Bool.and(y, True{}) == True{} : Bool}, hz: {Bool.and(z, True{}) == True{} : Bool})
  -> {Bool.and(x, Bool.and(y, Bool.and(z, True{}))) == True{} : Bool}:
  match x:
    case False{}:
      hx
    case True{}:
      match y:
        case False{}:
          hy
        case True{}:
          hz

def pr3(+c: Nat) -> {L.printable(d3(c)) == True{} : Bool}:
  and3(L.in_range32(L.code(Dec.digit_chr(Nat.mod(Nat.div(Nat.div(c, 10n), 10n), 10n))), 32, 126),
       L.in_range32(L.code(Dec.digit_chr(Nat.mod(Nat.div(c, 10n), 10n))), 32, 126),
       L.in_range32(L.code(Dec.digit_chr(Nat.mod(c, 10n))), 32, 126),
       pdig(Nat.mod(Nat.div(Nat.div(c, 10n), 10n), 10n), N.mod_lt(Nat.div(Nat.div(c, 10n), 10n), 9n)),
       pdig(Nat.mod(Nat.div(c, 10n), 10n), N.mod_lt(Nat.div(c, 10n), 9n)),
       pdig(Nat.mod(c, 10n), N.mod_lt(c, 9n)))

def show3e.go(+c3: Nat, e0: {Nat.is_lt(3n+c3, 10n) == False{} : Bool}, e1: {Nat.is_lt(Nat.div(3n+c3, 10n), 10n) == False{} : Bool},
             e2: {Nat.is_lt(Nat.div(Nat.div(3n+c3, 10n), 10n), 10n) == True{} : Bool}) -> {Dec.show(3n+c3) == d3(3n+c3) : String}:
  %Equal.sym(Bool, Nat.is_lt(3n+c3, 10n), False{}, e0)
    : {Dec.show.go(3n+c3, _, Nat.div(3n+c3, 10n), SCon{Dec.digit_chr(Nat.mod(3n+c3, 10n)), SNil{}}) == d3(3n+c3) : String}
  %Equal.sym(Bool, Nat.is_lt(Nat.div(3n+c3, 10n), 10n), False{}, e1)
    : {Dec.show.go(2n+c3, _, Nat.div(Nat.div(3n+c3, 10n), 10n), SCon{Dec.digit_chr(Nat.mod(Nat.div(3n+c3, 10n), 10n)), SCon{Dec.digit_chr(Nat.mod(3n+c3, 10n)), SNil{}}}) == d3(3n+c3) : String}
  %Equal.sym(Bool, Nat.is_lt(Nat.div(Nat.div(3n+c3, 10n), 10n), 10n), True{}, e2)
    : {Dec.show.go(1n+c3, _, Nat.div(Nat.div(Nat.div(3n+c3, 10n), 10n), 10n), SCon{Dec.digit_chr(Nat.mod(Nat.div(Nat.div(3n+c3, 10n), 10n), 10n)), SCon{Dec.digit_chr(Nat.mod(Nat.div(3n+c3, 10n), 10n)), SCon{Dec.digit_chr(Nat.mod(3n+c3, 10n)), SNil{}}}}) == d3(3n+c3) : String}
  {==}

def show3e(c: Nat, +k: Nat, +h1: {Nat.is_ge(c, 100n) == True{} : Bool}, h2: {Nat.is_lt(c, Nat.mul(Nat.mul(k, 10n), 10n)) == True{} : Bool},
          hk: {Nat.is_le(k, 10n) == True{} : Bool}) -> {Dec.show(c) == d3(c) : String}:
  match c:
    case 0n:
      Empty.absurd({Dec.show(0n) == d3(0n) : String}, no_ft(h1))
    case 1n+c1:
      match c1:
        case 0n:
          Empty.absurd({Dec.show(1n) == d3(1n) : String}, no_ft(h1))
        case 1n+c2:
          match c2:
            case 0n:
              Empty.absurd({Dec.show(2n) == d3(2n) : String}, no_ft(h1))
            case 1n+(+c3):
              show3e.go(c3, ge_lt(10n, 100n, 3n+c3, {==}, h1),
                ge_lt(10n, 10n, Nat.div(3n+c3, 10n), {==}, q_ge(3n+c3, 10n, h1)),
                lt_mono(Nat.div(Nat.div(3n+c3, 10n), 10n), k, 10n, q_lt(Nat.div(3n+c3, 10n), k, q_lt(3n+c3, Nat.mul(k, 10n), h2)), hk))

def show3(+c: Nat, +k: Nat, +h1: {Nat.is_ge(c, 100n) == True{} : Bool}, +h2: {Nat.is_lt(c, Nat.mul(Nat.mul(k, 10n), 10n)) == True{} : Bool},
          +hk: {Nat.is_le(k, 10n) == True{} : Bool}) -> {String.length(Dec.show(c)) == 3n : Nat}:
  %Equal.sym(String, Dec.show(c), d3(c), show3e(c, k, h1, h2, hk)) : {String.length(_) == 3n : Nat}
  {==}

def dig_f(x: U32) -> Bool:
  L.is_digit(Chr{x})

def before_dig(d: String, +r: String, +h: {L.all_digits.go(d) == True{} : Bool}) -> {Http.before(d ++ (" " ++ r), 32) == d : String}:
  match d:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, 32), False{}, neq(U32.is_eq(k, 32), k, 32, dig_f, {==}, and_l(L.is_digit(Chr{k}), L.all_digits.go(rest), h), {==}))
            : {Http.before.go(SCon{Chr{k}, rest ++ (" " ++ r)}, 32, _) == SCon{Chr{k}, rest} : String}
          %before_dig(rest, r, and_r(L.is_digit(Chr{k}), L.all_digits.go(rest), h)) : {SCon{Chr{k}, Http.before(rest ++ (" " ++ r), 32)} == SCon{Chr{k}, _} : String}
          {==}

def ad_h(d: String) -> {Http.all_digits.go(d) == L.all_digits.go(d) : Bool}:
  match d:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %ad_h(rest) : {Http.all_digits.go(SCon{Chr{k}, rest}) == Bool.and(L.is_digit(Chr{k}), _) : Bool}
          {==}

def ad_of(d: String, h: {L.all_digits(d) == True{} : Bool}) -> {L.all_digits.go(d) == True{} : Bool}:
  match d:
    case SNil{}:
      Empty.absurd({L.all_digits.go(SNil{}) == True{} : Bool}, no_ft(h))
    case SCon{+c, +rest}:
      h

def tsl(d: String, +r: String, +h: {L.all_digits(d) == True{} : Bool}) -> {Http.trim_sp_l(d ++ (" " ++ r)) == d ++ (" " ++ r) : String}:
  match d:
    case SNil{}:
      Empty.absurd({Http.trim_sp_l(" " ++ r) == " " ++ r : String}, no_ft(h))
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, 32), False{}, neq(U32.is_eq(k, 32), k, 32, dig_f, {==}, and_l(L.is_digit(Chr{k}), L.all_digits.go(rest), h), {==}))
            : {Http.trim_sp_l.go(SCon{Chr{k}, rest ++ (" " ++ r)}, _) == SCon{Chr{k}, rest ++ (" " ++ r)} : String}
          {==}

def stat_core(+proto: String, +d: String, +r: String, +hl: {String.length(d) == 3n : Nat}, +hdg: {L.all_digits.go(d) == True{} : Bool})
  -> {Http.st_status(proto, d ++ (" " ++ r)) == Http.st_code(True{}, proto, d ++ (" " ++ r), d) : Http.Ph}:
  %Equal.sym(String, Http.before(d ++ (" " ++ r), 32), d, before_dig(d, r, hdg))
    : {Http.st_code(Bool.and(Nat.is_eq(String.length(_), 3n), Http.all_digits.go(_)), proto, d ++ (" " ++ r), _) == Http.st_code(True{}, proto, d ++ (" " ++ r), d) : Http.Ph}
  %Equal.sym(Nat, String.length(d), 3n, hl)
    : {Http.st_code(Bool.and(Nat.is_eq(_, 3n), Http.all_digits.go(d)), proto, d ++ (" " ++ r), d) == Http.st_code(True{}, proto, d ++ (" " ++ r), d) : Http.Ph}
  %Equal.sym(Bool, Http.all_digits.go(d), True{}, Equal.trans(Bool, Http.all_digits.go(d), L.all_digits.go(d), True{}, ad_h(d), hdg))
    : {Http.st_code(_, proto, d ++ (" " ++ r), d) == Http.st_code(True{}, proto, d ++ (" " ++ r), d) : Http.Ph}
  {==}

def show_val(+c: Nat) -> {Dec.value(Dec.show(c)) == c : Nat}:
  Equal.trans(Nat, Dec.value(Dec.show(c)), L.digits_value(Dec.show(c)), c, Equal.sym(Nat, L.digits_value.go(Dec.show(c), 0n), Dec.value.go(Dec.show(c), 0n), PDec.value_go_same(Dec.show(c), 0n)), L.dec_show_value(c))

def show_dig(+c: Nat) -> {L.all_digits(Dec.show(c)) == True{} : Bool}:
  and_l(L.all_digits(Dec.show(c)), Bool.or(String.eq(Dec.show(c), "0"), Bool.not(String.starts_with(Dec.show(c), "0"))), L.dec_show_canonical(c))

# a status line whose status starts with the code's 3 digits and a space
def stat_gen(+c: Nat, +r: String, +w: String, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool, +line0: String, +proto: String, +k: Nat,
    hpre: {Http.status_of(String.reverse.go(line0, Dec.show(c) ++ (" " ++ r))) == Http.st_status(proto, Http.trim_sp_l(Dec.show(c) ++ (" " ++ r))) : Http.Ph},
    +h1: {Nat.is_ge(c, 100n) == True{} : Bool}, +h2: {Nat.is_lt(c, Nat.mul(Nat.mul(k, 10n), 10n)) == True{} : Bool}, +hk: {Nat.is_le(k, 10n) == True{} : Bool},
    +hp: {L.printable(Dec.show(c) ++ (" " ++ r)) == True{} : Bool})
  -> {Http.feed.go((Dec.show(c) ++ (" " ++ r)) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HStat{7n, line0}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.st_code(True{}, proto, Dec.show(c) ++ (" " ++ r), Dec.show(c))}) : Http.Parse}:
  %stat_core(proto, Dec.show(c), r, show3(c, k, h1, h2, hk), ad_of(Dec.show(c), show_dig(c)))
    : {Http.feed.go((Dec.show(c) ++ (" " ++ r)) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HStat{7n, line0}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, _}) : Http.Parse}
  %tsl(Dec.show(c), r, show_dig(c))
    : {Http.feed.go((Dec.show(c) ++ (" " ++ r)) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HStat{7n, line0}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.st_status(proto, _)}) : Http.Parse}
  %hpre : {Http.feed.go((Dec.show(c) ++ (" " ++ r)) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HStat{7n, line0}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, _}) : Http.Parse}
  stat_line(Dec.show(c) ++ (" " ++ r), w, mb, hd, cl, line0, hp)

def and_i(p: Bool, -q: Bool, hp: {p == True{} : Bool}, hq: {q == True{} : Bool}) -> {Bool.and(p, q) == True{} : Bool}:
  match p:
    case True{}:
      hq
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(hp))

def or_l_t(p: Bool, -q: Bool, hp: {p == True{} : Bool}) -> {Bool.or(p, q) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({q == True{} : Bool}, no_ft(hp))

def pr_app(a: String, +b: String, +ha: {L.printable(a) == True{} : Bool}, +hb: {L.printable(b) == True{} : Bool}) -> {L.printable(a ++ b) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+c, +rest}:
      and_i(L.in_range32(L.code(c), 32, 126), L.printable(rest ++ b), and_l(L.in_range32(L.code(c), 32, 126), L.printable(rest), ha),
        pr_app(rest, b, and_r(L.in_range32(L.code(c), 32, 126), L.printable(rest), ha), hb))

def pr_show(+c: Nat, +k: Nat, +h1: {Nat.is_ge(c, 100n) == True{} : Bool}, +h2: {Nat.is_lt(c, Nat.mul(Nat.mul(k, 10n), 10n)) == True{} : Bool},
            +hk: {Nat.is_le(k, 10n) == True{} : Bool}) -> {L.printable(Dec.show(c)) == True{} : Bool}:
  %Equal.sym(String, Dec.show(c), d3(c), show3e(c, k, h1, h2, hk)) : {L.printable(_) == True{} : Bool}
  pr3(c)

# ---------------------------------------------------------------------
# http_interim
# ---------------------------------------------------------------------

def fb_int(nb: Bool, +c: Nat, +te: Maybe<&2, List<&2, String>>, +rr: Http.Resp, e: {nb == True{} : Bool}, hi: {Http.interim(c) == True{} : Bool})
  -> {Http.fr_body(nb, c, 1n, te, rr) == Http.HStat{0n, ""} : Http.Ph}:
  match nb:
    case True{}:
      %Equal.sym(Bool, Http.interim(c), True{}, hi) : {Http.pick(Http.Ph, _, Http.HStat{0n, ""}, Http.HDone{rr, ""}) == Http.HStat{0n, ""} : Http.Ph}
      {==}
    case False{}:
      Empty.absurd({Http.fr_body(False{}, c, 1n, te, rr) == Http.HStat{0n, ""} : Http.Ph}, no_ft(e))

def int_frame(+c: Nat, +st: String, +h0: {Bool.and(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n))) == True{} : Bool})
  -> {Http.framing(c, st, 1n, [], False{}) == Http.HStat{0n, ""} : Http.Ph}:
  fb_int(Http.no_body(False{}, c), c, None{}, Http.Resp{c, st, [], "", Bool.and(True{}, Bool.not(Nat.is_eq(c, 101n)))},
    or_l_t(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n)),
      and_l(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n)), h0)), h0)

def interim_main(+c: Nat, +reason: String, +r: Http.Resp, +rest: String,
    +h0: {Bool.and(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n))) == True{} : Bool},
    +h1: {Bool.and(L.printable(reason), L.resp_cl_ok(r)) == True{} : Bool})
  -> {L.parse_of(None{}, False{}, "HTTP/1.1 " ++ Dec.show(c) ++ " " ++ reason ++ "\r\n\r\n" ++ L.render_cl(r) ++ rest)
      == L.parse_of(None{}, False{}, L.render_cl(r) ++ rest) : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  %app_assoc(Dec.show(c), " " ++ reason, "\r\n" ++ ("\r\n" ++ (L.render_cl(r) ++ rest)))
    : {Http.done(Http.feed.go(_, Http.Parse{None{}, False{}, False{}, Http.HStat{7n, " 1.1/PTTH"}})) == L.parse_of(None{}, False{}, L.render_cl(r) ++ rest) : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  Equal.trans(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>,
    Http.done(Http.feed.go((Dec.show(c) ++ (" " ++ reason)) ++ ("\r\n" ++ ("\r\n" ++ (L.render_cl(r) ++ rest))), Http.Parse{None{}, False{}, False{}, Http.HStat{7n, " 1.1/PTTH"}})),
    Http.done(Http.feed.go("\r\n" ++ (L.render_cl(r) ++ rest), Http.Parse{None{}, False{}, False{}, Http.st_code(True{}, "HTTP/1.1", Dec.show(c) ++ (" " ++ reason), Dec.show(c))})),
    L.parse_of(None{}, False{}, L.render_cl(r) ++ rest),
    Equal.cong(Http.Parse, Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, p => Http.done(p),
      Http.feed.go((Dec.show(c) ++ (" " ++ reason)) ++ ("\r\n" ++ ("\r\n" ++ (L.render_cl(r) ++ rest))), Http.Parse{None{}, False{}, False{}, Http.HStat{7n, " 1.1/PTTH"}}),
      Http.feed.go("\r\n" ++ (L.render_cl(r) ++ rest), Http.Parse{None{}, False{}, False{}, Http.st_code(True{}, "HTTP/1.1", Dec.show(c) ++ (" " ++ reason), Dec.show(c))}),
      stat_gen(c, reason, "\r\n" ++ (L.render_cl(r) ++ rest), None{}, False{}, False{}, " 1.1/PTTH", "HTTP/1.1", 2n, {==},
        and_l(Nat.is_ge(c, 100n), Nat.is_le(c, 199n), and_l(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n)), h0)),
        le_lt(c, 199n, and_r(Nat.is_ge(c, 100n), Nat.is_le(c, 199n), and_l(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n)), h0))),
        {==},
        pr_app(Dec.show(c), " " ++ reason,
          pr_show(c, 2n, and_l(Nat.is_ge(c, 100n), Nat.is_le(c, 199n), and_l(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n)), h0)),
            le_lt(c, 199n, and_r(Nat.is_ge(c, 100n), Nat.is_le(c, 199n), and_l(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.not(Nat.is_eq(c, 101n)), h0))), {==}),
          and_l(L.printable(reason), L.resp_cl_ok(r), h1)))),
    Equal.cong(Http.Ph, Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, ph => Http.done(Http.feed.go(L.render_cl(r) ++ rest, Http.Parse{None{}, False{}, False{}, ph})),
      Http.framing(Dec.value(Dec.show(c)), Dec.show(c) ++ (" " ++ reason), 1n, [], False{}), Http.HStat{0n, ""},
      Equal.trans(Http.Ph, Http.framing(Dec.value(Dec.show(c)), Dec.show(c) ++ (" " ++ reason), 1n, [], False{}),
        Http.framing(c, Dec.show(c) ++ (" " ++ reason), 1n, [], False{}), Http.HStat{0n, ""},
        Equal.cong(Nat, Http.Ph, x => Http.framing(x, Dec.show(c) ++ (" " ++ reason), 1n, [], False{}), Dec.value(Dec.show(c)), c, show_val(c)),
        int_frame(c, Dec.show(c) ++ (" " ++ reason), h0))))

def L.http_interim(c, reason, r, rest, h0, h1):
  interim_main(c, reason, r, rest, h0, h1)


# ---------------------------------------------------------------------
# Reversal and trimming
# ---------------------------------------------------------------------

def rev(+s: String) -> String:
  String.reverse.go(s, "")

# the right trim: trim_ows is rtrim after trim_ows_l
def rtrim(+s: String) -> String:
  rev(Http.trim_ows_l(rev(s)))

def revacc2(s: String, +a: String, +b: String) -> {String.reverse.go(s, a ++ b) == String.reverse.go(s, a) ++ b : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      revacc2(rest, SCon{c, a}, b)

def revacc(+s: String, +acc: String) -> {String.reverse.go(s, acc) == rev(s) ++ acc : String}:
  revacc2(s, "", acc)

def revapp(a: String, +b: String, +acc: String) -> {String.reverse.go(a ++ b, acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      revapp(rest, b, SCon{c, acc})

# rev(a ++ b) == rev(b) ++ rev(a)
def rev_app(+a: String, +b: String) -> {rev(a ++ b) == rev(b) ++ rev(a) : String}:
  %revacc(b, rev(a)) : {rev(a ++ b) == _ : String}
  revapp(a, b, "")

def rev_rev(+s: String) -> {rev(rev(s)) == s : String}:
  %Equal.sym(String, rev(rev(s)), String.reverse.go("", s ++ ""), rr(s, "", "")) : {_ == s : String}
  app_nil(s)

def empty_app(a: String, +c: Char, +b: String) -> {String.is_empty(a ++ SCon{c, b}) == False{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +rest}:
      {==}

def empty_rev(s: String) -> {String.is_empty(rev(s)) == String.is_empty(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %Equal.sym(String, String.reverse.go(rest, SCon{c, SNil{}}), rev(rest) ++ SCon{c, SNil{}}, revacc(rest, SCon{c, SNil{}})) : {String.is_empty(_) == False{} : Bool}
      empty_app(rev(rest), c, SNil{})

def ws(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), U32.is_eq(k, 9))

def tl_step(b: Bool, +c: Char, +x: String, +y: String, h: {String.is_empty(Http.trim_ows_l.go(SCon{c, x}, b)) == False{} : Bool},
            ih: {String.is_empty(Http.trim_ows_l(x)) == False{} : Bool} -> {Http.trim_ows_l(x ++ y) == Http.trim_ows_l(x) ++ y : String})
  -> {Http.trim_ows_l.go(SCon{c, x ++ y}, b) == Http.trim_ows_l.go(SCon{c, x}, b) ++ y : String}:
  match b:
    case True{}:
      ih(h)
    case False{}:
      {==}

# left-trimming x ++ y stops inside x when x is not all blanks
def tl_app(x: String, +y: String, h: {String.is_empty(Http.trim_ows_l(x)) == False{} : Bool}) -> {Http.trim_ows_l(x ++ y) == Http.trim_ows_l(x) ++ y : String}:
  match x:
    case SNil{}:
      Empty.absurd({Http.trim_ows_l(y) == y : String}, no_tf(h))
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          tl_step(ws(k), Chr{k}, rest, y, h, hh => tl_app(rest, y, hh))

def tli_step(b: Bool, +k: U32, +x: String, +e: {ws(k) == b : Bool}, ih: {Http.trim_ows_l(Http.trim_ows_l(x)) == Http.trim_ows_l(x) : String})
  -> {Http.trim_ows_l(Http.trim_ows_l.go(SCon{Chr{k}, x}, b)) == Http.trim_ows_l.go(SCon{Chr{k}, x}, b) : String}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, ws(k), False{}, e) : {Http.trim_ows_l.go(SCon{Chr{k}, x}, _) == SCon{Chr{k}, x} : String}
      {==}

def tl_idem(x: String) -> {Http.trim_ows_l(Http.trim_ows_l(x)) == Http.trim_ows_l(x) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          tli_step(ws(k), k, rest, {==}, tl_idem(rest))

def rtrim_idem(+y: String) -> {rtrim(rtrim(y)) == rtrim(y) : String}:
  Equal.trans(String, rtrim(rtrim(y)), rev(Http.trim_ows_l(Http.trim_ows_l(rev(y)))), rtrim(y),
    Equal.cong(String, String, x => rev(Http.trim_ows_l(x)), rev(rev(Http.trim_ows_l(rev(y)))), Http.trim_ows_l(rev(y)), rev_rev(Http.trim_ows_l(rev(y)))),
    Equal.cong(String, String, x => rev(x), Http.trim_ows_l(Http.trim_ows_l(rev(y))), Http.trim_ows_l(rev(y)), tl_idem(rev(y))))

# the right trim of a ++ b is a ++ the right trim of b, when that is not empty
def rtrim_app(+a: String, +b: String, +h: {String.is_empty(rtrim(b)) == False{} : Bool}) -> {rtrim(a ++ b) == a ++ rtrim(b) : String}:
  Equal.trans(String, rtrim(a ++ b), rev(Http.trim_ows_l(rev(b) ++ rev(a))), a ++ rtrim(b),
    Equal.cong(String, String, x => rev(Http.trim_ows_l(x)), rev(a ++ b), rev(b) ++ rev(a), rev_app(a, b)),
    Equal.trans(String, rev(Http.trim_ows_l(rev(b) ++ rev(a))), rev(Http.trim_ows_l(rev(b)) ++ rev(a)), a ++ rtrim(b),
      Equal.cong(String, String, x => rev(x), Http.trim_ows_l(rev(b) ++ rev(a)), Http.trim_ows_l(rev(b)) ++ rev(a),
        tl_app(rev(b), rev(a), Equal.trans(Bool, String.is_empty(Http.trim_ows_l(rev(b))), String.is_empty(rtrim(b)), False{}, Equal.sym(Bool, String.is_empty(rtrim(b)), String.is_empty(Http.trim_ows_l(rev(b))), empty_rev(Http.trim_ows_l(rev(b)))), h))),
      Equal.trans(String, rev(Http.trim_ows_l(rev(b)) ++ rev(a)), rev(rev(a)) ++ rtrim(b), a ++ rtrim(b),
        rev_app(Http.trim_ows_l(rev(b)), rev(a)),
        Equal.cong(String, String, x => x ++ rtrim(b), rev(rev(a)), a, rev_rev(a)))))

# ---------------------------------------------------------------------
# lib's one-pass right trim is the reversing one
# ---------------------------------------------------------------------

def empty_nil(s: String, +h: {String.is_empty(s) == True{} : Bool}) -> {s == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Empty.absurd({SCon{c, t} == "" : String}, no_ft(h))

def tlae_step(b: Bool, +c: Char, +x: String, +y: String, +h: {String.is_empty(Http.trim_ows_l.go(SCon{c, x}, b)) == True{} : Bool},
              ih: {String.is_empty(Http.trim_ows_l(x)) == True{} : Bool} -> {Http.trim_ows_l(x ++ y) == Http.trim_ows_l(y) : String})
  -> {Http.trim_ows_l.go(SCon{c, x ++ y}, b) == Http.trim_ows_l(y) : String}:
  match b:
    case True{}:
      ih(h)
    case False{}:
      Empty.absurd({SCon{c, x ++ y} == Http.trim_ows_l(y) : String}, no_ft(h))

# left-trimming x ++ y skips an x of blanks
def tl_app_e(x: String, +y: String, +h: {String.is_empty(Http.trim_ows_l(x)) == True{} : Bool}) -> {Http.trim_ows_l(x ++ y) == Http.trim_ows_l(y) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          tlae_step(ws(k), Chr{k}, rest, y, h, hh => tl_app_e(rest, y, hh))

def rof_ne(t: String, +c: Char, +h: {String.is_empty(t) == False{} : Bool}) -> {Http.rtrim.of(t, c) == SCon{c, t} : String}:
  match t:
    case SNil{}:
      Empty.absurd({Http.rtrim.of(SNil{}, c) == SCon{c, SNil{}} : String}, no_tf(h))
    case SCon{+d, +r}:
      {==}

def rone(w: Bool, +k: U32) -> {Http.rtrim.one(w, Chr{k}) == rev(Http.trim_ows_l.go(SCon{Chr{k}, SNil{}}, w)) : String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def rf_case(b: Bool, +k: U32, +x: String, +e: {String.is_empty(Http.trim_ows_l(rev(x))) == b : Bool})
  -> {Http.rtrim.of(rtrim(x), Chr{k}) == rev(Http.trim_ows_l(rev(x) ++ SCon{Chr{k}, SNil{}})) : String}:
  match b:
    case False{}:
      Equal.trans(String, Http.rtrim.of(rtrim(x), Chr{k}), SCon{Chr{k}, rtrim(x)}, rev(Http.trim_ows_l(rev(x) ++ SCon{Chr{k}, SNil{}})),
        rof_ne(rtrim(x), Chr{k}, Equal.trans(Bool, String.is_empty(rtrim(x)), String.is_empty(Http.trim_ows_l(rev(x))), False{}, empty_rev(Http.trim_ows_l(rev(x))), e)),
        Equal.sym(String, rev(Http.trim_ows_l(rev(x) ++ SCon{Chr{k}, SNil{}})), SCon{Chr{k}, rtrim(x)},
          Equal.trans(String, rev(Http.trim_ows_l(rev(x) ++ SCon{Chr{k}, SNil{}})), rev(Http.trim_ows_l(rev(x)) ++ SCon{Chr{k}, SNil{}}), SCon{Chr{k}, rtrim(x)},
            Equal.cong(String, String, z => rev(z), Http.trim_ows_l(rev(x) ++ SCon{Chr{k}, SNil{}}), Http.trim_ows_l(rev(x)) ++ SCon{Chr{k}, SNil{}}, tl_app(rev(x), SCon{Chr{k}, SNil{}}, e)),
            rev_app(Http.trim_ows_l(rev(x)), SCon{Chr{k}, SNil{}}))))
    case True{}:
      %Equal.sym(String, Http.trim_ows_l(rev(x)), "", empty_nil(Http.trim_ows_l(rev(x)), e)) : {Http.rtrim.of(rev(_), Chr{k}) == rev(Http.trim_ows_l(rev(x) ++ SCon{Chr{k}, SNil{}})) : String}
      %Equal.sym(String, Http.trim_ows_l(rev(x) ++ SCon{Chr{k}, SNil{}}), Http.trim_ows_l(SCon{Chr{k}, SNil{}}), tl_app_e(rev(x), SCon{Chr{k}, SNil{}}, e)) : {Http.rtrim.of(SNil{}, Chr{k}) == rev(_) : String}
      rone(ws(k), k)

# lib's rtrim is the right trim by reversing
def rf_eq(s: String) -> {Http.rtrim(s) == rtrim(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +x}:
      match c:
        case Chr{+k}:
          %Equal.sym(String, Http.rtrim(x), rtrim(x), rf_eq(x)) : {Http.rtrim.of(_, Chr{k}) == rtrim(SCon{Chr{k}, x}) : String}
          %Equal.sym(String, String.reverse.go(x, SCon{Chr{k}, SNil{}}), rev(x) ++ SCon{Chr{k}, SNil{}}, revacc(x, SCon{Chr{k}, SNil{}}))
            : {Http.rtrim.of(rtrim(x), Chr{k}) == rev(Http.trim_ows_l(_)) : String}
          rf_case(String.is_empty(Http.trim_ows_l(rev(x))), k, x, {==})

# lib's trim is the reversing one
def tr_eq(+s: String) -> {Http.trim_ows(s) == rtrim(Http.trim_ows_l(s)) : String}:
  rf_eq(Http.trim_ows_l(s))

# ---------------------------------------------------------------------
# http_request: lib's helpers are LAWS', def for def
# ---------------------------------------------------------------------

def pick_h(-A: Data, c: Bool, -a: A, -b: A, -x: A, -y: A, ea: {a == x : A}, eb: {b == y : A})
  -> {Http.pick(A, c, a, b) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def and_f(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def eqfin_rec(+a: Char, +b: Char, p: (String & String) & Cmp) -> {String.eq.fin(String.cmp.rec(a, b, p)) == String.eq.fin(p) : Bool}:
  match p:
    case (ab, r):
      match ab:
        case (u, v):
          {==}

def sg_false(a: String, b: String) -> {Http.seq.go(a, b, False{}) == False{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, at}:
      match b:
        case SNil{}:
          {==}
        case SCon{d, bt}:
          {==}

def sg_fin(t: Cmp, +x: U32, +y: U32, +at: String, +bt: String, +ih: {Http.seq.go(at, bt, True{}) == Bool.and(True{}, String.eq(at, bt)) : Bool})
  -> {Http.seq.go(at, bt, Cmp.is_eq(t)) == String.eq.fin(String.cmp.fin(at, bt, ((Chr{x}, Chr{y}), t))) : Bool}:
  match t:
    case LT{}:
      sg_false(at, bt)
    case GT{}:
      sg_false(at, bt)
    case EQ{}:
      Equal.trans(Bool, Http.seq.go(at, bt, True{}), String.eq(at, bt), String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(at, bt))),
        ih, Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(at, bt))), String.eq(at, bt), eqfin_rec(Chr{x}, Chr{y}, String.cmp(at, bt))))

def sg2(c: Char, d: Char, +at: String, +bt: String, +ih: {Http.seq.go(at, bt, True{}) == Bool.and(True{}, String.eq(at, bt)) : Bool})
  -> {Http.seq.go(SCon{c, at}, SCon{d, bt}, True{}) == Bool.and(True{}, String.eq(SCon{c, at}, SCon{d, bt})) : Bool}:
  match c:
    case Chr{+x}:
      match d:
        case Chr{+y}:
          sg_fin(U32.cmp(x, y), x, y, at, bt, ih)

def sg(a: String, b: String, ok: Bool) -> {Http.seq.go(a, b, ok) == Bool.and(ok, String.eq(a, b)) : Bool}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{d, bt}:
          {==}
    case SCon{c, +at}:
      match b:
        case SNil{}:
          Equal.sym(Bool, Bool.and(ok, False{}), False{}, and_f(ok))
        case SCon{d, +bt}:
          match ok:
            case False{}:
              {==}
            case True{}:
              sg2(c, d, at, bt, sg(at, bt, True{}))

# lib's byte-by-byte string equality is Base's
def seq_eq(a: String, b: String) -> {Http.seq(a, b) == String.eq(a, b) : Bool}:
  sg(a, b, True{})

def has_char_h(s: String, +k: U32) -> {Http.has_char(s, k) == L.has_char(s, k) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %has_char_h(rest, k) : {Bool.or(U32.is_eq(x, k), Http.has_char(rest, k)) == Bool.or(U32.is_eq(x, k), _) : Bool}
          {==}

def byte_at_h(s: String, +i: Nat) -> {Http.byte_at(s, i) == L.byte_at(s, i) : U32}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              byte_at_h(rest, j)

def tlh_step(b: Bool, +x: U32, +rest: String, +ih: {Http.trim_ows_l(rest) == L.trim_ows_l(rest) : String})
  -> {Http.trim_ows_l.go(SCon{Chr{x}, rest}, b) == L.pick(String, b, L.trim_ows_l(rest), SCon{Chr{x}, rest}) : String}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

def trim_l_h(s: String) -> {Http.trim_ows_l(s) == L.trim_ows_l(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          tlh_step(Bool.or(U32.is_eq(x, 32), U32.is_eq(x, 9)), x, rest, trim_l_h(rest))

def trim_h(+s: String) -> {Http.trim_ows(s) == L.trim_ows(s) : String}:
  %Equal.sym(String, Http.trim_ows(s), rtrim(Http.trim_ows_l(s)), tr_eq(s)) : {_ == L.trim_ows(s) : String}
  %trim_l_h(s) : {rtrim(Http.trim_ows_l(s)) == String.reverse(L.trim_ows_l(String.reverse(_))) : String}
  %trim_l_h(String.reverse(Http.trim_ows_l(s))) : {rtrim(Http.trim_ows_l(s)) == String.reverse(_) : String}
  {==}

def nl_h(s: String) -> {Http.nl_to_space(s) == L.nl_to_space(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %nl_h(rest) : {Http.nl_to_space(SCon{Chr{x}, rest}) == L.pick(String, Bool.or(U32.is_eq(x, 10), U32.is_eq(x, 13)), " ", SCon{Chr{x}, SNil{}}) ++ _ : String}
          %pick_h(String, Bool.or(U32.is_eq(x, 10), U32.is_eq(x, 13)), " ", SCon{Chr{x}, SNil{}}, " ", SCon{Chr{x}, SNil{}}, {==}, {==})
            : {Http.nl_to_space(SCon{Chr{x}, rest}) == _ ++ Http.nl_to_space(rest) : String}
          {==}

def tbh(al: Bool, +k: U32) -> {Http.tb.of(al, k) == Bool.or(al, L.has_char("!#$%&'*+-.^_`|~", k)) : Bool}:
  match al:
    case True{}:
      {==}
    case False{}:
      {==}

# lib's token bytes are LAWS'
def tb_eq(+k: U32) -> {Http.token_byte(k) == L.token_byte(k) : Bool}:
  tbh(Http.is_alnum(k), k)

def all_token_h(s: String) -> {Http.all_token(s) == L.all_token(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %all_token_h(rest) : {Http.all_token(SCon{Chr{x}, rest}) == Bool.and(L.token_byte(x), _) : Bool}
          %tb_eq(x) : {Http.all_token(SCon{Chr{x}, rest}) == Bool.and(_, Http.all_token(rest)) : Bool}
          {==}

def token_h(+s: String) -> {Http.token(s) == L.token(s) : Bool}:
  %all_token_h(s) : {Http.token(s) == Bool.and(Bool.not(String.is_empty(s)), _) : Bool}
  {==}

def hdr_lines_h(+k: String, vs: List<&2, String>) -> {Http.hdr_lines(k, vs) == L.hdr_lines(k, vs) : String}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      %hdr_lines_h(k, rest) : {Http.hdr_lines(k, Con{v, rest}) == k ++ ": " ++ L.trim_ows(L.nl_to_space(v)) ++ "\r\n" ++ _ : String}
      %nl_h(v) : {Http.hdr_lines(k, Con{v, rest}) == k ++ ": " ++ L.trim_ows(_) ++ "\r\n" ++ Http.hdr_lines(k, rest) : String}
      %trim_h(Http.nl_to_space(v)) : {Http.hdr_lines(k, Con{v, rest}) == k ++ ": " ++ _ ++ "\r\n" ++ Http.hdr_lines(k, rest) : String}
      {==}

def hdrs_text_h(hs: List<&2, Hdr.Header>) -> {Http.hdrs_text(hs) == L.hdrs_text(hs) : String}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      match h:
        case Hdr.Header{+k, +vs}:
          %hdrs_text_h(rest) : {Http.hdrs_text(Con{Hdr.Header{k, vs}, rest}) == L.pick(String, L.token(k), L.hdr_lines(k, vs), "") ++ _ : String}
          %token_h(k) : {Http.hdrs_text(Con{Hdr.Header{k, vs}, rest}) == L.pick(String, _, L.hdr_lines(k, vs), "") ++ Http.hdrs_text(rest) : String}
          %pick_h(String, Http.token(k), Http.hdr_lines(k, vs), "", L.hdr_lines(k, vs), "", hdr_lines_h(k, vs), {==})
            : {Http.hdrs_text(Con{Hdr.Header{k, vs}, rest}) == _ ++ Http.hdrs_text(rest) : String}
          {==}

def insert_h2(h: Hdr.Header, x: Hdr.Header, +rest: List<&2, Hdr.Header>, ih: {Http.insert_hdr(h, rest) == L.insert_hdr(h, rest) : List<&2, Hdr.Header>})
  -> {Http.insert_hdr(h, Con{x, rest}) == L.insert_hdr(h, Con{x, rest}) : List<&2, Hdr.Header>}:
  match h x:
    case Hdr.Header{+k1, +v1} Hdr.Header{+k2, +v2}:
      pick_h(List<&2, Hdr.Header>, String.is_lt(k1, k2),
        Con{Hdr.Header{k1, v1}, Con{Hdr.Header{k2, v2}, rest}}, Con{Hdr.Header{k2, v2}, Http.insert_hdr(Hdr.Header{k1, v1}, rest)},
        Con{Hdr.Header{k1, v1}, Con{Hdr.Header{k2, v2}, rest}}, Con{Hdr.Header{k2, v2}, L.insert_hdr(Hdr.Header{k1, v1}, rest)},
        {==}, Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, t => Con{Hdr.Header{k2, v2}, t}, Http.insert_hdr(Hdr.Header{k1, v1}, rest), L.insert_hdr(Hdr.Header{k1, v1}, rest), ih))

def insert_h(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> {Http.insert_hdr(h, hs) == L.insert_hdr(h, hs) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      insert_h2(h, x, rest, insert_h(h, rest))

def sort_h(hs: List<&2, Hdr.Header>) -> {Http.sort_hdrs(hs) == L.sort_hdrs(hs) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %sort_h(rest) : {Http.insert_hdr(h, Http.sort_hdrs(rest)) == L.insert_hdr(h, _) : List<&2, Hdr.Header>}
      insert_h(h, Http.sort_hdrs(rest))

def drop_exact_h2(+k: String, h: Hdr.Header, +rest: List<&2, Hdr.Header>, +ih: {Http.drop_exact(k, rest) == L.drop_exact(k, rest) : List<&2, Hdr.Header>})
  -> {Http.drop_exact(k, Con{h, rest}) == L.drop_exact(k, Con{h, rest}) : List<&2, Hdr.Header>}:
  match h:
    case Hdr.Header{+hk, +hv}:
      pick_h(List<&2, Hdr.Header>, String.eq(hk, k), Http.drop_exact(k, rest), Con{Hdr.Header{hk, hv}, Http.drop_exact(k, rest)},
        L.drop_exact(k, rest), Con{Hdr.Header{hk, hv}, L.drop_exact(k, rest)},
        ih, Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, t => Con{Hdr.Header{hk, hv}, t}, Http.drop_exact(k, rest), L.drop_exact(k, rest), ih))

def drop_exact_h(+k: String, hs: List<&2, Hdr.Header>) -> {Http.drop_exact(k, hs) == L.drop_exact(k, hs) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      drop_exact_h2(k, h, rest, drop_exact_h(k, rest))

def set_hdr_h(+k: String, +v: String, +hs: List<&2, Hdr.Header>) -> {Http.set_hdr(k, v, hs) == L.set_hdr(k, v, hs) : List<&2, Hdr.Header>}:
  %drop_exact_h(k, hs) : {Http.set_hdr(k, v, hs) == List.append(&2, Hdr.Header, _, [Hdr.Header{k, [v]}]) : List<&2, Hdr.Header>}
  {==}

def hdr_get_h2(+k: String, h: Hdr.Header, +rest: List<&2, Hdr.Header>, +ih: {Http.hdr_get(k, rest) == L.hdr_get(k, rest) : Maybe<&2, List<&2, String>>})
  -> {Http.hdr_get(k, Con{h, rest}) == L.hdr_get(k, Con{h, rest}) : Maybe<&2, List<&2, String>>}:
  match h:
    case Hdr.Header{+hk, +hv}:
      %Equal.sym(Bool, Http.seq(hk, k), String.eq(hk, k), seq_eq(hk, k))
        : {Http.pick(Maybe<&2, List<&2, String>>, _, Some{hv}, Http.hdr_get(k, rest)) == L.pick(Maybe<&2, List<&2, String>>, String.eq(hk, k), Some{hv}, L.hdr_get(k, rest)) : Maybe<&2, List<&2, String>>}
      pick_h(Maybe<&2, List<&2, String>>, String.eq(hk, k), Some{hv}, Http.hdr_get(k, rest), Some{hv}, L.hdr_get(k, rest), {==}, ih)


def hdr_get_h(+k: String, hs: List<&2, Hdr.Header>) -> {Http.hdr_get(k, hs) == L.hdr_get(k, hs) : Maybe<&2, List<&2, String>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      hdr_get_h2(k, h, rest, hdr_get_h(k, rest))

def first_of_h(+d: String, +m: Maybe<&2, List<&2, String>>) -> {Http.first_of(d, m) == L.first_of(d, m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+vs}:
      {==}

def hexu_h(+n: U32) -> {Http.hexu(n) == L.hexu(n) : String}:
  %pick_h(U32, U32.is_lt(n, 10), (48 + n : U32), (55 + n : U32), (48 + n : U32), (55 + n : U32), {==}, {==})
    : {Http.hexu(n) == L.str1(_) : String}
  {==}

def hex_val_h(+k: U32) -> {Http.hex_val32(k) == L.hex_val(k) : U32}:
  pick_h(U32, L.in_range32(k, 48, 57), (k - 48 : U32), Http.pick(U32, L.in_range32(k, 65, 70), (k - 55 : U32), (k - 87 : U32)),
    (k - 48 : U32), L.pick(U32, L.in_range32(k, 65, 70), (k - 55 : U32), (k - 87 : U32)), {==},
    pick_h(U32, L.in_range32(k, 65, 70), (k - 55 : U32), (k - 87 : U32), (k - 55 : U32), (k - 87 : U32), {==}, {==}))

def valid_h(s: String) -> {Http.valid_encoded(s) == L.valid_encoded(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %valid_h(rest) : {Http.valid_encoded(SCon{Chr{x}, rest}) == Bool.and(Bool.or(L.unreserved(x), L.has_char("!$&'()*+,;=:@/%[]", x)), _) : Bool}
          {==}

def esc_h(s: String) -> {Http.escape_path(s) == L.escape_path(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %esc_h(rest) : {Http.escape_path(SCon{Chr{x}, rest}) == L.pick(String, Bool.or(L.unreserved(x), L.has_char("$&+,/:;=@", x)), L.str1(x), "%" ++ L.hexu((x >> 4n : U32)) ++ L.hexu((x .&. 15 : U32))) ++ _ : String}
          %hexu_h((x >> 4n : U32)) : {Http.escape_path(SCon{Chr{x}, rest}) == L.pick(String, Bool.or(L.unreserved(x), L.has_char("$&+,/:;=@", x)), L.str1(x), "%" ++ _ ++ L.hexu((x .&. 15 : U32))) ++ Http.escape_path(rest) : String}
          %hexu_h((x .&. 15 : U32)) : {Http.escape_path(SCon{Chr{x}, rest}) == L.pick(String, Bool.or(L.unreserved(x), L.has_char("$&+,/:;=@", x)), L.str1(x), "%" ++ Http.hexu((x >> 4n : U32)) ++ _) ++ Http.escape_path(rest) : String}
          %pick_h(String, Bool.or(L.unreserved(x), L.has_char("$&+,/:;=@", x)), L.str1(x), "%" ++ Http.hexu((x >> 4n : U32)) ++ Http.hexu((x .&. 15 : U32)), L.str1(x), "%" ++ Http.hexu((x >> 4n : U32)) ++ Http.hexu((x .&. 15 : U32)), {==}, {==})
            : {Http.escape_path(SCon{Chr{x}, rest}) == _ ++ Http.escape_path(rest) : String}
          {==}

def before_q_h(s: String) -> {Http.before_q(s) == L.before_q(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          pick_h(String, U32.is_eq(x, 63), "", SCon{Chr{x}, Http.before_q(rest)}, "", SCon{Chr{x}, L.before_q(rest)}, {==},
            Equal.cong(String, String, t => SCon{Chr{x}, t}, Http.before_q(rest), L.before_q(rest), before_q_h(rest)))

def ue_v(+s: String)
  -> {((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + Http.hex_val32(Http.byte_at(s, 2n))) .&. 255 : U32)
      == ((L.hex_val(L.byte_at(s, 1n)) * 16 + L.hex_val(L.byte_at(s, 2n))) .&. 255 : U32) : U32}:
  %byte_at_h(s, 1n) : {((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + Http.hex_val32(Http.byte_at(s, 2n))) .&. 255 : U32) == ((L.hex_val(_) * 16 + L.hex_val(L.byte_at(s, 2n))) .&. 255 : U32) : U32}
  %byte_at_h(s, 2n) : {((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + Http.hex_val32(Http.byte_at(s, 2n))) .&. 255 : U32) == ((L.hex_val(Http.byte_at(s, 1n)) * 16 + L.hex_val(_)) .&. 255 : U32) : U32}
  %hex_val_h(Http.byte_at(s, 1n)) : {((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + Http.hex_val32(Http.byte_at(s, 2n))) .&. 255 : U32) == ((_ * 16 + L.hex_val(Http.byte_at(s, 2n))) .&. 255 : U32) : U32}
  %hex_val_h(Http.byte_at(s, 2n)) : {((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + Http.hex_val32(Http.byte_at(s, 2n))) .&. 255 : U32) == ((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + _) .&. 255 : U32) : U32}
  {==}

def ue_step(p: Bool, +f: Nat, +s: String,
  +ih3: {Http.unescape.go(f, String.drop(s, 3n)) == L.unescape.go(f, String.drop(s, 3n)) : String},
  +ih1: {Http.unescape.go(f, String.drop(s, 1n)) == L.unescape.go(f, String.drop(s, 1n)) : String})
  -> {Http.str1(Http.pick(U32, p, ((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + Http.hex_val32(Http.byte_at(s, 2n))) .&. 255 : U32), Http.byte_at(s, 0n)))
        ++ Http.unescape.go(f, String.drop(s, Http.pick(Nat, p, 3n, 1n)))
      == L.str1(L.pick(U32, p, ((L.hex_val(L.byte_at(s, 1n)) * 16 + L.hex_val(L.byte_at(s, 2n))) .&. 255 : U32), L.byte_at(s, 0n)))
        ++ L.unescape.go(f, String.drop(s, L.pick(Nat, p, 3n, 1n))) : String}:
  match p:
    case True{}:
      %ih3 : {Http.str1(((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + Http.hex_val32(Http.byte_at(s, 2n))) .&. 255 : U32)) ++ Http.unescape.go(f, String.drop(s, 3n))
              == L.str1(((L.hex_val(L.byte_at(s, 1n)) * 16 + L.hex_val(L.byte_at(s, 2n))) .&. 255 : U32)) ++ _ : String}
      %ue_v(s) : {Http.str1(((Http.hex_val32(Http.byte_at(s, 1n)) * 16 + Http.hex_val32(Http.byte_at(s, 2n))) .&. 255 : U32)) ++ Http.unescape.go(f, String.drop(s, 3n))
              == L.str1(_) ++ Http.unescape.go(f, String.drop(s, 3n)) : String}
      {==}
    case False{}:
      %ih1 : {Http.str1(Http.byte_at(s, 0n)) ++ Http.unescape.go(f, String.drop(s, 1n)) == L.str1(L.byte_at(s, 0n)) ++ _ : String}
      %byte_at_h(s, 0n) : {Http.str1(Http.byte_at(s, 0n)) ++ Http.unescape.go(f, String.drop(s, 1n)) == L.str1(_) ++ Http.unescape.go(f, String.drop(s, 1n)) : String}
      {==}

def ue_h(fuel: Nat, +s: String) -> {Http.unescape.go(fuel, s) == L.unescape.go(fuel, s) : String}:
  match fuel:
    case 0n:
      {==}
    case 1n+(+f):
      match s:
        case SNil{}:
          {==}
        case SCon{+c, +rest}:
          match c:
            case Chr{+x}:
              ue_step(Bool.and(U32.is_eq(x, 37), Nat.is_ge(String.length(SCon{Chr{x}, rest}), 3n)), f, SCon{Chr{x}, rest},
                ue_h(f, String.drop(SCon{Chr{x}, rest}, 3n)), ue_h(f, String.drop(SCon{Chr{x}, rest}, 1n)))

def request_uri_h(+path: String) -> {Http.request_uri(path) == L.request_uri(path) : String}:
  %before_q_h(path) : {Http.request_uri(path) == L.pick(String, L.valid_encoded(_), _, L.escape_path(L.unescape(_))) ++ String.drop(path, String.length(_)) : String}
  %valid_h(Http.before_q(path)) : {Http.request_uri(path) == L.pick(String, _, Http.before_q(path), L.escape_path(L.unescape(Http.before_q(path)))) ++ String.drop(path, String.length(Http.before_q(path))) : String}
  %ue_h(String.length(Http.before_q(path)), Http.before_q(path))
    : {Http.request_uri(path) == L.pick(String, Http.valid_encoded(Http.before_q(path)), Http.before_q(path), L.escape_path(_)) ++ String.drop(path, String.length(Http.before_q(path))) : String}
  %esc_h(Http.unescape(Http.before_q(path)))
    : {Http.request_uri(path) == L.pick(String, Http.valid_encoded(Http.before_q(path)), Http.before_q(path), _) ++ String.drop(path, String.length(Http.before_q(path))) : String}
  %pick_h(String, Http.valid_encoded(Http.before_q(path)), Http.before_q(path), Http.escape_path(Http.unescape(Http.before_q(path))), Http.before_q(path), Http.escape_path(Http.unescape(Http.before_q(path))), {==}, {==})
    : {Http.request_uri(path) == _ ++ String.drop(path, String.length(Http.before_q(path))) : String}
  {==}

def port_h(+p: Maybe<&2, Nat>) -> {Http.port_text(p) == L.port_text(p) : String}:
  match p:
    case None{}:
      {==}
    case Some{+n}:
      {==}

def req_text(+a1: String, +a2: String, +a3: String, +a4: String, +a5: String, +a6: String, +a7: String, +a8: String) -> String:
  a1 ++ " " ++ a2 ++ " HTTP/1.1\r\n"
    ++ "Host: " ++ a3 ++ "\r\n"
    ++ "User-Agent: " ++ a4 ++ "\r\n"
    ++ a5 ++ a6 ++ a7 ++ "\r\n" ++ a8

def req_cong(+a1: String, +a2: String, +a3: String, +a4: String, +a5: String, +a6: String, +a7: String, +a8: String,
             +b2: String, +b3: String, +b4: String, +b5: String, +b6: String, +b7: String,
             e2: {a2 == b2 : String}, e3: {a3 == b3 : String}, e4: {a4 == b4 : String}, e5: {a5 == b5 : String}, e6: {a6 == b6 : String}, e7: {a7 == b7 : String})
  -> {req_text(a1, a2, a3, a4, a5, a6, a7, a8) == req_text(a1, b2, b3, b4, b5, b6, b7, a8) : String}:
  %e2 : {req_text(a1, a2, a3, a4, a5, a6, a7, a8) == req_text(a1, _, b3, b4, b5, b6, b7, a8) : String}
  %e3 : {req_text(a1, a2, a3, a4, a5, a6, a7, a8) == req_text(a1, a2, _, b4, b5, b6, b7, a8) : String}
  %e4 : {req_text(a1, a2, a3, a4, a5, a6, a7, a8) == req_text(a1, a2, a3, _, b5, b6, b7, a8) : String}
  %e5 : {req_text(a1, a2, a3, a4, a5, a6, a7, a8) == req_text(a1, a2, a3, a4, _, b6, b7, a8) : String}
  %e6 : {req_text(a1, a2, a3, a4, a5, a6, a7, a8) == req_text(a1, a2, a3, a4, a5, _, b7, a8) : String}
  %e7 : {req_text(a1, a2, a3, a4, a5, a6, a7, a8) == req_text(a1, a2, a3, a4, a5, a6, _, a8) : String}
  {==}

def host_h(+host: String, +port: Maybe<&2, Nat>, +hs: List<&2, Hdr.Header>)
  -> {Http.first_of(host ++ Http.port_text(port), Http.hdr_get("Host", hs)) == L.first_of(host ++ L.port_text(port), L.hdr_get("Host", hs)) : String}:
  %port_h(port) : {Http.first_of(host ++ Http.port_text(port), Http.hdr_get("Host", hs)) == L.first_of(host ++ _, L.hdr_get("Host", hs)) : String}
  %hdr_get_h("Host", hs) : {Http.first_of(host ++ Http.port_text(port), Http.hdr_get("Host", hs)) == L.first_of(host ++ Http.port_text(port), _) : String}
  first_of_h(host ++ Http.port_text(port), Http.hdr_get("Host", hs))

def ua_h(+hs: List<&2, Hdr.Header>)
  -> {Http.first_of("Go-http-client/1.1", Http.hdr_get("User-Agent", hs)) == L.first_of("Go-http-client/1.1", L.hdr_get("User-Agent", hs)) : String}:
  %hdr_get_h("User-Agent", hs) : {Http.first_of("Go-http-client/1.1", Http.hdr_get("User-Agent", hs)) == L.first_of("Go-http-client/1.1", _) : String}
  first_of_h("Go-http-client/1.1", Http.hdr_get("User-Agent", hs))

def named_h(+name: String, +hs: List<&2, Hdr.Header>)
  -> {Http.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, Http.set_hdr("X-Vegeta-Attack", name, hs))
      == L.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, L.set_hdr("X-Vegeta-Attack", name, hs)) : List<&2, Hdr.Header>}:
  pick_h(List<&2, Hdr.Header>, String.is_empty(name), hs, Http.set_hdr("X-Vegeta-Attack", name, hs), hs, L.set_hdr("X-Vegeta-Attack", name, hs), {==}, set_hdr_h("X-Vegeta-Attack", name, hs))

def rest_h(+seq: Nat, +name: String, +hs: List<&2, Hdr.Header>)
  -> {Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer",
        Http.set_hdr("X-Vegeta-Seq", Dec.show(seq), Http.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, Http.set_hdr("X-Vegeta-Attack", name, hs))))))))
      == L.drop_exact("Host", L.drop_exact("User-Agent", L.drop_exact("Content-Length", L.drop_exact("Transfer-Encoding", L.drop_exact("Trailer",
        L.set_hdr("X-Vegeta-Seq", Dec.show(seq), L.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, L.set_hdr("X-Vegeta-Attack", name, hs)))))))) : List<&2, Hdr.Header>}:
  +n0 = Http.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, Http.set_hdr("X-Vegeta-Attack", name, hs))
  +s0 = Http.set_hdr("X-Vegeta-Seq", Dec.show(seq), n0)
  %named_h(name, hs) : {Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0)))))
      == L.drop_exact("Host", L.drop_exact("User-Agent", L.drop_exact("Content-Length", L.drop_exact("Transfer-Encoding", L.drop_exact("Trailer", L.set_hdr("X-Vegeta-Seq", Dec.show(seq), _)))))) : List<&2, Hdr.Header>}
  %set_hdr_h("X-Vegeta-Seq", Dec.show(seq), n0) : {Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0)))))
      == L.drop_exact("Host", L.drop_exact("User-Agent", L.drop_exact("Content-Length", L.drop_exact("Transfer-Encoding", L.drop_exact("Trailer", _))))) : List<&2, Hdr.Header>}
  %drop_exact_h("Trailer", s0) : {Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0)))))
      == L.drop_exact("Host", L.drop_exact("User-Agent", L.drop_exact("Content-Length", L.drop_exact("Transfer-Encoding", _)))) : List<&2, Hdr.Header>}
  %drop_exact_h("Transfer-Encoding", Http.drop_exact("Trailer", s0)) : {Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0)))))
      == L.drop_exact("Host", L.drop_exact("User-Agent", L.drop_exact("Content-Length", _))) : List<&2, Hdr.Header>}
  %drop_exact_h("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0))) : {Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0)))))
      == L.drop_exact("Host", L.drop_exact("User-Agent", _)) : List<&2, Hdr.Header>}
  %drop_exact_h("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0)))) : {Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0)))))
      == L.drop_exact("Host", _) : List<&2, Hdr.Header>}
  drop_exact_h("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer", s0)))))

def text_h(+r: List<&2, Hdr.Header>, +q: List<&2, Hdr.Header>, e: {r == q : List<&2, Hdr.Header>})
  -> {Http.hdrs_text(Http.sort_hdrs(r)) == L.hdrs_text(L.sort_hdrs(q)) : String}:
  %e : {Http.hdrs_text(Http.sort_hdrs(r)) == L.hdrs_text(L.sort_hdrs(_)) : String}
  %sort_h(r) : {Http.hdrs_text(Http.sort_hdrs(r)) == L.hdrs_text(_) : String}
  hdrs_text_h(Http.sort_hdrs(r))

def L.http_request(t, u, body, seq, name, ka):
  match t:
    case Tgt.Target{+m, +tu, +hs, +tb}:
      match u:
        case Tgt.Url{+sc, +host, +port, +path}:
          req_cong(m, Http.request_uri(path), Http.first_of(host ++ Http.port_text(port), Http.hdr_get("Host", hs)),
            Http.first_of("Go-http-client/1.1", Http.hdr_get("User-Agent", hs)),
            Http.pick(String, L.needs_length(m, body), "Content-Length: " ++ Dec.show(String.length(body)) ++ "\r\n", ""),
            Http.hdrs_text(Http.sort_hdrs(Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer",
              Http.set_hdr("X-Vegeta-Seq", Dec.show(seq), Http.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, Http.set_hdr("X-Vegeta-Attack", name, hs)))))))))),
            Http.pick(String, ka, "", "Connection: close\r\n"), body,
            L.request_uri(path), L.first_of(host ++ L.port_text(port), L.hdr_get("Host", hs)),
            L.first_of("Go-http-client/1.1", L.hdr_get("User-Agent", hs)),
            L.pick(String, L.needs_length(m, body), "Content-Length: " ++ Dec.show(String.length(body)) ++ "\r\n", ""),
            L.hdrs_text(L.sort_hdrs(L.drop_exact("Host", L.drop_exact("User-Agent", L.drop_exact("Content-Length", L.drop_exact("Transfer-Encoding", L.drop_exact("Trailer",
              L.set_hdr("X-Vegeta-Seq", Dec.show(seq), L.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, L.set_hdr("X-Vegeta-Attack", name, hs)))))))))),
            L.pick(String, ka, "", "Connection: close\r\n"),
            request_uri_h(path), host_h(host, port, hs), ua_h(hs),
            pick_h(String, L.needs_length(m, body), "Content-Length: " ++ Dec.show(String.length(body)) ++ "\r\n", "", "Content-Length: " ++ Dec.show(String.length(body)) ++ "\r\n", "", {==}, {==}),
            text_h(Http.drop_exact("Host", Http.drop_exact("User-Agent", Http.drop_exact("Content-Length", Http.drop_exact("Transfer-Encoding", Http.drop_exact("Trailer",
              Http.set_hdr("X-Vegeta-Seq", Dec.show(seq), Http.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, Http.set_hdr("X-Vegeta-Attack", name, hs)))))))),
              L.drop_exact("Host", L.drop_exact("User-Agent", L.drop_exact("Content-Length", L.drop_exact("Transfer-Encoding", L.drop_exact("Trailer",
              L.set_hdr("X-Vegeta-Seq", Dec.show(seq), L.pick(List<&2, Hdr.Header>, String.is_empty(name), hs, L.set_hdr("X-Vegeta-Attack", name, hs)))))))),
              rest_h(seq, name, hs)),
            pick_h(String, ka, "", "Connection: close\r\n", "", "Connection: close\r\n", {==}, {==}))


# ---------------------------------------------------------------------
# String.eq decides equality
# ---------------------------------------------------------------------

def se_fin(t: Cmp, +x: U32, +y: U32, +t1: String, +t2: String, +e: {U32.cmp(x, y) == t : Cmp},
           h: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), t))) == True{} : Bool},
           ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String})
  -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}:
  match t:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, no_ft(h))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, no_ft(h))
    case EQ{}:
      %u32_eq(x, y, Equal.cong(Cmp, Bool, q => Cmp.is_eq(q), U32.cmp(x, y), EQ{}, e)) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t2} : String}
      %ih(Equal.trans(Bool, String.eq(t1, t2), String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), True{},
            Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), String.eq(t1, t2), eqfin_rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), h))
        : {SCon{Chr{x}, t1} == SCon{Chr{x}, _} : String}
      {==}

def str_eq2(c1: Char, c2: Char, +t1: String, +t2: String, h: {String.eq(SCon{c1, t1}, SCon{c2, t2}) == True{} : Bool},
            ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}) -> {SCon{c1, t1} == SCon{c2, t2} : String}:
  match c1:
    case Chr{+x}:
      match c2:
        case Chr{+y}:
          se_fin(U32.cmp(x, y), x, y, t1, t2, {==}, h, ih)

def str_eq(a: String, b: String, h: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{c, t}:
          Empty.absurd({SNil{} == SCon{c, t} : String}, no_ft(h))
    case SCon{c1, +t1}:
      match b:
        case SNil{}:
          Empty.absurd({SCon{c1, t1} == SNil{} : String}, no_ft(h))
        case SCon{c2, +t2}:
          str_eq2(c1, c2, t1, t2, h, hh => str_eq(t1, t2, hh))

# ---------------------------------------------------------------------
# Header lines
# ---------------------------------------------------------------------

# no byte is '\n'
def nlf(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.not(U32.is_eq(L.code(c), 10)), nlf(rest))

def not_f(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, no_tf(e))

def nsym(+k: U32, +lit: U32, -f: U32 -> Bool, +hk: {f(k) == True{} : Bool}, hl: {f(lit) == False{} : Bool}) -> {False{} == U32.is_eq(k, lit) : Bool}:
  Equal.sym(Bool, U32.is_eq(k, lit), False{}, neq(U32.is_eq(k, lit), k, lit, f, {==}, hk, hl))

def nlf_app(a: String, +b: String, +ha: {nlf(a) == True{} : Bool}, +hb: {nlf(b) == True{} : Bool}) -> {nlf(a ++ b) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+c, +rest}:
      and_i(Bool.not(U32.is_eq(L.code(c), 10)), nlf(rest ++ b), and_l(Bool.not(U32.is_eq(L.code(c), 10)), nlf(rest), ha),
        nlf_app(rest, b, and_r(Bool.not(U32.is_eq(L.code(c), 10)), nlf(rest), ha), hb))

def nlf_tok(s: String, +h: {L.all_token(s) == True{} : Bool}) -> {nlf(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          and_i(Bool.not(U32.is_eq(k, 10)), nlf(rest),
            not_f(U32.is_eq(k, 10), Equal.sym(Bool, False{}, U32.is_eq(k, 10), nsym(k, 10, x => L.token_byte(x), and_l(L.token_byte(k), L.all_token(rest), h), {==}))),
            nlf_tok(rest, and_r(L.token_byte(k), L.all_token(rest), h)))

def ctl_f(+x: U32) -> Bool:
  Bool.or(U32.is_eq(x, 9), Bool.and(U32.is_ge(x, 32), Bool.not(U32.is_eq(x, 127))))

def nlf_ctl(s: String, +h: {L.no_ctl(s) == True{} : Bool}) -> {nlf(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          and_i(Bool.not(U32.is_eq(k, 10)), nlf(rest),
            not_f(U32.is_eq(k, 10), Equal.sym(Bool, False{}, U32.is_eq(k, 10), nsym(k, 10, x => ctl_f(x), and_l(ctl_f(k), L.no_ctl(rest), h), {==}))),
            nlf_ctl(rest, and_r(ctl_f(k), L.no_ctl(rest), h)))

def not_t2(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {False{} == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))

def hdr_acc(s: String, +c: Nat, +st: String, +mi: Nat, +a: List<&2, Hdr.Header>, +pd: Maybe<&2, String>, +cur: String,
            +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool, +h: {nlf(s) == True{} : Bool})
  -> {Http.feed.go(s, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, cur}}) == Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, String.reverse.go(s, cur)}} : Http.Parse}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +rest}:
      match x:
        case Chr{+k}:
          %not_t2(U32.is_eq(k, 10), and_l(Bool.not(U32.is_eq(k, 10)), nlf(rest), h))
            : {Http.feed.go(rest, Http.Parse{mb, hd, cl, Http.hdr_byte(_, c, st, mi, a, pd, cur, Chr{k}, mb, hd)}) == Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, String.reverse.go(rest, SCon{Chr{k}, cur})}} : Http.Parse}
          hdr_acc(rest, c, st, mi, a, pd, SCon{Chr{k}, cur}, mb, hd, cl, and_r(Bool.not(U32.is_eq(k, 10)), nlf(rest), h))

# the CRLF ending a header line
def hdr_eol(+l1: String, +w: String, +c: Nat, +st: String, +mi: Nat, +a: List<&2, Hdr.Header>, +pd: Maybe<&2, String>,
            +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool)
  -> {Http.feed.go("\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, String.reverse.go(l1, "")}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.hdr_line(String.is_empty(l1), c, st, mi, a, pd, l1, mb, hd)}) : Http.Parse}:
  %Equal.sym(String, String.reverse.go(String.reverse.go(l1, ""), ""), String.reverse.go("", l1 ++ ""), rr(l1, "", ""))
    : {Http.feed.go(w, Http.Parse{mb, hd, cl, Http.hdr_line(String.is_empty(_), c, st, mi, a, pd, _, mb, hd)}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.hdr_line(String.is_empty(l1), c, st, mi, a, pd, l1, mb, hd)}) : Http.Parse}
  %app_nil(l1)
    : {Http.feed.go(w, Http.Parse{mb, hd, cl, Http.hdr_line(String.is_empty(l1 ++ ""), c, st, mi, a, pd, l1 ++ "", mb, hd)}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.hdr_line(String.is_empty(_), c, st, mi, a, pd, _, mb, hd)}) : Http.Parse}
  {==}

def hb_colon(b: Bool, +x: U32, +t: String, +ih: {Http.has_byte(t, 58) == True{} : Bool}) -> {Http.has_byte.go(SCon{Chr{x}, t}, 58, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def hc_colon(k: String, +v: String) -> {Http.has_byte(k ++ (": " ++ v), 58) == True{} : Bool}:
  match k:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          hb_colon(U32.is_eq(x, 58), x, rest ++ (": " ++ v), hc_colon(rest, v))

def line_ph(+k0: U32, +r: String, +c: Nat, +st: String, +mi: Nat, +a: List<&2, Hdr.Header>, +pd: Maybe<&2, String>, +t: List<&2, Hdr.Header>,
            +mb: Maybe<&2, Nat>, +hd: Bool,
            +hk: {L.token_byte(k0) == True{} : Bool}, +hcol: {Http.has_byte(SCon{Chr{k0}, r}, 58) == True{} : Bool},
            +hs: {Http.store_pend(pd, a) == Done{t} : Result<&2, &2, String, List<&2, Hdr.Header>>})
  -> {Http.hdr_line(False{}, c, st, mi, a, pd, SCon{Chr{k0}, r}, mb, hd) == Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, r})}, ""} : Http.Ph}:
  %nsym(k0, 32, x => L.token_byte(x), hk, {==})
    : {Http.hdr_cont(Bool.or(_, U32.is_eq(k0, 9)), c, st, mi, a, pd, SCon{Chr{k0}, r}) == Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, r})}, ""} : Http.Ph}
  %nsym(k0, 9, x => L.token_byte(x), hk, {==})
    : {Http.hdr_cont(Bool.or(False{}, _), c, st, mi, a, pd, SCon{Chr{k0}, r}) == Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, r})}, ""} : Http.Ph}
  %Equal.sym(Bool, Http.has_byte(SCon{Chr{k0}, r}, 58), True{}, hcol)
    : {Http.hdr_new(_, c, st, mi, a, pd, SCon{Chr{k0}, r}) == Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, r})}, ""} : Http.Ph}
  %Equal.sym(Result<&2, &2, String, List<&2, Hdr.Header>>, Http.store_pend(pd, a), Done{t}, hs)
    : {Http.hdr_next(_, c, st, mi, SCon{Chr{k0}, r}) == Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, r})}, ""} : Http.Ph}
  {==}

# one header line "k: v" read: the line before it is stored, this one pends
def line_feed(+k0: U32, +kr: String, +v: String, +w: String, +c: Nat, +st: String, +mi: Nat, +a: List<&2, Hdr.Header>, +pd: Maybe<&2, String>,
              +t: List<&2, Hdr.Header>, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
              +hk: {L.all_token(SCon{Chr{k0}, kr}) == True{} : Bool}, +hv: {L.no_ctl(v) == True{} : Bool},
              +hs: {Http.store_pend(pd, a) == Done{t} : Result<&2, &2, String, List<&2, Hdr.Header>>})
  -> {Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ (v ++ ("\r\n" ++ w))), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, ""}}) : Http.Parse}:
  Equal.trans(Http.Parse,
    Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ (v ++ ("\r\n" ++ w))), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}),
    Http.feed.go("\r\n" ++ w, Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ v), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}})),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, ""}}),
    Equal.trans(Http.Parse,
      Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ (v ++ ("\r\n" ++ w))), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}),
      Http.feed.go((SCon{Chr{k0}, kr} ++ (": " ++ v)) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}),
      Http.feed.go("\r\n" ++ w, Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ v), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}})),
      Equal.cong(String, Http.Parse, x => Http.feed.go(x, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}),
        SCon{Chr{k0}, kr} ++ (": " ++ (v ++ ("\r\n" ++ w))), (SCon{Chr{k0}, kr} ++ (": " ++ v)) ++ ("\r\n" ++ w),
        Equal.sym(String, (SCon{Chr{k0}, kr} ++ (": " ++ v)) ++ ("\r\n" ++ w), SCon{Chr{k0}, kr} ++ (": " ++ (v ++ ("\r\n" ++ w))), app_assoc(SCon{Chr{k0}, kr}, ": " ++ v, "\r\n" ++ w))),
      Equal.sym(Http.Parse, Http.feed.go("\r\n" ++ w, Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ v), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}})),
        Http.feed.go((SCon{Chr{k0}, kr} ++ (": " ++ v)) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}),
        split_go(SCon{Chr{k0}, kr} ++ (": " ++ v), "\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}))),
    Equal.trans(Http.Parse,
      Http.feed.go("\r\n" ++ w, Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ v), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}})),
      Http.feed.go("\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, String.reverse.go(SCon{Chr{k0}, kr} ++ (": " ++ v), "")}}),
      Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, ""}}),
      Equal.cong(Http.Parse, Http.Parse, p => Http.feed.go("\r\n" ++ w, p),
        Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ v), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}),
        Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, String.reverse.go(SCon{Chr{k0}, kr} ++ (": " ++ v), "")}},
        hdr_acc(SCon{Chr{k0}, kr} ++ (": " ++ v), c, st, mi, a, pd, "", mb, hd, cl, nlf_app(SCon{Chr{k0}, kr}, ": " ++ v, nlf_tok(SCon{Chr{k0}, kr}, hk), nlf_ctl(v, hv)))),
      Equal.trans(Http.Parse,
        Http.feed.go("\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, String.reverse.go(SCon{Chr{k0}, kr} ++ (": " ++ v), "")}}),
        Http.feed.go(w, Http.Parse{mb, hd, cl, Http.hdr_line(False{}, c, st, mi, a, pd, SCon{Chr{k0}, kr} ++ (": " ++ v), mb, hd)}),
        Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, ""}}),
        hdr_eol(SCon{Chr{k0}, kr} ++ (": " ++ v), w, c, st, mi, a, pd, mb, hd, cl),
        Equal.cong(Http.Ph, Http.Parse, ph => Http.feed.go(w, Http.Parse{mb, hd, cl, ph}),
          Http.hdr_line(False{}, c, st, mi, a, pd, SCon{Chr{k0}, kr} ++ (": " ++ v), mb, hd),
          Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, ""},
          line_ph(k0, kr ++ (": " ++ v), c, st, mi, a, pd, t, mb, hd, and_l(L.token_byte(k0), L.all_token(kr), hk), hc_colon(SCon{Chr{k0}, kr}, v), hs)))))

# ---------------------------------------------------------------------
# Storing a header line
# ---------------------------------------------------------------------

def before_nc(k: String, +z: String, +h: {L.all_token(k) == True{} : Bool}) -> {Http.before(k ++ z, 58) == k ++ Http.before(z, 58) : String}:
  match k:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %nsym(x, 58, y => L.token_byte(y), and_l(L.token_byte(x), L.all_token(rest), h), {==})
            : {Http.before.go(SCon{Chr{x}, rest ++ z}, 58, _) == SCon{Chr{x}, rest ++ Http.before(z, 58)} : String}
          %before_nc(rest, z, and_r(L.token_byte(x), L.all_token(rest), h))
            : {SCon{Chr{x}, Http.before(rest ++ z, 58)} == SCon{Chr{x}, _} : String}
          {==}

def after_nc(k: String, +z: String, +h: {L.all_token(k) == True{} : Bool}) -> {Http.after(k ++ z, 58) == Http.after(z, 58) : String}:
  match k:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %nsym(x, 58, y => L.token_byte(y), and_l(L.token_byte(x), L.all_token(rest), h), {==})
            : {Http.after.go(SCon{Chr{x}, rest ++ z}, 58, _) == Http.after(z, 58) : String}
          after_nc(rest, z, and_r(L.token_byte(x), L.all_token(rest), h))

def name_tok(k: String, +h: {L.all_token(k) == True{} : Bool}) -> {Http.all_name(k) == True{} : Bool}:
  match k:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %Equal.sym(Bool, Http.token_byte(x), True{}, Equal.trans(Bool, Http.token_byte(x), L.token_byte(x), True{}, tb_eq(x), and_l(L.token_byte(x), L.all_token(rest), h)))
            : {Bool.and(Bool.or(_, U32.is_eq(x, 32)), Http.all_name(rest)) == True{} : Bool}
          name_tok(rest, and_r(L.token_byte(x), L.all_token(rest), h))

def sp_tok(k: String, +h: {L.all_token(k) == True{} : Bool}) -> {Http.has_byte(k, 32) == False{} : Bool}:
  match k:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %nsym(x, 32, y => L.token_byte(y), and_l(L.token_byte(x), L.all_token(rest), h), {==})
            : {Http.has_byte.go(SCon{Chr{x}, rest}, 32, _) == False{} : Bool}
          sp_tok(rest, and_r(L.token_byte(x), L.all_token(rest), h))

def av_h(v: String) -> {Http.all_value(v) == L.no_ctl(v) : Bool}:
  match v:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %av_h(rest) : {Http.all_value(SCon{Chr{x}, rest}) == Bool.and(ctl_f(x), _) : Bool}
          {==}

# a line k ++ z whose name is the token k stores k's value
def store_k(+k0: U32, +kr: String, +z: String, +t: List<&2, Hdr.Header>,
            +hk: {L.all_token(SCon{Chr{k0}, kr}) == True{} : Bool}, +hz: {Http.before(z, 58) == "" : String},
            +hav: {Http.all_value(Http.after(z, 58)) == True{} : Bool})
  -> {Http.store(SCon{Chr{k0}, kr} ++ z, t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), Http.trim_ows(Http.after(z, 58)), t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}:
  %Equal.sym(String, Http.before(SCon{Chr{k0}, kr} ++ z, 58), SCon{Chr{k0}, kr},
     Equal.trans(String, Http.before(SCon{Chr{k0}, kr} ++ z, 58), SCon{Chr{k0}, kr} ++ Http.before(z, 58), SCon{Chr{k0}, kr},
       before_nc(SCon{Chr{k0}, kr}, z, hk),
       Equal.trans(String, SCon{Chr{k0}, kr} ++ Http.before(z, 58), SCon{Chr{k0}, kr} ++ "", SCon{Chr{k0}, kr},
         Equal.cong(String, String, y => SCon{Chr{k0}, kr} ++ y, Http.before(z, 58), "", hz), app_nil(SCon{Chr{k0}, kr}))))
    : {Http.store_of(Bool.and(Bool.and(Bool.not(String.is_empty(_)), Http.all_name(_)), Http.all_value(Http.after(SCon{Chr{k0}, kr} ++ z, 58))), _, Http.after(SCon{Chr{k0}, kr} ++ z, 58), SCon{Chr{k0}, kr} ++ z, t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), Http.trim_ows(Http.after(z, 58)), t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}
  %Equal.sym(String, Http.after(SCon{Chr{k0}, kr} ++ z, 58), Http.after(z, 58), after_nc(SCon{Chr{k0}, kr}, z, hk))
    : {Http.store_of(Bool.and(Bool.and(True{}, Http.all_name(SCon{Chr{k0}, kr})), Http.all_value(_)), SCon{Chr{k0}, kr}, _, SCon{Chr{k0}, kr} ++ z, t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), Http.trim_ows(Http.after(z, 58)), t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}
  %Equal.sym(Bool, Http.all_name(SCon{Chr{k0}, kr}), True{}, name_tok(SCon{Chr{k0}, kr}, hk))
    : {Http.store_of(Bool.and(_, Http.all_value(Http.after(z, 58))), SCon{Chr{k0}, kr}, Http.after(z, 58), SCon{Chr{k0}, kr} ++ z, t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), Http.trim_ows(Http.after(z, 58)), t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}
  %Equal.sym(Bool, Http.all_value(Http.after(z, 58)), True{}, hav)
    : {Http.store_of(_, SCon{Chr{k0}, kr}, Http.after(z, 58), SCon{Chr{k0}, kr} ++ z, t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), Http.trim_ows(Http.after(z, 58)), t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}
  %Equal.sym(Bool, Http.has_byte(SCon{Chr{k0}, kr}, 32), False{}, sp_tok(SCon{Chr{k0}, kr}, hk))
    : {Done{Http.hdr_add(Http.pick(String, _, SCon{Chr{k0}, kr}, Http.canon(SCon{Chr{k0}, kr})), Http.trim_ows(Http.after(z, 58)), t)} == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), Http.trim_ows(Http.after(z, 58)), t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}
  {==}

def tl_tok(+k0: U32, +z: String, +hk: {L.token_byte(k0) == True{} : Bool}) -> {Http.trim_ows_l(SCon{Chr{k0}, z}) == SCon{Chr{k0}, z} : String}:
  %nsym(k0, 32, y => L.token_byte(y), hk, {==}) : {Http.trim_ows_l.go(SCon{Chr{k0}, z}, Bool.or(_, U32.is_eq(k0, 9))) == SCon{Chr{k0}, z} : String}
  %nsym(k0, 9, y => L.token_byte(y), hk, {==}) : {Http.trim_ows_l.go(SCon{Chr{k0}, z}, Bool.or(False{}, _)) == SCon{Chr{k0}, z} : String}
  {==}

# a clean value has no blanks at its right end
def rtrim_clean0(+v: String, +ht: {rtrim(Http.trim_ows_l(v)) == v : String}) -> {rtrim(v) == v : String}:
  Equal.trans(String, rtrim(v), rtrim(rtrim(Http.trim_ows_l(v))), v,
    Equal.cong(String, String, x => rtrim(x), v, rtrim(Http.trim_ows_l(v)), Equal.sym(String, rtrim(Http.trim_ows_l(v)), v, ht)),
    Equal.trans(String, rtrim(rtrim(Http.trim_ows_l(v))), rtrim(Http.trim_ows_l(v)), v, rtrim_idem(Http.trim_ows_l(v)), ht))

def rtrim_clean(+v: String, +ht0: {Http.trim_ows(v) == v : String}) -> {rtrim(v) == v : String}:
  rtrim_clean0(v, Equal.trans(String, rtrim(Http.trim_ows_l(v)), Http.trim_ows(v), v, Equal.sym(String, Http.trim_ows(v), rtrim(Http.trim_ows_l(v)), tr_eq(v)), ht0))

def pline_nil(+k0: U32, +kr: String, +hk: {L.token_byte(k0) == True{} : Bool})
  -> {Http.trim_ows(SCon{Chr{k0}, kr} ++ ": ") == SCon{Chr{k0}, kr} ++ ":" : String}:
  Equal.trans(String, Http.trim_ows(SCon{Chr{k0}, kr} ++ ": "), rtrim(SCon{Chr{k0}, kr} ++ ": "), SCon{Chr{k0}, kr} ++ ":",
    Equal.trans(String, Http.trim_ows(SCon{Chr{k0}, kr ++ ": "}), rtrim(Http.trim_ows_l(SCon{Chr{k0}, kr ++ ": "})), rtrim(SCon{Chr{k0}, kr ++ ": "}), tr_eq(SCon{Chr{k0}, kr ++ ": "}),
      Equal.cong(String, String, x => rtrim(x), Http.trim_ows_l(SCon{Chr{k0}, kr ++ ": "}), SCon{Chr{k0}, kr ++ ": "}, tl_tok(k0, kr ++ ": ", hk))),
    rtrim_app(SCon{Chr{k0}, kr}, ": ", {==}))

def pline_con(+k0: U32, +kr: String, +c1: Char, +vr: String, +hk: {L.token_byte(k0) == True{} : Bool}, +ht: {Http.trim_ows(SCon{c1, vr}) == SCon{c1, vr} : String})
  -> {Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr})) == SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr}) : String}:
  Equal.trans(String, Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr})), rtrim((SCon{Chr{k0}, kr} ++ ": ") ++ SCon{c1, vr}), SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr}),
    Equal.trans(String, Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr})), rtrim(SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr})), rtrim((SCon{Chr{k0}, kr} ++ ": ") ++ SCon{c1, vr}),
      Equal.trans(String, Http.trim_ows(SCon{Chr{k0}, kr ++ (": " ++ SCon{c1, vr})}), rtrim(Http.trim_ows_l(SCon{Chr{k0}, kr ++ (": " ++ SCon{c1, vr})})), rtrim(SCon{Chr{k0}, kr ++ (": " ++ SCon{c1, vr})}), tr_eq(SCon{Chr{k0}, kr ++ (": " ++ SCon{c1, vr})}),
        Equal.cong(String, String, x => rtrim(x), Http.trim_ows_l(SCon{Chr{k0}, kr ++ (": " ++ SCon{c1, vr})}), SCon{Chr{k0}, kr ++ (": " ++ SCon{c1, vr})}, tl_tok(k0, kr ++ (": " ++ SCon{c1, vr}), hk))),
      Equal.cong(String, String, x => rtrim(x), SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr}), (SCon{Chr{k0}, kr} ++ ": ") ++ SCon{c1, vr},
        Equal.sym(String, (SCon{Chr{k0}, kr} ++ ": ") ++ SCon{c1, vr}, SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr}), app_assoc(SCon{Chr{k0}, kr}, ": ", SCon{c1, vr})))),
    Equal.trans(String, rtrim((SCon{Chr{k0}, kr} ++ ": ") ++ SCon{c1, vr}), (SCon{Chr{k0}, kr} ++ ": ") ++ rtrim(SCon{c1, vr}), SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr}),
      rtrim_app(SCon{Chr{k0}, kr} ++ ": ", SCon{c1, vr},
        Equal.cong(String, Bool, x => String.is_empty(x), rtrim(SCon{c1, vr}), SCon{c1, vr}, rtrim_clean(SCon{c1, vr}, ht))),
      Equal.trans(String, (SCon{Chr{k0}, kr} ++ ": ") ++ rtrim(SCon{c1, vr}), (SCon{Chr{k0}, kr} ++ ": ") ++ SCon{c1, vr}, SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr}),
        Equal.cong(String, String, x => (SCon{Chr{k0}, kr} ++ ": ") ++ x, rtrim(SCon{c1, vr}), SCon{c1, vr}, rtrim_clean(SCon{c1, vr}, ht)),
        app_assoc(SCon{Chr{k0}, kr}, ": ", SCon{c1, vr}))))

# the pending line of a header k: v stores k's canonical name and v
def store_ok(+k0: U32, +kr: String, v: String, +t: List<&2, Hdr.Header>,
             +hk: {L.all_token(SCon{Chr{k0}, kr}) == True{} : Bool}, +hv: {L.no_ctl(v) == True{} : Bool}, +ht: {Http.trim_ows(v) == v : String})
  -> {Http.store_pend(Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), v, t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}:
  match v:
    case SNil{}:
      %Equal.sym(String, Http.trim_ows(SCon{Chr{k0}, kr} ++ ": "), SCon{Chr{k0}, kr} ++ ":", pline_nil(k0, kr, and_l(L.token_byte(k0), L.all_token(kr), hk)))
        : {Http.store(_, t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), "", t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}
      store_k(k0, kr, ":", t, hk, {==}, {==})
    case SCon{+c1, +vr}:
      %Equal.sym(String, Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr})), SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr}), pline_con(k0, kr, c1, vr, and_l(L.token_byte(k0), L.all_token(kr), hk), ht))
        : {Http.store(_, t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), SCon{c1, vr}, t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}
      %ht : {Http.store(SCon{Chr{k0}, kr} ++ (": " ++ SCon{c1, vr}), t) == Done{Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), _, t)} : Result<&2, &2, String, List<&2, Hdr.Header>>}
      store_k(k0, kr, ": " ++ SCon{c1, vr}, t, hk, {==}, Equal.trans(Bool, Http.all_value(SCon{c1, vr}), L.no_ctl(SCon{c1, vr}), True{}, av_h(SCon{c1, vr}), hv))

# ---------------------------------------------------------------------
# A run of header lines, then the blank line
# ---------------------------------------------------------------------

type KV is Data:
  KV{k: String, v: String}

def plines(ps: List<&2, KV>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case KV{k, v}:
          k ++ (": " ++ (v ++ ("\r\n" ++ plines(rest))))

def addall(ps: List<&2, KV>, t: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match ps:
    case Nil{}:
      t
    case Con{kv, rest}:
      match kv:
        case KV{k, v}:
          addall(rest, Http.hdr_add(Http.canon(k), v, t))

def pok(ps: List<&2, KV>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{kv, rest}:
      match kv:
        case KV{+k, +v}:
          Bool.and(Bool.and(L.token(k), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(rest)))

def flat_nil(+w: String, +c: Nat, +st: String, +mi: Nat, +a: List<&2, Hdr.Header>, +pd: Maybe<&2, String>, +t: List<&2, Hdr.Header>,
             +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool, +hs: {Http.store_pend(pd, a) == Done{t} : Result<&2, &2, String, List<&2, Hdr.Header>>})
  -> {Http.feed.go("\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, t, hd)}) : Http.Parse}:
  %Equal.sym(Result<&2, &2, String, List<&2, Hdr.Header>>, Http.store_pend(pd, a), Done{t}, hs)
    : {Http.feed.go(w, Http.Parse{mb, hd, cl, Http.hdr_end(_, c, st, mi, mb, hd)}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, t, hd)}) : Http.Parse}
  {==}

def flat_con(+k0: U32, +kr: String, +v: String, +r: List<&2, KV>, +w: String, +c: Nat, +st: String, +mi: Nat,
             +a: List<&2, Hdr.Header>, +pd: Maybe<&2, String>, +t: List<&2, Hdr.Header>, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
             +hs: {Http.store_pend(pd, a) == Done{t} : Result<&2, &2, String, List<&2, Hdr.Header>>},
             +hp: {Bool.and(Bool.and(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r))) == True{} : Bool},
             ih: {Http.feed.go(plines(r) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, ""}})
                  == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(r, Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), v, t)), hd)}) : Http.Parse})
  -> {Http.feed.go(plines(Con{KV{SCon{Chr{k0}, kr}, v}, r}) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(Con{KV{SCon{Chr{k0}, kr}, v}, r}, t), hd)}) : Http.Parse}:
  %Equal.sym(String, (SCon{Chr{k0}, kr} ++ (": " ++ (v ++ ("\r\n" ++ plines(r))))) ++ ("\r\n" ++ w), SCon{Chr{k0}, kr} ++ ((": " ++ (v ++ ("\r\n" ++ plines(r)))) ++ ("\r\n" ++ w)), app_assoc(SCon{Chr{k0}, kr}, ": " ++ (v ++ ("\r\n" ++ plines(r))), "\r\n" ++ w))
    : {Http.feed.go(_, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(r, Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), v, t)), hd)}) : Http.Parse}
  %Equal.sym(String, (v ++ ("\r\n" ++ plines(r))) ++ ("\r\n" ++ w), v ++ (("\r\n" ++ plines(r)) ++ ("\r\n" ++ w)), app_assoc(v, "\r\n" ++ plines(r), "\r\n" ++ w))
    : {Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ _), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(r, Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), v, t)), hd)}) : Http.Parse}
  Equal.trans(Http.Parse,
    Http.feed.go(SCon{Chr{k0}, kr} ++ (": " ++ (v ++ ("\r\n" ++ (plines(r) ++ ("\r\n" ++ w))))), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}),
    Http.feed.go(plines(r) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, ""}}),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(r, Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), v, t)), hd)}),
    line_feed(k0, kr, v, plines(r) ++ ("\r\n" ++ w), c, st, mi, a, pd, t, mb, hd, cl,
      and_r(Bool.not(String.is_empty(SCon{Chr{k0}, kr})), L.all_token(SCon{Chr{k0}, kr}), and_l(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v), and_l(Bool.and(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), hp))),
      and_r(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v), and_l(Bool.and(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), hp)),
      hs),
    ih)

def flat(ps: List<&2, KV>, +w: String, +c: Nat, +st: String, +mi: Nat, +a: List<&2, Hdr.Header>, +pd: Maybe<&2, String>, +t: List<&2, Hdr.Header>,
         +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
         +hs: {Http.store_pend(pd, a) == Done{t} : Result<&2, &2, String, List<&2, Hdr.Header>>}, +hp: {pok(ps) == True{} : Bool})
  -> {Http.feed.go(plines(ps) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(ps, t), hd)}) : Http.Parse}:
  match ps:
    case Nil{}:
      flat_nil(w, c, st, mi, a, pd, t, mb, hd, cl, hs)
    case Con{kv, +r}:
      match kv:
        case KV{k, +v}:
          match k:
            case SNil{}:
              Empty.absurd({Http.feed.go(plines(Con{KV{SNil{}, v}, r}) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, a, pd, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(Con{KV{SNil{}, v}, r}, t), hd)}) : Http.Parse},
                no_ft(hp))
            case SCon{k1, +kr}:
              match k1:
                case Chr{+k0}:
                  flat_con(k0, kr, v, r, w, c, st, mi, a, pd, t, mb, hd, cl, hs, hp,
                    flat(r, w, c, st, mi, t, Some{Http.trim_ows(SCon{Chr{k0}, kr} ++ (": " ++ v))}, Http.hdr_add(Http.canon(SCon{Chr{k0}, kr}), v, t), mb, hd, cl,
                      store_ok(k0, kr, v, t,
                        and_r(Bool.not(String.is_empty(SCon{Chr{k0}, kr})), L.all_token(SCon{Chr{k0}, kr}), and_l(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v), and_l(Bool.and(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), hp))),
                        and_r(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v), and_l(Bool.and(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), hp)),
                        str_eq(Http.trim_ows(v), v, and_l(String.eq(Http.trim_ows(v), v), pok(r), and_r(Bool.and(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), hp)))),
                      and_r(String.eq(Http.trim_ows(v), v), pok(r), and_r(Bool.and(L.token(SCon{Chr{k0}, kr}), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), hp))))

# ---------------------------------------------------------------------
# A response's header text as KV lines
# ---------------------------------------------------------------------

def kvs(+k: String, vs: List<&2, String>, tail: List<&2, KV>) -> List<&2, KV>:
  match vs:
    case Nil{}:
      tail
    case Con{+v, +rest}:
      Con{KV{k, v}, kvs(k, rest, tail)}

def fl(hs: List<&2, Hdr.Header>) -> List<&2, KV>:
  match hs:
    case Nil{}:
      []
    case Con{+h, +rest}:
      kvs(L.hdr_key(h), L.hdr_vals(h), fl(rest))

def nl_id(s: String, +h: {L.no_ctl(s) == True{} : Bool}) -> {L.nl_to_space(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %nsym(k, 10, x => ctl_f(x), and_l(ctl_f(k), L.no_ctl(rest), h), {==})
            : {L.pick(String, Bool.or(_, U32.is_eq(k, 13)), " ", SCon{Chr{k}, SNil{}}) ++ L.nl_to_space(rest) == SCon{Chr{k}, rest} : String}
          %nsym(k, 13, x => ctl_f(x), and_l(ctl_f(k), L.no_ctl(rest), h), {==})
            : {L.pick(String, Bool.or(False{}, _), " ", SCon{Chr{k}, SNil{}}) ++ L.nl_to_space(rest) == SCon{Chr{k}, rest} : String}
          %nl_id(rest, and_r(ctl_f(k), L.no_ctl(rest), h)) : {SCon{Chr{k}, L.nl_to_space(rest)} == SCon{Chr{k}, _} : String}
          {==}

# a clean value is written as it is
def val_txt(+v: String, +h: {L.clean_val(v) == True{} : Bool}) -> {L.trim_ows(L.nl_to_space(v)) == v : String}:
  %Equal.sym(String, L.nl_to_space(v), v, nl_id(v, and_l(L.no_ctl(v), String.eq(L.trim_ows(v), v), and_r(L.bytes(v), Bool.and(L.no_ctl(v), String.eq(L.trim_ows(v), v)), h))))
    : {L.trim_ows(_) == v : String}
  str_eq(L.trim_ows(v), v, and_r(L.no_ctl(v), String.eq(L.trim_ows(v), v), and_r(L.bytes(v), Bool.and(L.no_ctl(v), String.eq(L.trim_ows(v), v)), h)))

def txt_vals(+k: String, vs: List<&2, String>, +tail: List<&2, KV>, +h: {L.all_clean(vs) == True{} : Bool})
  -> {L.hdr_lines(k, vs) ++ plines(tail) == plines(kvs(k, vs, tail)) : String}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      %Equal.sym(String, (k ++ (": " ++ (L.trim_ows(L.nl_to_space(v)) ++ ("\r\n" ++ L.hdr_lines(k, rest))))) ++ plines(tail),
          k ++ ((": " ++ (L.trim_ows(L.nl_to_space(v)) ++ ("\r\n" ++ L.hdr_lines(k, rest)))) ++ plines(tail)),
          app_assoc(k, ": " ++ (L.trim_ows(L.nl_to_space(v)) ++ ("\r\n" ++ L.hdr_lines(k, rest))), plines(tail)))
        : {_ == plines(kvs(k, Con{v, rest}, tail)) : String}
      %Equal.sym(String, (L.trim_ows(L.nl_to_space(v)) ++ ("\r\n" ++ L.hdr_lines(k, rest))) ++ plines(tail),
          L.trim_ows(L.nl_to_space(v)) ++ (("\r\n" ++ L.hdr_lines(k, rest)) ++ plines(tail)),
          app_assoc(L.trim_ows(L.nl_to_space(v)), "\r\n" ++ L.hdr_lines(k, rest), plines(tail)))
        : {k ++ (": " ++ _) == plines(kvs(k, Con{v, rest}, tail)) : String}
      %Equal.sym(String, L.trim_ows(L.nl_to_space(v)), v, val_txt(v, and_l(L.clean_val(v), L.all_clean(rest), h)))
        : {k ++ (": " ++ (_ ++ ("\r\n" ++ (L.hdr_lines(k, rest) ++ plines(tail))))) == plines(kvs(k, Con{v, rest}, tail)) : String}
      %Equal.sym(String, L.hdr_lines(k, rest) ++ plines(tail), plines(kvs(k, rest, tail)), txt_vals(k, rest, tail, and_r(L.clean_val(v), L.all_clean(rest), h)))
        : {k ++ (": " ++ (v ++ ("\r\n" ++ _))) == plines(kvs(k, Con{v, rest}, tail)) : String}
      {==}

def clean_of(+h: Hdr.Header, +rest: List<&2, Hdr.Header>, +e: {L.hdrs_resp_ok(Con{h, rest}) == True{} : Bool}) -> {L.all_clean(L.hdr_vals(h)) == True{} : Bool}:
  and_l(L.all_clean(L.hdr_vals(h)), L.hdrs_resp_ok(rest), and_r(Bool.and(Bool.not(L.has_key(L.hdr_key(h), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(h)))), Bool.and(L.all_clean(L.hdr_vals(h)), L.hdrs_resp_ok(rest)),
    and_r(Bool.and(L.token(L.hdr_key(h)), String.eq(L.canon(L.hdr_key(h)), L.hdr_key(h))), Bool.and(Bool.and(Bool.not(L.has_key(L.hdr_key(h), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(h)))), Bool.and(L.all_clean(L.hdr_vals(h)), L.hdrs_resp_ok(rest))), e)))

def rest_of(+h: Hdr.Header, +rest: List<&2, Hdr.Header>, +e: {L.hdrs_resp_ok(Con{h, rest}) == True{} : Bool}) -> {L.hdrs_resp_ok(rest) == True{} : Bool}:
  and_r(L.all_clean(L.hdr_vals(h)), L.hdrs_resp_ok(rest), and_r(Bool.and(Bool.not(L.has_key(L.hdr_key(h), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(h)))), Bool.and(L.all_clean(L.hdr_vals(h)), L.hdrs_resp_ok(rest)),
    and_r(Bool.and(L.token(L.hdr_key(h)), String.eq(L.canon(L.hdr_key(h)), L.hdr_key(h))), Bool.and(Bool.and(Bool.not(L.has_key(L.hdr_key(h), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(h)))), Bool.and(L.all_clean(L.hdr_vals(h)), L.hdrs_resp_ok(rest))), e)))

def txt(hs: List<&2, Hdr.Header>, +h: {L.hdrs_resp_ok(hs) == True{} : Bool}) -> {L.resp_hdr_lines(hs) == plines(fl(hs)) : String}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(String, L.resp_hdr_lines(rest), plines(fl(rest)), txt(rest, rest_of(x, rest, h)))
        : {L.hdr_lines(L.hdr_key(x), L.hdr_vals(x)) ++ _ == plines(fl(Con{x, rest})) : String}
      txt_vals(L.hdr_key(x), L.hdr_vals(x), fl(rest), clean_of(x, rest, h))

# ---------------------------------------------------------------------
# Equality of names, lists
# ---------------------------------------------------------------------

def bcmp_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          bcmp_refl(b)

def u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      word_refl(32n, w)

def str_refl(s: String) -> {String.eq(s, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_refl(x)) : {String.eq.fin(String.cmp.fin(t, t, ((Chr{x}, Chr{x}), _))) == True{} : Bool}
          Equal.trans(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{x}, String.cmp(t, t))), String.eq(t, t), True{}, eqfin_rec(Chr{x}, Chr{x}, String.cmp(t, t)), str_refl(t))

def eq_sym_f(b: Bool, +x: String, +y: String, +e: {String.eq(x, y) == b : Bool}, +f: {String.eq(y, x) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        no_tf(Equal.trans(Bool, True{}, String.eq(y, x), False{},
          Equal.trans(Bool, True{}, String.eq(y, y), String.eq(y, x), Equal.sym(Bool, String.eq(y, y), True{}, str_refl(y)),
            Equal.cong(String, Bool, z => String.eq(y, z), y, x, Equal.sym(String, x, y, str_eq(x, y, e)))), f)))

def eq_sym_of(b: Bool, +x: String, +y: String, +e: {String.eq(y, x) == b : Bool}) -> {String.eq(x, y) == b : Bool}:
  match b:
    case True{}:
      %str_eq(y, x, e) : {String.eq(_, y) == True{} : Bool}
      str_refl(y)
    case False{}:
      eq_sym_f(String.eq(x, y), x, y, {==}, e)

def lapp_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, []) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(List<&2, A>, List<&2, A>, t => Con{x, t}, List.append(&2, A, rest, []), rest, lapp_nil(A, rest))

def lapp_assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>)
  -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Equal.cong(List<&2, A>, List<&2, A>, t => Con{x, t}, List.append(&2, A, List.append(&2, A, rest, ys), zs), List.append(&2, A, rest, List.append(&2, A, ys, zs)), lapp_assoc(A, rest, ys, zs))

# ---------------------------------------------------------------------
# Grouping header values by name
# ---------------------------------------------------------------------

def add_new2(x: Hdr.Header, +t: List<&2, Hdr.Header>, +k: String, +v: String, +h: {L.has_key(k, Con{x, t}) == False{} : Bool},
             ih: {L.has_key(k, t) == False{} : Bool} -> {Http.hdr_add(k, v, t) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, [v]}]) : List<&2, Hdr.Header>})
  -> {Http.hdr_add(k, v, Con{x, t}) == List.append(&2, Hdr.Header, Con{x, t}, [Hdr.Header{k, [v]}]) : List<&2, Hdr.Header>}:
  match x:
    case Hdr.Header{+kx, +vx}:
      %Equal.sym(Bool, Http.seq(kx, k), False{}, Equal.trans(Bool, Http.seq(kx, k), String.eq(kx, k), False{}, seq_eq(kx, k), or_f_l(String.eq(kx, k), L.has_key(k, t), h)))
        : {Http.pick(List<&2, Hdr.Header>, _, Con{Hdr.Header{k, List.append(&2, String, vx, [v])}, t}, Con{Hdr.Header{kx, vx}, Http.hdr_add(k, v, t)}) == List.append(&2, Hdr.Header, Con{Hdr.Header{kx, vx}, t}, [Hdr.Header{k, [v]}]) : List<&2, Hdr.Header>}
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => Con{Hdr.Header{kx, vx}, z}, Http.hdr_add(k, v, t), List.append(&2, Hdr.Header, t, [Hdr.Header{k, [v]}]), ih(or_f_r(String.eq(kx, k), L.has_key(k, t), h)))

def add_new(+k: String, +v: String, t: List<&2, Hdr.Header>, +h: {L.has_key(k, t) == False{} : Bool})
  -> {Http.hdr_add(k, v, t) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, [v]}]) : List<&2, Hdr.Header>}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      add_new2(x, rest, k, v, h, hh => add_new(k, v, rest, hh))

def add_old2(x: Hdr.Header, +t: List<&2, Hdr.Header>, +k: String, +v: String, +us: List<&2, String>, +h: {L.has_key(k, Con{x, t}) == False{} : Bool},
             ih: {L.has_key(k, t) == False{} : Bool} -> {Http.hdr_add(k, v, List.append(&2, Hdr.Header, t, [Hdr.Header{k, us}])) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, [v])}]) : List<&2, Hdr.Header>})
  -> {Http.hdr_add(k, v, List.append(&2, Hdr.Header, Con{x, t}, [Hdr.Header{k, us}])) == List.append(&2, Hdr.Header, Con{x, t}, [Hdr.Header{k, List.append(&2, String, us, [v])}]) : List<&2, Hdr.Header>}:
  match x:
    case Hdr.Header{+kx, +vx}:
      %Equal.sym(Bool, Http.seq(kx, k), False{}, Equal.trans(Bool, Http.seq(kx, k), String.eq(kx, k), False{}, seq_eq(kx, k), or_f_l(String.eq(kx, k), L.has_key(k, t), h)))
        : {Http.pick(List<&2, Hdr.Header>, _, Con{Hdr.Header{k, List.append(&2, String, vx, [v])}, List.append(&2, Hdr.Header, t, [Hdr.Header{k, us}])}, Con{Hdr.Header{kx, vx}, Http.hdr_add(k, v, List.append(&2, Hdr.Header, t, [Hdr.Header{k, us}]))})
           == List.append(&2, Hdr.Header, Con{Hdr.Header{kx, vx}, t}, [Hdr.Header{k, List.append(&2, String, us, [v])}]) : List<&2, Hdr.Header>}
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => Con{Hdr.Header{kx, vx}, z}, Http.hdr_add(k, v, List.append(&2, Hdr.Header, t, [Hdr.Header{k, us}])), List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, [v])}]), ih(or_f_r(String.eq(kx, k), L.has_key(k, t), h)))

def add_old(+k: String, +v: String, t: List<&2, Hdr.Header>, +us: List<&2, String>, +h: {L.has_key(k, t) == False{} : Bool})
  -> {Http.hdr_add(k, v, List.append(&2, Hdr.Header, t, [Hdr.Header{k, us}])) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, [v])}]) : List<&2, Hdr.Header>}:
  match t:
    case Nil{}:
      %Equal.sym(Bool, Http.seq(k, k), True{}, Equal.trans(Bool, Http.seq(k, k), String.eq(k, k), True{}, seq_eq(k, k), str_refl(k)))
        : {Http.pick(List<&2, Hdr.Header>, _, Con{Hdr.Header{k, List.append(&2, String, us, [v])}, []}, Con{Hdr.Header{k, us}, Http.hdr_add(k, v, [])}) == [Hdr.Header{k, List.append(&2, String, us, [v])}] : List<&2, Hdr.Header>}
      {==}
    case Con{+x, +rest}:
      add_old2(x, rest, k, v, us, h, hh => add_old(k, v, rest, us, hh))

def addvals(+k: String, vs: List<&2, String>, t: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match vs:
    case Nil{}:
      t
    case Con{+v, +rest}:
      addvals(k, rest, Http.hdr_add(k, v, t))

def addvals_old(+k: String, vs: List<&2, String>, +t: List<&2, Hdr.Header>, +us: List<&2, String>, +h: {L.has_key(k, t) == False{} : Bool})
  -> {addvals(k, vs, List.append(&2, Hdr.Header, t, [Hdr.Header{k, us}])) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, vs)}]) : List<&2, Hdr.Header>}:
  match vs:
    case Nil{}:
      %Equal.sym(List<&2, String>, List.append(&2, String, us, []), us, lapp_nil(String, us)) : {List.append(&2, Hdr.Header, t, [Hdr.Header{k, us}]) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, _}]) : List<&2, Hdr.Header>}
      {==}
    case Con{+v, +rest}:
      %Equal.sym(List<&2, Hdr.Header>, Http.hdr_add(k, v, List.append(&2, Hdr.Header, t, [Hdr.Header{k, us}])), List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, [v])}]), add_old(k, v, t, us, h))
        : {addvals(k, rest, _) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, Con{v, rest})}]) : List<&2, Hdr.Header>}
      %Equal.sym(List<&2, Hdr.Header>, addvals(k, rest, List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, [v])}])), List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, List.append(&2, String, us, [v]), rest)}]), addvals_old(k, rest, t, List.append(&2, String, us, [v]), h))
        : {_ == List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, Con{v, rest})}]) : List<&2, Hdr.Header>}
      %Equal.sym(List<&2, String>, List.append(&2, String, List.append(&2, String, us, [v]), rest), List.append(&2, String, us, List.append(&2, String, [v], rest)), lapp_assoc(String, us, [v], rest))
        : {List.append(&2, Hdr.Header, t, [Hdr.Header{k, _}]) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, List.append(&2, String, us, Con{v, rest})}]) : List<&2, Hdr.Header>}
      {==}

def addvals_new(+k: String, vs: List<&2, String>, +t: List<&2, Hdr.Header>, +h: {L.has_key(k, t) == False{} : Bool}, +hne: {List.is_empty(&2, String, vs) == False{} : Bool})
  -> {addvals(k, vs, t) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}]) : List<&2, Hdr.Header>}:
  match vs:
    case Nil{}:
      Empty.absurd({t == List.append(&2, Hdr.Header, t, [Hdr.Header{k, []}]) : List<&2, Hdr.Header>}, no_tf(hne))
    case Con{+v, +rest}:
      %Equal.sym(List<&2, Hdr.Header>, Http.hdr_add(k, v, t), List.append(&2, Hdr.Header, t, [Hdr.Header{k, [v]}]), add_new(k, v, t, h))
        : {addvals(k, rest, _) == List.append(&2, Hdr.Header, t, [Hdr.Header{k, Con{v, rest}}]) : List<&2, Hdr.Header>}
      addvals_old(k, rest, t, [v], h)

def addall_kvs(+k: String, vs: List<&2, String>, +tail: List<&2, KV>, +t: List<&2, Hdr.Header>)
  -> {addall(kvs(k, vs, tail), t) == addall(tail, addvals(Http.canon(k), vs, t)) : List<&2, Hdr.Header>}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      addall_kvs(k, rest, tail, Http.hdr_add(Http.canon(k), v, t))

def canon_go_h(s: String, +up: Bool) -> {Http.canon.go(s, up) == L.canon.go(s, up) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %canon_go_h(rest, U32.is_eq(k, 45))
            : {Http.canon.go(SCon{Chr{k}, rest}, up) == SCon{Chr{L.pick(U32, Bool.and(up, L.in_range32(k, 97, 122)), (k - 32 : U32), L.pick(U32, Bool.and(Bool.not(up), L.in_range32(k, 65, 90)), (k + 32 : U32), k))}, _} : String}
          %pick_h(U32, Bool.and(up, L.in_range32(k, 97, 122)), (k - 32 : U32), Http.pick(U32, Bool.and(Bool.not(up), L.in_range32(k, 65, 90)), (k + 32 : U32), k),
              (k - 32 : U32), L.pick(U32, Bool.and(Bool.not(up), L.in_range32(k, 65, 90)), (k + 32 : U32), k), {==},
              pick_h(U32, Bool.and(Bool.not(up), L.in_range32(k, 65, 90)), (k + 32 : U32), k, (k + 32 : U32), k, {==}, {==}))
            : {Http.canon.go(SCon{Chr{k}, rest}, up) == SCon{Chr{_}, Http.canon.go(rest, U32.is_eq(k, 45))} : String}
          {==}

def canon_h(+s: String) -> {Http.canon(s) == L.canon(s) : String}:
  %Equal.sym(Bool, Http.token(s), L.token(s), token_h(s)) : {Http.pick(String, _, Http.canon.go(s, True{}), s) == L.canon(s) : String}
  pick_h(String, L.token(s), Http.canon.go(s, True{}), s, L.canon.go(s, True{}), s, canon_go_h(s, True{}), {==})

# the six conjuncts of hdrs_resp_ok on a header
def hr_1(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +e: {Bool.and(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6))) == True{} : Bool}) -> {a1 == True{} : Bool}:
  and_l(a1, a2, and_l(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6)), e))

def hr_2(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +e: {Bool.and(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6))) == True{} : Bool}) -> {a2 == True{} : Bool}:
  and_r(a1, a2, and_l(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6)), e))

def hr_3(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +e: {Bool.and(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6))) == True{} : Bool}) -> {a3 == True{} : Bool}:
  and_l(a3, a4, and_l(Bool.and(a3, a4), Bool.and(a5, a6), and_r(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6)), e)))

def hr_4(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +e: {Bool.and(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6))) == True{} : Bool}) -> {a4 == True{} : Bool}:
  and_r(a3, a4, and_l(Bool.and(a3, a4), Bool.and(a5, a6), and_r(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6)), e)))

def hr_5(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +e: {Bool.and(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6))) == True{} : Bool}) -> {a5 == True{} : Bool}:
  and_l(a5, a6, and_r(Bool.and(a3, a4), Bool.and(a5, a6), and_r(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6)), e)))

def hr_6(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +e: {Bool.and(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6))) == True{} : Bool}) -> {a6 == True{} : Bool}:
  and_r(a5, a6, and_r(Bool.and(a3, a4), Bool.and(a5, a6), and_r(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6)), e)))

def disj(hs: List<&2, Hdr.Header>, +t: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +rest}:
      Bool.and(Bool.not(L.has_key(L.hdr_key(h), t)), disj(rest, t))

def disj_nil(hs: List<&2, Hdr.Header>) -> {disj(hs, []) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      disj_nil(rest)

def or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def has_key_app(+k: String, t: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>)
  -> {L.has_key(k, List.append(&2, Hdr.Header, t, u)) == Bool.or(L.has_key(k, t), L.has_key(k, u)) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Bool, L.has_key(k, List.append(&2, Hdr.Header, rest, u)), Bool.or(L.has_key(k, rest), L.has_key(k, u)), has_key_app(k, rest, u))
        : {Bool.or(String.eq(L.hdr_key(x), k), _) == Bool.or(Bool.or(String.eq(L.hdr_key(x), k), L.has_key(k, rest)), L.has_key(k, u)) : Bool}
      or_assoc(String.eq(L.hdr_key(x), k), L.has_key(k, rest), L.has_key(k, u))

def not_or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.not(Bool.or(a, Bool.or(b, False{}))) == True{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.not(Bool.or(_, Bool.or(b, False{}))) == True{} : Bool}
  %Equal.sym(Bool, b, False{}, hb) : {Bool.not(Bool.or(False{}, Bool.or(_, False{}))) == True{} : Bool}
  {==}

def disj_ext(rest: List<&2, Hdr.Header>, +t: List<&2, Hdr.Header>, +k: String, +vs: List<&2, String>,
             +h1: {disj(rest, t) == True{} : Bool}, +h2: {L.has_key(k, rest) == False{} : Bool})
  -> {disj(rest, List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}])) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      and_i(Bool.not(L.has_key(L.hdr_key(y), List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}]))), disj(r, List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}])),
        Equal.trans(Bool, Bool.not(L.has_key(L.hdr_key(y), List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}]))),
          Bool.not(Bool.or(L.has_key(L.hdr_key(y), t), Bool.or(String.eq(k, L.hdr_key(y)), False{}))), True{},
          Equal.cong(Bool, Bool, z => Bool.not(z), L.has_key(L.hdr_key(y), List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}])),
            Bool.or(L.has_key(L.hdr_key(y), t), Bool.or(String.eq(k, L.hdr_key(y)), False{})), has_key_app(L.hdr_key(y), t, [Hdr.Header{k, vs}])),
          not_or_ff(L.has_key(L.hdr_key(y), t), String.eq(k, L.hdr_key(y)),
            not_t(L.has_key(L.hdr_key(y), t), and_l(Bool.not(L.has_key(L.hdr_key(y), t)), disj(r, t), h1)),
            eq_sym_of(False{}, k, L.hdr_key(y), or_f_l(String.eq(L.hdr_key(y), k), L.has_key(k, r), h2)))),
        disj_ext(r, t, k, vs, and_r(Bool.not(L.has_key(L.hdr_key(y), t)), disj(r, t), h1), or_f_r(String.eq(L.hdr_key(y), k), L.has_key(k, r), h2)))

def addall_fl(hs: List<&2, Hdr.Header>, +t: List<&2, Hdr.Header>, +hd: {disj(hs, t) == True{} : Bool}, +h: {L.hdrs_resp_ok(hs) == True{} : Bool})
  -> {addall(fl(hs), t) == List.append(&2, Hdr.Header, t, hs) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      Equal.sym(List<&2, Hdr.Header>, List.append(&2, Hdr.Header, t, []), t, lapp_nil(Hdr.Header, t))
    case Con{x, +rest}:
      match x:
        case Hdr.Header{+k, +vs}:
          Equal.trans(List<&2, Hdr.Header>, addall(kvs(k, vs, fl(rest)), t), addall(fl(rest), addvals(Http.canon(k), vs, t)), List.append(&2, Hdr.Header, t, Con{Hdr.Header{k, vs}, rest}),
            addall_kvs(k, vs, fl(rest), t),
            Equal.trans(List<&2, Hdr.Header>, addall(fl(rest), addvals(Http.canon(k), vs, t)), addall(fl(rest), addvals(k, vs, t)), List.append(&2, Hdr.Header, t, Con{Hdr.Header{k, vs}, rest}),
              Equal.cong(String, List<&2, Hdr.Header>, z => addall(fl(rest), addvals(z, vs, t)), Http.canon(k), k,
                Equal.trans(String, Http.canon(k), L.canon(k), k, canon_h(k),
                  str_eq(L.canon(k), k, hr_2(L.token(k), String.eq(L.canon(k), k), Bool.not(L.has_key(k, rest)), Bool.not(List.is_empty(&2, String, vs)), L.all_clean(vs), L.hdrs_resp_ok(rest), h)))),
              Equal.trans(List<&2, Hdr.Header>, addall(fl(rest), addvals(k, vs, t)), addall(fl(rest), List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}])), List.append(&2, Hdr.Header, t, Con{Hdr.Header{k, vs}, rest}),
                Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => addall(fl(rest), z), addvals(k, vs, t), List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}]),
                  addvals_new(k, vs, t, not_t(L.has_key(k, t), and_l(Bool.not(L.has_key(k, t)), disj(rest, t), hd)),
                    not_t(List.is_empty(&2, String, vs), hr_4(L.token(k), String.eq(L.canon(k), k), Bool.not(L.has_key(k, rest)), Bool.not(List.is_empty(&2, String, vs)), L.all_clean(vs), L.hdrs_resp_ok(rest), h)))),
                Equal.trans(List<&2, Hdr.Header>, addall(fl(rest), List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}])), List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}]), rest), List.append(&2, Hdr.Header, t, Con{Hdr.Header{k, vs}, rest}),
                  addall_fl(rest, List.append(&2, Hdr.Header, t, [Hdr.Header{k, vs}]),
                    disj_ext(rest, t, k, vs, and_r(Bool.not(L.has_key(k, t)), disj(rest, t), hd),
                      not_t(L.has_key(k, rest), hr_3(L.token(k), String.eq(L.canon(k), k), Bool.not(L.has_key(k, rest)), Bool.not(List.is_empty(&2, String, vs)), L.all_clean(vs), L.hdrs_resp_ok(rest), h))),
                    hr_6(L.token(k), String.eq(L.canon(k), k), Bool.not(L.has_key(k, rest)), Bool.not(List.is_empty(&2, String, vs)), L.all_clean(vs), L.hdrs_resp_ok(rest), h)),
                  lapp_assoc(Hdr.Header, t, [Hdr.Header{k, vs}], rest)))))

def pok_vals(+k: String, vs: List<&2, String>, +tail: List<&2, KV>, +htok: {L.token(k) == True{} : Bool}, +hc: {L.all_clean(vs) == True{} : Bool}, +ht: {pok(tail) == True{} : Bool})
  -> {pok(kvs(k, vs, tail)) == True{} : Bool}:
  match vs:
    case Nil{}:
      ht
    case Con{+v, +rest}:
      and_i(Bool.and(L.token(k), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(kvs(k, rest, tail))),
        and_i(L.token(k), L.no_ctl(v), htok,
          and_l(L.no_ctl(v), String.eq(L.trim_ows(v), v), and_r(L.bytes(v), Bool.and(L.no_ctl(v), String.eq(L.trim_ows(v), v)), and_l(L.clean_val(v), L.all_clean(rest), hc)))),
        and_i(String.eq(Http.trim_ows(v), v), pok(kvs(k, rest, tail)),
          Equal.trans(Bool, String.eq(Http.trim_ows(v), v), String.eq(L.trim_ows(v), v), True{},
            Equal.cong(String, Bool, z => String.eq(z, v), Http.trim_ows(v), L.trim_ows(v), trim_h(v)),
            and_r(L.no_ctl(v), String.eq(L.trim_ows(v), v), and_r(L.bytes(v), Bool.and(L.no_ctl(v), String.eq(L.trim_ows(v), v)), and_l(L.clean_val(v), L.all_clean(rest), hc)))),
          pok_vals(k, rest, tail, htok, and_r(L.clean_val(v), L.all_clean(rest), hc), ht)))

def pok_fl(hs: List<&2, Hdr.Header>, +h: {L.hdrs_resp_ok(hs) == True{} : Bool}) -> {pok(fl(hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      pok_vals(L.hdr_key(x), L.hdr_vals(x), fl(rest),
        hr_1(L.token(L.hdr_key(x)), String.eq(L.canon(L.hdr_key(x)), L.hdr_key(x)), Bool.not(L.has_key(L.hdr_key(x), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(x))), L.all_clean(L.hdr_vals(x)), L.hdrs_resp_ok(rest), h),
        hr_5(L.token(L.hdr_key(x)), String.eq(L.canon(L.hdr_key(x)), L.hdr_key(x)), Bool.not(L.has_key(L.hdr_key(x), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(x))), L.all_clean(L.hdr_vals(x)), L.hdrs_resp_ok(rest), h),
        pok_fl(rest, hr_6(L.token(L.hdr_key(x)), String.eq(L.canon(L.hdr_key(x)), L.hdr_key(x)), Bool.not(L.has_key(L.hdr_key(x), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(x))), L.all_clean(L.hdr_vals(x)), L.hdrs_resp_ok(rest), h)))

# ---------------------------------------------------------------------
# Header lookups
# ---------------------------------------------------------------------

def hdr_get_none2(x: Hdr.Header, +rest: List<&2, Hdr.Header>, +k: String, +h: {L.has_key(k, Con{x, rest}) == False{} : Bool},
                  ih: {L.has_key(k, rest) == False{} : Bool} -> {Http.hdr_get(k, rest) == None{} : Maybe<&2, List<&2, String>>})
  -> {Http.hdr_get(k, Con{x, rest}) == None{} : Maybe<&2, List<&2, String>>}:
  match x:
    case Hdr.Header{+kx, +vx}:
      %Equal.sym(Bool, Http.seq(kx, k), False{}, Equal.trans(Bool, Http.seq(kx, k), String.eq(kx, k), False{}, seq_eq(kx, k), or_f_l(String.eq(kx, k), L.has_key(k, rest), h)))
        : {Http.pick(Maybe<&2, List<&2, String>>, _, Some{vx}, Http.hdr_get(k, rest)) == None{} : Maybe<&2, List<&2, String>>}
      ih(or_f_r(String.eq(kx, k), L.has_key(k, rest), h))

def hdr_get_none(+k: String, hs: List<&2, Hdr.Header>, +h: {L.has_key(k, hs) == False{} : Bool}) -> {Http.hdr_get(k, hs) == None{} : Maybe<&2, List<&2, String>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      hdr_get_none2(x, rest, k, h, hh => hdr_get_none(k, rest, hh))

def hdr_del_none2(x: Hdr.Header, +rest: List<&2, Hdr.Header>, +k: String, +h: {L.has_key(k, Con{x, rest}) == False{} : Bool},
                  ih: {L.has_key(k, rest) == False{} : Bool} -> {Http.hdr_del(k, rest) == rest : List<&2, Hdr.Header>})
  -> {Http.hdr_del(k, Con{x, rest}) == Con{x, rest} : List<&2, Hdr.Header>}:
  match x:
    case Hdr.Header{+kx, +vx}:
      %Equal.sym(Bool, Http.seq(kx, k), False{}, Equal.trans(Bool, Http.seq(kx, k), String.eq(kx, k), False{}, seq_eq(kx, k), or_f_l(String.eq(kx, k), L.has_key(k, rest), h)))
        : {Http.pick(List<&2, Hdr.Header>, _, Http.hdr_del(k, rest), Con{Hdr.Header{kx, vx}, Http.hdr_del(k, rest)}) == Con{Hdr.Header{kx, vx}, rest} : List<&2, Hdr.Header>}
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => Con{Hdr.Header{kx, vx}, z}, Http.hdr_del(k, rest), rest, ih(or_f_r(String.eq(kx, k), L.has_key(k, rest), h)))

def hdr_del_none(+k: String, hs: List<&2, Hdr.Header>, +h: {L.has_key(k, hs) == False{} : Bool}) -> {Http.hdr_del(k, hs) == hs : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      hdr_del_none2(x, rest, k, h, hh => hdr_del_none(k, rest, hh))

def hdr_set_none2(x: Hdr.Header, +rest: List<&2, Hdr.Header>, +k: String, +vs: List<&2, String>, +h: {L.has_key(k, Con{x, rest}) == False{} : Bool},
                  ih: {L.has_key(k, rest) == False{} : Bool} -> {Http.hdr_set(k, vs, rest) == rest : List<&2, Hdr.Header>})
  -> {Http.hdr_set(k, vs, Con{x, rest}) == Con{x, rest} : List<&2, Hdr.Header>}:
  match x:
    case Hdr.Header{+kx, +vx}:
      %Equal.sym(Bool, Http.seq(kx, k), False{}, Equal.trans(Bool, Http.seq(kx, k), String.eq(kx, k), False{}, seq_eq(kx, k), or_f_l(String.eq(kx, k), L.has_key(k, rest), h)))
        : {Http.pick(List<&2, Hdr.Header>, _, Con{Hdr.Header{k, vs}, Http.hdr_set(k, vs, rest)}, Con{Hdr.Header{kx, vx}, Http.hdr_set(k, vs, rest)}) == Con{Hdr.Header{kx, vx}, rest} : List<&2, Hdr.Header>}
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => Con{Hdr.Header{kx, vx}, z}, Http.hdr_set(k, vs, rest), rest, ih(or_f_r(String.eq(kx, k), L.has_key(k, rest), h)))

def hdr_set_none(+k: String, +vs: List<&2, String>, hs: List<&2, Hdr.Header>, +h: {L.has_key(k, hs) == False{} : Bool}) -> {Http.hdr_set(k, vs, hs) == hs : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      hdr_set_none2(x, rest, k, vs, h, hh => hdr_set_none(k, vs, rest, hh))

def hdr_get_skip2(x: Hdr.Header, +rest: List<&2, Hdr.Header>, +k: String, +u: List<&2, Hdr.Header>, +h: {L.has_key(k, Con{x, rest}) == False{} : Bool},
                  ih: {L.has_key(k, rest) == False{} : Bool} -> {Http.hdr_get(k, List.append(&2, Hdr.Header, rest, u)) == Http.hdr_get(k, u) : Maybe<&2, List<&2, String>>})
  -> {Http.hdr_get(k, List.append(&2, Hdr.Header, Con{x, rest}, u)) == Http.hdr_get(k, u) : Maybe<&2, List<&2, String>>}:
  match x:
    case Hdr.Header{+kx, +vx}:
      %Equal.sym(Bool, Http.seq(kx, k), False{}, Equal.trans(Bool, Http.seq(kx, k), String.eq(kx, k), False{}, seq_eq(kx, k), or_f_l(String.eq(kx, k), L.has_key(k, rest), h)))
        : {Http.pick(Maybe<&2, List<&2, String>>, _, Some{vx}, Http.hdr_get(k, List.append(&2, Hdr.Header, rest, u))) == Http.hdr_get(k, u) : Maybe<&2, List<&2, String>>}
      ih(or_f_r(String.eq(kx, k), L.has_key(k, rest), h))

# a lookup skips a list without the name
def hdr_get_skip(+k: String, hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +h: {L.has_key(k, hs) == False{} : Bool})
  -> {Http.hdr_get(k, List.append(&2, Hdr.Header, hs, u)) == Http.hdr_get(k, u) : Maybe<&2, List<&2, String>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      hdr_get_skip2(x, rest, k, u, h, hh => hdr_get_skip(k, rest, u, hh))

def pick_app(b: Bool, +x: Hdr.Header, +r: List<&2, Hdr.Header>, +w: List<&2, Hdr.Header>)
  -> {Http.pick(List<&2, Hdr.Header>, b, List.append(&2, Hdr.Header, r, w), Con{x, List.append(&2, Hdr.Header, r, w)}) == List.append(&2, Hdr.Header, Http.pick(List<&2, Hdr.Header>, b, r, Con{x, r}), w) : List<&2, Hdr.Header>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def hdr_del_app(+k: String, hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>)
  -> {Http.hdr_del(k, List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, Http.hdr_del(k, hs), Http.hdr_del(k, u)) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del(k, List.append(&2, Hdr.Header, rest, u)), List.append(&2, Hdr.Header, Http.hdr_del(k, rest), Http.hdr_del(k, u)), hdr_del_app(k, rest, u))
        : {Http.pick(List<&2, Hdr.Header>, Http.seq(Http.hdr_key(x), k), _, Con{x, _}) == List.append(&2, Hdr.Header, Http.hdr_del(k, Con{x, rest}), Http.hdr_del(k, u)) : List<&2, Hdr.Header>}
      pick_app(Http.seq(Http.hdr_key(x), k), x, Http.hdr_del(k, rest), Http.hdr_del(k, u))

def hs_case(b: Bool, +kx: String, +vx: List<&2, String>, +rest: List<&2, Hdr.Header>, +k: String, +vs: List<&2, String>,
            +e: {Http.seq(kx, k) == b : Bool},
            +hg: {Http.pick(Maybe<&2, List<&2, String>>, b, Some{vx}, Http.hdr_get(k, rest)) == Some{vs} : Maybe<&2, List<&2, String>>},
            +hnk: {L.has_key(kx, rest) == False{} : Bool},
            ih: {Http.hdr_get(k, rest) == Some{vs} : Maybe<&2, List<&2, String>>} -> {Http.hdr_set(k, vs, rest) == rest : List<&2, Hdr.Header>})
  -> {Http.pick(List<&2, Hdr.Header>, b, Con{Hdr.Header{k, vs}, Http.hdr_set(k, vs, rest)}, Con{Hdr.Header{kx, vx}, Http.hdr_set(k, vs, rest)}) == Con{Hdr.Header{kx, vx}, rest} : List<&2, Hdr.Header>}:
  match b:
    case True{}:
      %Equal.sym(String, kx, k, str_eq(kx, k, Equal.trans(Bool, String.eq(kx, k), Http.seq(kx, k), b, Equal.sym(Bool, Http.seq(kx, k), String.eq(kx, k), seq_eq(kx, k)), e))) : {Con{Hdr.Header{k, vs}, Http.hdr_set(k, vs, rest)} == Con{Hdr.Header{_, vx}, rest} : List<&2, Hdr.Header>}
      %Equal.sym(List<&2, String>, vx, vs, Equal.cong(Maybe<&2, List<&2, String>>, List<&2, String>, m => Maybe.default(&2, List<&2, String>, m, []), Some{vx}, Some{vs}, hg))
        : {Con{Hdr.Header{k, vs}, Http.hdr_set(k, vs, rest)} == Con{Hdr.Header{k, _}, rest} : List<&2, Hdr.Header>}
      %Equal.sym(List<&2, Hdr.Header>, Http.hdr_set(k, vs, rest), rest,
          hdr_set_none(k, vs, rest, Equal.trans(Bool, L.has_key(k, rest), L.has_key(kx, rest), False{},
            Equal.cong(String, Bool, z => L.has_key(z, rest), k, kx, Equal.sym(String, kx, k, str_eq(kx, k, Equal.trans(Bool, String.eq(kx, k), Http.seq(kx, k), b, Equal.sym(Bool, Http.seq(kx, k), String.eq(kx, k), seq_eq(kx, k)), e)))), hnk)))
        : {Con{Hdr.Header{k, vs}, _} == Con{Hdr.Header{k, vs}, rest} : List<&2, Hdr.Header>}
      {==}
    case False{}:
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => Con{Hdr.Header{kx, vx}, z}, Http.hdr_set(k, vs, rest), rest, ih(hg))

def hdr_set_id2(x: Hdr.Header, +rest: List<&2, Hdr.Header>, +k: String, +vs: List<&2, String>,
                +hg: {Http.hdr_get(k, Con{x, rest}) == Some{vs} : Maybe<&2, List<&2, String>>}, +hok: {L.hdrs_resp_ok(Con{x, rest}) == True{} : Bool},
                ih: {L.hdrs_resp_ok(rest) == True{} : Bool} -> {Http.hdr_get(k, rest) == Some{vs} : Maybe<&2, List<&2, String>>} -> {Http.hdr_set(k, vs, rest) == rest : List<&2, Hdr.Header>})
  -> {Http.hdr_set(k, vs, Con{x, rest}) == Con{x, rest} : List<&2, Hdr.Header>}:
  match x:
    case Hdr.Header{+kx, +vx}:
      hs_case(Http.seq(kx, k), kx, vx, rest, k, vs, {==}, hg,
        not_t(L.has_key(kx, rest), hr_3(L.token(kx), String.eq(L.canon(kx), kx), Bool.not(L.has_key(kx, rest)), Bool.not(List.is_empty(&2, String, vx)), L.all_clean(vx), L.hdrs_resp_ok(rest), hok)),
        ih(hr_6(L.token(kx), String.eq(L.canon(kx), kx), Bool.not(L.has_key(kx, rest)), Bool.not(List.is_empty(&2, String, vx)), L.all_clean(vx), L.hdrs_resp_ok(rest), hok)))

# setting a name to the values it has changes nothing (names are distinct)
def hdr_set_id(+k: String, +vs: List<&2, String>, hs: List<&2, Hdr.Header>, +hg: {Http.hdr_get(k, hs) == Some{vs} : Maybe<&2, List<&2, String>>},
               +hok: {L.hdrs_resp_ok(hs) == True{} : Bool}) -> {Http.hdr_set(k, vs, hs) == hs : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      hdr_set_id2(x, rest, k, vs, hg, hok, h2 => h1 => hdr_set_id(k, vs, rest, h1, h2))

def one_val_eq(+v: String, m: Maybe<&2, List<&2, String>>, +h: {L.one_val(v, m) == True{} : Bool}) -> {m == Some{[v]} : Maybe<&2, List<&2, String>>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{[v]} : Maybe<&2, List<&2, String>>}, no_ft(h))
    case Some{vs}:
      match vs:
        case Nil{}:
          Empty.absurd({Some{[]} == Some{[v]} : Maybe<&2, List<&2, String>>}, no_ft(h))
        case Con{+x, rest}:
          match rest:
            case Nil{}:
              Equal.cong(String, Maybe<&2, List<&2, String>>, z => Some{[z]}, x, v, str_eq(x, v, and_l(String.eq(x, v), True{}, h)))
            case Con{y, more}:
              Empty.absurd({Some{Con{x, Con{y, more}}} == Some{[v]} : Maybe<&2, List<&2, String>>}, no_ft(and_r(String.eq(x, v), False{}, h)))

# ---------------------------------------------------------------------
# Connection tokens: lib's reading is LAWS'
# ---------------------------------------------------------------------

def split_cons_h(+c: Char, ps: List<&2, String>) -> {Http.split_cons(c, ps) == L.split_cons(c, ps) : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +rest}:
      {==}

def split_on_h(+k: U32, s: String) -> {Http.split_on(k, s) == L.split_on(k, s) : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+x}:
          %split_on_h(k, rest) : {Http.split_on(k, SCon{Chr{x}, rest}) == L.pick(List<&2, String>, U32.is_eq(x, k), Con{"", _}, L.split_cons(Chr{x}, _)) : List<&2, String>}
          pick_h(List<&2, String>, U32.is_eq(x, k), Con{"", Http.split_on(k, rest)}, Http.split_cons(Chr{x}, Http.split_on(k, rest)), Con{"", Http.split_on(k, rest)}, L.split_cons(Chr{x}, Http.split_on(k, rest)),
            {==}, split_cons_h(Chr{x}, Http.split_on(k, rest)))

def trim_all_h(vs: List<&2, String>) -> {Http.trim_all(vs) == L.trim_all(vs) : List<&2, String>}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      %trim_all_h(rest) : {Http.trim_all(Con{v, rest}) == Con{L.trim_ows(v), _} : List<&2, String>}
      %trim_h(v) : {Http.trim_all(Con{v, rest}) == Con{_, Http.trim_all(rest)} : List<&2, String>}
      {==}

def token_list_h(+v: String) -> {Http.token_list(v) == L.token_list(v) : List<&2, String>}:
  %split_on_h(44, v) : {Http.token_list(v) == L.trim_all(_) : List<&2, String>}
  trim_all_h(Http.split_on(44, v))

def any_ci_h(+v: String, vs: List<&2, String>) -> {Http.any_ci(v, vs) == L.any_ci(v, vs) : Bool}:
  match vs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %any_ci_h(v, rest) : {Http.any_ci(v, Con{x, rest}) == Bool.or(String.eq(String.to_lower(x), String.to_lower(v)), _) : Bool}
      %seq_eq(String.to_lower(x), String.to_lower(v)) : {Http.any_ci(v, Con{x, rest}) == Bool.or(_, Http.any_ci(v, rest)) : Bool}
      {==}

def any_token_h(+t: String, vs: List<&2, String>) -> {Http.any_token(t, vs) == L.any_token(t, vs) : Bool}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      %any_token_h(t, rest) : {Http.any_token(t, Con{v, rest}) == Bool.or(L.any_ci(t, L.token_list(v)), _) : Bool}
      %token_list_h(v) : {Http.any_token(t, Con{v, rest}) == Bool.or(L.any_ci(t, _), Http.any_token(t, rest)) : Bool}
      %any_ci_h(t, Http.token_list(v)) : {Http.any_token(t, Con{v, rest}) == Bool.or(_, Http.any_token(t, rest)) : Bool}
      {==}

def some_token_h(+t: String, +m: Maybe<&2, List<&2, String>>) -> {Http.some_token(t, m) == L.some_token(t, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+vs}:
      any_token_h(t, vs)

def conn_token_h(+t: String, +hs: List<&2, Hdr.Header>) -> {Http.conn_token(t, hs) == L.conn_token(t, hs) : Bool}:
  %hdr_get_h("Connection", hs) : {Http.conn_token(t, hs) == L.some_token(t, _) : Bool}
  some_token_h(t, Http.hdr_get("Connection", hs))

# ---------------------------------------------------------------------
# Framing a Content-Length response
# ---------------------------------------------------------------------

def and_t(x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def pf_id(+h: List<&2, Hdr.Header>, +hp: {Http.hdr_get("Pragma", h) == None{} : Maybe<&2, List<&2, String>>}) -> {Http.pragma_fix(h) == h : List<&2, Hdr.Header>}:
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Pragma", h), None{}, hp)
    : {Http.pragma_fix.of(Http.first_no_cache(_), h) == h : List<&2, Hdr.Header>}
  {==}

def sd_g(s: String, +h: {L.all_digits(s) == True{} : Bool}) -> {Bool.and(Bool.not(String.is_empty(s)), Http.all_digits.go(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case SCon{+c, +rest}:
      Equal.trans(Bool, Http.all_digits.go(SCon{c, rest}), L.all_digits.go(SCon{c, rest}), True{}, ad_h(SCon{c, rest}), h)

def fr_cl_main(+c: Nat, +st: String, +mi: Nat, +h: List<&2, Hdr.Header>, +hs: List<&2, Hdr.Header>, +k: Bool, +n: Nat,
    +hp: {Http.hdr_get("Pragma", h) == None{} : Maybe<&2, List<&2, String>>},
    +hte: {Http.hdr_get("Transfer-Encoding", h) == None{} : Maybe<&2, List<&2, String>>},
    +hted: {Http.hdr_del("Transfer-Encoding", h) == h : List<&2, Hdr.Header>},
    +hcf: {Http.conn_fix(mi, h) == hs : List<&2, Hdr.Header>},
    +hko: {Http.keep_of(mi, h) == k : Bool},
    +hnb: {Http.no_body(False{}, c) == False{} : Bool},
    +h101: {Nat.is_eq(c, 101n) == False{} : Bool},
    +hcl: {Http.hdr_get("Content-Length", hs) == Some{[Dec.show(n)]} : Maybe<&2, List<&2, String>>},
    +hset: {Http.hdr_set("Content-Length", [Dec.show(n)], hs) == hs : List<&2, Hdr.Header>})
  -> {Http.framing(c, st, mi, h, False{}) == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}:
  %Equal.sym(List<&2, Hdr.Header>, Http.pragma_fix(h), h, pf_id(h, hp))
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", _), Http.Resp{c, st, Http.conn_fix(mi, Http.hdr_del("Transfer-Encoding", _)), "", Bool.and(Http.keep_of(mi, _), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del("Transfer-Encoding", h), h, hted)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, Http.conn_fix(mi, _), "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.conn_fix(mi, h), hs, hcf)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, _, "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Http.keep_of(mi, h), k, hko)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, hs, "", Bool.and(_, Bool.not(Nat.is_eq(c, 101n)))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Nat.is_eq(c, 101n), False{}, h101)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, hs, "", Bool.and(k, Bool.not(_))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Bool.and(k, True{}), k, and_t(k))
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, hs, "", _})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Transfer-Encoding", h), None{}, hte)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, _, Http.Resp{c, st, hs, "", k})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Http.no_body(False{}, c), False{}, hnb)
    : {Http.fr_body(_, c, mi, None{}, Http.Resp{c, st, hs, "", k})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Content-Length", hs), Some{[Dec.show(n)]}, hcl)
    : {Http.fr_cl(_, Http.Resp{c, st, hs, "", k}) == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_set("Content-Length", [Dec.show(n)], hs), hs, hset)
    : {Http.fr_cl_read(Bool.and(Bool.not(String.is_empty(Dec.show(n))), Http.all_digits.go(Dec.show(n))), Dec.show(n), Http.Resp{c, st, _, "", k})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Bool.and(Bool.not(String.is_empty(Dec.show(n))), Http.all_digits.go(Dec.show(n))), True{}, sd_g(Dec.show(n), show_dig(n)))
    : {Http.fr_cl_read(_, Dec.show(n), Http.Resp{c, st, hs, "", k}) == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Nat, Dec.value(Dec.show(n)), n, show_val(n))
    : {Http.fr_len(Some{_}, Http.Resp{c, st, hs, "", k}) == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  {==}


def fr_cl_gen(+c: Nat, +st: String, +mi: Nat, +h: List<&2, Hdr.Header>, +h2: List<&2, Hdr.Header>, +hs: List<&2, Hdr.Header>, +k: Bool, +n: Nat,
    +hpf: {Http.pragma_fix(h) == h2 : List<&2, Hdr.Header>},
    +hte: {Http.hdr_get("Transfer-Encoding", h2) == None{} : Maybe<&2, List<&2, String>>},
    +hted: {Http.hdr_del("Transfer-Encoding", h2) == h2 : List<&2, Hdr.Header>},
    +hcf: {Http.conn_fix(mi, h2) == hs : List<&2, Hdr.Header>},
    +hko: {Http.keep_of(mi, h2) == k : Bool},
    +hnb: {Http.no_body(False{}, c) == False{} : Bool},
    +h101: {Nat.is_eq(c, 101n) == False{} : Bool},
    +hcl: {Http.hdr_get("Content-Length", hs) == Some{[Dec.show(n)]} : Maybe<&2, List<&2, String>>},
    +hset: {Http.hdr_set("Content-Length", [Dec.show(n)], hs) == hs : List<&2, Hdr.Header>})
  -> {Http.framing(c, st, mi, h, False{}) == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}:
  %Equal.sym(List<&2, Hdr.Header>, Http.pragma_fix(h), h2, hpf)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", _), Http.Resp{c, st, Http.conn_fix(mi, Http.hdr_del("Transfer-Encoding", _)), "", Bool.and(Http.keep_of(mi, _), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del("Transfer-Encoding", h2), h2, hted)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, Http.conn_fix(mi, _), "", Bool.and(Http.keep_of(mi, h2), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.conn_fix(mi, h2), hs, hcf)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, _, "", Bool.and(Http.keep_of(mi, h2), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Http.keep_of(mi, h2), k, hko)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, hs, "", Bool.and(_, Bool.not(Nat.is_eq(c, 101n)))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Nat.is_eq(c, 101n), False{}, h101)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, hs, "", Bool.and(k, Bool.not(_))})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Bool.and(k, True{}), k, and_t(k))
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, hs, "", _})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Transfer-Encoding", h2), None{}, hte)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, _, Http.Resp{c, st, hs, "", k})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Http.no_body(False{}, c), False{}, hnb)
    : {Http.fr_body(_, c, mi, None{}, Http.Resp{c, st, hs, "", k})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Content-Length", hs), Some{[Dec.show(n)]}, hcl)
    : {Http.fr_cl(_, Http.Resp{c, st, hs, "", k}) == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_set("Content-Length", [Dec.show(n)], hs), hs, hset)
    : {Http.fr_cl_read(Bool.and(Bool.not(String.is_empty(Dec.show(n))), Http.all_digits.go(Dec.show(n))), Dec.show(n), Http.Resp{c, st, _, "", k})
       == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Bool, Bool.and(Bool.not(String.is_empty(Dec.show(n))), Http.all_digits.go(Dec.show(n))), True{}, sd_g(Dec.show(n), show_dig(n)))
    : {Http.fr_cl_read(_, Dec.show(n), Http.Resp{c, st, hs, "", k}) == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  %Equal.sym(Nat, Dec.value(Dec.show(n)), n, show_val(n))
    : {Http.fr_len(Some{_}, Http.Resp{c, st, hs, "", k}) == Http.fr_len(Some{n}, Http.Resp{c, st, hs, "", k}) : Http.Ph}
  {==}

# ---------------------------------------------------------------------
# A status that starts with the code
# ---------------------------------------------------------------------

def swi(b: Bool, +x: U32, +y: U32, +xt: String, +yt: String, +e: {U32.is_eq(x, y) == b : Bool},
        +h: {String.starts_with.if(xt, yt, b) == True{} : Bool},
        ih: {String.starts_with(xt, yt) == True{} : Bool} -> {xt == yt ++ String.drop(xt, String.length(yt)) : String})
  -> {SCon{Chr{x}, xt} == SCon{Chr{y}, yt ++ String.drop(xt, String.length(yt))} : String}:
  match b:
    case True{}:
      %u32_eq(x, y, e) : {SCon{Chr{x}, xt} == SCon{Chr{_}, yt ++ String.drop(xt, String.length(yt))} : String}
      Equal.cong(String, String, z => SCon{Chr{x}, z}, xt, yt ++ String.drop(xt, String.length(yt)), ih(h))
    case False{}:
      Empty.absurd({SCon{Chr{x}, xt} == SCon{Chr{y}, yt ++ String.drop(xt, String.length(yt))} : String}, no_ft(h))

def sw_split2(cx: Char, cy: Char, +xt: String, +yt: String, +h: {String.starts_with(SCon{cx, xt}, SCon{cy, yt}) == True{} : Bool},
              ih: {String.starts_with(xt, yt) == True{} : Bool} -> {xt == yt ++ String.drop(xt, String.length(yt)) : String})
  -> {SCon{cx, xt} == SCon{cy, yt ++ String.drop(xt, String.length(yt))} : String}:
  match cx:
    case Chr{+x}:
      match cy:
        case Chr{+y}:
          swi(U32.is_eq(x, y), x, y, xt, yt, {==}, h, ih)

# a string that starts with p is p and the rest
def sw_split(s: String, p: String, +h: {String.starts_with(s, p) == True{} : Bool}) -> {s == p ++ String.drop(s, String.length(p)) : String}:
  match s:
    case SNil{}:
      match p:
        case SNil{}:
          {==}
        case SCon{y, yt}:
          Empty.absurd({SNil{} == SCon{y, yt} ++ SNil{} : String}, no_ft(h))
    case SCon{+x, +xt}:
      match p:
        case SNil{}:
          {==}
        case SCon{+y, +yt}:
          sw_split2(x, y, xt, yt, h, hh => sw_split(xt, yt, hh))

def st_eq(+c: Nat, +st: String, +h: {String.starts_with(st, Dec.show(c) ++ " ") == True{} : Bool})
  -> {st == Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))) : String}:
  Equal.trans(String, st, (Dec.show(c) ++ " ") ++ String.drop(st, String.length(Dec.show(c) ++ " ")), Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))),
    sw_split(st, Dec.show(c) ++ " ", h), app_assoc(Dec.show(c), " ", String.drop(st, String.length(Dec.show(c) ++ " "))))

def ge_c0(c: Nat) -> {Nat.is_ge(c, 0n) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+cp:
      {==}

# c >= a and b <= a: c >= b
def ge_mono(b: Nat, a: Nat, c: Nat, +hab: {Nat.is_le(b, a) == True{} : Bool}, +h: {Nat.is_ge(c, a) == True{} : Bool}) -> {Nat.is_ge(c, b) == True{} : Bool}:
  match b:
    case 0n:
      ge_c0(c)
    case 1n+bp:
      match a:
        case 0n:
          Empty.absurd({Nat.is_ge(c, 1n+bp) == True{} : Bool}, no_ft(hab))
        case 1n+ap:
          match c:
            case 0n:
              Empty.absurd({Nat.is_ge(0n, 1n+bp) == True{} : Bool}, no_ft(h))
            case 1n+cp:
              ge_mono(bp, ap, cp, hab, h)

def ge_100(+c: Nat, +h: {Nat.is_ge(c, 200n) == True{} : Bool}) -> {Nat.is_ge(c, 100n) == True{} : Bool}:
  ge_mono(100n, 200n, c, {==}, h)

# the status line of a response with status st
def stat_st(+c: Nat, +st: String, +w: String, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
    +h1: {Nat.is_ge(c, 200n) == True{} : Bool}, +h2: {Nat.is_le(c, 599n) == True{} : Bool},
    +hp: {L.printable(st) == True{} : Bool}, +hs: {String.starts_with(st, Dec.show(c) ++ " ") == True{} : Bool})
  -> {Http.feed.go("HTTP/1.1 " ++ (st ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HStat{0n, ""}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, 1n, [], None{}, ""}}) : Http.Parse}:
  %Equal.sym(String, st, Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))), st_eq(c, st, hs))
    : {Http.feed.go("HTTP/1.1 " ++ (_ ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HStat{0n, ""}})
       == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{c, _, 1n, [], None{}, ""}}) : Http.Parse}
  %show_val(c)
    : {Http.feed.go("HTTP/1.1 " ++ ((Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " ")))) ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HStat{0n, ""}})
       == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{_, Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))), 1n, [], None{}, ""}}) : Http.Parse}
  stat_gen(c, String.drop(st, String.length(Dec.show(c) ++ " ")), w, mb, hd, cl, " 1.1/PTTH", "HTTP/1.1", 6n, {==}, ge_100(c, h1), le_lt(c, 599n, h2), {==},
    Equal.trans(Bool, L.printable(Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " ")))), L.printable(st), True{},
      Equal.cong(String, Bool, z => L.printable(z), Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))), st, Equal.sym(String, st, Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))), st_eq(c, st, hs))),
      hp))

# ---------------------------------------------------------------------
# The header block of a response
# ---------------------------------------------------------------------

def plines_app(a: List<&2, KV>, +b: List<&2, KV>) -> {plines(List.append(&2, KV, a, b)) == plines(a) ++ plines(b) : String}:
  match a:
    case Nil{}:
      {==}
    case Con{kv, +r}:
      match kv:
        case KV{+k, +v}:
          Equal.trans(String, k ++ (": " ++ (v ++ ("\r\n" ++ plines(List.append(&2, KV, r, b))))), k ++ (": " ++ (v ++ ("\r\n" ++ (plines(r) ++ plines(b))))), (k ++ (": " ++ (v ++ ("\r\n" ++ plines(r))))) ++ plines(b),
            Equal.cong(String, String, z => k ++ (": " ++ (v ++ ("\r\n" ++ z))), plines(List.append(&2, KV, r, b)), plines(r) ++ plines(b), plines_app(r, b)),
            Equal.trans(String, k ++ (": " ++ (v ++ ("\r\n" ++ (plines(r) ++ plines(b))))), k ++ (": " ++ ((v ++ ("\r\n" ++ plines(r))) ++ plines(b))), (k ++ (": " ++ (v ++ ("\r\n" ++ plines(r))))) ++ plines(b),
              Equal.cong(String, String, z => k ++ (": " ++ z), v ++ ("\r\n" ++ (plines(r) ++ plines(b))), (v ++ ("\r\n" ++ plines(r))) ++ plines(b),
                Equal.sym(String, (v ++ ("\r\n" ++ plines(r))) ++ plines(b), v ++ ("\r\n" ++ (plines(r) ++ plines(b))), app_assoc(v, "\r\n" ++ plines(r), plines(b)))),
              Equal.sym(String, (k ++ (": " ++ (v ++ ("\r\n" ++ plines(r))))) ++ plines(b), k ++ (": " ++ ((v ++ ("\r\n" ++ plines(r))) ++ plines(b))), app_assoc(k, ": " ++ (v ++ ("\r\n" ++ plines(r))), plines(b)))))

def pok_app(a: List<&2, KV>, +b: List<&2, KV>, +ha: {pok(a) == True{} : Bool}, +hb: {pok(b) == True{} : Bool}) -> {pok(List.append(&2, KV, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{kv, +r}:
      match kv:
        case KV{+k, +v}:
          and_i(Bool.and(L.token(k), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(List.append(&2, KV, r, b))),
            and_l(Bool.and(L.token(k), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), ha),
            and_i(String.eq(Http.trim_ows(v), v), pok(List.append(&2, KV, r, b)),
              and_l(String.eq(Http.trim_ows(v), v), pok(r), and_r(Bool.and(L.token(k), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), ha)),
              pok_app(r, b, and_r(String.eq(Http.trim_ows(v), v), pok(r), and_r(Bool.and(L.token(k), L.no_ctl(v)), Bool.and(String.eq(Http.trim_ows(v), v), pok(r)), ha)), hb)))

def addall_app(a: List<&2, KV>, +b: List<&2, KV>, +t: List<&2, Hdr.Header>) -> {addall(List.append(&2, KV, a, b), t) == addall(b, addall(a, t)) : List<&2, Hdr.Header>}:
  match a:
    case Nil{}:
      {==}
    case Con{kv, +r}:
      match kv:
        case KV{+k, +v}:
          addall_app(r, b, Http.hdr_add(Http.canon(k), v, t))

def head_keep(+hs: List<&2, Hdr.Header>, +w: String, +c: Nat, +st: String, +mi: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
              +hok: {L.hdrs_resp_ok(hs) == True{} : Bool})
  -> {Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, hs, hd)}) : Http.Parse}:
  %Equal.sym(String, L.resp_hdr_lines(hs), plines(fl(hs)), txt(hs, hok))
    : {Http.feed.go(_ ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, hs, hd)}) : Http.Parse}
  Equal.trans(Http.Parse, Http.feed.go(plines(fl(hs)) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(fl(hs), []), hd)}), Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, hs, hd)}),
    flat(fl(hs), w, c, st, mi, [], None{}, [], mb, hd, cl, {==}, pok_fl(hs, hok)),
    Equal.cong(List<&2, Hdr.Header>, Http.Parse, z => Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, z, hd)}), addall(fl(hs), []), hs, addall_fl(hs, [], disj_nil(hs), hok)))

def head_close(+hs: List<&2, Hdr.Header>, +w: String, +c: Nat, +st: String, +mi: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
               +hok: {L.hdrs_resp_ok(hs) == True{} : Bool}, +hnc: {L.has_key("Connection", hs) == False{} : Bool})
  -> {Http.feed.go(L.resp_hdr_lines(hs) ++ ("Connection: close\r\n" ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hd)}) : Http.Parse}:
  %Equal.sym(String, L.resp_hdr_lines(hs), plines(fl(hs)), txt(hs, hok))
    : {Http.feed.go(_ ++ ("Connection: close\r\n" ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hd)}) : Http.Parse}
  %app_assoc(plines(fl(hs)), plines([KV{"Connection", "close"}]), "\r\n" ++ w)
    : {Http.feed.go(_, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hd)}) : Http.Parse}
  %plines_app(fl(hs), [KV{"Connection", "close"}])
    : {Http.feed.go(_ ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hd)}) : Http.Parse}
  Equal.trans(Http.Parse, Http.feed.go(plines(List.append(&2, KV, fl(hs), [KV{"Connection", "close"}])) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(List.append(&2, KV, fl(hs), [KV{"Connection", "close"}]), []), hd)}),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hd)}),
    flat(List.append(&2, KV, fl(hs), [KV{"Connection", "close"}]), w, c, st, mi, [], None{}, [], mb, hd, cl, {==}, pok_app(fl(hs), [KV{"Connection", "close"}], pok_fl(hs, hok), {==})),
    Equal.cong(List<&2, Hdr.Header>, Http.Parse, z => Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, z, hd)}),
      addall(List.append(&2, KV, fl(hs), [KV{"Connection", "close"}]), []), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]),
      Equal.trans(List<&2, Hdr.Header>, addall(List.append(&2, KV, fl(hs), [KV{"Connection", "close"}]), []), addall([KV{"Connection", "close"}], addall(fl(hs), [])), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]),
        addall_app(fl(hs), [KV{"Connection", "close"}], []),
        Equal.trans(List<&2, Hdr.Header>, addall([KV{"Connection", "close"}], addall(fl(hs), [])), addall([KV{"Connection", "close"}], hs), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]),
          Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => addall([KV{"Connection", "close"}], z), addall(fl(hs), []), hs, addall_fl(hs, [], disj_nil(hs), hok)),
          add_new("Connection", "close", hs, hnc)))))

# ---------------------------------------------------------------------
# What resp_base_ok says
# ---------------------------------------------------------------------

def rA(+c: Nat, +hs: List<&2, Hdr.Header>, +k: Bool) -> Bool:
  Bool.and(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.and(Bool.and(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs)))), Bool.not(L.has_key("Pragma", hs))))

def rF(+c: Nat, +hs: List<&2, Hdr.Header>) -> Bool:
  Bool.not(Bool.or(L.has_key("Transfer-Encoding", hs), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))))

def rB(+st: String, +c: Nat) -> Bool:
  String.starts_with(st, Dec.show(c) ++ " ")

def rC(+st: String, +hs: List<&2, Hdr.Header>) -> Bool:
  Bool.and(L.printable(st), L.hdrs_resp_ok(hs))

def rb_A(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +k: Bool, +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool}) -> {rA(c, hs, k) == True{} : Bool}:
  and_l(rA(c, hs, k), Bool.and(rB(st, c), Bool.and(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs)))), h)

def rb_B(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +k: Bool, +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool}) -> {rB(st, c) == True{} : Bool}:
  and_l(rB(st, c), Bool.and(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs))), and_r(rA(c, hs, k), Bool.and(rB(st, c), Bool.and(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs)))), h))

def rb_C(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +k: Bool, +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool}) -> {rC(st, hs) == True{} : Bool}:
  and_l(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs)), and_r(rB(st, c), Bool.and(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs))), and_r(rA(c, hs, k), Bool.and(rB(st, c), Bool.and(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs)))), h)))

def rb_F(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +k: Bool, +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool}) -> {rF(c, hs) == True{} : Bool}:
  and_r(L.bytes(b), rF(c, hs), and_r(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs)), and_r(rB(st, c), Bool.and(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs))), and_r(rA(c, hs, k), Bool.and(rB(st, c), Bool.and(rC(st, hs), Bool.and(L.bytes(b), rF(c, hs)))), h))))

def rA_ge(+c: Nat, +hs: List<&2, Hdr.Header>, +k: Bool, +h: {rA(c, hs, k) == True{} : Bool}) -> {Nat.is_ge(c, 200n) == True{} : Bool}:
  and_l(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), and_l(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.and(Bool.and(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs)))), Bool.not(L.has_key("Pragma", hs))), h))

def rA_le(+c: Nat, +hs: List<&2, Hdr.Header>, +k: Bool, +h: {rA(c, hs, k) == True{} : Bool}) -> {Nat.is_le(c, 599n) == True{} : Bool}:
  and_r(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), and_l(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.and(Bool.and(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs)))), Bool.not(L.has_key("Pragma", hs))), h))

def rA_rest(+c: Nat, +hs: List<&2, Hdr.Header>, +k: Bool, +h: {rA(c, hs, k) == True{} : Bool})
  -> {Bool.and(Bool.and(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs)))), Bool.not(L.has_key("Pragma", hs))) == True{} : Bool}:
  and_r(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.and(Bool.and(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs)))), Bool.not(L.has_key("Pragma", hs))), h)

def rA_close(+c: Nat, +hs: List<&2, Hdr.Header>, +k: Bool, +h: {rA(c, hs, k) == True{} : Bool}) -> {L.says_close(hs) == False{} : Bool}:
  not_t(L.says_close(hs), and_l(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs))), and_l(Bool.and(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs)))), Bool.not(L.has_key("Pragma", hs)), rA_rest(c, hs, k, h))))

def rA_conn(+c: Nat, +hs: List<&2, Hdr.Header>, +k: Bool, +h: {rA(c, hs, k) == True{} : Bool}) -> {Bool.or(k, Bool.not(L.has_key("Connection", hs))) == True{} : Bool}:
  and_r(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs))), and_l(Bool.and(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs)))), Bool.not(L.has_key("Pragma", hs)), rA_rest(c, hs, k, h)))

def rA_prag(+c: Nat, +hs: List<&2, Hdr.Header>, +k: Bool, +h: {rA(c, hs, k) == True{} : Bool}) -> {L.has_key("Pragma", hs) == False{} : Bool}:
  not_t(L.has_key("Pragma", hs), and_r(Bool.and(Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs)))), Bool.not(L.has_key("Pragma", hs)), rA_rest(c, hs, k, h)))

def rF_te(+c: Nat, +hs: List<&2, Hdr.Header>, +h: {rF(c, hs) == True{} : Bool}) -> {L.has_key("Transfer-Encoding", hs) == False{} : Bool}:
  or_f_l(L.has_key("Transfer-Encoding", hs), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n)), not_t(Bool.or(L.has_key("Transfer-Encoding", hs), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), h))

def rF_codes(+c: Nat, +hs: List<&2, Hdr.Header>, +h: {rF(c, hs) == True{} : Bool}) -> {Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n)) == False{} : Bool}:
  or_f_r(L.has_key("Transfer-Encoding", hs), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n)), not_t(Bool.or(L.has_key("Transfer-Encoding", hs), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), h))

def le_f(b: Nat, a: Nat, c: Nat, +hab: {Nat.is_lt(b, a) == True{} : Bool}, +h: {Nat.is_ge(c, a) == True{} : Bool}) -> {Nat.is_le(c, b) == False{} : Bool}:
  match b:
    case 0n:
      match a:
        case 0n:
          Empty.absurd({Nat.is_le(c, 0n) == False{} : Bool}, no_ft(hab))
        case 1n+ap:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(0n, 0n) == False{} : Bool}, no_ft(h))
            case 1n+cp:
              {==}
    case 1n+bp:
      match a:
        case 0n:
          Empty.absurd({Nat.is_le(c, 1n+bp) == False{} : Bool}, no_ft(hab))
        case 1n+ap:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(0n, 1n+bp) == False{} : Bool}, no_ft(h))
            case 1n+cp:
              le_f(bp, ap, cp, hab, h)

def eq_f(b: Nat, a: Nat, c: Nat, +hab: {Nat.is_lt(b, a) == True{} : Bool}, +h: {Nat.is_ge(c, a) == True{} : Bool}) -> {Nat.is_eq(c, b) == False{} : Bool}:
  match b:
    case 0n:
      match a:
        case 0n:
          Empty.absurd({Nat.is_eq(c, 0n) == False{} : Bool}, no_ft(hab))
        case 1n+ap:
          match c:
            case 0n:
              Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, no_ft(h))
            case 1n+cp:
              {==}
    case 1n+bp:
      match a:
        case 0n:
          Empty.absurd({Nat.is_eq(c, 1n+bp) == False{} : Bool}, no_ft(hab))
        case 1n+ap:
          match c:
            case 0n:
              Empty.absurd({Nat.is_eq(0n, 1n+bp) == False{} : Bool}, no_ft(h))
            case 1n+cp:
              eq_f(bp, ap, cp, hab, h)

def nb_f(+c: Nat, +h1: {Nat.is_ge(c, 200n) == True{} : Bool}, +h2: {Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n)) == False{} : Bool})
  -> {Http.no_body(False{}, c) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(c, 199n), False{}, le_f(199n, 200n, c, {==}, h1))
    : {Bool.or(Bool.and(Nat.is_ge(c, 100n), _), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(Nat.is_ge(c, 100n), False{}), False{}, and_f(Nat.is_ge(c, 100n)))
    : {Bool.or(_, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))) == False{} : Bool}
  h2

# ---------------------------------------------------------------------
# The head of a Content-Length response, read
# ---------------------------------------------------------------------

def hcl_of(+hs: List<&2, Hdr.Header>, +n: Nat, +hv: {L.vals_are("Content-Length", Dec.show(n), hs) == True{} : Bool})
  -> {Http.hdr_get("Content-Length", hs) == Some{[Dec.show(n)]} : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get("Content-Length", hs), L.hdr_get("Content-Length", hs), Some{[Dec.show(n)]},
    hdr_get_h("Content-Length", hs), one_val_eq(Dec.show(n), L.hdr_get("Content-Length", hs), hv))

def ct_close_f(+hs: List<&2, Hdr.Header>, +h: {L.says_close(hs) == False{} : Bool}) -> {Http.conn_token("close", hs) == False{} : Bool}:
  Equal.trans(Bool, Http.conn_token("close", hs), L.conn_token("close", hs), False{}, conn_token_h("close", hs), h)

def hcf_keep(+hs: List<&2, Hdr.Header>, +h: {L.says_close(hs) == False{} : Bool}) -> {Http.conn_fix(1n, hs) == hs : List<&2, Hdr.Header>}:
  %Equal.sym(Bool, Http.conn_token("close", hs), False{}, ct_close_f(hs, h))
    : {Http.conn_fix.of(_, hs) == hs : List<&2, Hdr.Header>}
  {==}

def hko_keep(+hs: List<&2, Hdr.Header>, +h: {L.says_close(hs) == False{} : Bool}) -> {Http.keep_of(1n, hs) == True{} : Bool}:
  %Equal.sym(Bool, Http.conn_token("close", hs), False{}, ct_close_f(hs, h)) : {Bool.not(_) == True{} : Bool}
  {==}

def hs_keep(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +mb: Maybe<&2, Nat>, +cl: Bool,
            +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, True{}}) == True{} : Bool},
            +hv: {L.vals_are("Content-Length", Dec.show(String.length(b)), hs) == True{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, True{}}), Http.Parse{mb, False{}, cl, Http.HStat{0n, ""}})
      == Http.Parse{mb, False{}, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", True{}})} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, True{}}), Http.Parse{mb, False{}, cl, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), Http.Parse{mb, False{}, cl, Http.HHdr{c, st, 1n, [], None{}, ""}}),
    Http.Parse{mb, False{}, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", True{}})},
    stat_st(c, st, L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), mb, False{}, cl,
      rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), rA_le(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)),
      and_l(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)), rb_B(c, st, hs, b, True{}, h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), Http.Parse{mb, False{}, cl, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.Parse{mb, False{}, cl, Http.framing(c, st, 1n, hs, False{})},
      Http.Parse{mb, False{}, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", True{}})},
      head_keep(hs, "", c, st, 1n, mb, False{}, cl, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h))),
      Equal.cong(Http.Ph, Http.Parse, ph => Http.Parse{mb, False{}, cl, ph}, Http.framing(c, st, 1n, hs, False{}), Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", True{}}),
        fr_cl_main(c, st, 1n, hs, hs, True{}, String.length(b),
          hdr_get_none("Pragma", hs, rA_prag(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))),
          hdr_get_none("Transfer-Encoding", hs, rF_te(c, hs, rb_F(c, st, hs, b, True{}, h))),
          hdr_del_none("Transfer-Encoding", hs, rF_te(c, hs, rb_F(c, st, hs, b, True{}, h))),
          hcf_keep(hs, rA_close(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))),
          hko_keep(hs, rA_close(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))),
          nb_f(c, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), rF_codes(c, hs, rb_F(c, st, hs, b, True{}, h))),
          eq_f(101n, 200n, c, {==}, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))),
          hcl_of(hs, String.length(b), hv),
          hdr_set_id("Content-Length", [Dec.show(String.length(b))], hs, hcl_of(hs, String.length(b), hv), and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)))))))

def hnc_of(+hs: List<&2, Hdr.Header>, +h: {Bool.or(False{}, Bool.not(L.has_key("Connection", hs))) == True{} : Bool}) -> {L.has_key("Connection", hs) == False{} : Bool}:
  not_t(L.has_key("Connection", hs), h)

def ct_close_t(+hs: List<&2, Hdr.Header>, +hnc: {L.has_key("Connection", hs) == False{} : Bool})
  -> {Http.conn_token("close", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])) == True{} : Bool}:
  Equal.cong(Maybe<&2, List<&2, String>>, Bool, m => Http.some_token("close", m),
    Http.hdr_get("Connection", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])), Http.hdr_get("Connection", [Hdr.Header{"Connection", ["close"]}]),
    hdr_get_skip("Connection", hs, [Hdr.Header{"Connection", ["close"]}], hnc))

def hcf_close(+hs: List<&2, Hdr.Header>, +hnc: {L.has_key("Connection", hs) == False{} : Bool})
  -> {Http.conn_fix(1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])) == hs : List<&2, Hdr.Header>}:
  %Equal.sym(Bool, Http.conn_token("close", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])), True{}, ct_close_t(hs, hnc))
    : {Http.conn_fix.of(_, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])) == hs : List<&2, Hdr.Header>}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del("Connection", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])),
      List.append(&2, Hdr.Header, Http.hdr_del("Connection", hs), Http.hdr_del("Connection", [Hdr.Header{"Connection", ["close"]}])), hdr_del_app("Connection", hs, [Hdr.Header{"Connection", ["close"]}]))
    : {_ == hs : List<&2, Hdr.Header>}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del("Connection", hs), hs, hdr_del_none("Connection", hs, hnc))
    : {List.append(&2, Hdr.Header, _, []) == hs : List<&2, Hdr.Header>}
  lapp_nil(Hdr.Header, hs)

def hko_close(+hs: List<&2, Hdr.Header>, +hnc: {L.has_key("Connection", hs) == False{} : Bool})
  -> {Http.keep_of(1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])) == False{} : Bool}:
  %Equal.sym(Bool, Http.conn_token("close", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])), True{}, ct_close_t(hs, hnc)) : {Bool.not(_) == False{} : Bool}
  {==}

def hte_close(+k: String, +hs: List<&2, Hdr.Header>, +h: {L.has_key(k, hs) == False{} : Bool}, +h2: {Http.hdr_get(k, [Hdr.Header{"Connection", ["close"]}]) == None{} : Maybe<&2, List<&2, String>>})
  -> {Http.hdr_get(k, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])) == None{} : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get(k, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])), Http.hdr_get(k, [Hdr.Header{"Connection", ["close"]}]), None{},
    hdr_get_skip(k, hs, [Hdr.Header{"Connection", ["close"]}], h), h2)

def hted_close(+hs: List<&2, Hdr.Header>, +h: {L.has_key("Transfer-Encoding", hs) == False{} : Bool})
  -> {Http.hdr_del("Transfer-Encoding", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])) == List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]) : List<&2, Hdr.Header>}:
  Equal.trans(List<&2, Hdr.Header>, Http.hdr_del("Transfer-Encoding", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])),
    List.append(&2, Hdr.Header, Http.hdr_del("Transfer-Encoding", hs), [Hdr.Header{"Connection", ["close"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]),
    hdr_del_app("Transfer-Encoding", hs, [Hdr.Header{"Connection", ["close"]}]),
    Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, z, [Hdr.Header{"Connection", ["close"]}]), Http.hdr_del("Transfer-Encoding", hs), hs, hdr_del_none("Transfer-Encoding", hs, h)))

def hs_close(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +mb: Maybe<&2, Nat>, +cl: Bool,
             +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}) == True{} : Bool},
             +hv: {L.vals_are("Content-Length", Dec.show(String.length(b)), hs) == True{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, False{}}), Http.Parse{mb, False{}, cl, Http.HStat{0n, ""}})
      == Http.Parse{mb, False{}, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", False{}})} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, False{}}), Http.Parse{mb, False{}, cl, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(hs) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), Http.Parse{mb, False{}, cl, Http.HHdr{c, st, 1n, [], None{}, ""}}),
    Http.Parse{mb, False{}, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", False{}})},
    stat_st(c, st, L.resp_hdr_lines(hs) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), mb, False{}, cl,
      rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), rA_le(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)),
      and_l(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)), rb_B(c, st, hs, b, False{}, h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(hs) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), Http.Parse{mb, False{}, cl, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.Parse{mb, False{}, cl, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), False{})},
      Http.Parse{mb, False{}, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", False{}})},
      head_close(hs, "", c, st, 1n, mb, False{}, cl, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)),
        hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)))),
      Equal.cong(Http.Ph, Http.Parse, ph => Http.Parse{mb, False{}, cl, ph},
        Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), False{}), Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", False{}}),
        fr_cl_main(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hs, False{}, String.length(b),
          hte_close("Pragma", hs, rA_prag(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), {==}),
          hte_close("Transfer-Encoding", hs, rF_te(c, hs, rb_F(c, st, hs, b, False{}, h)), {==}),
          hted_close(hs, rF_te(c, hs, rb_F(c, st, hs, b, False{}, h))),
          hcf_close(hs, hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)))),
          hko_close(hs, hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)))),
          nb_f(c, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), rF_codes(c, hs, rb_F(c, st, hs, b, False{}, h))),
          eq_f(101n, 200n, c, {==}, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))),
          hcl_of(hs, String.length(b), hv),
          hdr_set_id("Content-Length", [Dec.show(String.length(b))], hs, hcl_of(hs, String.length(b), hv), and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)))))))

# ---------------------------------------------------------------------
# Bodies and what follows
# ---------------------------------------------------------------------

# the body bytes kept (last first) after reading b under -max-body mb
def kacc(+mb: Maybe<&2, Nat>, b: String, +kept: Nat, +acc: String) -> String:
  match b:
    case SNil{}:
      acc
    case SCon{+c, +rest}:
      kacc(mb, rest, Http.pick(Nat, Http.room(mb, kept), 1n+kept, kept), Http.pick(String, Http.room(mb, kept), SCon{c, acc}, acc))

def kacc_none(b: String, +kept: Nat, +acc: String) -> {kacc(None{}, b, kept, acc) == String.reverse.go(b, acc) : String}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      kacc_none(rest, 1n+kept, SCon{c, acc})

def body_run(b: String, +c: Char, +r: Http.Resp, +acc: String, +kept: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(SCon{c, b}, Http.Parse{mb, hd, cl, Http.HLen{r, String.length(SCon{c, b}), acc, kept}})
      == Http.Parse{mb, hd, cl, Http.HDone{Http.with_body(r, String.reverse(kacc(mb, SCon{c, b}, kept, acc))), ""}} : Http.Parse}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c2, +rest}:
      body_run(rest, c2, r, Http.pick(String, Http.room(mb, kept), SCon{c, acc}, acc), Http.pick(Nat, Http.room(mb, kept), 1n+kept, kept), mb, hd, cl)

def done_run(x: String, +r: Http.Resp, +rest0: String, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(x, Http.Parse{mb, hd, cl, Http.HDone{r, rest0}}) == Http.Parse{mb, hd, cl, Http.HDone{r, String.reverse.go(x, rest0)}} : Http.Parse}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      done_run(t, r, SCon{c, rest0}, mb, hd, cl)

def finish(+r: Http.Resp, +rest: String, +mb: Maybe<&2, Nat>, +hd: Bool)
  -> {Http.done(Http.feed.go(rest, Http.Parse{mb, hd, False{}, Http.HDone{r, ""}})) == Some{Done{(r, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  %Equal.sym(Http.Parse, Http.feed.go(rest, Http.Parse{mb, hd, False{}, Http.HDone{r, ""}}), Http.Parse{mb, hd, False{}, Http.HDone{r, String.reverse.go(rest, "")}}, done_run(rest, r, "", mb, hd, False{}))
    : {Http.done(_) == Some{Done{(r, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %rev_rev(rest)
    : {Some{Done{(r, rev(rev(rest)))}} == Some{Done{(r, _)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  {==}

def body_none(b: String, +c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +k: Bool, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(b, Http.Parse{None{}, hd, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", k})}) == Http.Parse{None{}, hd, cl, Http.HDone{Http.Resp{c, st, hs, b, k}, ""}} : Http.Parse}:
  match b:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      %Equal.sym(Http.Parse, Http.feed.go(SCon{x, t}, Http.Parse{None{}, hd, cl, Http.HLen{Http.Resp{c, st, hs, "", k}, String.length(SCon{x, t}), "", 0n}}),
          Http.Parse{None{}, hd, cl, Http.HDone{Http.with_body(Http.Resp{c, st, hs, "", k}, String.reverse(kacc(None{}, SCon{x, t}, 0n, ""))), ""}},
          body_run(t, x, Http.Resp{c, st, hs, "", k}, "", 0n, None{}, hd, cl)) : {_ == Http.Parse{None{}, hd, cl, Http.HDone{Http.Resp{c, st, hs, SCon{x, t}, k}, ""}} : Http.Parse}
      %Equal.sym(String, kacc(None{}, SCon{x, t}, 0n, ""), String.reverse.go(SCon{x, t}, ""), kacc_none(SCon{x, t}, 0n, "")) : {Http.Parse{None{}, hd, cl, Http.HDone{Http.Resp{c, st, hs, String.reverse(_), k}, ""}} == Http.Parse{None{}, hd, cl, Http.HDone{Http.Resp{c, st, hs, SCon{x, t}, k}, ""}} : Http.Parse}
      %rev_rev(SCon{x, t}) : {Http.Parse{None{}, hd, cl, Http.HDone{Http.Resp{c, st, hs, rev(rev(SCon{x, t})), k}, ""}} == Http.Parse{None{}, hd, cl, Http.HDone{Http.Resp{c, st, hs, _, k}, ""}} : Http.Parse}
      {==}

# ---------------------------------------------------------------------
# http_cl
# ---------------------------------------------------------------------

def head_cl(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, k: Bool, +mb: Maybe<&2, Nat>, +cl: Bool,
            +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool},
            +hv: {L.vals_are("Content-Length", Dec.show(String.length(b)), hs) == True{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, k}), Http.Parse{mb, False{}, cl, Http.HStat{0n, ""}})
      == Http.Parse{mb, False{}, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", k})} : Http.Parse}:
  match k:
    case True{}:
      hs_keep(c, st, hs, b, mb, cl, h, hv)
    case False{}:
      hs_close(c, st, hs, b, mb, cl, h, hv)

# feeding a ++ b ++ c is feeding each in turn
def feed3(+a: String, +b: String, +c: String, +p: Http.Parse)
  -> {Http.feed.go((a ++ b) ++ c, p) == Http.feed.go(c, Http.feed.go(b, Http.feed.go(a, p))) : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go((a ++ b) ++ c, p), Http.feed.go(c, Http.feed.go(a ++ b, p)), Http.feed.go(c, Http.feed.go(b, Http.feed.go(a, p))),
    Equal.sym(Http.Parse, Http.feed.go(c, Http.feed.go(a ++ b, p)), Http.feed.go((a ++ b) ++ c, p), split_go(a ++ b, c, p)),
    Equal.cong(Http.Parse, Http.Parse, q => Http.feed.go(c, q), Http.feed.go(a ++ b, p), Http.feed.go(b, Http.feed.go(a, p)),
      Equal.sym(Http.Parse, Http.feed.go(b, Http.feed.go(a, p)), Http.feed.go(a ++ b, p), split_go(a, b, p))))

def cl_main(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +k: Bool, +rest: String,
            +h: {L.resp_cl_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool})
  -> {L.parse_of(None{}, False{}, L.render_cl(Http.Resp{c, st, hs, b, k}) ++ rest) == Some{Done{(Http.Resp{c, st, hs, b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  %Equal.sym(Http.Parse, Http.feed.go((L.render_head(Http.Resp{c, st, hs, b, k}) ++ b) ++ rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.feed.go(rest, Http.feed.go(b, Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, k}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}))),
      feed3(L.render_head(Http.Resp{c, st, hs, b, k}), b, rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}))
    : {Http.done(_) == Some{Done{(Http.Resp{c, st, hs, b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %Equal.sym(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, k}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", k})},
      head_cl(c, st, hs, b, k, None{}, False{},
        and_l(L.resp_base_ok(Http.Resp{c, st, hs, b, k}), L.vals_are("Content-Length", Dec.show(String.length(b)), hs), h),
        and_r(L.resp_base_ok(Http.Resp{c, st, hs, b, k}), L.vals_are("Content-Length", Dec.show(String.length(b)), hs), h)))
    : {Http.done(Http.feed.go(rest, Http.feed.go(b, _))) == Some{Done{(Http.Resp{c, st, hs, b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %Equal.sym(Http.Parse, Http.feed.go(b, Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", k})}),
      Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, k}, ""}}, body_none(b, c, st, hs, k, False{}, False{}))
    : {Http.done(Http.feed.go(rest, _)) == Some{Done{(Http.Resp{c, st, hs, b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  finish(Http.Resp{c, st, hs, b, k}, rest, None{}, False{})

def L.http_cl(r, rest, h):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      cl_main(c, st, hs, b, k, rest, h)

# ---------------------------------------------------------------------
# -max-body: the first m bytes are kept
# ---------------------------------------------------------------------

def lt_self0(k: Nat) -> {Nat.is_lt(k, Nat.add(k, 0n)) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      lt_self0(kp)

def lt_add_s(k: Nat, -j: Nat) -> {Nat.is_lt(k, Nat.add(k, 1n+j)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+kp:
      lt_add_s(kp, j)

def take0(s: String) -> {String.take(s, 0n) == "" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# with j bytes of room left, the first j bytes are kept
def ks(b: String, +kept: Nat, +acc: String, +m: Nat, j: Nat, +e: {Nat.add(kept, j) == m : Nat})
  -> {kacc(Some{m}, b, kept, acc) == String.reverse.go(String.take(b, j), acc) : String}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match j:
        case 0n:
          %Equal.sym(Bool, Nat.is_lt(kept, m), False{}, Equal.trans(Bool, Nat.is_lt(kept, m), Nat.is_lt(kept, Nat.add(kept, 0n)), False{},
              Equal.cong(Nat, Bool, z => Nat.is_lt(kept, z), m, Nat.add(kept, 0n), Equal.sym(Nat, Nat.add(kept, 0n), m, e)), lt_self0(kept)))
            : {kacc(Some{m}, rest, Http.pick(Nat, _, 1n+kept, kept), Http.pick(String, _, SCon{c, acc}, acc)) == acc : String}
          Equal.trans(String, kacc(Some{m}, rest, kept, acc), String.reverse.go(String.take(rest, 0n), acc), acc,
            ks(rest, kept, acc, m, 0n, e), Equal.cong(String, String, z => String.reverse.go(z, acc), String.take(rest, 0n), "", take0(rest)))
        case 1n+jp:
          %Equal.sym(Bool, Nat.is_lt(kept, m), True{}, Equal.trans(Bool, Nat.is_lt(kept, m), Nat.is_lt(kept, Nat.add(kept, 1n+jp)), True{},
              Equal.cong(Nat, Bool, z => Nat.is_lt(kept, z), m, Nat.add(kept, 1n+jp), Equal.sym(Nat, Nat.add(kept, 1n+jp), m, e)), lt_add_s(kept, jp)))
            : {kacc(Some{m}, rest, Http.pick(Nat, _, 1n+kept, kept), Http.pick(String, _, SCon{c, acc}, acc)) == String.reverse.go(String.take(SCon{c, rest}, 1n+jp), acc) : String}
          ks(rest, 1n+kept, SCon{c, acc}, m, jp, Equal.trans(Nat, 1n+Nat.add(kept, jp), Nat.add(kept, 1n+jp), m, N.add_succ(kept, jp), e))

def body_some(b: String, +m: Nat, +c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +k: Bool, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(b, Http.Parse{Some{m}, hd, cl, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", k})}) == Http.Parse{Some{m}, hd, cl, Http.HDone{Http.Resp{c, st, hs, String.take(b, m), k}, ""}} : Http.Parse}:
  match b:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      %Equal.sym(Http.Parse, Http.feed.go(SCon{x, t}, Http.Parse{Some{m}, hd, cl, Http.HLen{Http.Resp{c, st, hs, "", k}, String.length(SCon{x, t}), "", 0n}}),
          Http.Parse{Some{m}, hd, cl, Http.HDone{Http.with_body(Http.Resp{c, st, hs, "", k}, String.reverse(kacc(Some{m}, SCon{x, t}, 0n, ""))), ""}},
          body_run(t, x, Http.Resp{c, st, hs, "", k}, "", 0n, Some{m}, hd, cl)) : {_ == Http.Parse{Some{m}, hd, cl, Http.HDone{Http.Resp{c, st, hs, String.take(SCon{x, t}, m), k}, ""}} : Http.Parse}
      %Equal.sym(String, kacc(Some{m}, SCon{x, t}, 0n, ""), String.reverse.go(String.take(SCon{x, t}, m), ""), ks(SCon{x, t}, 0n, "", m, m, {==}))
        : {Http.Parse{Some{m}, hd, cl, Http.HDone{Http.Resp{c, st, hs, String.reverse(_), k}, ""}} == Http.Parse{Some{m}, hd, cl, Http.HDone{Http.Resp{c, st, hs, String.take(SCon{x, t}, m), k}, ""}} : Http.Parse}
      %rev_rev(String.take(SCon{x, t}, m))
        : {Http.Parse{Some{m}, hd, cl, Http.HDone{Http.Resp{c, st, hs, rev(rev(String.take(SCon{x, t}, m))), k}, ""}} == Http.Parse{Some{m}, hd, cl, Http.HDone{Http.Resp{c, st, hs, _, k}, ""}} : Http.Parse}
      {==}

def max_main(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +k: Bool, +m: Nat, +rest: String,
             +h: {L.resp_cl_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool})
  -> {L.parse_of(Some{m}, False{}, L.render_cl(Http.Resp{c, st, hs, b, k}) ++ rest) == Some{Done{(Http.Resp{c, st, hs, String.take(b, m), k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  %Equal.sym(Http.Parse, Http.feed.go((L.render_head(Http.Resp{c, st, hs, b, k}) ++ b) ++ rest, Http.Parse{Some{m}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.feed.go(rest, Http.feed.go(b, Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, k}), Http.Parse{Some{m}, False{}, False{}, Http.HStat{0n, ""}}))),
      feed3(L.render_head(Http.Resp{c, st, hs, b, k}), b, rest, Http.Parse{Some{m}, False{}, False{}, Http.HStat{0n, ""}}))
    : {Http.done(_) == Some{Done{(Http.Resp{c, st, hs, String.take(b, m), k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %Equal.sym(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, b, k}), Http.Parse{Some{m}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.Parse{Some{m}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", k})},
      head_cl(c, st, hs, b, k, Some{m}, False{},
        and_l(L.resp_base_ok(Http.Resp{c, st, hs, b, k}), L.vals_are("Content-Length", Dec.show(String.length(b)), hs), h),
        and_r(L.resp_base_ok(Http.Resp{c, st, hs, b, k}), L.vals_are("Content-Length", Dec.show(String.length(b)), hs), h)))
    : {Http.done(Http.feed.go(rest, Http.feed.go(b, _))) == Some{Done{(Http.Resp{c, st, hs, String.take(b, m), k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %Equal.sym(Http.Parse, Http.feed.go(b, Http.Parse{Some{m}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", k})}),
      Http.Parse{Some{m}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, String.take(b, m), k}, ""}}, body_some(b, m, c, st, hs, k, False{}, False{}))
    : {Http.done(Http.feed.go(rest, _)) == Some{Done{(Http.Resp{c, st, hs, String.take(b, m), k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  finish(Http.Resp{c, st, hs, String.take(b, m), k}, rest, Some{m}, False{})

def L.http_max_body(r, m, rest, h):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      max_main(c, st, hs, b, k, m, rest, h)

# ---------------------------------------------------------------------
# http_partial: mid-body, the body so far
# ---------------------------------------------------------------------

def partial_run(t: String, +r: Http.Resp, n: Nat, +acc: String, +kept: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
                +h: {Nat.is_lt(String.length(t), n) == True{} : Bool})
  -> {Http.partial(Http.feed.go(t, Http.Parse{mb, hd, cl, Http.HLen{r, n, acc, kept}})) == String.reverse(kacc(mb, t, kept, acc)) : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match n:
        case 0n:
          Empty.absurd({Http.partial(Http.feed.go(SCon{c, rest}, Http.Parse{mb, hd, cl, Http.HLen{r, 0n, acc, kept}})) == String.reverse(kacc(mb, SCon{c, rest}, kept, acc)) : String}, no_ft(h))
        case 1n+np:
          match np:
            case 0n:
              Empty.absurd({Http.partial(Http.feed.go(SCon{c, rest}, Http.Parse{mb, hd, cl, Http.HLen{r, 1n, acc, kept}})) == String.reverse(kacc(mb, SCon{c, rest}, kept, acc)) : String},
                N.lt_zero(String.length(rest), h))
            case 1n+(+nq):
              partial_run(rest, r, 1n+nq, Http.pick(String, Http.room(mb, kept), SCon{c, acc}, acc), Http.pick(Nat, Http.room(mb, kept), 1n+kept, kept), mb, hd, cl, h)

def len_take_lt(b: String, k: Nat, +h: {Nat.is_lt(k, String.length(b)) == True{} : Bool}) -> {Nat.is_lt(String.length(String.take(b, k)), String.length(b)) == True{} : Bool}:
  match b:
    case SNil{}:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.lt_zero(k, h))
    case SCon{c, +rest}:
      match k:
        case 0n:
          {==}
        case 1n+kp:
          len_take_lt(rest, kp, h)

def take_take(b: String, k: Nat) -> {String.take(String.take(b, k), k) == String.take(b, k) : String}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match k:
        case 0n:
          {==}
        case 1n+kp:
          Equal.cong(String, String, z => SCon{c, z}, String.take(String.take(rest, kp), kp), String.take(rest, kp), take_take(rest, kp))

def kept_take(m: Maybe<&2, Nat>, +t: String, +k: Nat)
  -> {String.reverse(kacc(m, String.take(t, k), 0n, "")) == String.take(String.take(t, k), Maybe.default(&2, Nat, m, k)) : String}:
  match m:
    case None{}:
      %Equal.sym(String, kacc(None{}, String.take(t, k), 0n, ""), String.reverse.go(String.take(t, k), ""), kacc_none(String.take(t, k), 0n, ""))
        : {String.reverse(_) == String.take(String.take(t, k), k) : String}
      %Equal.sym(String, String.take(String.take(t, k), k), String.take(t, k), take_take(t, k)) : {rev(rev(String.take(t, k))) == _ : String}
      rev_rev(String.take(t, k))
    case Some{+mm}:
      %Equal.sym(String, kacc(Some{mm}, String.take(t, k), 0n, ""), String.reverse.go(String.take(String.take(t, k), mm), ""), ks(String.take(t, k), 0n, "", mm, mm, {==}))
        : {String.reverse(_) == String.take(String.take(t, k), mm) : String}
      rev_rev(String.take(String.take(t, k), mm))

def partial_main(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, b: String, +k: Bool, +n: Nat, +m: Maybe<&2, Nat>,
                 +h0: {L.resp_cl_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool}, +h1: {Nat.is_lt(n, String.length(b)) == True{} : Bool})
  -> {Http.partial(Http.feed(Http.start(m, False{}), L.render_head(Http.Resp{c, st, hs, b, k}) ++ String.take(b, n)))
      == String.take(String.take(b, n), Maybe.default(&2, Nat, m, n)) : String}:
  match b:
    case SNil{}:
      Empty.absurd({Http.partial(Http.feed(Http.start(m, False{}), L.render_head(Http.Resp{c, st, hs, "", k}) ++ String.take("", n))) == String.take(String.take("", n), Maybe.default(&2, Nat, m, n)) : String},
        N.lt_zero(n, h1))
    case SCon{+x, +t}:
      %Equal.sym(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, SCon{x, t}, k}) ++ String.take(SCon{x, t}, n), Http.Parse{m, False{}, False{}, Http.HStat{0n, ""}}),
          Http.feed.go(String.take(SCon{x, t}, n), Http.feed.go(L.render_head(Http.Resp{c, st, hs, SCon{x, t}, k}), Http.Parse{m, False{}, False{}, Http.HStat{0n, ""}})),
          Equal.sym(Http.Parse, Http.feed.go(String.take(SCon{x, t}, n), Http.feed.go(L.render_head(Http.Resp{c, st, hs, SCon{x, t}, k}), Http.Parse{m, False{}, False{}, Http.HStat{0n, ""}})),
            Http.feed.go(L.render_head(Http.Resp{c, st, hs, SCon{x, t}, k}) ++ String.take(SCon{x, t}, n), Http.Parse{m, False{}, False{}, Http.HStat{0n, ""}}),
            split_go(L.render_head(Http.Resp{c, st, hs, SCon{x, t}, k}), String.take(SCon{x, t}, n), Http.Parse{m, False{}, False{}, Http.HStat{0n, ""}})))
        : {Http.partial(_) == String.take(String.take(SCon{x, t}, n), Maybe.default(&2, Nat, m, n)) : String}
      %Equal.sym(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, SCon{x, t}, k}), Http.Parse{m, False{}, False{}, Http.HStat{0n, ""}}),
          Http.Parse{m, False{}, False{}, Http.fr_len(Some{String.length(SCon{x, t})}, Http.Resp{c, st, hs, "", k})},
          head_cl(c, st, hs, SCon{x, t}, k, m, False{},
            and_l(L.resp_base_ok(Http.Resp{c, st, hs, SCon{x, t}, k}), L.vals_are("Content-Length", Dec.show(String.length(SCon{x, t})), hs), h0),
            and_r(L.resp_base_ok(Http.Resp{c, st, hs, SCon{x, t}, k}), L.vals_are("Content-Length", Dec.show(String.length(SCon{x, t})), hs), h0)))
        : {Http.partial(Http.feed.go(String.take(SCon{x, t}, n), _)) == String.take(String.take(SCon{x, t}, n), Maybe.default(&2, Nat, m, n)) : String}
      Equal.trans(String, Http.partial(Http.feed.go(String.take(SCon{x, t}, n), Http.Parse{m, False{}, False{}, Http.HLen{Http.Resp{c, st, hs, "", k}, String.length(SCon{x, t}), "", 0n}})),
        String.reverse(kacc(m, String.take(SCon{x, t}, n), 0n, "")), String.take(String.take(SCon{x, t}, n), Maybe.default(&2, Nat, m, n)),
        partial_run(String.take(SCon{x, t}, n), Http.Resp{c, st, hs, "", k}, String.length(SCon{x, t}), "", 0n, m, False{}, False{}, len_take_lt(SCon{x, t}, n, h1)),
        kept_take(m, SCon{x, t}, n))

def L.http_partial(r, k, m, h0, h1):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +kk}:
      partial_main(c, st, hs, b, kk, k, m, h0, h1)

# ---------------------------------------------------------------------
# http_waits: no answer before the last byte
# ---------------------------------------------------------------------

def fph(x: String, ph: Http.Ph, +mb: Maybe<&2, Nat>, +hd: Bool) -> Http.Ph:
  match x:
    case SNil{}:
      ph
    case SCon{+c, +t}:
      fph(t, Http.step_ph(ph, mb, hd, c), mb, hd)

def feed_fph(x: String, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool, ph: Http.Ph)
  -> {Http.feed.go(x, Http.Parse{mb, hd, cl, ph}) == Http.Parse{mb, hd, cl, fph(x, ph, mb, hd)} : Http.Parse}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      feed_fph(t, mb, hd, cl, Http.step_ph(ph, mb, hd, c))

def fph_fail(x: String, +m: String, +mb: Maybe<&2, Nat>, +hd: Bool) -> {fph(x, Http.HFail{m}, mb, hd) == Http.HFail{m} : Http.Ph}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      fph_fail(t, m, mb, hd)

def fph_done(x: String, +r: Http.Resp, +rest: String, +mb: Maybe<&2, Nat>, +hd: Bool) -> {fph(x, Http.HDone{r, rest}, mb, hd) == Http.HDone{r, String.reverse.go(x, rest)} : Http.Ph}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      fph_done(t, r, SCon{c, rest}, mb, hd)

def take_drop(s: String, k: Nat) -> {String.take(s, k) ++ String.drop(s, k) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match k:
        case 0n:
          {==}
        case 1n+kp:
          Equal.cong(String, String, z => SCon{c, z}, String.take(rest, kp) ++ String.drop(rest, kp), rest, take_drop(rest, kp))

def drop_ne(s: String, k: Nat, +h: {Nat.is_lt(k, String.length(s)) == True{} : Bool}) -> {String.is_empty(String.drop(s, k)) == False{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({String.is_empty(String.drop(SNil{}, k)) == False{} : Bool}, N.lt_zero(k, h))
    case SCon{c, +rest}:
      match k:
        case 0n:
          {==}
        case 1n+kp:
          drop_ne(rest, kp, h)

def res_rest(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> String:
  match m:
    case None{}:
      ""
    case Some{res}:
      match res:
        case Fail{e}:
          ""
        case Done{p}:
          match p:
            case (a, b):
              b

def res_done(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{res}:
      match res:
        case Fail{e}:
          False{}
        case Done{p}:
          True{}

def ne_revgo(d: String, +acc: String, +h: {String.is_empty(d) == False{} : Bool}) -> {String.is_empty(String.reverse.go(d, acc)) == False{} : Bool}:
  match d:
    case SNil{}:
      Empty.absurd({String.is_empty(acc) == False{} : Bool}, no_tf(h))
    case SCon{+c, +t}:
      %Equal.sym(String, String.reverse.go(t, SCon{c, acc}), rev(t) ++ SCon{c, acc}, revacc(t, SCon{c, acc})) : {String.is_empty(_) == False{} : Bool}
      empty_app(rev(t), c, acc)

# reading on from a prefix that already answered can't answer with nothing left
def wt(ph: Http.Ph, +d: String, +r: Http.Resp, +hne: {String.is_empty(d) == False{} : Bool},
       +hf: {Http.done_open(fph(d, ph, None{}, False{})) == Some{Done{(r, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>})
  -> {Http.done_open(ph) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  match ph:
    case Http.HStat{n, line}:
      {==}
    case Http.HHdr{code, status, minor, hs, pend, line}:
      {==}
    case Http.HLen{rr, left, body, kept}:
      {==}
    case Http.HChSize{rr, line, body, kept}:
      {==}
    case Http.HChData{rr, left, body, kept}:
      {==}
    case Http.HChCR{rr, body, kept}:
      {==}
    case Http.HChLF{rr, body, kept}:
      {==}
    case Http.HTrail{rr, line, body}:
      {==}
    case Http.HClose{rr, body, kept}:
      {==}
    case Http.HDone{+rr, +rest}:
      Empty.absurd({Http.done_open(Http.HDone{rr, rest}) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>},
        no_tf(Equal.trans(Bool, True{}, String.is_empty(rev(String.reverse.go(d, rest))), False{},
          Equal.cong(String, Bool, z => String.is_empty(z), "", rev(String.reverse.go(d, rest)),
            Equal.sym(String, rev(String.reverse.go(d, rest)), "",
              Equal.trans(String, rev(String.reverse.go(d, rest)), res_rest(Http.done_open(fph(d, Http.HDone{rr, rest}, None{}, False{}))), "",
                Equal.cong(Http.Ph, String, q => res_rest(Http.done_open(q)), Http.HDone{rr, String.reverse.go(d, rest)}, fph(d, Http.HDone{rr, rest}, None{}, False{}),
                  Equal.sym(Http.Ph, fph(d, Http.HDone{rr, rest}, None{}, False{}), Http.HDone{rr, String.reverse.go(d, rest)}, fph_done(d, rr, rest, None{}, False{}))),
                Equal.cong(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, String, q => res_rest(q), Http.done_open(fph(d, Http.HDone{rr, rest}, None{}, False{})), Some{Done{(r, "")}}, hf)))),
          Equal.trans(Bool, String.is_empty(rev(String.reverse.go(d, rest))), String.is_empty(String.reverse.go(d, rest)), False{},
            empty_rev(String.reverse.go(d, rest)), ne_revgo(d, rest, hne)))))
    case Http.HFail{+msg}:
      Empty.absurd({Http.done_open(Http.HFail{msg}) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>},
        no_ft(Equal.trans(Bool, False{}, res_done(Http.done_open(fph(d, Http.HFail{msg}, None{}, False{}))), True{},
          Equal.cong(Http.Ph, Bool, q => res_done(Http.done_open(q)), Http.HFail{msg}, fph(d, Http.HFail{msg}, None{}, False{}),
            Equal.sym(Http.Ph, fph(d, Http.HFail{msg}, None{}, False{}), Http.HFail{msg}, fph_fail(d, msg, None{}, False{}))),
          Equal.cong(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, Bool, q => res_done(q), Http.done_open(fph(d, Http.HFail{msg}, None{}, False{})), Some{Done{(r, "")}}, hf))))

def waits_gen(+s: String, +r: Http.Resp, +n: Nat,
              +full: {L.parse_of(None{}, False{}, s ++ "") == Some{Done{(r, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>},
              +h1: {Nat.is_lt(n, String.length(s)) == True{} : Bool})
  -> {L.parse_of(None{}, False{}, String.take(s, n)) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  Equal.trans(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>,
    Http.done(Http.feed.go(String.take(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
    Http.done_open(fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{})), None{},
    Equal.cong(Http.Parse, Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, p => Http.done(p),
      Http.feed.go(String.take(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.Parse{None{}, False{}, False{}, fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{})},
      feed_fph(String.take(s, n), None{}, False{}, False{}, Http.HStat{0n, ""})),
    wt(fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{}), String.drop(s, n), r, drop_ne(s, n, h1),
      Equal.trans(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>,
        Http.done_open(fph(String.drop(s, n), fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{}), None{}, False{})),
        Http.done(Http.feed.go(s ++ "", Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})), Some{Done{(r, "")}},
        Equal.sym(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>,
          Http.done(Http.feed.go(s ++ "", Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
          Http.done_open(fph(String.drop(s, n), fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{}), None{}, False{})),
          Equal.cong(Http.Parse, Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, p => Http.done(p),
            Http.feed.go(s ++ "", Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
            Http.Parse{None{}, False{}, False{}, fph(String.drop(s, n), fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{}), None{}, False{})},
            Equal.trans(Http.Parse, Http.feed.go(s ++ "", Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
              Http.feed.go(String.take(s, n) ++ String.drop(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
              Http.Parse{None{}, False{}, False{}, fph(String.drop(s, n), fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{}), None{}, False{})},
              Equal.cong(String, Http.Parse, z => Http.feed.go(z, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}), s ++ "", String.take(s, n) ++ String.drop(s, n),
                Equal.trans(String, s ++ "", s, String.take(s, n) ++ String.drop(s, n), app_nil(s), Equal.sym(String, String.take(s, n) ++ String.drop(s, n), s, take_drop(s, n)))),
              Equal.trans(Http.Parse, Http.feed.go(String.take(s, n) ++ String.drop(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
                Http.feed.go(String.drop(s, n), Http.feed.go(String.take(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
                Http.Parse{None{}, False{}, False{}, fph(String.drop(s, n), fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{}), None{}, False{})},
                Equal.sym(Http.Parse, Http.feed.go(String.drop(s, n), Http.feed.go(String.take(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
                  Http.feed.go(String.take(s, n) ++ String.drop(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
                  split_go(String.take(s, n), String.drop(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
                Equal.trans(Http.Parse, Http.feed.go(String.drop(s, n), Http.feed.go(String.take(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
                  Http.feed.go(String.drop(s, n), Http.Parse{None{}, False{}, False{}, fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{})}),
                  Http.Parse{None{}, False{}, False{}, fph(String.drop(s, n), fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{}), None{}, False{})},
                  Equal.cong(Http.Parse, Http.Parse, p => Http.feed.go(String.drop(s, n), p),
                    Http.feed.go(String.take(s, n), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
                    Http.Parse{None{}, False{}, False{}, fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{})},
                    feed_fph(String.take(s, n), None{}, False{}, False{}, Http.HStat{0n, ""})),
                  feed_fph(String.drop(s, n), None{}, False{}, False{}, fph(String.take(s, n), Http.HStat{0n, ""}, None{}, False{}))))))),
        full)))

def L.http_waits(r, k, h0, h1):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +kk}:
      waits_gen(L.render_cl(Http.Resp{c, st, hs, b, kk}), Http.Resp{c, st, hs, b, kk}, k, cl_main(c, st, hs, b, kk, "", h0), h1)

# ---------------------------------------------------------------------
# http_until_close: a body framed by the close
# ---------------------------------------------------------------------

def fr_eof_main(+c: Nat, +st: String, +mi: Nat, +h: List<&2, Hdr.Header>, +hs: List<&2, Hdr.Header>,
    +hp: {Http.hdr_get("Pragma", h) == None{} : Maybe<&2, List<&2, String>>},
    +hte: {Http.hdr_get("Transfer-Encoding", h) == None{} : Maybe<&2, List<&2, String>>},
    +hted: {Http.hdr_del("Transfer-Encoding", h) == h : List<&2, Hdr.Header>},
    +hcf: {Http.conn_fix(mi, h) == hs : List<&2, Hdr.Header>},
    +hnb: {Http.no_body(False{}, c) == False{} : Bool},
    +hcl: {Http.hdr_get("Content-Length", hs) == None{} : Maybe<&2, List<&2, String>>})
  -> {Http.framing(c, st, mi, h, False{}) == Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n} : Http.Ph}:
  %Equal.sym(List<&2, Hdr.Header>, Http.pragma_fix(h), h, pf_id(h, hp))
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", _), Http.Resp{c, st, Http.conn_fix(mi, Http.hdr_del("Transfer-Encoding", _)), "", Bool.and(Http.keep_of(mi, _), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n} : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del("Transfer-Encoding", h), h, hted)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, Http.conn_fix(mi, _), "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n} : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.conn_fix(mi, h), hs, hcf)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, _, "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n} : Http.Ph}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Transfer-Encoding", h), None{}, hte)
    : {Http.fr_body(Http.no_body(False{}, c), c, mi, _, Http.Resp{c, st, hs, "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n} : Http.Ph}
  %Equal.sym(Bool, Http.no_body(False{}, c), False{}, hnb)
    : {Http.fr_body(_, c, mi, None{}, Http.Resp{c, st, hs, "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n} : Http.Ph}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Content-Length", hs), None{}, hcl)
    : {Http.fr_cl(_, Http.Resp{c, st, hs, "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))}) == Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n} : Http.Ph}
  {==}

def kk(+mb: Maybe<&2, Nat>, b: String, +kept: Nat) -> Nat:
  match b:
    case SNil{}:
      kept
    case SCon{+c, +rest}:
      kk(mb, rest, Http.pick(Nat, Http.room(mb, kept), 1n+kept, kept))

def close_run(b: String, +r: Http.Resp, +acc: String, +kept: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(b, Http.Parse{mb, hd, cl, Http.HClose{r, acc, kept}}) == Http.Parse{mb, hd, cl, Http.HClose{r, kacc(mb, b, kept, acc), kk(mb, b, kept)}} : Http.Parse}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      close_run(rest, r, Http.pick(String, Http.room(mb, kept), SCon{c, acc}, acc), Http.pick(Nat, Http.room(mb, kept), 1n+kept, kept), mb, hd, cl)

def plain_state(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +mb: Maybe<&2, Nat>, +cl: Bool,
                +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}) == True{} : Bool}, +hcl: {L.has_key("Content-Length", hs) == False{} : Bool})
  -> {Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}), Http.Parse{mb, False{}, cl, Http.HStat{0n, ""}})
      == Http.Parse{mb, False{}, cl, Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n}} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}), Http.Parse{mb, False{}, cl, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), Http.Parse{mb, False{}, cl, Http.HHdr{c, st, 1n, [], None{}, ""}}),
    Http.Parse{mb, False{}, cl, Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n}},
    stat_st(c, st, L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), mb, False{}, cl,
      rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), rA_le(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)),
      and_l(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)), rb_B(c, st, hs, b, False{}, h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), Http.Parse{mb, False{}, cl, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.Parse{mb, False{}, cl, Http.framing(c, st, 1n, hs, False{})},
      Http.Parse{mb, False{}, cl, Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n}},
      head_keep(hs, "", c, st, 1n, mb, False{}, cl, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h))),
      Equal.cong(Http.Ph, Http.Parse, ph => Http.Parse{mb, False{}, cl, ph}, Http.framing(c, st, 1n, hs, False{}), Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n},
        fr_eof_main(c, st, 1n, hs, hs,
          hdr_get_none("Pragma", hs, rA_prag(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))),
          hdr_get_none("Transfer-Encoding", hs, rF_te(c, hs, rb_F(c, st, hs, b, False{}, h))),
          hdr_del_none("Transfer-Encoding", hs, rF_te(c, hs, rb_F(c, st, hs, b, False{}, h))),
          hcf_keep(hs, rA_close(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))),
          nb_f(c, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), rF_codes(c, hs, rb_F(c, st, hs, b, False{}, h))),
          hdr_get_none("Content-Length", hs, hcl)))))

def until_feed(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String,
               +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}) == True{} : Bool}, +hcl: {L.has_key("Content-Length", hs) == False{} : Bool})
  -> {Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}) ++ b, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})
      == Http.Parse{None{}, False{}, False{}, Http.HClose{Http.Resp{c, st, hs, "", False{}}, kacc(None{}, b, 0n, ""), kk(None{}, b, 0n)}} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}) ++ b, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
    Http.feed.go(b, Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
    Http.Parse{None{}, False{}, False{}, Http.HClose{Http.Resp{c, st, hs, "", False{}}, kacc(None{}, b, 0n, ""), kk(None{}, b, 0n)}},
    Equal.sym(Http.Parse, Http.feed.go(b, Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
      Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}) ++ b, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      split_go(L.render_plain(Http.Resp{c, st, hs, b, False{}}), b, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
    Equal.trans(Http.Parse, Http.feed.go(b, Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
      Http.feed.go(b, Http.Parse{None{}, False{}, False{}, Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n}}),
      Http.Parse{None{}, False{}, False{}, Http.HClose{Http.Resp{c, st, hs, "", False{}}, kacc(None{}, b, 0n, ""), kk(None{}, b, 0n)}},
      Equal.cong(Http.Parse, Http.Parse, p => Http.feed.go(b, p), Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
        Http.Parse{None{}, False{}, False{}, Http.HClose{Http.Resp{c, st, hs, "", False{}}, "", 0n}}, plain_state(c, st, hs, b, None{}, False{}, h, hcl)),
      close_run(b, Http.Resp{c, st, hs, "", False{}}, "", 0n, None{}, False{}, False{})))

def until_eof(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String,
              +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}) == True{} : Bool}, +hcl: {L.has_key("Content-Length", hs) == False{} : Bool})
  -> {L.parse_eof(None{}, False{}, L.render_plain(Http.Resp{c, st, hs, b, False{}}) ++ b) == Some{Done{(Http.Resp{c, st, hs, b, False{}}, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  %Equal.sym(Http.Parse, Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}) ++ b, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.Parse{None{}, False{}, False{}, Http.HClose{Http.Resp{c, st, hs, "", False{}}, kacc(None{}, b, 0n, ""), kk(None{}, b, 0n)}}, until_feed(c, st, hs, b, h, hcl))
    : {Http.done(Http.eof(_)) == Some{Done{(Http.Resp{c, st, hs, b, False{}}, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %Equal.sym(String, kacc(None{}, b, 0n, ""), String.reverse.go(b, ""), kacc_none(b, 0n, ""))
    : {Some{Done{(Http.Resp{c, st, hs, String.reverse(_), False{}}, "")}} == Some{Done{(Http.Resp{c, st, hs, b, False{}}, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %rev_rev(b) : {Some{Done{(Http.Resp{c, st, hs, rev(rev(b)), False{}}, "")}} == Some{Done{(Http.Resp{c, st, hs, _, False{}}, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  {==}

def until_open(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String,
               +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}) == True{} : Bool}, +hcl: {L.has_key("Content-Length", hs) == False{} : Bool})
  -> {L.parse_of(None{}, False{}, L.render_plain(Http.Resp{c, st, hs, b, False{}}) ++ b) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  %Equal.sym(Http.Parse, Http.feed.go(L.render_plain(Http.Resp{c, st, hs, b, False{}}) ++ b, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.Parse{None{}, False{}, False{}, Http.HClose{Http.Resp{c, st, hs, "", False{}}, kacc(None{}, b, 0n, ""), kk(None{}, b, 0n)}}, until_feed(c, st, hs, b, h, hcl))
    : {Http.done(_) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  {==}

def until_main(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, k: Bool,
               +h: {L.resp_eof_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool})
  -> {L.parse_eof(None{}, False{}, L.render_plain(Http.Resp{c, st, hs, b, k}) ++ b) == Some{Done{(Http.Resp{c, st, hs, b, k}, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
   & {L.parse_of(None{}, False{}, L.render_plain(Http.Resp{c, st, hs, b, k}) ++ b) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  match k:
    case True{}:
      Empty.absurd({L.parse_eof(None{}, False{}, L.render_plain(Http.Resp{c, st, hs, b, True{}}) ++ b) == Some{Done{(Http.Resp{c, st, hs, b, True{}}, "")}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
        & {L.parse_of(None{}, False{}, L.render_plain(Http.Resp{c, st, hs, b, True{}}) ++ b) == None{} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>},
        no_ft(and_r(Bool.not(L.has_key("Content-Length", hs)), False{}, and_r(L.resp_base_ok(Http.Resp{c, st, hs, b, True{}}), Bool.and(Bool.not(L.has_key("Content-Length", hs)), False{}), h))))
    case False{}:
      (until_eof(c, st, hs, b, and_l(L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}), Bool.and(Bool.not(L.has_key("Content-Length", hs)), True{}), h),
         not_t(L.has_key("Content-Length", hs), and_l(Bool.not(L.has_key("Content-Length", hs)), True{}, and_r(L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}), Bool.and(Bool.not(L.has_key("Content-Length", hs)), True{}), h)))),
       until_open(c, st, hs, b, and_l(L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}), Bool.and(Bool.not(L.has_key("Content-Length", hs)), True{}), h),
         not_t(L.has_key("Content-Length", hs), and_l(Bool.not(L.has_key("Content-Length", hs)), True{}, and_r(L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}), Bool.and(Bool.not(L.has_key("Content-Length", hs)), True{}), h)))))

def L.http_until_close(r, h):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      until_main(c, st, hs, b, k, h)

# the ten conjuncts of resp_nobody_ok
def nb1(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a1 == True{} : Bool}:
  and_l(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h)

def nb2(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a2 == True{} : Bool}:
  and_l(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h))

def nb3(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a3 == True{} : Bool}:
  and_l(a3, a4, and_l(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))), and_r(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h))))

def nb4(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a4 == True{} : Bool}:
  and_r(a3, a4, and_l(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))), and_r(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h))))

def nb5(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a5 == True{} : Bool}:
  and_l(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))), and_r(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))), and_r(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h))))

def nb6(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a6 == True{} : Bool}:
  and_l(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)), and_r(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))), and_r(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))), and_r(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h)))))

def nb7(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a7 == True{} : Bool}:
  and_l(a7, Bool.and(Bool.and(a8, a9), a10), and_r(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)), and_r(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))), and_r(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))), and_r(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h))))))

def nb8(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a8 == True{} : Bool}:
  and_l(a8, a9, and_l(Bool.and(a8, a9), a10, and_r(a7, Bool.and(Bool.and(a8, a9), a10), and_r(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)), and_r(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))), and_r(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))), and_r(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h))))))))

def nb9(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a9 == True{} : Bool}:
  and_r(a8, a9, and_l(Bool.and(a8, a9), a10, and_r(a7, Bool.and(Bool.and(a8, a9), a10), and_r(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)), and_r(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))), and_r(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))), and_r(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h))))))))

def nb10(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool, +a8: Bool, +a9: Bool, +a10: Bool, +h: {Bool.and(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))))) == True{} : Bool}) -> {a10 == True{} : Bool}:
  and_r(Bool.and(a8, a9), a10, and_r(a7, Bool.and(Bool.and(a8, a9), a10), and_r(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)), and_r(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))), and_r(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))), and_r(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10))))), and_r(a1, Bool.and(a2, Bool.and(Bool.and(a3, a4), Bool.and(a5, Bool.and(a6, Bool.and(a7, Bool.and(Bool.and(a8, a9), a10)))))), h)))))))

# ---------------------------------------------------------------------
# http_no_body
# ---------------------------------------------------------------------

def or_r_t(p: Bool, -q: Bool, +h: {q == True{} : Bool}) -> {Bool.or(p, q) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      h

def nbt(hd: Bool, +c: Nat, +h: {Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))) == True{} : Bool}) -> {Http.no_body(hd, c) == True{} : Bool}:
  match hd:
    case True{}:
      {==}
    case False{}:
      or_r_t(Bool.and(Nat.is_ge(c, 100n), Nat.is_le(c, 199n)), Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n)), h)

def int_f(+c: Nat, +h1: {Nat.is_ge(c, 200n) == True{} : Bool}) -> {Http.interim(c) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(c, 199n), False{}, le_f(199n, 200n, c, {==}, h1))
    : {Bool.and(Bool.and(Nat.is_ge(c, 100n), _), Bool.not(Nat.is_eq(c, 101n))) == False{} : Bool}
  %Equal.sym(Bool, Bool.and(Nat.is_ge(c, 100n), False{}), False{}, and_f(Nat.is_ge(c, 100n)))
    : {Bool.and(_, Bool.not(Nat.is_eq(c, 101n))) == False{} : Bool}
  {==}

def fr_nb_main(+c: Nat, +st: String, +mi: Nat, +h: List<&2, Hdr.Header>, +hs: List<&2, Hdr.Header>, +k: Bool, +hd: Bool,
    +hp: {Http.hdr_get("Pragma", h) == None{} : Maybe<&2, List<&2, String>>},
    +hte: {Http.hdr_get("Transfer-Encoding", h) == None{} : Maybe<&2, List<&2, String>>},
    +hted: {Http.hdr_del("Transfer-Encoding", h) == h : List<&2, Hdr.Header>},
    +hcf: {Http.conn_fix(mi, h) == hs : List<&2, Hdr.Header>},
    +hko: {Http.keep_of(mi, h) == k : Bool},
    +hnb: {Http.no_body(hd, c) == True{} : Bool},
    +h101: {Nat.is_eq(c, 101n) == False{} : Bool},
    +hint: {Http.interim(c) == False{} : Bool})
  -> {Http.framing(c, st, mi, h, hd) == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}:
  %Equal.sym(List<&2, Hdr.Header>, Http.pragma_fix(h), h, pf_id(h, hp))
    : {Http.fr_body(Http.no_body(hd, c), c, mi, Http.hdr_get("Transfer-Encoding", _), Http.Resp{c, st, Http.conn_fix(mi, Http.hdr_del("Transfer-Encoding", _)), "", Bool.and(Http.keep_of(mi, _), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del("Transfer-Encoding", h), h, hted)
    : {Http.fr_body(Http.no_body(hd, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, Http.conn_fix(mi, _), "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.conn_fix(mi, h), hs, hcf)
    : {Http.fr_body(Http.no_body(hd, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, _, "", Bool.and(Http.keep_of(mi, h), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  %Equal.sym(Bool, Http.keep_of(mi, h), k, hko)
    : {Http.fr_body(Http.no_body(hd, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, hs, "", Bool.and(_, Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  %Equal.sym(Bool, Nat.is_eq(c, 101n), False{}, h101)
    : {Http.fr_body(Http.no_body(hd, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, hs, "", Bool.and(k, Bool.not(_))})
       == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  %Equal.sym(Bool, Bool.and(k, True{}), k, and_t(k))
    : {Http.fr_body(Http.no_body(hd, c), c, mi, Http.hdr_get("Transfer-Encoding", h), Http.Resp{c, st, hs, "", _})
       == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Transfer-Encoding", h), None{}, hte)
    : {Http.fr_body(Http.no_body(hd, c), c, mi, _, Http.Resp{c, st, hs, "", k})
       == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  %Equal.sym(Bool, Http.no_body(hd, c), True{}, hnb)
    : {Http.fr_body(_, c, mi, None{}, Http.Resp{c, st, hs, "", k})
       == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  %Equal.sym(Bool, Http.interim(c), False{}, hint)
    : {Http.pick(Http.Ph, _, Http.HStat{0n, ""}, Http.HDone{Http.Resp{c, st, hs, "", k}, ""}) == Http.HDone{Http.Resp{c, st, hs, "", k}, ""} : Http.Ph}
  {==}

def nb_head_t(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +hd: Bool,
    +h: {L.resp_nobody_ok(hd, Http.Resp{c, st, hs, "", True{}}) == True{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", True{}}), Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}}) == Http.Parse{None{}, hd, False{}, Http.HDone{Http.Resp{c, st, hs, "", True{}}, ""}} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", True{}}), Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), Http.Parse{None{}, hd, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
    Http.Parse{None{}, hd, False{}, Http.HDone{Http.Resp{c, st, hs, "", True{}}, ""}},
    stat_st(c, st, L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), None{}, hd, False{}, and_l(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), nb1(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)), and_r(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), nb1(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)), nb4(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h), nb3(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), Http.Parse{None{}, hd, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.Parse{None{}, hd, False{}, Http.framing(c, st, 1n, hs, hd)},
      Http.Parse{None{}, hd, False{}, Http.HDone{Http.Resp{c, st, hs, "", True{}}, ""}},
      head_keep(hs, "", c, st, 1n, None{}, hd, False{}, nb5(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)),
      Equal.cong(Http.Ph, Http.Parse, ph => Http.Parse{None{}, hd, False{}, ph}, Http.framing(c, st, 1n, hs, hd), Http.HDone{Http.Resp{c, st, hs, "", True{}}, ""},
        fr_nb_main(c, st, 1n, hs, hs, True{}, hd, hdr_get_none("Pragma", hs, not_t(L.has_key("Pragma", hs), nb10(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), hdr_get_none("Transfer-Encoding", hs, not_t(L.has_key("Transfer-Encoding", hs), nb6(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), hdr_del_none("Transfer-Encoding", hs, not_t(L.has_key("Transfer-Encoding", hs), nb6(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), hcf_keep(hs, not_t(L.says_close(hs), nb8(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), hko_keep(hs, not_t(L.says_close(hs), nb8(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), nbt(hd, c, nb2(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)), eq_f(101n, 200n, c, {==}, and_l(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), nb1(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), int_f(c, and_l(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), nb1(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(True{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)))))))

def nb_head_f(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +hd: Bool,
    +h: {L.resp_nobody_ok(hd, Http.Resp{c, st, hs, "", False{}}) == True{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", False{}}), Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}}) == Http.Parse{None{}, hd, False{}, Http.HDone{Http.Resp{c, st, hs, "", False{}}, ""}} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", False{}}), Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(hs) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), Http.Parse{None{}, hd, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
    Http.Parse{None{}, hd, False{}, Http.HDone{Http.Resp{c, st, hs, "", False{}}, ""}},
    stat_st(c, st, L.resp_hdr_lines(hs) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), None{}, hd, False{}, and_l(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), nb1(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)), and_r(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), nb1(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)), nb4(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h), nb3(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(hs) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), Http.Parse{None{}, hd, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.Parse{None{}, hd, False{}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hd)},
      Http.Parse{None{}, hd, False{}, Http.HDone{Http.Resp{c, st, hs, "", False{}}, ""}},
      head_close(hs, "", c, st, 1n, None{}, hd, False{}, nb5(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h), hnc_of(hs, nb9(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))),
      Equal.cong(Http.Ph, Http.Parse, ph => Http.Parse{None{}, hd, False{}, ph}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hd), Http.HDone{Http.Resp{c, st, hs, "", False{}}, ""},
        fr_nb_main(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hs, False{}, hd, hte_close("Pragma", hs, not_t(L.has_key("Pragma", hs), nb10(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)), {==}), hte_close("Transfer-Encoding", hs, not_t(L.has_key("Transfer-Encoding", hs), nb6(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)), {==}), hted_close(hs, not_t(L.has_key("Transfer-Encoding", hs), nb6(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), hcf_close(hs, hnc_of(hs, nb9(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), hko_close(hs, hnc_of(hs, nb9(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), nbt(hd, c, nb2(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)), eq_f(101n, 200n, c, {==}, and_l(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), nb1(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h))), int_f(c, and_l(Nat.is_ge(c, 200n), Nat.is_le(c, 599n), nb1(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(""), Bool.not(L.says_close(hs)), Bool.or(False{}, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)))))))

def nb_head(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, k: Bool, +hd: Bool,
    +h: {L.resp_nobody_ok(hd, Http.Resp{c, st, hs, "", k}) == True{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", k}), Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}}) == Http.Parse{None{}, hd, False{}, Http.HDone{Http.Resp{c, st, hs, "", k}, ""}} : Http.Parse}:
  match k:
    case True{}:
      nb_head_t(c, st, hs, hd, h)
    case False{}:
      nb_head_f(c, st, hs, hd, h)

def nobody_main(+hd: Bool, +c: Nat, +st: String, +hs: List<&2, Hdr.Header>, b: String, +k: Bool, +rest: String,
    +h: {L.resp_nobody_ok(hd, Http.Resp{c, st, hs, b, k}) == True{} : Bool})
  -> {L.parse_of(None{}, hd, L.render_head(Http.Resp{c, st, hs, b, k}) ++ rest) == Some{Done{(Http.Resp{c, st, hs, b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  match b:
    case SCon{x, t}:
      Empty.absurd({L.parse_of(None{}, hd, L.render_head(Http.Resp{c, st, hs, SCon{x, t}, k}) ++ rest) == Some{Done{(Http.Resp{c, st, hs, SCon{x, t}, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>},
        no_ft(nb7(Bool.and(Nat.is_ge(c, 200n), Nat.is_le(c, 599n)), Bool.or(hd, Bool.or(Nat.is_eq(c, 204n), Nat.is_eq(c, 304n))), String.starts_with(st, Dec.show(c) ++ " "), L.printable(st), L.hdrs_resp_ok(hs), Bool.not(L.has_key("Transfer-Encoding", hs)), String.is_empty(SCon{x, t}), Bool.not(L.says_close(hs)), Bool.or(k, Bool.not(L.has_key("Connection", hs))), Bool.not(L.has_key("Pragma", hs)), h)))
    case SNil{}:
      %Equal.sym(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", k}) ++ rest, Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}}),
          Http.feed.go(rest, Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", k}), Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}})),
          Equal.sym(Http.Parse, Http.feed.go(rest, Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", k}), Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}})),
            Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", k}) ++ rest, Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}}),
            split_go(L.render_head(Http.Resp{c, st, hs, "", k}), rest, Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}})))
        : {Http.done(_) == Some{Done{(Http.Resp{c, st, hs, "", k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
      %Equal.sym(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, hs, "", k}), Http.Parse{None{}, hd, False{}, Http.HStat{0n, ""}}),
          Http.Parse{None{}, hd, False{}, Http.HDone{Http.Resp{c, st, hs, "", k}, ""}}, nb_head(c, st, hs, k, hd, h))
        : {Http.done(Http.feed.go(rest, _)) == Some{Done{(Http.Resp{c, st, hs, "", k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
      finish(Http.Resp{c, st, hs, "", k}, rest, None{}, hd)

def L.http_no_body(head, r, rest, h):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      nobody_main(head, c, st, hs, b, k, rest, h)

# the same in HTTP/1.0
def stat_st0(+c: Nat, +st: String, +w: String, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
    +h1: {Nat.is_ge(c, 200n) == True{} : Bool}, +h2: {Nat.is_le(c, 599n) == True{} : Bool},
    +hp: {L.printable(st) == True{} : Bool}, +hs: {String.starts_with(st, Dec.show(c) ++ " ") == True{} : Bool})
  -> {Http.feed.go("HTTP/1.0 " ++ (st ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HStat{0n, ""}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{c, st, 0n, [], None{}, ""}}) : Http.Parse}:
  %Equal.sym(String, st, Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))), st_eq(c, st, hs))
    : {Http.feed.go("HTTP/1.0 " ++ (_ ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HStat{0n, ""}})
       == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{c, _, 0n, [], None{}, ""}}) : Http.Parse}
  %show_val(c)
    : {Http.feed.go("HTTP/1.0 " ++ ((Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " ")))) ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HStat{0n, ""}})
       == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HHdr{_, Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))), 0n, [], None{}, ""}}) : Http.Parse}
  stat_gen(c, String.drop(st, String.length(Dec.show(c) ++ " ")), w, mb, hd, cl, " 0.1/PTTH", "HTTP/1.0", 6n, {==}, ge_100(c, h1), le_lt(c, 599n, h2), {==},
    Equal.trans(Bool, L.printable(Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " ")))), L.printable(st), True{},
      Equal.cong(String, Bool, z => L.printable(z), Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))), st, Equal.sym(String, st, Dec.show(c) ++ (" " ++ String.drop(st, String.length(Dec.show(c) ++ " "))), st_eq(c, st, hs))),
      hp))

# ---------------------------------------------------------------------
# http_10
# ---------------------------------------------------------------------

def hko_10(+hs: List<&2, Hdr.Header>, +h: {L.says_close(hs) == False{} : Bool}) -> {Http.keep_of(0n, hs) == L.conn_token("keep-alive", hs) : Bool}:
  %Equal.sym(Bool, Http.conn_token("close", hs), False{}, ct_close_f(hs, h)) : {Bool.and(Http.conn_token("keep-alive", hs), Bool.not(_)) == L.conn_token("keep-alive", hs) : Bool}
  %Equal.sym(Bool, Bool.and(Http.conn_token("keep-alive", hs), True{}), Http.conn_token("keep-alive", hs), and_t(Http.conn_token("keep-alive", hs))) : {_ == L.conn_token("keep-alive", hs) : Bool}
  conn_token_h("keep-alive", hs)

def head_10(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String,
            +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, True{}}) == True{} : Bool},
            +hv: {L.vals_are("Content-Length", Dec.show(String.length(b)), hs) == True{} : Bool})
  -> {Http.feed.go("HTTP/1.0 " ++ (st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ "")))), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})
      == Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", L.conn_token("keep-alive", hs)})} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go("HTTP/1.0 " ++ (st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ "")))), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 0n, [], None{}, ""}}),
    Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", L.conn_token("keep-alive", hs)})},
    stat_st0(c, st, L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), None{}, False{}, False{},
      rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), rA_le(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)),
      and_l(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)), rb_B(c, st, hs, b, True{}, h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 0n, [], None{}, ""}}),
      Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 0n, hs, False{})},
      Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", L.conn_token("keep-alive", hs)})},
      head_keep(hs, "", c, st, 0n, None{}, False{}, False{}, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h))),
      Equal.cong(Http.Ph, Http.Parse, ph => Http.Parse{None{}, False{}, False{}, ph}, Http.framing(c, st, 0n, hs, False{}), Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", L.conn_token("keep-alive", hs)}),
        fr_cl_main(c, st, 0n, hs, hs, L.conn_token("keep-alive", hs), String.length(b),
          hdr_get_none("Pragma", hs, rA_prag(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))),
          hdr_get_none("Transfer-Encoding", hs, rF_te(c, hs, rb_F(c, st, hs, b, True{}, h))),
          hdr_del_none("Transfer-Encoding", hs, rF_te(c, hs, rb_F(c, st, hs, b, True{}, h))),
          {==},
          hko_10(hs, rA_close(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))),
          nb_f(c, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), rF_codes(c, hs, rb_F(c, st, hs, b, True{}, h))),
          eq_f(101n, 200n, c, {==}, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))),
          hcl_of(hs, String.length(b), hv),
          hdr_set_id("Content-Length", [Dec.show(String.length(b))], hs, hcl_of(hs, String.length(b), hv), and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)))))))

def drop0(s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def main_10(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, k: Bool, +rest: String,
            +h: {Bool.and(L.resp_cl_ok(Http.Resp{c, st, hs, b, k}), k) == True{} : Bool})
  -> {L.parse_of(None{}, False{}, "HTTP/1.0 " ++ String.drop(L.render_cl(Http.Resp{c, st, hs, b, k}), 9n) ++ rest)
      == Some{Done{(Http.Resp{c, st, hs, b, L.conn_token("keep-alive", hs)}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  match k:
    case False{}:
      Empty.absurd({L.parse_of(None{}, False{}, "HTTP/1.0 " ++ String.drop(L.render_cl(Http.Resp{c, st, hs, b, False{}}), 9n) ++ rest)
        == Some{Done{(Http.Resp{c, st, hs, b, L.conn_token("keep-alive", hs)}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>},
        no_ft(and_r(L.resp_cl_ok(Http.Resp{c, st, hs, b, False{}}), False{}, h)))
    case True{}:
      %Equal.sym(String, String.drop((st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ "")))) ++ b, 0n), (st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ "")))) ++ b, drop0((st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ "")))) ++ b))
        : {Http.done(Http.feed.go(_ ++ rest, Http.Parse{None{}, False{}, False{}, Http.HStat{7n, " 0.1/PTTH"}})) == Some{Done{(Http.Resp{c, st, hs, b, L.conn_token("keep-alive", hs)}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
      %Equal.sym(Http.Parse, Http.feed.go((("HTTP/1.0 " ++ (st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""))))) ++ b) ++ rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
          Http.feed.go(rest, Http.feed.go(b, Http.feed.go(("HTTP/1.0 " ++ (st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""))))), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}))),
          feed3(("HTTP/1.0 " ++ (st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""))))), b, rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}))
        : {Http.done(_) == Some{Done{(Http.Resp{c, st, hs, b, L.conn_token("keep-alive", hs)}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
      %Equal.sym(Http.Parse, Http.feed.go(("HTTP/1.0 " ++ (st ++ ("\r\n" ++ (L.resp_hdr_lines(hs) ++ ("\r\n" ++ ""))))), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
          Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", L.conn_token("keep-alive", hs)})},
          head_10(c, st, hs, b,
            and_l(L.resp_base_ok(Http.Resp{c, st, hs, b, True{}}), L.vals_are("Content-Length", Dec.show(String.length(b)), hs), and_l(L.resp_cl_ok(Http.Resp{c, st, hs, b, True{}}), True{}, h)),
            and_r(L.resp_base_ok(Http.Resp{c, st, hs, b, True{}}), L.vals_are("Content-Length", Dec.show(String.length(b)), hs), and_l(L.resp_cl_ok(Http.Resp{c, st, hs, b, True{}}), True{}, h))))
        : {Http.done(Http.feed.go(rest, Http.feed.go(b, _))) == Some{Done{(Http.Resp{c, st, hs, b, L.conn_token("keep-alive", hs)}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
      %Equal.sym(Http.Parse, Http.feed.go(b, Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, hs, "", L.conn_token("keep-alive", hs)})}),
          Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, L.conn_token("keep-alive", hs)}, ""}}, body_none(b, c, st, hs, L.conn_token("keep-alive", hs), False{}, False{}))
        : {Http.done(Http.feed.go(rest, _)) == Some{Done{(Http.Resp{c, st, hs, b, L.conn_token("keep-alive", hs)}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
      finish(Http.Resp{c, st, hs, b, L.conn_token("keep-alive", hs)}, rest, None{}, False{})

def L.http_10(r, rest, h):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      main_10(c, st, hs, b, k, rest, h)

# ---------------------------------------------------------------------
# Lookups past the end of a list
# ---------------------------------------------------------------------

def gor(m1: Maybe<&2, List<&2, String>>, +m2: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match m1:
    case None{}:
      m2
    case Some{v}:
      Some{v}

def hga_step(b: Bool, +vx: List<&2, String>, +r1: Maybe<&2, List<&2, String>>, +r0: Maybe<&2, List<&2, String>>, +u: Maybe<&2, List<&2, String>>,
             +ih: {r1 == gor(r0, u) : Maybe<&2, List<&2, String>>})
  -> {Http.pick(Maybe<&2, List<&2, String>>, b, Some{vx}, r1) == gor(Http.pick(Maybe<&2, List<&2, String>>, b, Some{vx}, r0), u) : Maybe<&2, List<&2, String>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def hdr_get_app2(x: Hdr.Header, +rest: List<&2, Hdr.Header>, +k: String, +u: List<&2, Hdr.Header>,
                 +ih: {Http.hdr_get(k, List.append(&2, Hdr.Header, rest, u)) == gor(Http.hdr_get(k, rest), Http.hdr_get(k, u)) : Maybe<&2, List<&2, String>>})
  -> {Http.hdr_get(k, List.append(&2, Hdr.Header, Con{x, rest}, u)) == gor(Http.hdr_get(k, Con{x, rest}), Http.hdr_get(k, u)) : Maybe<&2, List<&2, String>>}:
  match x:
    case Hdr.Header{+kx, +vx}:
      hga_step(Http.seq(kx, k), vx, Http.hdr_get(k, List.append(&2, Hdr.Header, rest, u)), Http.hdr_get(k, rest), Http.hdr_get(k, u), ih)

def hdr_get_app(+k: String, hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>)
  -> {Http.hdr_get(k, List.append(&2, Hdr.Header, hs, u)) == gor(Http.hdr_get(k, hs), Http.hdr_get(k, u)) : Maybe<&2, List<&2, String>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      hdr_get_app2(x, rest, k, u, hdr_get_app(k, rest, u))

def gor_none(m: Maybe<&2, List<&2, String>>) -> {gor(m, None{}) == m : Maybe<&2, List<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

# a lookup ignores a tail without the name
def hdr_get_keep(+k: String, +hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +hu: {Http.hdr_get(k, u) == None{} : Maybe<&2, List<&2, String>>})
  -> {Http.hdr_get(k, List.append(&2, Hdr.Header, hs, u)) == Http.hdr_get(k, hs) : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get(k, List.append(&2, Hdr.Header, hs, u)), gor(Http.hdr_get(k, hs), None{}), Http.hdr_get(k, hs),
    Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get(k, List.append(&2, Hdr.Header, hs, u)), gor(Http.hdr_get(k, hs), Http.hdr_get(k, u)), gor(Http.hdr_get(k, hs), None{}),
      hdr_get_app(k, hs, u), Equal.cong(Maybe<&2, List<&2, String>>, Maybe<&2, List<&2, String>>, z => gor(Http.hdr_get(k, hs), z), Http.hdr_get(k, u), None{}, hu)),
    gor_none(Http.hdr_get(k, hs)))

def hsa_step(b: Bool, +x: Hdr.Header, +k: String, +vs: List<&2, String>, +r0: List<&2, Hdr.Header>, +w: List<&2, Hdr.Header>)
  -> {Http.pick(List<&2, Hdr.Header>, b, Con{Hdr.Header{k, vs}, List.append(&2, Hdr.Header, r0, w)}, Con{x, List.append(&2, Hdr.Header, r0, w)})
      == List.append(&2, Hdr.Header, Http.pick(List<&2, Hdr.Header>, b, Con{Hdr.Header{k, vs}, r0}, Con{x, r0}), w) : List<&2, Hdr.Header>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def hdr_set_app(+k: String, +vs: List<&2, String>, hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>)
  -> {Http.hdr_set(k, vs, List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, Http.hdr_set(k, vs, hs), Http.hdr_set(k, vs, u)) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(List<&2, Hdr.Header>, Http.hdr_set(k, vs, List.append(&2, Hdr.Header, rest, u)), List.append(&2, Hdr.Header, Http.hdr_set(k, vs, rest), Http.hdr_set(k, vs, u)), hdr_set_app(k, vs, rest, u))
        : {Http.pick(List<&2, Hdr.Header>, Http.seq(Http.hdr_key(x), k), Con{Hdr.Header{k, vs}, _}, Con{x, _}) == List.append(&2, Hdr.Header, Http.hdr_set(k, vs, Con{x, rest}), Http.hdr_set(k, vs, u)) : List<&2, Hdr.Header>}
      hsa_step(Http.seq(Http.hdr_key(x), k), x, k, vs, Http.hdr_set(k, vs, rest), Http.hdr_set(k, vs, u))

def hr_mk(+a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +h1: {a1 == True{} : Bool}, +h2: {a2 == True{} : Bool}, +h3: {a3 == True{} : Bool},
          +h4: {a4 == True{} : Bool}, +h5: {a5 == True{} : Bool}, +h6: {a6 == True{} : Bool})
  -> {Bool.and(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6))) == True{} : Bool}:
  and_i(Bool.and(a1, a2), Bool.and(Bool.and(a3, a4), Bool.and(a5, a6)), and_i(a1, a2, h1, h2),
    and_i(Bool.and(a3, a4), Bool.and(a5, a6), and_i(a3, a4, h3, h4), and_i(a5, a6, h5, h6)))

# a well-formed header list stays well formed with one more, new name at the end
def hok_app1(hs: List<&2, Hdr.Header>, +x: Hdr.Header, +hok: {L.hdrs_resp_ok(hs) == True{} : Bool}, +hnk: {L.has_key(L.hdr_key(x), hs) == False{} : Bool},
             +hx: {L.hdrs_resp_ok([x]) == True{} : Bool})
  -> {L.hdrs_resp_ok(List.append(&2, Hdr.Header, hs, [x])) == True{} : Bool}:
  match hs:
    case Nil{}:
      hx
    case Con{+y, +rest}:
      hr_mk(L.token(L.hdr_key(y)), String.eq(L.canon(L.hdr_key(y)), L.hdr_key(y)), Bool.not(L.has_key(L.hdr_key(y), List.append(&2, Hdr.Header, rest, [x]))),
        Bool.not(List.is_empty(&2, String, L.hdr_vals(y))), L.all_clean(L.hdr_vals(y)), L.hdrs_resp_ok(List.append(&2, Hdr.Header, rest, [x])),
        hr_1(L.token(L.hdr_key(y)), String.eq(L.canon(L.hdr_key(y)), L.hdr_key(y)), Bool.not(L.has_key(L.hdr_key(y), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(y))), L.all_clean(L.hdr_vals(y)), L.hdrs_resp_ok(rest), hok),
        hr_2(L.token(L.hdr_key(y)), String.eq(L.canon(L.hdr_key(y)), L.hdr_key(y)), Bool.not(L.has_key(L.hdr_key(y), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(y))), L.all_clean(L.hdr_vals(y)), L.hdrs_resp_ok(rest), hok),
        Equal.trans(Bool, Bool.not(L.has_key(L.hdr_key(y), List.append(&2, Hdr.Header, rest, [x]))), Bool.not(Bool.or(L.has_key(L.hdr_key(y), rest), Bool.or(String.eq(L.hdr_key(x), L.hdr_key(y)), False{}))), True{},
          Equal.cong(Bool, Bool, z => Bool.not(z), L.has_key(L.hdr_key(y), List.append(&2, Hdr.Header, rest, [x])), Bool.or(L.has_key(L.hdr_key(y), rest), Bool.or(String.eq(L.hdr_key(x), L.hdr_key(y)), False{})),
            has_key_app(L.hdr_key(y), rest, [x])),
          not_or_ff(L.has_key(L.hdr_key(y), rest), String.eq(L.hdr_key(x), L.hdr_key(y)),
            not_t(L.has_key(L.hdr_key(y), rest), hr_3(L.token(L.hdr_key(y)), String.eq(L.canon(L.hdr_key(y)), L.hdr_key(y)), Bool.not(L.has_key(L.hdr_key(y), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(y))), L.all_clean(L.hdr_vals(y)), L.hdrs_resp_ok(rest), hok)),
            eq_sym_of(False{}, L.hdr_key(x), L.hdr_key(y), or_f_l(String.eq(L.hdr_key(y), L.hdr_key(x)), L.has_key(L.hdr_key(x), rest), hnk)))),
        hr_4(L.token(L.hdr_key(y)), String.eq(L.canon(L.hdr_key(y)), L.hdr_key(y)), Bool.not(L.has_key(L.hdr_key(y), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(y))), L.all_clean(L.hdr_vals(y)), L.hdrs_resp_ok(rest), hok),
        hr_5(L.token(L.hdr_key(y)), String.eq(L.canon(L.hdr_key(y)), L.hdr_key(y)), Bool.not(L.has_key(L.hdr_key(y), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(y))), L.all_clean(L.hdr_vals(y)), L.hdrs_resp_ok(rest), hok),
        hok_app1(rest, x, hr_6(L.token(L.hdr_key(y)), String.eq(L.canon(L.hdr_key(y)), L.hdr_key(y)), Bool.not(L.has_key(L.hdr_key(y), rest)), Bool.not(List.is_empty(&2, String, L.hdr_vals(y))), L.all_clean(L.hdr_vals(y)), L.hdrs_resp_ok(rest), hok),
          or_f_r(String.eq(L.hdr_key(y), L.hdr_key(x)), L.has_key(L.hdr_key(x), rest), hnk), hx))

# ---------------------------------------------------------------------
# http_pragma
# ---------------------------------------------------------------------

def pf_add(+h: List<&2, Hdr.Header>, +hp: {Http.hdr_get("Pragma", h) == Some{["no-cache"]} : Maybe<&2, List<&2, String>>}, +hcc: {Http.hdr_get("Cache-Control", h) == None{} : Maybe<&2, List<&2, String>>})
  -> {Http.pragma_fix(h) == List.append(&2, Hdr.Header, h, [Hdr.Header{"Cache-Control", ["no-cache"]}]) : List<&2, Hdr.Header>}:
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Pragma", h), Some{["no-cache"]}, hp)
    : {Http.pragma_fix.of(Http.first_no_cache(_), h) == List.append(&2, Hdr.Header, h, [Hdr.Header{"Cache-Control", ["no-cache"]}]) : List<&2, Hdr.Header>}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Cache-Control", h), None{}, hcc)
    : {Http.pragma_fix.cc(Maybe.is_none(&2, List<&2, String>, _), h) == List.append(&2, Hdr.Header, h, [Hdr.Header{"Cache-Control", ["no-cache"]}]) : List<&2, Hdr.Header>}
  {==}

def hted_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +h: {L.has_key("Transfer-Encoding", hs) == False{} : Bool}, +hu: {Http.hdr_del("Transfer-Encoding", u) == u : List<&2, Hdr.Header>})
  -> {Http.hdr_del("Transfer-Encoding", List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, hs, u) : List<&2, Hdr.Header>}:
  Equal.trans(List<&2, Hdr.Header>, Http.hdr_del("Transfer-Encoding", List.append(&2, Hdr.Header, hs, u)), List.append(&2, Hdr.Header, Http.hdr_del("Transfer-Encoding", hs), Http.hdr_del("Transfer-Encoding", u)), List.append(&2, Hdr.Header, hs, u),
    hdr_del_app("Transfer-Encoding", hs, u),
    Equal.trans(List<&2, Hdr.Header>, List.append(&2, Hdr.Header, Http.hdr_del("Transfer-Encoding", hs), Http.hdr_del("Transfer-Encoding", u)), List.append(&2, Hdr.Header, hs, Http.hdr_del("Transfer-Encoding", u)), List.append(&2, Hdr.Header, hs, u),
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, z, Http.hdr_del("Transfer-Encoding", u)), Http.hdr_del("Transfer-Encoding", hs), hs, hdr_del_none("Transfer-Encoding", hs, h)),
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, hs, z), Http.hdr_del("Transfer-Encoding", u), u, hu)))

def ct_keep_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +hu: {Http.hdr_get("Connection", u) == None{} : Maybe<&2, List<&2, String>>}, +h: {L.says_close(hs) == False{} : Bool})
  -> {Http.conn_token("close", List.append(&2, Hdr.Header, hs, u)) == False{} : Bool}:
  Equal.trans(Bool, Http.conn_token("close", List.append(&2, Hdr.Header, hs, u)), Http.conn_token("close", hs), False{},
    Equal.cong(Maybe<&2, List<&2, String>>, Bool, m => Http.some_token("close", m), Http.hdr_get("Connection", List.append(&2, Hdr.Header, hs, u)), Http.hdr_get("Connection", hs), hdr_get_keep("Connection", hs, u, hu)),
    ct_close_f(hs, h))

def hcf_keep_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +hu: {Http.hdr_get("Connection", u) == None{} : Maybe<&2, List<&2, String>>}, +h: {L.says_close(hs) == False{} : Bool})
  -> {Http.conn_fix(1n, List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, hs, u) : List<&2, Hdr.Header>}:
  %Equal.sym(Bool, Http.conn_token("close", List.append(&2, Hdr.Header, hs, u)), False{}, ct_keep_u(hs, u, hu, h))
    : {Http.conn_fix.of(_, List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, hs, u) : List<&2, Hdr.Header>}
  {==}

def hko_keep_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +hu: {Http.hdr_get("Connection", u) == None{} : Maybe<&2, List<&2, String>>}, +h: {L.says_close(hs) == False{} : Bool})
  -> {Http.keep_of(1n, List.append(&2, Hdr.Header, hs, u)) == True{} : Bool}:
  %Equal.sym(Bool, Http.conn_token("close", List.append(&2, Hdr.Header, hs, u)), False{}, ct_keep_u(hs, u, hu, h)) : {Bool.not(_) == True{} : Bool}
  {==}

def ct_close_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +hnc: {L.has_key("Connection", hs) == False{} : Bool}, +hu: {Http.some_token("close", Http.hdr_get("Connection", u)) == True{} : Bool})
  -> {Http.conn_token("close", List.append(&2, Hdr.Header, hs, u)) == True{} : Bool}:
  Equal.trans(Bool, Http.conn_token("close", List.append(&2, Hdr.Header, hs, u)), Http.some_token("close", Http.hdr_get("Connection", u)), True{},
    Equal.cong(Maybe<&2, List<&2, String>>, Bool, m => Http.some_token("close", m), Http.hdr_get("Connection", List.append(&2, Hdr.Header, hs, u)), Http.hdr_get("Connection", u), hdr_get_skip("Connection", hs, u, hnc)), hu)

def hcf_close_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +w: List<&2, Hdr.Header>, +hnc: {L.has_key("Connection", hs) == False{} : Bool}, +hu: {Http.some_token("close", Http.hdr_get("Connection", u)) == True{} : Bool},
                +hw: {Http.hdr_del("Connection", u) == w : List<&2, Hdr.Header>})
  -> {Http.conn_fix(1n, List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, hs, w) : List<&2, Hdr.Header>}:
  %Equal.sym(Bool, Http.conn_token("close", List.append(&2, Hdr.Header, hs, u)), True{}, ct_close_u(hs, u, hnc, hu))
    : {Http.conn_fix.of(_, List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, hs, w) : List<&2, Hdr.Header>}
  Equal.trans(List<&2, Hdr.Header>, Http.hdr_del("Connection", List.append(&2, Hdr.Header, hs, u)), List.append(&2, Hdr.Header, Http.hdr_del("Connection", hs), Http.hdr_del("Connection", u)), List.append(&2, Hdr.Header, hs, w),
    hdr_del_app("Connection", hs, u),
    Equal.trans(List<&2, Hdr.Header>, List.append(&2, Hdr.Header, Http.hdr_del("Connection", hs), Http.hdr_del("Connection", u)), List.append(&2, Hdr.Header, hs, Http.hdr_del("Connection", u)), List.append(&2, Hdr.Header, hs, w),
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, z, Http.hdr_del("Connection", u)), Http.hdr_del("Connection", hs), hs, hdr_del_none("Connection", hs, hnc)),
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, hs, z), Http.hdr_del("Connection", u), w, hw)))

def hko_close_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +hnc: {L.has_key("Connection", hs) == False{} : Bool}, +hu: {Http.some_token("close", Http.hdr_get("Connection", u)) == True{} : Bool})
  -> {Http.keep_of(1n, List.append(&2, Hdr.Header, hs, u)) == False{} : Bool}:
  %Equal.sym(Bool, Http.conn_token("close", List.append(&2, Hdr.Header, hs, u)), True{}, ct_close_u(hs, u, hnc, hu)) : {Bool.not(_) == False{} : Bool}
  {==}

def or_ff(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, ha) : {Bool.or(_, b) == False{} : Bool}
  hb

def hcl_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +n: Nat, +hu: {Http.hdr_get("Content-Length", u) == None{} : Maybe<&2, List<&2, String>>}, +hv: {L.vals_are("Content-Length", Dec.show(n), hs) == True{} : Bool})
  -> {Http.hdr_get("Content-Length", List.append(&2, Hdr.Header, hs, u)) == Some{[Dec.show(n)]} : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get("Content-Length", List.append(&2, Hdr.Header, hs, u)), Http.hdr_get("Content-Length", hs), Some{[Dec.show(n)]}, hdr_get_keep("Content-Length", hs, u, hu), hcl_of(hs, n, hv))

def hset_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +n: Nat, +hu: {Http.hdr_set("Content-Length", [Dec.show(n)], u) == u : List<&2, Hdr.Header>}, +hv: {L.vals_are("Content-Length", Dec.show(n), hs) == True{} : Bool},
           +hok: {L.hdrs_resp_ok(hs) == True{} : Bool})
  -> {Http.hdr_set("Content-Length", [Dec.show(n)], List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, hs, u) : List<&2, Hdr.Header>}:
  Equal.trans(List<&2, Hdr.Header>, Http.hdr_set("Content-Length", [Dec.show(n)], List.append(&2, Hdr.Header, hs, u)), List.append(&2, Hdr.Header, Http.hdr_set("Content-Length", [Dec.show(n)], hs), Http.hdr_set("Content-Length", [Dec.show(n)], u)), List.append(&2, Hdr.Header, hs, u),
    hdr_set_app("Content-Length", [Dec.show(n)], hs, u),
    Equal.trans(List<&2, Hdr.Header>, List.append(&2, Hdr.Header, Http.hdr_set("Content-Length", [Dec.show(n)], hs), Http.hdr_set("Content-Length", [Dec.show(n)], u)), List.append(&2, Hdr.Header, hs, Http.hdr_set("Content-Length", [Dec.show(n)], u)), List.append(&2, Hdr.Header, hs, u),
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, z, Http.hdr_set("Content-Length", [Dec.show(n)], u)), Http.hdr_set("Content-Length", [Dec.show(n)], hs), hs, hdr_set_id("Content-Length", [Dec.show(n)], hs, hcl_of(hs, n, hv), hok)),
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, hs, z), Http.hdr_set("Content-Length", [Dec.show(n)], u), u, hu)))

def prag_head_t(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String,
    +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, True{}}) == True{} : Bool},
    +hv: {L.vals_are("Content-Length", Dec.show(String.length(b)), hs) == True{} : Bool},
    +hcc: {L.has_key("Cache-Control", hs) == False{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, True{}}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})
      == Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", True{}})} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, True{}}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}])) ++ ("\r\n" ++ ""), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
    Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", True{}})},
    stat_st(c, st, L.resp_hdr_lines(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}])) ++ ("\r\n" ++ ""), None{}, False{}, False{}, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), rA_le(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), and_l(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)), rb_B(c, st, hs, b, True{}, h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}])) ++ ("\r\n" ++ ""), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), False{})},
      Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", True{}})},
      head_keep(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), "", c, st, 1n, None{}, False{}, False{}, hok_app1(hs, Hdr.Header{"Pragma", ["no-cache"]}, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)), rA_prag(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), {==})),
      Equal.cong(Http.Ph, Http.Parse, ph => Http.Parse{None{}, False{}, False{}, ph}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), False{}), Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", True{}}),
        fr_cl_gen(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), True{}, String.length(b), Equal.trans(List<&2, Hdr.Header>, Http.pragma_fix(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}])), List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Cache-Control", ["no-cache"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), pf_add(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), hdr_get_skip("Pragma", hs, [Hdr.Header{"Pragma", ["no-cache"]}], rA_prag(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))), hdr_get_skip("Cache-Control", hs, [Hdr.Header{"Pragma", ["no-cache"]}], hcc)), lapp_assoc(Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}], [Hdr.Header{"Cache-Control", ["no-cache"]}])), hdr_get_skip("Transfer-Encoding", hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], rF_te(c, hs, rb_F(c, st, hs, b, True{}, h))), hted_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], rF_te(c, hs, rb_F(c, st, hs, b, True{}, h)), {==}), hcf_keep_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], {==}, rA_close(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))), hko_keep_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], {==}, rA_close(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))), nb_f(c, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), rF_codes(c, hs, rb_F(c, st, hs, b, True{}, h))), eq_f(101n, 200n, c, {==}, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))), hcl_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], String.length(b), {==}, hv), hset_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], String.length(b), {==}, hv, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)))))))

def prag_head_f(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String,
    +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}) == True{} : Bool},
    +hv: {L.vals_are("Content-Length", Dec.show(String.length(b)), hs) == True{} : Bool},
    +hcc: {L.has_key("Cache-Control", hs) == False{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, False{}}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})
      == Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", False{}})} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, False{}}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}])) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
    Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", False{}})},
    stat_st(c, st, L.resp_hdr_lines(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}])) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), None{}, False{}, False{}, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), rA_le(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), and_l(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)), rb_B(c, st, hs, b, False{}, h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}])) ++ ("Connection: close\r\n" ++ ("\r\n" ++ "")), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}]), False{})},
      Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", False{}})},
      head_close(List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), "", c, st, 1n, None{}, False{}, False{}, hok_app1(hs, Hdr.Header{"Pragma", ["no-cache"]}, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)), rA_prag(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), {==}), Equal.trans(Bool, L.has_key("Connection", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}])), Bool.or(L.has_key("Connection", hs), L.has_key("Connection", [Hdr.Header{"Pragma", ["no-cache"]}])), False{}, has_key_app("Connection", hs, [Hdr.Header{"Pragma", ["no-cache"]}]), or_ff(L.has_key("Connection", hs), L.has_key("Connection", [Hdr.Header{"Pragma", ["no-cache"]}]), hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))), {==}))),
      Equal.cong(Http.Ph, Http.Parse, ph => Http.Parse{None{}, False{}, False{}, ph}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}]), False{}), Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", False{}}),
        fr_cl_gen(c, st, 1n, List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), False{}, String.length(b), Equal.trans(List<&2, Hdr.Header>, Http.pragma_fix(List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}])), List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}]), [Hdr.Header{"Cache-Control", ["no-cache"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), pf_add(List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}]), Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get("Pragma", List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}])), Http.hdr_get("Pragma", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}])), Some{["no-cache"]}, Equal.cong(List<&2, Hdr.Header>, Maybe<&2, List<&2, String>>, z => Http.hdr_get("Pragma", z), List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}]), lapp_assoc(Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}], [Hdr.Header{"Connection", ["close"]}])), hdr_get_skip("Pragma", hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}], rA_prag(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)))), Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get("Cache-Control", List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}])), Http.hdr_get("Cache-Control", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}])), None{}, Equal.cong(List<&2, Hdr.Header>, Maybe<&2, List<&2, String>>, z => Http.hdr_get("Cache-Control", z), List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}]), lapp_assoc(Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}], [Hdr.Header{"Connection", ["close"]}])), hdr_get_skip("Cache-Control", hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}], hcc))), Equal.trans(List<&2, Hdr.Header>, List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}]), [Hdr.Header{"Cache-Control", ["no-cache"]}]), List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), lapp_assoc(Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), [Hdr.Header{"Connection", ["close"]}], [Hdr.Header{"Cache-Control", ["no-cache"]}]), lapp_assoc(Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}], [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]))), hdr_get_skip("Transfer-Encoding", hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], rF_te(c, hs, rb_F(c, st, hs, b, False{}, h))), hted_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], rF_te(c, hs, rb_F(c, st, hs, b, False{}, h)), {==}), hcf_close_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))), {==}, {==}), hko_close_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))), {==}), nb_f(c, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), rF_codes(c, hs, rb_F(c, st, hs, b, False{}, h))), eq_f(101n, 200n, c, {==}, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))), hcl_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], String.length(b), {==}, hv), hset_u(hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}], String.length(b), {==}, hv, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)))))))

def prag_head(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, k: Bool,
    +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool},
    +hv: {L.vals_are("Content-Length", Dec.show(String.length(b)), hs) == True{} : Bool},
    +hcc: {L.has_key("Cache-Control", hs) == False{} : Bool})
  -> {Http.feed.go(L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, k}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})
      == Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", k})} : Http.Parse}:
  match k:
    case True{}:
      prag_head_t(c, st, hs, b, h, hv, hcc)
    case False{}:
      prag_head_f(c, st, hs, b, h, hv, hcc)

def prag_main(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +k: Bool, +rest: String,
    +h: {Bool.and(L.resp_cl_ok(Http.Resp{c, st, hs, b, k}), Bool.not(L.has_key("Cache-Control", hs))) == True{} : Bool})
  -> {L.parse_of(None{}, False{}, L.render_cl(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, k}) ++ rest) == Some{Done{(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  %Equal.sym(Http.Parse, Http.feed.go((L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, k}) ++ b) ++ rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.feed.go(rest, Http.feed.go(b, Http.feed.go(L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, k}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}))),
      feed3(L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, k}), b, rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}))
    : {Http.done(_) == Some{Done{(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %Equal.sym(Http.Parse, Http.feed.go(L.render_head(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}]), b, k}), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", k})},
      prag_head(c, st, hs, b, k,
        and_l(L.resp_base_ok(Http.Resp{c, st, hs, b, k}), L.vals_are("Content-Length", Dec.show(String.length(b)), hs), and_l(L.resp_cl_ok(Http.Resp{c, st, hs, b, k}), Bool.not(L.has_key("Cache-Control", hs)), h)),
        and_r(L.resp_base_ok(Http.Resp{c, st, hs, b, k}), L.vals_are("Content-Length", Dec.show(String.length(b)), hs), and_l(L.resp_cl_ok(Http.Resp{c, st, hs, b, k}), Bool.not(L.has_key("Cache-Control", hs)), h)),
        not_t(L.has_key("Cache-Control", hs), and_r(L.resp_cl_ok(Http.Resp{c, st, hs, b, k}), Bool.not(L.has_key("Cache-Control", hs)), h))))
    : {Http.done(Http.feed.go(rest, Http.feed.go(b, _))) == Some{Done{(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %Equal.sym(Http.Parse, Http.feed.go(b, Http.Parse{None{}, False{}, False{}, Http.fr_len(Some{String.length(b)}, Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), "", k})}),
      Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), b, k}, ""}}, body_none(b, c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), k, False{}, False{}))
    : {Http.done(Http.feed.go(rest, _)) == Some{Done{(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  finish(Http.Resp{c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Pragma", ["no-cache"]}, Hdr.Header{"Cache-Control", ["no-cache"]}]), b, k}, rest, None{}, False{})

def L.http_pragma(r, rest, h):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      prag_main(c, st, hs, b, k, rest, h)

# ---------------------------------------------------------------------
# Hex digits (chunk sizes)
# ---------------------------------------------------------------------

# a byte a chunk-size line may end its hex number with: a hex digit, not
# LF, CR, ';', a space or a tab
def hxc(+k: U32) -> Bool:
  Bool.and(Tgt.is_hex(k), Bool.and(Bool.not(U32.is_eq(k, 10)), Bool.and(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k))))))

def hxs(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(hxc(L.code(c)), hxs(rest))

def hd(+d: Nat) -> String:
  L.hexd(U32.from_nat(d))

def hd_ok(+d: Nat, h: {Nat.is_lt(d, 16n) == True{} : Bool}) -> {hxs(hd(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+d1:
      match d1:
        case 0n:
          {==}
        case 1n+d2:
          match d2:
            case 0n:
              {==}
            case 1n+d3:
              match d3:
                case 0n:
                  {==}
                case 1n+d4:
                  match d4:
                    case 0n:
                      {==}
                    case 1n+d5:
                      match d5:
                        case 0n:
                          {==}
                        case 1n+d6:
                          match d6:
                            case 0n:
                              {==}
                            case 1n+d7:
                              match d7:
                                case 0n:
                                  {==}
                                case 1n+d8:
                                  match d8:
                                    case 0n:
                                      {==}
                                    case 1n+d9:
                                      match d9:
                                        case 0n:
                                          {==}
                                        case 1n+d10:
                                          match d10:
                                            case 0n:
                                              {==}
                                            case 1n+d11:
                                              match d11:
                                                case 0n:
                                                  {==}
                                                case 1n+d12:
                                                  match d12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+d13:
                                                      match d13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+d14:
                                                          match d14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+d15:
                                                              match d15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+j:
                                                                  Empty.absurd({hxs(hd(16n+j)) == True{} : Bool}, N.lt_zero(j, h))

def hd_val(+d: Nat, +a: Nat, h: {Nat.is_lt(d, 16n) == True{} : Bool}) -> {Http.hex_value(hd(d), a) == Nat.add(Nat.mul(a, 16n), d) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+d1:
      match d1:
        case 0n:
          {==}
        case 1n+d2:
          match d2:
            case 0n:
              {==}
            case 1n+d3:
              match d3:
                case 0n:
                  {==}
                case 1n+d4:
                  match d4:
                    case 0n:
                      {==}
                    case 1n+d5:
                      match d5:
                        case 0n:
                          {==}
                        case 1n+d6:
                          match d6:
                            case 0n:
                              {==}
                            case 1n+d7:
                              match d7:
                                case 0n:
                                  {==}
                                case 1n+d8:
                                  match d8:
                                    case 0n:
                                      {==}
                                    case 1n+d9:
                                      match d9:
                                        case 0n:
                                          {==}
                                        case 1n+d10:
                                          match d10:
                                            case 0n:
                                              {==}
                                            case 1n+d11:
                                              match d11:
                                                case 0n:
                                                  {==}
                                                case 1n+d12:
                                                  match d12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+d13:
                                                      match d13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+d14:
                                                          match d14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+d15:
                                                              match d15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+j:
                                                                  Empty.absurd({Http.hex_value(hd(16n+j), a) == Nat.add(Nat.mul(a, 16n), 16n+j) : Nat}, N.lt_zero(j, h))

def hxs_app(a: String, +b: String, +ha: {hxs(a) == True{} : Bool}, +hb: {hxs(b) == True{} : Bool}) -> {hxs(a ++ b) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{+c, +rest}:
      and_i(hxc(L.code(c)), hxs(rest ++ b), and_l(hxc(L.code(c)), hxs(rest), ha), hxs_app(rest, b, and_r(hxc(L.code(c)), hxs(rest), ha), hb))

def hv_app(x: String, +y: String, +acc: Nat) -> {Http.hex_value(x ++ y, acc) == Http.hex_value(y, Http.hex_value(x, acc)) : Nat}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      hv_app(rest, y, Nat.add(Nat.mul(acc, 16n), Http.hex_val(Http.code(c))))

# q < 16q + x + 1
def g16(q: Nat, +x: Nat) -> {Nat.is_lt(q, 1n+Nat.add(Nat.mul(q, 16n), x)) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+(+qp):
      %N.add_swap(Nat.mul(qp, 16n), 15n, x)
        : {Nat.is_lt(qp, 1n+_) == True{} : Bool}
      g16(qp, Nat.add(15n, x))

def lt_qr2(q: Nat, r: Nat, -n: Nat, +e: {1n+n == Nat.add(Nat.mul(q, 16n), r) : Nat}) -> {Nat.is_lt(q, Nat.add(Nat.mul(q, 16n), r)) == True{} : Bool}:
  match q:
    case 0n:
      match r:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.no_zero(n, e))
        case 1n+rp:
          {==}
    case 1n+(+qp):
      match r:
        case 0n:
          %N.add_swap(Nat.mul(qp, 16n), 14n, 0n)
            : {Nat.is_lt(qp, 1n+_) == True{} : Bool}
          g16(qp, 14n)
        case 1n+(+rp):
          %N.add_succ(Nat.mul(1n+qp, 16n), rp)
            : {Nat.is_lt(1n+qp, _) == True{} : Bool}
          g16(1n+qp, rp)

def lt_qr(+q: Nat, +r: Nat, -n: Nat, +e: {1n+n == Nat.add(Nat.mul(q, 16n), r) : Nat}) -> {Nat.is_lt(q, 1n+n) == True{} : Bool}:
  %Equal.sym(Nat, 1n+n, Nat.add(Nat.mul(q, 16n), r), e) : {Nat.is_lt(q, _) == True{} : Bool}
  lt_qr2(q, r, n, e)

def lt1_le(a: Nat, b: Nat, +h: {Nat.is_lt(a, 1n+b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, N.lt_zero(ap, h))
        case 1n+bp:
          lt1_le(ap, bp, h)

def le_trans(a: Nat, b: Nat, c: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      match c:
        case 0n:
          {==}
        case 1n+cp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, no_ft(h1))
        case 1n+bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, no_ft(h2))
            case 1n+cp:
              le_trans(ap, bp, cp, h1, h2)

# the quotient of 1+n by 16 is at most n
def div16_le(+n: Nat) -> {Nat.is_le(Nat.div(1n+n, 16n), n) == True{} : Bool}:
  lt1_le(Nat.div(1n+n, 16n), n, lt_qr(Nat.div(1n+n, 16n), Nat.mod(1n+n, 16n), n, N.div_mod_eq(1n+n, 15n)))

def hd_hxs(f: Nat, n: Nat, +h: {Nat.is_le(n, f) == True{} : Bool}) -> {hxs(L.hex_digits(f, n)) == True{} : Bool}:
  match f:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+np:
          Empty.absurd({hxs(L.hex_digits(0n, 1n+np)) == True{} : Bool}, no_ft(h))
    case 1n+(+fp):
      match n:
        case 0n:
          {==}
        case 1n+(+np):
          hxs_app(L.hex_digits(fp, Nat.div(1n+np, 16n)), hd(Nat.mod(1n+np, 16n)),
            hd_hxs(fp, Nat.div(1n+np, 16n), le_trans(Nat.div(1n+np, 16n), np, fp, div16_le(np), h)),
            hd_ok(Nat.mod(1n+np, 16n), N.mod_lt(1n+np, 15n)))

def hd_value(f: Nat, n: Nat, +h: {Nat.is_le(n, f) == True{} : Bool}) -> {Http.hex_value(L.hex_digits(f, n), 0n) == n : Nat}:
  match f:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+np:
          Empty.absurd({Http.hex_value(L.hex_digits(0n, 1n+np), 0n) == 1n+np : Nat}, no_ft(h))
    case 1n+(+fp):
      match n:
        case 0n:
          {==}
        case 1n+(+np):
          Equal.trans(Nat, Http.hex_value(L.hex_digits(fp, Nat.div(1n+np, 16n)) ++ hd(Nat.mod(1n+np, 16n)), 0n),
            Http.hex_value(hd(Nat.mod(1n+np, 16n)), Http.hex_value(L.hex_digits(fp, Nat.div(1n+np, 16n)), 0n)), 1n+np,
            hv_app(L.hex_digits(fp, Nat.div(1n+np, 16n)), hd(Nat.mod(1n+np, 16n)), 0n),
            Equal.trans(Nat, Http.hex_value(hd(Nat.mod(1n+np, 16n)), Http.hex_value(L.hex_digits(fp, Nat.div(1n+np, 16n)), 0n)),
              Http.hex_value(hd(Nat.mod(1n+np, 16n)), Nat.div(1n+np, 16n)), 1n+np,
              Equal.cong(Nat, Nat, z => Http.hex_value(hd(Nat.mod(1n+np, 16n)), z), Http.hex_value(L.hex_digits(fp, Nat.div(1n+np, 16n)), 0n), Nat.div(1n+np, 16n),
                hd_value(fp, Nat.div(1n+np, 16n), le_trans(Nat.div(1n+np, 16n), np, fp, div16_le(np), h))),
              Equal.trans(Nat, Http.hex_value(hd(Nat.mod(1n+np, 16n)), Nat.div(1n+np, 16n)), Nat.add(Nat.mul(Nat.div(1n+np, 16n), 16n), Nat.mod(1n+np, 16n)), 1n+np,
                hd_val(Nat.mod(1n+np, 16n), Nat.div(1n+np, 16n), N.mod_lt(1n+np, 15n)),
                Equal.sym(Nat, 1n+np, Nat.add(Nat.mul(Nat.div(1n+np, 16n), 16n), Nat.mod(1n+np, 16n)), N.div_mod_eq(1n+np, 15n)))))

def le_self(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      le_self(np)

def hexd_ne(x: String, +k: U32) -> {String.is_empty(x ++ L.hexd(k)) == False{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# the hex of a positive size: its digits, its value, not empty
def hex_hxs(+m: Nat) -> {hxs(L.hex(1n+m)) == True{} : Bool}:
  hd_hxs(1n+m, 1n+m, le_self(1n+m))

def hex_val_of(+m: Nat) -> {Http.hex_value(L.hex(1n+m), 0n) == 1n+m : Nat}:
  hd_value(1n+m, 1n+m, le_self(1n+m))

def hex_ne(+m: Nat) -> {String.is_empty(L.hex(1n+m)) == False{} : Bool}:
  hexd_ne(L.hex_digits(m, Nat.div(1n+m, 16n)), U32.from_nat(Nat.mod(1n+m, 16n)))

# what hxs says of a byte
def hx_1(+k: U32, +h: {hxc(k) == True{} : Bool}) -> {Tgt.is_hex(k) == True{} : Bool}:
  and_l(Tgt.is_hex(k), Bool.and(Bool.not(U32.is_eq(k, 10)), Bool.and(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k))))), h)

def hx_r1(+k: U32, +h: {hxc(k) == True{} : Bool}) -> {Bool.and(Bool.not(U32.is_eq(k, 10)), Bool.and(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k))))) == True{} : Bool}:
  and_r(Tgt.is_hex(k), Bool.and(Bool.not(U32.is_eq(k, 10)), Bool.and(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k))))), h)

def hx_nl(+k: U32, +h: {hxc(k) == True{} : Bool}) -> {Bool.not(U32.is_eq(k, 10)) == True{} : Bool}:
  and_l(Bool.not(U32.is_eq(k, 10)), Bool.and(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k)))), hx_r1(k, h))

def hx_r2(+k: U32, +h: {hxc(k) == True{} : Bool}) -> {Bool.and(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k)))) == True{} : Bool}:
  and_r(Bool.not(U32.is_eq(k, 10)), Bool.and(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k)))), hx_r1(k, h))

def hx_cr(+k: U32, +h: {hxc(k) == True{} : Bool}) -> {U32.is_eq(k, 13) == False{} : Bool}:
  not_t(U32.is_eq(k, 13), and_l(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k))), hx_r2(k, h)))

def hx_semi(+k: U32, +h: {hxc(k) == True{} : Bool}) -> {U32.is_eq(k, 59) == False{} : Bool}:
  not_t(U32.is_eq(k, 59), and_l(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k)), and_r(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k))), hx_r2(k, h))))

def hx_ws(+k: U32, +h: {hxc(k) == True{} : Bool}) -> {ws(k) == False{} : Bool}:
  not_t(ws(k), and_r(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k)), and_r(Bool.not(U32.is_eq(k, 13)), Bool.and(Bool.not(U32.is_eq(k, 59)), Bool.not(ws(k))), hx_r2(k, h))))

def hxs_nlf(s: String, +h: {hxs(s) == True{} : Bool}) -> {nlf(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          and_i(Bool.not(U32.is_eq(k, 10)), nlf(rest), hx_nl(k, and_l(hxc(k), hxs(rest), h)), hxs_nlf(rest, and_r(hxc(k), hxs(rest), h)))

def hxs_cr(s: String, +h: {hxs(s) == True{} : Bool}) -> {Http.has_byte(s, 13) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, 13), False{}, hx_cr(k, and_l(hxc(k), hxs(rest), h)))
            : {Http.has_byte.go(SCon{Chr{k}, rest}, 13, _) == False{} : Bool}
          hxs_cr(rest, and_r(hxc(k), hxs(rest), h))

def hxs_semi(s: String, +h: {hxs(s) == True{} : Bool}) -> {Http.before(s, 59) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, 59), False{}, hx_semi(k, and_l(hxc(k), hxs(rest), h)))
            : {Http.before.go(SCon{Chr{k}, rest}, 59, _) == SCon{Chr{k}, rest} : String}
          Equal.cong(String, String, z => SCon{Chr{k}, z}, Http.before(rest, 59), rest, hxs_semi(rest, and_r(hxc(k), hxs(rest), h)))

def rof_hx(t: String, +k: U32, +hw: {ws(k) == False{} : Bool}) -> {Http.rtrim.of(t, Chr{k}) == SCon{Chr{k}, t} : String}:
  match t:
    case SNil{}:
      %Equal.sym(Bool, ws(k), False{}, hw) : {Http.rtrim.one(_, Chr{k}) == SCon{Chr{k}, SNil{}} : String}
      {==}
    case SCon{+d, +r}:
      {==}

def hxs_rtrim(s: String, +h: {hxs(s) == True{} : Bool}) -> {Http.rtrim(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %Equal.sym(String, Http.rtrim(rest), rest, hxs_rtrim(rest, and_r(hxc(k), hxs(rest), h))) : {Http.rtrim.of(_, Chr{k}) == SCon{Chr{k}, rest} : String}
          rof_hx(rest, k, hx_ws(k, and_l(hxc(k), hxs(rest), h)))

def hxs_all(s: String, +h: {hxs(s) == True{} : Bool}) -> {Http.all_hex(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          and_i(Tgt.is_hex(k), Http.all_hex(rest), hx_1(k, and_l(hxc(k), hxs(rest), h)), hxs_all(rest, and_r(hxc(k), hxs(rest), h)))

# ---------------------------------------------------------------------
# Chunk-size lines and chunk data
# ---------------------------------------------------------------------

def chs_acc(s: String, +r: Http.Resp, +cur: String, +body: String, +kept: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool, +h: {nlf(s) == True{} : Bool})
  -> {Http.feed.go(s, Http.Parse{mb, hd, cl, Http.HChSize{r, cur, body, kept}}) == Http.Parse{mb, hd, cl, Http.HChSize{r, String.reverse.go(s, cur), body, kept}} : Http.Parse}:
  match s:
    case SNil{}:
      {==}
    case SCon{+x, +rest}:
      match x:
        case Chr{+k}:
          %not_t2(U32.is_eq(k, 10), and_l(Bool.not(U32.is_eq(k, 10)), nlf(rest), h))
            : {Http.feed.go(rest, Http.Parse{mb, hd, cl, Http.size_byte(_, r, cur, body, kept, Chr{k})}) == Http.Parse{mb, hd, cl, Http.HChSize{r, String.reverse.go(rest, SCon{Chr{k}, cur}), body, kept}} : Http.Parse}
          chs_acc(rest, r, SCon{Chr{k}, cur}, body, kept, mb, hd, cl, and_r(Bool.not(U32.is_eq(k, 10)), nlf(rest), h))

# a chunk-size line holding the hex of 1+m reads as that size
def chunk_line_ok(+m: Nat, +r: Http.Resp, +body: String, +kept: Nat)
  -> {Http.chunk_line(True{}, L.hex(1n+m), r, body, kept) == Http.HChData{r, 1n+m, body, kept} : Http.Ph}:
  %Equal.sym(Bool, Http.has_byte(L.hex(1n+m), 13), False{}, hxs_cr(L.hex(1n+m), hex_hxs(m)))
    : {Http.pick(Http.Ph, _, Http.HFail{"invalid CR in chunked line"}, Http.chunk_hex(Http.before(Http.trim_ows_r(L.hex(1n+m)), 59), r, body, kept)) == Http.HChData{r, 1n+m, body, kept} : Http.Ph}
  %Equal.sym(String, Http.rtrim(L.hex(1n+m)), L.hex(1n+m), hxs_rtrim(L.hex(1n+m), hex_hxs(m)))
    : {Http.chunk_hex(Http.before(_, 59), r, body, kept) == Http.HChData{r, 1n+m, body, kept} : Http.Ph}
  %Equal.sym(String, Http.before(L.hex(1n+m), 59), L.hex(1n+m), hxs_semi(L.hex(1n+m), hex_hxs(m)))
    : {Http.chunk_hex(_, r, body, kept) == Http.HChData{r, 1n+m, body, kept} : Http.Ph}
  %Equal.sym(Bool, String.is_empty(L.hex(1n+m)), False{}, hex_ne(m))
    : {Http.pick(Http.Ph, _, Http.HFail{"empty hex number for chunk length"}, Http.pick(Http.Ph, Http.all_hex(L.hex(1n+m)), Http.chunk_size(Http.hex_value(L.hex(1n+m), 0n), r, body, kept), Http.HFail{"invalid byte in chunk length"})) == Http.HChData{r, 1n+m, body, kept} : Http.Ph}
  %Equal.sym(Bool, Http.all_hex(L.hex(1n+m)), True{}, hxs_all(L.hex(1n+m), hex_hxs(m)))
    : {Http.pick(Http.Ph, _, Http.chunk_size(Http.hex_value(L.hex(1n+m), 0n), r, body, kept), Http.HFail{"invalid byte in chunk length"}) == Http.HChData{r, 1n+m, body, kept} : Http.Ph}
  %Equal.sym(Nat, Http.hex_value(L.hex(1n+m), 0n), 1n+m, hex_val_of(m))
    : {Http.chunk_size(_, r, body, kept) == Http.HChData{r, 1n+m, body, kept} : Http.Ph}
  {==}

def size_line(+m: Nat, +w: String, +r: Http.Resp, +body: String, +kept: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(L.hex(1n+m) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HChSize{r, "", body, kept}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HChData{r, 1n+m, body, kept}}) : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.hex(1n+m) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HChSize{r, "", body, kept}}),
    Http.feed.go("\r\n" ++ w, Http.feed.go(L.hex(1n+m), Http.Parse{mb, hd, cl, Http.HChSize{r, "", body, kept}})),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HChData{r, 1n+m, body, kept}}),
    Equal.sym(Http.Parse, Http.feed.go("\r\n" ++ w, Http.feed.go(L.hex(1n+m), Http.Parse{mb, hd, cl, Http.HChSize{r, "", body, kept}})),
      Http.feed.go(L.hex(1n+m) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HChSize{r, "", body, kept}}),
      split_go(L.hex(1n+m), "\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HChSize{r, "", body, kept}})),
    Equal.trans(Http.Parse, Http.feed.go("\r\n" ++ w, Http.feed.go(L.hex(1n+m), Http.Parse{mb, hd, cl, Http.HChSize{r, "", body, kept}})),
      Http.feed.go("\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HChSize{r, String.reverse.go(L.hex(1n+m), ""), body, kept}}),
      Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HChData{r, 1n+m, body, kept}}),
      Equal.cong(Http.Parse, Http.Parse, p => Http.feed.go("\r\n" ++ w, p), Http.feed.go(L.hex(1n+m), Http.Parse{mb, hd, cl, Http.HChSize{r, "", body, kept}}),
        Http.Parse{mb, hd, cl, Http.HChSize{r, String.reverse.go(L.hex(1n+m), ""), body, kept}},
        chs_acc(L.hex(1n+m), r, "", body, kept, mb, hd, cl, hxs_nlf(L.hex(1n+m), hex_hxs(m)))),
      Equal.trans(Http.Parse, Http.feed.go("\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HChSize{r, String.reverse.go(L.hex(1n+m), ""), body, kept}}),
        Http.feed.go(w, Http.Parse{mb, hd, cl, Http.chunk_line(True{}, L.hex(1n+m), r, body, kept)}),
        Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HChData{r, 1n+m, body, kept}}),
        Equal.cong(String, Http.Parse, z => Http.feed.go(w, Http.Parse{mb, hd, cl, Http.chunk_line(True{}, z, r, body, kept)}), rev(rev(L.hex(1n+m))), L.hex(1n+m), rev_rev(L.hex(1n+m))),
        Equal.cong(Http.Ph, Http.Parse, ph => Http.feed.go(w, Http.Parse{mb, hd, cl, ph}), Http.chunk_line(True{}, L.hex(1n+m), r, body, kept), Http.HChData{r, 1n+m, body, kept}, chunk_line_ok(m, r, body, kept)))))

def data_run(b: String, +c: Char, +r: Http.Resp, +acc: String, +kept: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(SCon{c, b}, Http.Parse{mb, hd, cl, Http.HChData{r, String.length(SCon{c, b}), acc, kept}})
      == Http.Parse{mb, hd, cl, Http.HChCR{r, kacc(mb, SCon{c, b}, kept, acc), kk(mb, SCon{c, b}, kept)}} : Http.Parse}:
  match b:
    case SNil{}:
      {==}
    case SCon{+c2, +rest}:
      data_run(rest, c2, r, Http.pick(String, Http.room(mb, kept), SCon{c, acc}, acc), Http.pick(Nat, Http.room(mb, kept), 1n+kept, kept), mb, hd, cl)

# one chunk's data and CRLF
def chunk_data(+x: Char, +t: String, +w: String, +r: Http.Resp, +acc: String, +kept: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(SCon{x, t} ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HChData{r, String.length(SCon{x, t}), acc, kept}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HChSize{r, "", kacc(mb, SCon{x, t}, kept, acc), kk(mb, SCon{x, t}, kept)}}) : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(SCon{x, t} ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HChData{r, String.length(SCon{x, t}), acc, kept}}),
    Http.feed.go("\r\n" ++ w, Http.feed.go(SCon{x, t}, Http.Parse{mb, hd, cl, Http.HChData{r, String.length(SCon{x, t}), acc, kept}})),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.HChSize{r, "", kacc(mb, SCon{x, t}, kept, acc), kk(mb, SCon{x, t}, kept)}}),
    Equal.sym(Http.Parse, Http.feed.go("\r\n" ++ w, Http.feed.go(SCon{x, t}, Http.Parse{mb, hd, cl, Http.HChData{r, String.length(SCon{x, t}), acc, kept}})),
      Http.feed.go(SCon{x, t} ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HChData{r, String.length(SCon{x, t}), acc, kept}}),
      split_go(SCon{x, t}, "\r\n" ++ w, Http.Parse{mb, hd, cl, Http.HChData{r, String.length(SCon{x, t}), acc, kept}})),
    Equal.cong(Http.Parse, Http.Parse, p => Http.feed.go("\r\n" ++ w, p),
      Http.feed.go(SCon{x, t}, Http.Parse{mb, hd, cl, Http.HChData{r, String.length(SCon{x, t}), acc, kept}}),
      Http.Parse{mb, hd, cl, Http.HChCR{r, kacc(mb, SCon{x, t}, kept, acc), kk(mb, SCon{x, t}, kept)}},
      data_run(t, x, r, acc, kept, mb, hd, cl)))

# a whole chunk (without -max-body)
def one_chunk(+x: Char, +t: String, +w: String, +r: Http.Resp, +acc: String, +kept: Nat, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(L.chunk(SCon{x, t}) ++ w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", acc, kept}})
      == Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}}) : Http.Parse}:
  %Equal.sym(String, (L.hex(String.length(SCon{x, t})) ++ ("\r\n" ++ (SCon{x, t} ++ "\r\n"))) ++ w, L.hex(String.length(SCon{x, t})) ++ (("\r\n" ++ (SCon{x, t} ++ "\r\n")) ++ w),
      app_assoc(L.hex(String.length(SCon{x, t})), "\r\n" ++ (SCon{x, t} ++ "\r\n"), w))
    : {Http.feed.go(_, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", acc, kept}}) == Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}}) : Http.Parse}
  %Equal.sym(String, (SCon{x, t} ++ "\r\n") ++ w, SCon{x, t} ++ ("\r\n" ++ w), app_assoc(SCon{x, t}, "\r\n", w))
    : {Http.feed.go(L.hex(String.length(SCon{x, t})) ++ ("\r\n" ++ _), Http.Parse{None{}, hd, cl, Http.HChSize{r, "", acc, kept}}) == Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}}) : Http.Parse}
  %kacc_none(SCon{x, t}, kept, acc)
    : {Http.feed.go(L.hex(String.length(SCon{x, t})) ++ ("\r\n" ++ (SCon{x, t} ++ ("\r\n" ++ w))), Http.Parse{None{}, hd, cl, Http.HChSize{r, "", acc, kept}}) == Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", _, kk(None{}, SCon{x, t}, kept)}}) : Http.Parse}
  Equal.trans(Http.Parse, Http.feed.go(L.hex(String.length(SCon{x, t})) ++ ("\r\n" ++ (SCon{x, t} ++ ("\r\n" ++ w))), Http.Parse{None{}, hd, cl, Http.HChSize{r, "", acc, kept}}),
    Http.feed.go(SCon{x, t} ++ ("\r\n" ++ w), Http.Parse{None{}, hd, cl, Http.HChData{r, String.length(SCon{x, t}), acc, kept}}),
    Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", kacc(None{}, SCon{x, t}, kept, acc), kk(None{}, SCon{x, t}, kept)}}),
    size_line(String.length(t), SCon{x, t} ++ ("\r\n" ++ w), r, acc, kept, None{}, hd, cl),
    chunk_data(x, t, w, r, acc, kept, None{}, hd, cl))

def kk_app(a: String, +b: String, +mb: Maybe<&2, Nat>, +k: Nat) -> {kk(mb, a ++ b, k) == kk(mb, b, kk(mb, a, k)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      kk_app(rest, b, mb, Http.pick(Nat, Http.room(mb, k), 1n+k, k))

def ch_fin(+x: Char, +t: String, +n: Nat, +r: Http.Resp, +acc: String, +kept: Nat, +hd: Bool, +cl: Bool)
  -> {Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(String.drop(t, n), String.reverse.go(SCon{x, String.take(t, n)}, acc)), kk(None{}, String.drop(t, n), kk(None{}, SCon{x, String.take(t, n)}, kept))}}
      == Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}} : Http.Parse}:
  %revapp(SCon{x, String.take(t, n)}, String.drop(t, n), acc)
    : {Http.Parse{None{}, hd, cl, Http.HChSize{r, "", _, kk(None{}, String.drop(t, n), kk(None{}, SCon{x, String.take(t, n)}, kept))}} == Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}} : Http.Parse}
  %kk_app(SCon{x, String.take(t, n)}, String.drop(t, n), None{}, kept)
    : {Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, String.take(t, n) ++ String.drop(t, n)}, acc), _}} == Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}} : Http.Parse}
  %Equal.sym(String, String.take(t, n) ++ String.drop(t, n), t, take_drop(t, n))
    : {Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, _}, acc), kk(None{}, SCon{x, _}, kept)}} == Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}} : Http.Parse}
  {==}

# the chunks of a body, however cut, read back as the body
def chs(sizes: List<&2, Nat>, b: String, +w: String, +r: Http.Resp, +acc: String, +kept: Nat, +hd: Bool, +cl: Bool)
  -> {Http.feed.go(L.chunks(sizes, b) ++ w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", acc, kept}})
      == Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(b, acc), kk(None{}, b, kept)}}) : Http.Parse}:
  match sizes:
    case Nil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{+x, +t}:
          one_chunk(x, t, w, r, acc, kept, hd, cl)
    case Con{n, +rest}:
      match n:
        case 0n:
          chs(rest, b, w, r, acc, kept, hd, cl)
        case 1n+(+np):
          match b:
            case SNil{}:
              chs(rest, SNil{}, w, r, acc, kept, hd, cl)
            case SCon{+x, +t}:
              %Equal.sym(String, (L.chunk(SCon{x, String.take(t, np)}) ++ L.chunks(rest, String.drop(t, np))) ++ w, L.chunk(SCon{x, String.take(t, np)}) ++ (L.chunks(rest, String.drop(t, np)) ++ w),
                  app_assoc(L.chunk(SCon{x, String.take(t, np)}), L.chunks(rest, String.drop(t, np)), w))
                : {Http.feed.go(_, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", acc, kept}}) == Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}}) : Http.Parse}
              Equal.trans(Http.Parse, Http.feed.go(L.chunk(SCon{x, String.take(t, np)}) ++ (L.chunks(rest, String.drop(t, np)) ++ w), Http.Parse{None{}, hd, cl, Http.HChSize{r, "", acc, kept}}),
                Http.feed.go(L.chunks(rest, String.drop(t, np)) ++ w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, String.take(t, np)}, acc), kk(None{}, SCon{x, String.take(t, np)}, kept)}}),
                Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}}),
                one_chunk(x, String.take(t, np), L.chunks(rest, String.drop(t, np)) ++ w, r, acc, kept, hd, cl),
                Equal.trans(Http.Parse, Http.feed.go(L.chunks(rest, String.drop(t, np)) ++ w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, String.take(t, np)}, acc), kk(None{}, SCon{x, String.take(t, np)}, kept)}}),
                  Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(String.drop(t, np), String.reverse.go(SCon{x, String.take(t, np)}, acc)), kk(None{}, String.drop(t, np), kk(None{}, SCon{x, String.take(t, np)}, kept))}}),
                  Http.feed.go(w, Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}}),
                  chs(rest, String.drop(t, np), w, r, String.reverse.go(SCon{x, String.take(t, np)}, acc), kk(None{}, SCon{x, String.take(t, np)}, kept), hd, cl),
                  Equal.cong(Http.Parse, Http.Parse, p => Http.feed.go(w, p),
                    Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(String.drop(t, np), String.reverse.go(SCon{x, String.take(t, np)}, acc)), kk(None{}, String.drop(t, np), kk(None{}, SCon{x, String.take(t, np)}, kept))}},
                    Http.Parse{None{}, hd, cl, Http.HChSize{r, "", String.reverse.go(SCon{x, t}, acc), kk(None{}, SCon{x, t}, kept)}},
                    ch_fin(x, t, np, r, acc, kept, hd, cl))))

# ---------------------------------------------------------------------
# http_chunked
# ---------------------------------------------------------------------

# a response's header lines, then some more lines, then the blank line
def head_ex(+hs: List<&2, Hdr.Header>, +ex: List<&2, KV>, +w: String, +c: Nat, +st: String, +mi: Nat, +mb: Maybe<&2, Nat>, +hd: Bool, +cl: Bool,
            +hok: {L.hdrs_resp_ok(hs) == True{} : Bool}, +hpx: {pok(ex) == True{} : Bool})
  -> {Http.feed.go(L.resp_hdr_lines(hs) ++ (plines(ex) ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}})
      == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(ex, hs), hd)}) : Http.Parse}:
  %Equal.sym(String, L.resp_hdr_lines(hs), plines(fl(hs)), txt(hs, hok))
    : {Http.feed.go(_ ++ (plines(ex) ++ ("\r\n" ++ w)), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(ex, hs), hd)}) : Http.Parse}
  %app_assoc(plines(fl(hs)), plines(ex), "\r\n" ++ w)
    : {Http.feed.go(_, Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(ex, hs), hd)}) : Http.Parse}
  %plines_app(fl(hs), ex)
    : {Http.feed.go(_ ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}) == Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(ex, hs), hd)}) : Http.Parse}
  Equal.trans(Http.Parse, Http.feed.go(plines(List.append(&2, KV, fl(hs), ex)) ++ ("\r\n" ++ w), Http.Parse{mb, hd, cl, Http.HHdr{c, st, mi, [], None{}, ""}}),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(List.append(&2, KV, fl(hs), ex), []), hd)}),
    Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, addall(ex, hs), hd)}),
    flat(List.append(&2, KV, fl(hs), ex), w, c, st, mi, [], None{}, [], mb, hd, cl, {==}, pok_app(fl(hs), ex, pok_fl(hs, hok), hpx)),
    Equal.cong(List<&2, Hdr.Header>, Http.Parse, z => Http.feed.go(w, Http.Parse{mb, hd, cl, Http.framing(c, st, mi, z, hd)}),
      addall(List.append(&2, KV, fl(hs), ex), []), addall(ex, hs),
      Equal.trans(List<&2, Hdr.Header>, addall(List.append(&2, KV, fl(hs), ex), []), addall(ex, addall(fl(hs), [])), addall(ex, hs),
        addall_app(fl(hs), ex, []),
        Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => addall(ex, z), addall(fl(hs), []), hs, addall_fl(hs, [], disj_nil(hs), hok)))))

def fr_te_main(+c: Nat, +st: String, +h: List<&2, Hdr.Header>, +h2: List<&2, Hdr.Header>, +hs1: List<&2, Hdr.Header>, +hs: List<&2, Hdr.Header>, +k: Bool,
    +hpf: {Http.pragma_fix(h) == h2 : List<&2, Hdr.Header>},
    +hte: {Http.hdr_get("Transfer-Encoding", h2) == Some{["chunked"]} : Maybe<&2, List<&2, String>>},
    +hted: {Http.hdr_del("Transfer-Encoding", h2) == hs1 : List<&2, Hdr.Header>},
    +hcf: {Http.conn_fix(1n, hs1) == hs : List<&2, Hdr.Header>},
    +hko: {Http.keep_of(1n, h2) == k : Bool},
    +hnb: {Http.no_body(False{}, c) == False{} : Bool},
    +h101: {Nat.is_eq(c, 101n) == False{} : Bool},
    +hcl: {Http.hdr_del("Content-Length", hs) == hs : List<&2, Hdr.Header>})
  -> {Http.framing(c, st, 1n, h, False{}) == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}:
  %Equal.sym(List<&2, Hdr.Header>, Http.pragma_fix(h), h2, hpf)
    : {Http.fr_body(Http.no_body(False{}, c), c, 1n, Http.hdr_get("Transfer-Encoding", _), Http.Resp{c, st, Http.conn_fix(1n, Http.hdr_del("Transfer-Encoding", _)), "", Bool.and(Http.keep_of(1n, _), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del("Transfer-Encoding", h2), hs1, hted)
    : {Http.fr_body(Http.no_body(False{}, c), c, 1n, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, Http.conn_fix(1n, _), "", Bool.and(Http.keep_of(1n, h2), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.conn_fix(1n, hs1), hs, hcf)
    : {Http.fr_body(Http.no_body(False{}, c), c, 1n, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, _, "", Bool.and(Http.keep_of(1n, h2), Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  %Equal.sym(Bool, Http.keep_of(1n, h2), k, hko)
    : {Http.fr_body(Http.no_body(False{}, c), c, 1n, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, hs, "", Bool.and(_, Bool.not(Nat.is_eq(c, 101n)))})
       == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  %Equal.sym(Bool, Nat.is_eq(c, 101n), False{}, h101)
    : {Http.fr_body(Http.no_body(False{}, c), c, 1n, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, hs, "", Bool.and(k, Bool.not(_))})
       == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  %Equal.sym(Bool, Bool.and(k, True{}), k, and_t(k))
    : {Http.fr_body(Http.no_body(False{}, c), c, 1n, Http.hdr_get("Transfer-Encoding", h2), Http.Resp{c, st, hs, "", _})
       == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  %Equal.sym(Maybe<&2, List<&2, String>>, Http.hdr_get("Transfer-Encoding", h2), Some{["chunked"]}, hte)
    : {Http.fr_body(Http.no_body(False{}, c), c, 1n, _, Http.Resp{c, st, hs, "", k})
       == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  %Equal.sym(Bool, Http.no_body(False{}, c), False{}, hnb)
    : {Http.fr_body(_, c, 1n, Some{["chunked"]}, Http.Resp{c, st, hs, "", k})
       == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  %Equal.sym(List<&2, Hdr.Header>, Http.hdr_del("Content-Length", hs), hs, hcl)
    : {Http.HChSize{Http.Resp{c, st, _, "", k}, "", "", 0n} == Http.HChSize{Http.Resp{c, st, hs, "", k}, "", "", 0n} : Http.Ph}
  {==}

def hdd(+k: String, +hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +w: List<&2, Hdr.Header>, +h: {L.has_key(k, hs) == False{} : Bool}, +hu: {Http.hdr_del(k, u) == w : List<&2, Hdr.Header>})
  -> {Http.hdr_del(k, List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, hs, w) : List<&2, Hdr.Header>}:
  Equal.trans(List<&2, Hdr.Header>, Http.hdr_del(k, List.append(&2, Hdr.Header, hs, u)), List.append(&2, Hdr.Header, Http.hdr_del(k, hs), Http.hdr_del(k, u)), List.append(&2, Hdr.Header, hs, w),
    hdr_del_app(k, hs, u),
    Equal.trans(List<&2, Hdr.Header>, List.append(&2, Hdr.Header, Http.hdr_del(k, hs), Http.hdr_del(k, u)), List.append(&2, Hdr.Header, hs, Http.hdr_del(k, u)), List.append(&2, Hdr.Header, hs, w),
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, z, Http.hdr_del(k, u)), Http.hdr_del(k, hs), hs, hdr_del_none(k, hs, h)),
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => List.append(&2, Hdr.Header, hs, z), Http.hdr_del(k, u), w, hu)))

def pf_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +h: {L.has_key("Pragma", hs) == False{} : Bool}, +hu: {Http.hdr_get("Pragma", u) == None{} : Maybe<&2, List<&2, String>>})
  -> {Http.pragma_fix(List.append(&2, Hdr.Header, hs, u)) == List.append(&2, Hdr.Header, hs, u) : List<&2, Hdr.Header>}:
  pf_id(List.append(&2, Hdr.Header, hs, u), Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get("Pragma", List.append(&2, Hdr.Header, hs, u)), Http.hdr_get("Pragma", u), None{}, hdr_get_skip("Pragma", hs, u, h), hu))

def te_u(+hs: List<&2, Hdr.Header>, +u: List<&2, Hdr.Header>, +h: {L.has_key("Transfer-Encoding", hs) == False{} : Bool}, +hu: {Http.hdr_get("Transfer-Encoding", u) == Some{["chunked"]} : Maybe<&2, List<&2, String>>})
  -> {Http.hdr_get("Transfer-Encoding", List.append(&2, Hdr.Header, hs, u)) == Some{["chunked"]} : Maybe<&2, List<&2, String>>}:
  Equal.trans(Maybe<&2, List<&2, String>>, Http.hdr_get("Transfer-Encoding", List.append(&2, Hdr.Header, hs, u)), Http.hdr_get("Transfer-Encoding", u), Some{["chunked"]}, hdr_get_skip("Transfer-Encoding", hs, u, h), hu)

def chk_head_t(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +sizes: List<&2, Nat>,
    +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, True{}}) == True{} : Bool}, +hcl: {L.has_key("Content-Length", hs) == False{} : Bool})
  -> {Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, True{}}, sizes), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}) == Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, True{}}, ""}} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, True{}}, sizes), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(hs) ++ (plines([KV{"Transfer-Encoding", "chunked"}]) ++ ("\r\n" ++ (L.chunks(sizes, b) ++ "0\r\n\r\n"))), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, True{}}, ""}},
    stat_st(c, st, L.resp_hdr_lines(hs) ++ (plines([KV{"Transfer-Encoding", "chunked"}]) ++ ("\r\n" ++ (L.chunks(sizes, b) ++ "0\r\n\r\n"))), None{}, False{}, False{}, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), rA_le(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), and_l(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)), rb_B(c, st, hs, b, True{}, h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(hs) ++ (plines([KV{"Transfer-Encoding", "chunked"}]) ++ ("\r\n" ++ (L.chunks(sizes, b) ++ "0\r\n\r\n"))), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, addall([KV{"Transfer-Encoding", "chunked"}], hs), False{})}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, True{}}, ""}},
      head_ex(hs, [KV{"Transfer-Encoding", "chunked"}], L.chunks(sizes, b) ++ "0\r\n\r\n", c, st, 1n, None{}, False{}, False{}, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, True{}, h)), {==}),
      Equal.trans(Http.Parse, Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, addall([KV{"Transfer-Encoding", "chunked"}], hs), False{})}),
        Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}]), False{})}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, True{}}, ""}},
        Equal.cong(List<&2, Hdr.Header>, Http.Parse, z => Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, z, False{})}), addall([KV{"Transfer-Encoding", "chunked"}], hs), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}]), add_new("Transfer-Encoding", "chunked", hs, rF_te(c, hs, rb_F(c, st, hs, b, True{}, h)))),
        Equal.trans(Http.Parse, Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}]), False{})}),
          Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.HChSize{Http.Resp{c, st, hs, "", True{}}, "", "", 0n}}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, True{}}, ""}},
          Equal.cong(Http.Ph, Http.Parse, ph => Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, ph}), Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}]), False{}), Http.HChSize{Http.Resp{c, st, hs, "", True{}}, "", "", 0n}, fr_te_main(c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}]), hs, hs, True{}, pf_u(hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}], rA_prag(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), {==}), te_u(hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}], rF_te(c, hs, rb_F(c, st, hs, b, True{}, h)), {==}), Equal.trans(List<&2, Hdr.Header>, Http.hdr_del("Transfer-Encoding", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}])), List.append(&2, Hdr.Header, hs, []), hs, hdd("Transfer-Encoding", hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}], [], rF_te(c, hs, rb_F(c, st, hs, b, True{}, h)), {==}), lapp_nil(Hdr.Header, hs)), hcf_keep(hs, rA_close(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))), hko_keep_u(hs, [Hdr.Header{"Transfer-Encoding", ["chunked"]}], {==}, rA_close(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))), nb_f(c, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h)), rF_codes(c, hs, rb_F(c, st, hs, b, True{}, h))), eq_f(101n, 200n, c, {==}, rA_ge(c, hs, True{}, rb_A(c, st, hs, b, True{}, h))), hdr_del_none("Content-Length", hs, hcl))),
          Equal.trans(Http.Parse, Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.HChSize{Http.Resp{c, st, hs, "", True{}}, "", "", 0n}}),
            Http.feed.go("0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.HChSize{Http.Resp{c, st, hs, "", True{}}, "", String.reverse.go(b, ""), kk(None{}, b, 0n)}}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, True{}}, ""}},
            chs(sizes, b, "0\r\n\r\n", Http.Resp{c, st, hs, "", True{}}, "", 0n, False{}, False{}),
            Equal.cong(String, Http.Parse, z => Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, z, True{}}, ""}}, rev(rev(b)), b, rev_rev(b)))))))

def chk_head_f(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +sizes: List<&2, Nat>,
    +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, False{}}) == True{} : Bool}, +hcl: {L.has_key("Content-Length", hs) == False{} : Bool})
  -> {Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, False{}}, sizes), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}) == Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, False{}}, ""}} : Http.Parse}:
  Equal.trans(Http.Parse, Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, False{}}, sizes), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
    Http.feed.go(L.resp_hdr_lines(hs) ++ (plines([KV{"Connection", "close"}, KV{"Transfer-Encoding", "chunked"}]) ++ ("\r\n" ++ (L.chunks(sizes, b) ++ "0\r\n\r\n"))), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, False{}}, ""}},
    stat_st(c, st, L.resp_hdr_lines(hs) ++ (plines([KV{"Connection", "close"}, KV{"Transfer-Encoding", "chunked"}]) ++ ("\r\n" ++ (L.chunks(sizes, b) ++ "0\r\n\r\n"))), None{}, False{}, False{}, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), rA_le(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), and_l(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)), rb_B(c, st, hs, b, False{}, h)),
    Equal.trans(Http.Parse, Http.feed.go(L.resp_hdr_lines(hs) ++ (plines([KV{"Connection", "close"}, KV{"Transfer-Encoding", "chunked"}]) ++ ("\r\n" ++ (L.chunks(sizes, b) ++ "0\r\n\r\n"))), Http.Parse{None{}, False{}, False{}, Http.HHdr{c, st, 1n, [], None{}, ""}}),
      Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, addall([KV{"Connection", "close"}, KV{"Transfer-Encoding", "chunked"}], hs), False{})}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, False{}}, ""}},
      head_ex(hs, [KV{"Connection", "close"}, KV{"Transfer-Encoding", "chunked"}], L.chunks(sizes, b) ++ "0\r\n\r\n", c, st, 1n, None{}, False{}, False{}, and_r(L.printable(st), L.hdrs_resp_ok(hs), rb_C(c, st, hs, b, False{}, h)), {==}),
      Equal.trans(Http.Parse, Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, addall([KV{"Connection", "close"}, KV{"Transfer-Encoding", "chunked"}], hs), False{})}),
        Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}]), False{})}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, False{}}, ""}},
        Equal.cong(List<&2, Hdr.Header>, Http.Parse, z => Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, z, False{})}), addall([KV{"Connection", "close"}, KV{"Transfer-Encoding", "chunked"}], hs), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}]), Equal.trans(List<&2, Hdr.Header>, Http.hdr_add("Transfer-Encoding", "chunked", Http.hdr_add("Connection", "close", hs)), Http.hdr_add("Transfer-Encoding", "chunked", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}]), Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, z => Http.hdr_add("Transfer-Encoding", "chunked", z), Http.hdr_add("Connection", "close", hs), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), add_new("Connection", "close", hs, hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))))), Equal.trans(List<&2, Hdr.Header>, Http.hdr_add("Transfer-Encoding", "chunked", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])), List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), [Hdr.Header{"Transfer-Encoding", ["chunked"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}]), add_new("Transfer-Encoding", "chunked", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), Equal.trans(Bool, L.has_key("Transfer-Encoding", List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}])), Bool.or(L.has_key("Transfer-Encoding", hs), L.has_key("Transfer-Encoding", [Hdr.Header{"Connection", ["close"]}])), False{}, has_key_app("Transfer-Encoding", hs, [Hdr.Header{"Connection", ["close"]}]), or_ff(L.has_key("Transfer-Encoding", hs), L.has_key("Transfer-Encoding", [Hdr.Header{"Connection", ["close"]}]), rF_te(c, hs, rb_F(c, st, hs, b, False{}, h)), {==}))), lapp_assoc(Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}], [Hdr.Header{"Transfer-Encoding", ["chunked"]}])))),
        Equal.trans(Http.Parse, Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}]), False{})}),
          Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.HChSize{Http.Resp{c, st, hs, "", False{}}, "", "", 0n}}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, False{}}, ""}},
          Equal.cong(Http.Ph, Http.Parse, ph => Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, ph}), Http.framing(c, st, 1n, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}]), False{}), Http.HChSize{Http.Resp{c, st, hs, "", False{}}, "", "", 0n}, fr_te_main(c, st, List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}]), List.append(&2, Hdr.Header, hs, [Hdr.Header{"Connection", ["close"]}]), hs, False{}, pf_u(hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}], rA_prag(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), {==}), te_u(hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}], rF_te(c, hs, rb_F(c, st, hs, b, False{}, h)), {==}), hdd("Transfer-Encoding", hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}], [Hdr.Header{"Connection", ["close"]}], rF_te(c, hs, rb_F(c, st, hs, b, False{}, h)), {==}), hcf_close(hs, hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)))), hko_close_u(hs, [Hdr.Header{"Connection", ["close"]}, Hdr.Header{"Transfer-Encoding", ["chunked"]}], hnc_of(hs, rA_conn(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))), {==}), nb_f(c, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h)), rF_codes(c, hs, rb_F(c, st, hs, b, False{}, h))), eq_f(101n, 200n, c, {==}, rA_ge(c, hs, False{}, rb_A(c, st, hs, b, False{}, h))), hdr_del_none("Content-Length", hs, hcl))),
          Equal.trans(Http.Parse, Http.feed.go(L.chunks(sizes, b) ++ "0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.HChSize{Http.Resp{c, st, hs, "", False{}}, "", "", 0n}}),
            Http.feed.go("0\r\n\r\n", Http.Parse{None{}, False{}, False{}, Http.HChSize{Http.Resp{c, st, hs, "", False{}}, "", String.reverse.go(b, ""), kk(None{}, b, 0n)}}), Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, False{}}, ""}},
            chs(sizes, b, "0\r\n\r\n", Http.Resp{c, st, hs, "", False{}}, "", 0n, False{}, False{}),
            Equal.cong(String, Http.Parse, z => Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, z, False{}}, ""}}, rev(rev(b)), b, rev_rev(b)))))))

def chk_head(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, k: Bool, +sizes: List<&2, Nat>,
    +h: {L.resp_base_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool}, +hcl: {L.has_key("Content-Length", hs) == False{} : Bool})
  -> {Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, k}, sizes), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}) == Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, k}, ""}} : Http.Parse}:
  match k:
    case True{}:
      chk_head_t(c, st, hs, b, sizes, h, hcl)
    case False{}:
      chk_head_f(c, st, hs, b, sizes, h, hcl)

def chunked_main(+c: Nat, +st: String, +hs: List<&2, Hdr.Header>, +b: String, +k: Bool, +sizes: List<&2, Nat>, +rest: String,
    +h: {L.resp_te_ok(Http.Resp{c, st, hs, b, k}) == True{} : Bool})
  -> {L.parse_of(None{}, False{}, L.render_chunked(Http.Resp{c, st, hs, b, k}, sizes) ++ rest) == Some{Done{(Http.Resp{c, st, hs, b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  %Equal.sym(Http.Parse, Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, k}, sizes) ++ rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.feed.go(rest, Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, k}, sizes), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
      Equal.sym(Http.Parse, Http.feed.go(rest, Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, k}, sizes), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})),
        Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, k}, sizes) ++ rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
        split_go(L.render_chunked(Http.Resp{c, st, hs, b, k}, sizes), rest, Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}})))
    : {Http.done(_) == Some{Done{(Http.Resp{c, st, hs, b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  %Equal.sym(Http.Parse, Http.feed.go(L.render_chunked(Http.Resp{c, st, hs, b, k}, sizes), Http.Parse{None{}, False{}, False{}, Http.HStat{0n, ""}}),
      Http.Parse{None{}, False{}, False{}, Http.HDone{Http.Resp{c, st, hs, b, k}, ""}},
      chk_head(c, st, hs, b, k, sizes, and_l(L.resp_base_ok(Http.Resp{c, st, hs, b, k}), Bool.not(L.has_key("Content-Length", hs)), h),
        not_t(L.has_key("Content-Length", hs), and_r(L.resp_base_ok(Http.Resp{c, st, hs, b, k}), Bool.not(L.has_key("Content-Length", hs)), h))))
    : {Http.done(Http.feed.go(rest, _)) == Some{Done{(Http.Resp{c, st, hs, b, k}, rest)}} : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}
  finish(Http.Resp{c, st, hs, b, k}, rest, None{}, False{})

def L.http_chunked(r, sizes, rest, h):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      chunked_main(c, st, hs, b, k, sizes, rest, h)

def L.http_waits_chunked(r, sizes, k, h0, h1):
  match r:
    case Http.Resp{+c, +st, +hs, +b, +kk}:
      waits_gen(L.render_chunked(Http.Resp{c, st, hs, b, kk}, sizes), Http.Resp{c, st, hs, b, kk}, k, chunked_main(c, st, hs, b, kk, sizes, "", h0), h1)

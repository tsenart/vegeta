# Proofs of the HTTP client laws (conn_*). GENERATED: edit scripts/gen-conn-proof and run
#   cd scripts/gen-conn-proof && python3 gen.py ../../proofs/conn.bend
import Base
import ../LAWS.bend as L
import ../lib/conn.bend as Conn
import ../lib/http.bend as Http
import ../lib/hit.bend as Hit
import ../lib/civil.bend as Civil
import ../lib/target.bend as Tgt
import ../lib/hdr.bend as Hdr
import ./nat.bend as N

def pick_s(b: Bool, +x: String, +y: String) -> {Conn.pick(String, b, x, y) == L.pick(String, b, x, y) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def hit_ans(+name: String, +seq: Nat, +ts: Civil.Time, +lat: Nat, +m: String, +u: String, +nb: Nat, r: Http.Resp)
  -> {Conn.to_hit(name, seq, ts, lat, m, u, nb, Conn.Answered{r})
      == Hit.Hit{name, seq, L.r_code(r), ts, lat, nb, String.length(L.r_body(r)), L.pick(String, L.is_ok(L.r_code(r)), "", L.r_status(r)),
       Some{L.r_body(r)}, m, u, Some{L.r_hdrs(r)}} : Hit.Hit}:
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      %pick_s(L.is_ok(c), "", st) : {Conn.to_hit(name, seq, ts, lat, m, u, nb, Conn.Answered{Http.Resp{c, st, hs, b, k}}) == Hit.Hit{name, seq, c, ts, lat, nb, String.length(b), _, Some{b}, m, u, Some{hs}} : Hit.Hit}
      {==}

def L.conn_to_hit(name, seq, ts, lat, m, u, nb, r, e, pb):
  (hit_ans(name, seq, ts, lat, m, u, nb, r), {==})

def first_t(c: Conn.Cfg, r: Conn.Req)
  -> {List.head(&2, Conn.Cmd, L.ccs_of(Conn.start(c, r, True{}))) == Some{Conn.Send{L.q_text(c, r)}} : Maybe<&2, Conn.Cmd>}:
  match c:
    case Conn.CCfg{+ka, +to, +mb, +rd}:
      match r:
        case Conn.Req{+t, +u, +ip, +b, +s, +n}:
          {==}

def first_f(+c: Conn.Cfg, r: Conn.Req)
  -> {List.head(&2, Conn.Cmd, L.ccs_of(Conn.start(c, r, False{}))) == Some{Conn.Open{L.q_ip(r), L.u_port(L.q_url(r))}} : Maybe<&2, Conn.Cmd>}:
  match r:
    case Conn.Req{+t, +u, +ip, +b, +s, +n}:
      match u:
        case Tgt.Url{+sc, +h, +p, +pa}:
          {==}

def first_of(open: Bool, +c: Conn.Cfg, +r: Conn.Req)
  -> {List.head(&2, Conn.Cmd, L.ccs_of(Conn.start(c, r, open)))
   == Some{L.pick(Conn.Cmd, open, Conn.Send{L.q_text(c, r)}, Conn.Open{L.q_ip(r), L.u_port(L.q_url(r))})} : Maybe<&2, Conn.Cmd>}:
  match open:
    case True{}:
      first_t(c, r)
    case False{}:
      first_f(c, r)

def L.conn_first(c, r, open):
  first_of(open, c, r)

# ---------------------------------------------------------------------
# Strings
# ---------------------------------------------------------------------

def w_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{} : Cmp}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+(+p):
      match a:
        case WCon{ah, +at}:
          match ah:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, w_refl(p, at)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, w_refl(p, at)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}

def eq_rec(-h1: Char, -h2: Char, r: (String & String) & Cmp) -> {String.eq.fin(String.cmp.rec(h1, h2, r)) == String.eq.fin(r) : Bool}:
  match r:
    case (xy, c):
      match xy:
        case (x, y):
          {==}

def seq_refl(x: String) -> {String.eq(x, x) == True{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{u}:
          match u:
            case U32{w}:
              %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, w_refl(32n, w)) : {String.eq.fin(String.cmp.fin(t, t, ((Chr{U32{w}}, Chr{U32{w}}), _))) == True{} : Bool}
              %Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{U32{w}}, Chr{U32{w}}, String.cmp(t, t))), String.eq.fin(String.cmp(t, t)), eq_rec(Chr{U32{w}}, Chr{U32{w}}, String.cmp(t, t))) : {_ == True{} : Bool}
              seq_refl(t)

# ---------------------------------------------------------------------
# conn_eof
# ---------------------------------------------------------------------

def eof_of(c: Conn.Cfg, q: Conn.Req)
  -> {L.fails_with(L.err_prefix(q) ++ "EOF", None{}, L.last_batch(L.ctimeline(c, q, False{}, [Conn.Opened{}, Conn.Sent{}, Conn.Eof{}]), [])) == True{} : Bool}:
  match c:
    case Conn.CCfg{+ka, +to, +mb, +rd}:
      match q:
        case Conn.Req{+t, +u, +ip, +b, +s, +n}:
          match t:
            case Tgt.Target{+m, +tu, +hs, +tb}:
              match u:
                case Tgt.Url{+sc, +h, +p, +pa}:
                  %Equal.sym(Bool, String.eq(L.err_prefix(Conn.Req{Tgt.Target{m, tu, hs, tb}, Tgt.Url{sc, h, p, pa}, ip, b, s, n}) ++ "EOF", L.err_prefix(Conn.Req{Tgt.Target{m, tu, hs, tb}, Tgt.Url{sc, h, p, pa}, ip, b, s, n}) ++ "EOF"), True{},
                      seq_refl(L.err_prefix(Conn.Req{Tgt.Target{m, tu, hs, tb}, Tgt.Url{sc, h, p, pa}, ip, b, s, n}) ++ "EOF"))
                    : {Bool.and(Bool.and(_, True{}), True{}) == True{} : Bool}
                  {==}

def L.conn_eof(c, q):
  eof_of(c, q)

# ---------------------------------------------------------------------
# The machine's state
# ---------------------------------------------------------------------

def ov(s: Conn.State) -> Bool:
  match s:
    case Conn.CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}:
      v


def op(s: Conn.State) -> Bool:
  match s:
    case Conn.CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}:
      o

# ---------------------------------------------------------------------
# Bool facts
# ---------------------------------------------------------------------

def bool_absurd(-x: Bool, -y: Bool, e: {False{} == True{} : Bool}) -> {x == y : Bool}:
  Empty.absurd({x == y : Bool}, N.false_ne_true(e))

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      bool_absurd(b, True{}, e)

def and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ea

# ---------------------------------------------------------------------
# conn_live's invariant: an unfinished request waits on what its phase
# awaits, and a redirect acted on is waiting for a connection
# ---------------------------------------------------------------------

def ph_ok(ph: Conn.Phase, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool) -> Bool:
  match ph:
    case Conn.PResolve{}:
      rs
    case Conn.POpen{}:
      op
    case Conn.PSend{}:
      sd
    case Conn.PRecv{}:
      Bool.and(rv, out)

def ph_rp(ph: Conn.Phase) -> Bool:
  match ph:
    case Conn.PResolve{}:
      True{}
    case Conn.POpen{}:
      True{}
    case Conn.PSend{}:
      False{}
    case Conn.PRecv{}:
      False{}

def met_ok(met: Bool, +ph: Conn.Phase) -> Bool:
  match met:
    case True{}:
      ph_rp(ph)
    case False{}:
      True{}

def ph_okw(+ph: Conn.Phase, w: L.Wait) -> Bool:
  match w:
    case L.Wait{a, b, d, e, f, g}:
      ph_ok(ph, a, b, d, e, f)

def w_dn(w: L.Wait) -> Bool:
  match w:
    case L.Wait{a, b, d, e, f, g}:
      g

def inv.of(v: Bool, +met: Bool, +ph: Conn.Phase, +w: L.Wait) -> Bool:
  match v:
    case True{}:
      w_dn(w)
    case False{}:
      Bool.and(ph_okw(ph, w), met_ok(met, ph))

def inv(s: Conn.State, +w: L.Wait) -> Bool:
  match s:
    case Conn.CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}:
      inv.of(v, Conn.rx_met(x), ph, w)

def wcmds(cs: List<&2, Conn.Cmd>, +w: L.Wait) -> L.Wait:
  match cs:
    case Nil{}:
      w
    case Con{+k, +rest}:
      wcmds(rest, L.w_cmd(w, k))

def met_popen(m: Bool) -> {met_ok(m, Conn.POpen{}) == True{} : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# an event clears what it answers; the phase's wait is kept otherwise
def up_rs(ph: Conn.Phase, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, h: {ph_ok(ph, rs, op, sd, rv, out) == True{} : Bool})
  -> {ph_ok(ph, True{}, op, sd, rv, out) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      h
    case Conn.PSend{}:
      h
    case Conn.PRecv{}:
      h

def up_op(ph: Conn.Phase, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, h: {ph_ok(ph, rs, op, sd, rv, out) == True{} : Bool})
  -> {ph_ok(ph, rs, True{}, sd, rv, out) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      h
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      h
    case Conn.PRecv{}:
      h

def up_sd(ph: Conn.Phase, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, h: {ph_ok(ph, rs, op, sd, rv, out) == True{} : Bool})
  -> {ph_ok(ph, rs, op, True{}, rv, out) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      h
    case Conn.POpen{}:
      h
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      h

def up_rv(ph: Conn.Phase, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, h: {ph_ok(ph, rs, op, sd, rv, out) == True{} : Bool})
  -> {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      h
    case Conn.POpen{}:
      h
    case Conn.PSend{}:
      h
    case Conn.PRecv{}:
      and_r(rv, out, h)

def up_sent(ph: Conn.Phase, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, h: {ph_ok(ph, rs, op, sd, rv, out) == True{} : Bool})
  -> {ph_ok(ph, rs, op, True{}, rv, True{}) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      h
    case Conn.POpen{}:
      h
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      %Equal.sym(Bool, rv, True{}, and_l(rv, out, h)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}

def met_sr(m: Bool, h: {met_ok(m, Conn.PSend{}) == True{} : Bool}) -> {met_ok(m, Conn.PRecv{}) == True{} : Bool}:
  match m:
    case True{}:
      h
    case False{}:
      {==}

# ---------------------------------------------------------------------
# conn_answer's facts: the parse is the parse of the bytes since the
# last Send, and the lib reads a response's redirect as LAWS reads it
# ---------------------------------------------------------------------

def pe(ef: Bool, +p: Http.Parse) -> Http.Parse:
  match ef:
    case True{}:
      Http.eof(p)
    case False{}:
      p

def PE(+mb: Maybe<&2, Nat>, +hd: Bool, +bf: String, +ef: Bool) -> Http.Parse:
  pe(ef, Http.feed(Http.start(mb, hd), bf))

def inv_a.of(v: Bool, +x: Conn.Rx, +mb: Maybe<&2, Nat>, +hd: Bool, +bf: String, +ef: Bool) -> Data:
  match v:
    case True{}:
      Unit
    case False{}:
      {Conn.rx_p(x) == PE(mb, hd, bf, ef) : Http.Parse}

def inv_a(s: Conn.State, +mb: Maybe<&2, Nat>, +hd: Bool, +bf: String, +ef: Bool) -> Data:
  match s:
    case Conn.CState{q, o, v, k, x, ph, pd, pt, hp, ip, pr}:
      inv_a.of(v, x, mb, hd, bf, ef)

# the checker's head, bytes and close after a batch (only a Send resets them)
def a_hd(cs: List<&2, Conn.Cmd>, +h: Bool) -> Bool:
  match cs:
    case Nil{}:
      h
    case Con{+k, +rest}:
      match k:
        case Conn.Send{d}:
          a_hd(rest, String.starts_with(d, "HEAD "))
        case _:
          a_hd(rest, h)

def a_bf(cs: List<&2, Conn.Cmd>, +b: String) -> String:
  match cs:
    case Nil{}:
      b
    case Con{+k, +rest}:
      match k:
        case Conn.Send{d}:
          a_bf(rest, "")
        case _:
          a_bf(rest, b)

def a_ef(cs: List<&2, Conn.Cmd>, +e: Bool) -> Bool:
  match cs:
    case Nil{}:
      e
    case Con{+k, +rest}:
      match k:
        case Conn.Send{d}:
          a_ef(rest, False{})
        case _:
          a_ef(rest, e)

def ev_bf(e: Conn.Ev, +b: String) -> String:
  match e:
    case Conn.Got{d}:
      b ++ d
    case _:
      b

def ev_ef(e: Conn.Ev, +f: Bool) -> Bool:
  match e:
    case Conn.Eof{}:
      True{}
    case _:
      f

def feed_app(a: String, +b: String, +p: Http.Parse) -> {Http.feed(Http.feed(p, a), b) == Http.feed(p, a ++ b) : Http.Parse}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      feed_app(r, b, Http.step(p, c))

def feed_eof(d: String, p: Http.Parse) -> {Http.feed(Http.eof(p), d) == Http.eof(Http.feed(p, d)) : Http.Parse}:
  match d:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      match p:
        case Http.Parse{+mb, +hd, +cl, +ph}:
          feed_eof(r, Http.Parse{mb, hd, cl, Http.step_ph(ph, mb, hd, c)})

def eof_eof(p: Http.Parse) -> {Http.eof(Http.eof(p)) == Http.eof(p) : Http.Parse}:
  match p:
    case Http.Parse{mb, hd, cl, ph}:
      {==}

def pe_feed(ef: Bool, +mb: Maybe<&2, Nat>, +hd: Bool, +bf: String, +d: String) -> {Http.feed(PE(mb, hd, bf, ef), d) == PE(mb, hd, bf ++ d, ef) : Http.Parse}:
  match ef:
    case True{}:
      %Equal.sym(Http.Parse, Http.feed(Http.eof(Http.feed(Http.start(mb, hd), bf)), d), Http.eof(Http.feed(Http.feed(Http.start(mb, hd), bf), d)), feed_eof(d, Http.feed(Http.start(mb, hd), bf)))
        : {_ == Http.eof(Http.feed(Http.start(mb, hd), bf ++ d)) : Http.Parse}
      %feed_app(bf, d, Http.start(mb, hd)) : {Http.eof(Http.feed(Http.feed(Http.start(mb, hd), bf), d)) == Http.eof(_) : Http.Parse}
      {==}
    case False{}:
      feed_app(bf, d, Http.start(mb, hd))

def pe_eof(ef: Bool, +mb: Maybe<&2, Nat>, +hd: Bool, +bf: String) -> {Http.eof(PE(mb, hd, bf, ef)) == PE(mb, hd, bf, True{}) : Http.Parse}:
  match ef:
    case True{}:
      eof_eof(Http.feed(Http.start(mb, hd), bf))
    case False{}:
      {==}

def pb_pe(ef: Bool, +mb: Maybe<&2, Nat>, +hd: Bool, +bf: String) -> {L.parse_buf(ef, mb, hd, bf) == Http.done(PE(mb, hd, bf, ef)) : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>}:
  match ef:
    case True{}:
      {==}
    case False{}:
      {==}

def or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# names, canonically: the lib's and LAWS'
def tbh(al: Bool, +k: U32) -> {Http.tb.of(al, k) == Bool.or(al, L.has_char("!#$%&'*+-.^_`|~", k)) : Bool}:
  match al:
    case True{}:
      {==}
    case False{}:
      {==}

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

def pick_u(b: Bool, +x: U32, +y: U32) -> {Http.pick(U32, b, x, y) == L.pick(U32, b, x, y) : U32}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pick_str(b: Bool, +x: String, +y: String) -> {Http.pick(String, b, x, y) == L.pick(String, b, x, y) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def canon_go_h(s: String, +up: Bool) -> {Http.canon.go(s, up) == L.canon.go(s, up) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %canon_go_h(rest, U32.is_eq(k, 45))
            : {Http.canon.go(SCon{Chr{k}, rest}, up) == SCon{Chr{L.pick(U32, Bool.and(up, L.in_range32(k, 97, 122)), (k - 32 : U32), L.pick(U32, Bool.and(Bool.not(up), L.in_range32(k, 65, 90)), (k + 32 : U32), k))}, _} : String}
          %pick_u(Bool.and(Bool.not(up), Http.in_range32(k, 65, 90)), (k + 32 : U32), k)
            : {Http.canon.go(SCon{Chr{k}, rest}, up) == SCon{Chr{L.pick(U32, Bool.and(up, L.in_range32(k, 97, 122)), (k - 32 : U32), _)}, Http.canon.go(rest, U32.is_eq(k, 45))} : String}
          %pick_u(Bool.and(up, Http.in_range32(k, 97, 122)), (k - 32 : U32), Http.pick(U32, Bool.and(Bool.not(up), Http.in_range32(k, 65, 90)), (k + 32 : U32), k))
            : {Http.canon.go(SCon{Chr{k}, rest}, up) == SCon{Chr{_}, Http.canon.go(rest, U32.is_eq(k, 45))} : String}
          {==}

def canon_h(+s: String) -> {Http.canon(s) == L.canon(s) : String}:
  %token_h(s) : {Http.canon(s) == L.pick(String, _, L.canon.go(s, True{}), s) : String}
  %canon_go_h(s, True{}) : {Http.canon(s) == L.pick(String, Http.token(s), _, s) : String}
  pick_str(Http.token(s), Http.canon.go(s, True{}), s)

def gci_hit(hs: List<&2, Hdr.Header>, +k: String, +v: List<&2, String>) -> {Conn.hdr_get_ci.go(hs, True{}, k, v) == Some{v} : Maybe<&2, List<&2, String>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, rest}:
      {==}

def gci_step(b: Bool, +k: String, +vs: List<&2, String>, +rest: List<&2, Hdr.Header>,
  ih: {L.hdr_get_ci(k, rest) == Conn.hdr_get_ci.go(rest, False{}, k, vs) : Maybe<&2, List<&2, String>>})
  -> {L.pick(Maybe<&2, List<&2, String>>, b, Some{vs}, L.hdr_get_ci(k, rest)) == Conn.hdr_get_ci.go(rest, b, k, vs) : Maybe<&2, List<&2, String>>}:
  match b:
    case True{}:
      Equal.sym(Maybe<&2, List<&2, String>>, Conn.hdr_get_ci.go(rest, True{}, k, vs), Some{vs}, gci_hit(rest, k, vs))
    case False{}:
      ih

def gci_any(hs: List<&2, Hdr.Header>, +k: String, +v: List<&2, String>, +w: List<&2, String>)
  -> {Conn.hdr_get_ci.go(hs, False{}, k, v) == Conn.hdr_get_ci.go(hs, False{}, k, w) : Maybe<&2, List<&2, String>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, rest}:
      {==}

def gci_h(hs: List<&2, Hdr.Header>, +k: String) -> {L.hdr_get_ci(k, hs) == Conn.hdr_get_ci.go(hs, False{}, k, []) : Maybe<&2, List<&2, String>>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      match h:
        case Hdr.Header{+key, +vs}:
          %canon_h(key) : {L.pick(Maybe<&2, List<&2, String>>, String.eq(_, k), Some{vs}, L.hdr_get_ci(k, rest)) == Conn.hdr_get_ci.go(rest, String.eq(Http.canon(key), k), k, vs) : Maybe<&2, List<&2, String>>}
          gci_step(String.eq(Http.canon(key), k), k, vs, rest,
            Equal.trans(Maybe<&2, List<&2, String>>, L.hdr_get_ci(k, rest), Conn.hdr_get_ci.go(rest, False{}, k, []), Conn.hdr_get_ci.go(rest, False{}, k, vs),
              gci_h(rest, k), gci_any(rest, k, [], vs)))

def first_h(+d: String, m: Maybe<&2, List<&2, String>>) -> {L.first_of(d, m) == Http.first_of(d, m) : String}:
  match m:
    case None{}:
      {==}
    case Some{vs}:
      {==}

def isr_h(r: Http.Resp) -> {L.is_redirect(r) == Conn.is_redirect(r) : Bool}:
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      %Equal.sym(Maybe<&2, List<&2, String>>, L.hdr_get_ci("Location", hs), Conn.hdr_get_ci.go(hs, False{}, "Location", []), gci_h(hs, "Location"))
        : {Bool.and(Conn.is_30x(c), Bool.not(String.is_empty(L.first_of("", _)))) == Conn.is_redirect(Http.Resp{c, st, hs, b, k}) : Bool}
      %Equal.sym(String, L.first_of("", Conn.hdr_get_ci("Location", hs)), Http.first_of("", Conn.hdr_get_ci("Location", hs)), first_h("", Conn.hdr_get_ci("Location", hs)))
        : {Bool.and(Conn.is_30x(c), Bool.not(String.is_empty(_))) == Conn.is_redirect(Http.Resp{c, st, hs, b, k}) : Bool}
      {==}

def fr_h(+ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>)
  -> {L.final_resp(Conn.CCfg{ka, to, mb, rd}, m) == Conn.final_of(Conn.CCfg{ka, to, mb, rd}, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{res}:
      match res:
        case Fail{e}:
          {==}
        case Done{pr}:
          match pr:
            case (+r, +lo):
              %Equal.sym(Bool, L.is_redirect(r), Conn.is_redirect(r), isr_h(r)) : {Bool.not(Bool.and(Maybe.is_some(&2, Nat, rd), _)) == Bool.not(Bool.and(Maybe.is_some(&2, Nat, rd), Conn.is_redirect(r))) : Bool}
              {==}

# a redirect the client would follow is no answer
def rd_ok(rd: Maybe<&2, Nat>, +r: Http.Resp, +h: {Bool.not(Bool.and(Maybe.is_some(&2, Nat, rd), Conn.is_redirect(r))) == True{} : Bool})
  -> {Bool.or(Maybe.is_none(&2, Nat, rd), Bool.not(L.is_redirect(r))) == True{} : Bool}:
  match rd:
    case None{}:
      {==}
    case Some{n}:
      %Equal.sym(Bool, L.is_redirect(r), Conn.is_redirect(r), isr_h(r)) : {Bool.not(_) == True{} : Bool}
      h

# an answer is what the parse made of the bytes
def eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def sb_refl(a: Bool) -> {L.same_bool(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def strs_refl(xs: List<&2, String>) -> {L.strs_eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Bool, String.eq(x, x), True{}, seq_refl(x)) : {Bool.and(_, L.strs_eq(rest, rest)) == True{} : Bool}
      strs_refl(rest)

def hdrs_refl(hs: List<&2, Hdr.Header>) -> {L.hdrs_eq(hs, hs) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      match h:
        case Hdr.Header{+key, +vs}:
          %Equal.sym(Bool, String.eq(key, key), True{}, seq_refl(key)) : {Bool.and(Bool.and(_, L.strs_eq(vs, vs)), L.hdrs_eq(rest, rest)) == True{} : Bool}
          %Equal.sym(Bool, L.strs_eq(vs, vs), True{}, strs_refl(vs)) : {Bool.and(Bool.and(True{}, _), L.hdrs_eq(rest, rest)) == True{} : Bool}
          hdrs_refl(rest)

def aok(+ka: Bool, r: Http.Resp, +lo: String)
  -> {L.answer_of(ka, Some{Done{(r, lo)}}, r, Bool.and(Bool.and(Conn.r_keep(r), ka), String.is_empty(lo))) == True{} : Bool}:
  match r:
    case Http.Resp{+c, +st, +hs, +b, +k}:
      %Equal.sym(Bool, Nat.is_eq(c, c), True{}, eq_refl(c)) : {Bool.and(Bool.and(Bool.and(_, String.eq(st, st)), Bool.and(Bool.and(L.hdrs_eq(hs, hs), String.eq(b, b)), L.same_bool(k, k))), L.same_bool(Bool.and(Bool.and(k, ka), String.is_empty(lo)), Bool.and(Bool.and(k, ka), String.is_empty(lo)))) == True{} : Bool}
      %Equal.sym(Bool, String.eq(st, st), True{}, seq_refl(st)) : {Bool.and(Bool.and(Bool.and(True{}, _), Bool.and(Bool.and(L.hdrs_eq(hs, hs), String.eq(b, b)), L.same_bool(k, k))), L.same_bool(Bool.and(Bool.and(k, ka), String.is_empty(lo)), Bool.and(Bool.and(k, ka), String.is_empty(lo)))) == True{} : Bool}
      %Equal.sym(Bool, L.hdrs_eq(hs, hs), True{}, hdrs_refl(hs)) : {Bool.and(Bool.and(True{}, Bool.and(Bool.and(_, String.eq(b, b)), L.same_bool(k, k))), L.same_bool(Bool.and(Bool.and(k, ka), String.is_empty(lo)), Bool.and(Bool.and(k, ka), String.is_empty(lo)))) == True{} : Bool}
      %Equal.sym(Bool, String.eq(b, b), True{}, seq_refl(b)) : {Bool.and(Bool.and(True{}, Bool.and(Bool.and(True{}, _), L.same_bool(k, k))), L.same_bool(Bool.and(Bool.and(k, ka), String.is_empty(lo)), Bool.and(Bool.and(k, ka), String.is_empty(lo)))) == True{} : Bool}
      %Equal.sym(Bool, L.same_bool(k, k), True{}, sb_refl(k)) : {Bool.and(Bool.and(True{}, Bool.and(True{}, _)), L.same_bool(Bool.and(Bool.and(k, ka), String.is_empty(lo)), Bool.and(Bool.and(k, ka), String.is_empty(lo)))) == True{} : Bool}
      sb_refl(Bool.and(Bool.and(k, ka), String.is_empty(lo)))

def fr_eq(+ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +hd: Bool, +bf: String, ef: Bool, +p: Http.Parse, -b: Bool,
  +hp: {p == PE(mb, hd, bf, ef) : Http.Parse}, +hf: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(p)) == b : Bool})
  -> {L.final_resp(Conn.CCfg{ka, to, mb, rd}, L.parse_buf(ef, mb, hd, bf)) == b : Bool}:
  %Equal.sym(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, L.parse_buf(ef, mb, hd, bf), Http.done(PE(mb, hd, bf, ef)), pb_pe(ef, mb, hd, bf))
    : {L.final_resp(Conn.CCfg{ka, to, mb, rd}, _) == b : Bool}
  %hp : {L.final_resp(Conn.CCfg{ka, to, mb, rd}, Http.done(_)) == b : Bool}
  %Equal.sym(Bool, L.final_resp(Conn.CCfg{ka, to, mb, rd}, Http.done(p)), Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(p)), fr_h(ka, to, mb, rd, Http.done(p)))
    : {_ == b : Bool}
  hf

# ---------------------------------------------------------------------
# conn_finish: one lemma per dispatcher of Conn.step.ev
# ---------------------------------------------------------------------

def fin_sendpend(hp: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hp:
    case True{}:
      {==}
    case False{}:
      {==}


def fin_opened(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      fin_sendpend(hp, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, Conn.POpen{}, pd, pt, ip, pr, T)
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def fin_sent(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def fin_sendfailed(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match l:
    case True{}:
      {==}
    case False{}:
      {==}


def fin_answer(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>, +hf: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, m) == True{} : Bool})
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{res}:
      match res:
        case Fail{e}:
          {==}
        case Done{pr}:
          match pr:
            case (+r0, +lo0):
              {==}

def fin_followopen(kept: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +hp2: Nat, +T: List<&2, L.CItem>, +ev: {Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o) == kept : Bool})
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)))) : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      {==}


def fin_followhost(same: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)))) : Bool}:
  match same:
    case True{}:
      fin_followopen(Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, nq, text, Conn.u_port(Conn.q_url(nq)), T, {==})
    case False{}:
      {==}


def fin_followok(ok: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nt: Tgt.Target, +pu: Result<&2, &2, String, Tgt.Url>, +kk: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)))) : Bool}:
  match ok:
    case True{}:
      fin_followhost(Conn.same_host(Conn.u_host(Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)})), Conn.u_host(Conn.q_url(Conn.cur_req(k)))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}, Http.request(Conn.q_target(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_body(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_seq(q), Conn.q_name(q), Conn.c_ka(Conn.CCfg{ka, to, mb, rd})), T)
    case False{}:
      {==}


def fin_redirect(stop: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match stop:
    case True{}:
      {==}
    case False{}:
      fin_followok(Result.is_done(&2, &2, String, Tgt.Url, Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})))))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))))), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), T)


def fin_badof(body: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +good: Http.Parse, +msg: String, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)))) : Bool}:
  match body:
    case True{}:
      {==}
    case False{}:
      {==}


def fin_gotmore(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def fin_gotbad(b: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)))) : Bool}:
  match b:
    case True{}:
      fin_badof(Conn.p_body(Conn.upto(data, False{}, old, old)), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.upto(data, False{}, old, old), Conn.bad.msg(Conn.p_stat(Conn.upto(data, False{}, old, old)), Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Conn.fail_msg(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet})))), T)
    case False{}:
      fin_gotmore(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, T)


def fin_gotdue(dd: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)))) : Bool}:
  match dd:
    case True{}:
      fin_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)
    case False{}:
      fin_gotbad(Conn.is_fail(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, old, data, T)


def fin_gotfin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +p2: Http.Parse, +d: String, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(p2)) == f : Bool})
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)))) : Bool}:
  match f:
    case True{}:
      fin_answer(Http.done(p2), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T, ev)
    case False{}:
      fin_gotdue(Conn.due(Conn.rx_feed(Conn.CCfg{ka, to, mb, rd}, Conn.Rx{xb, xhd, xp, xp0, xmet}, p2, d)), ka, to, mb, rd, q, o, k, Conn.rx_buf(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), Conn.rx_hd(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), p2, Conn.rx_p0(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), xmet, ph, pd, pt, hp, ip, pr, xp, d, T)


def fin_eofnl(nl: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match nl:
    case True{}:
      {==}
    case False{}:
      {==}


def fin_eofempty(em: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match em:
    case True{}:
      {==}
    case False{}:
      fin_eofnl(String.ends_with(Conn.final_from(String.reverse(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet}))), "\n"), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def fin_eoftext(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hin:
    case True{}:
      {==}
    case False{}:
      fin_eofempty(String.is_empty(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def fin_eofredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match r:
    case True{}:
      fin_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)
    case False{}:
      fin_eoftext(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def fin_eofmet(xmet: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match xmet:
    case True{}:
      {==}
    case False{}:
      fin_eofredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, False{}})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, False{}, ph, pd, pt, hp, ip, pr, T)


def fin_eoflost(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match l:
    case True{}:
      {==}
    case False{}:
      fin_eofmet(xmet, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, ph, pd, pt, hp, ip, pr, T)


def fin_eoffin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(xp)) == f : Bool})
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match f:
    case True{}:
      fin_answer(Http.done(xp), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T, ev)
    case False{}:
      fin_eoflost(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def fin_latein(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hin:
    case True{}:
      {==}
    case False{}:
      {==}


def fin_lateredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      fin_latein(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def fin_resolved(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def fin_resolvefailed(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def fin_ev(e: Conn.Ev, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_cfinish(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), False{}) == L.chk_cfinish(T, ov(L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match e:
    case Conn.Opened{}:
      fin_opened(ph, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, T)
    case Conn.OpenFailed{+m}:
      {==}
    case Conn.Sent{}:
      fin_sent(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, T)
    case Conn.SendFailed{+m}:
      fin_sendfailed(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, False{}, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, m, T)
    case Conn.Got{+d}:
      fin_gotfin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d))), ka, to, mb, rd, q, o, Conn.set_got(k, d), xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d), d, T, {==})
    case Conn.Eof{}:
      fin_eoffin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Conn.rx_p(Conn.rx_eof(Conn.Rx{xb, xhd, xp, xp0, xmet})))), ka, to, mb, rd, q, False{}, k, xb, xhd, Http.eof(xp), xp0, xmet, ph, pd, pt, hp, ip, pr, T, {==})
    case Conn.Late{}:
      fin_lateredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)
    case Conn.Resolved{+ip2}:
      fin_resolved(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip2, pr, T)
    case Conn.ResolveFailed{+m}:
      fin_resolvefailed(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, m, T)


def fin_steps(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, s: Conn.State) -> {L.chk_cfinish(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, s), ov(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match s:
        case Conn.CState{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}:
          match v:
            case True{}:
              match x:
                case Conn.Rx{+xb, +xhd, +xp, +xp0, +xmet}:
                  fin_steps(rest, ka, to, mb, rd, Conn.CState{q, o, True{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})
            case False{}:
              match x:
                case Conn.Rx{+xb, +xhd, +xp, +xp0, +xmet}:
                  %Equal.sym(Bool, L.chk_cfinish(Con{L.CIEv{e}, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))))}, ov(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})),
                      L.chk_cfinish(L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), ov(L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))),
                      fin_ev(e, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))))
                    : {_ == True{} : Bool}
                  fin_steps(rest, ka, to, mb, rd, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))

# ---------------------------------------------------------------------
# conn_finish: the machine's over flag is the checker's done
# ---------------------------------------------------------------------

def fin_start(open: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +r: Conn.Req, +evs: List<&2, Conn.Ev>)
  -> {L.chk_cfinish(L.ctimeline(Conn.CCfg{ka, to, mb, rd}, r, open, evs), False{}) == True{} : Bool}:
  match open:
    case True{}:
      fin_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, True{})))
    case False{}:
      fin_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, False{})))

def fin_law(c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>) -> {L.chk_cfinish(L.ctimeline(c, r, open, evs), False{}) == True{} : Bool}:
  match c:
    case Conn.CCfg{+ka, +to, +mb, +rd}:
      fin_start(open, ka, to, mb, rd, r, evs)

def L.conn_finish(c, r, open, evs):
  fin_law(c, r, open, evs)

# ---------------------------------------------------------------------
# conn_send_open: one lemma per dispatcher
# ---------------------------------------------------------------------

def op_sendpend(hp: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), True{}) == L.chk_open(T, op(L.cst_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hp:
    case True{}:
      {==}
    case False{}:
      {==}


def op_opened(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), True{}) == L.chk_open(T, op(L.cst_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      op_sendpend(hp, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, Conn.POpen{}, pd, pt, ip, pr, T)
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def op_sent(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def op_sendfailed(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), o) == L.chk_open(T, op(L.cst_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match l:
    case True{}:
      {==}
    case False{}:
      {==}


def op_answer(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>, +hf: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, m) == True{} : Bool})
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), o) == L.chk_open(T, op(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{res}:
      match res:
        case Fail{e}:
          {==}
        case Done{pr}:
          match pr:
            case (+r0, +lo0):
              {==}

def op_followopen(kept: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +hp2: Nat, +T: List<&2, L.CItem>, +ev: {Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o) == kept : Bool})
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2))), T), o) == L.chk_open(T, op(L.cst_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)))) : Bool}:
  match kept:
    case True{}:
      %Equal.sym(Bool, o, True{}, and_r(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(xp0)), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o, ev))
        : {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.open(True{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, _, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2))), T), _) == L.chk_open(T, op(L.cst_of(Conn.follow.open(True{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, _, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)))) : Bool}
      {==}
    case False{}:
      {==}


def op_followhost(same: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text))), T), o) == L.chk_open(T, op(L.cst_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)))) : Bool}:
  match same:
    case True{}:
      op_followopen(Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, nq, text, Conn.u_port(Conn.q_url(nq)), T, {==})
    case False{}:
      {==}


def op_followok(ok: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nt: Tgt.Target, +pu: Result<&2, &2, String, Tgt.Url>, +kk: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk))), T), o) == L.chk_open(T, op(L.cst_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)))) : Bool}:
  match ok:
    case True{}:
      op_followhost(Conn.same_host(Conn.u_host(Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)})), Conn.u_host(Conn.q_url(Conn.cur_req(k)))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}, Http.request(Conn.q_target(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_body(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_seq(q), Conn.q_name(q), Conn.c_ka(Conn.CCfg{ka, to, mb, rd})), T)
    case False{}:
      {==}


def op_redirect(stop: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match stop:
    case True{}:
      {==}
    case False{}:
      op_followok(Result.is_done(&2, &2, String, Tgt.Url, Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})))))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))))), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), T)


def op_badof(body: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +good: Http.Parse, +msg: String, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg))), T), o) == L.chk_open(T, op(L.cst_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)))) : Bool}:
  match body:
    case True{}:
      {==}
    case False{}:
      {==}


def op_gotmore(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def op_gotbad(b: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data))), T), o) == L.chk_open(T, op(L.cst_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)))) : Bool}:
  match b:
    case True{}:
      op_badof(Conn.p_body(Conn.upto(data, False{}, old, old)), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.upto(data, False{}, old, old), Conn.bad.msg(Conn.p_stat(Conn.upto(data, False{}, old, old)), Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Conn.fail_msg(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet})))), T)
    case False{}:
      op_gotmore(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, T)


def op_gotdue(dd: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data))), T), o) == L.chk_open(T, op(L.cst_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)))) : Bool}:
  match dd:
    case True{}:
      op_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)
    case False{}:
      op_gotbad(Conn.is_fail(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, old, data, T)


def op_gotfin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +p2: Http.Parse, +d: String, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(p2)) == f : Bool})
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d))), T), o) == L.chk_open(T, op(L.cst_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)))) : Bool}:
  match f:
    case True{}:
      op_answer(Http.done(p2), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T, ev)
    case False{}:
      op_gotdue(Conn.due(Conn.rx_feed(Conn.CCfg{ka, to, mb, rd}, Conn.Rx{xb, xhd, xp, xp0, xmet}, p2, d)), ka, to, mb, rd, q, o, k, Conn.rx_buf(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), Conn.rx_hd(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), p2, Conn.rx_p0(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), xmet, ph, pd, pt, hp, ip, pr, xp, d, T)


def op_eofnl(nl: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match nl:
    case True{}:
      {==}
    case False{}:
      {==}


def op_eofempty(em: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match em:
    case True{}:
      {==}
    case False{}:
      op_eofnl(String.ends_with(Conn.final_from(String.reverse(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet}))), "\n"), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def op_eoftext(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hin:
    case True{}:
      {==}
    case False{}:
      op_eofempty(String.is_empty(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def op_eofredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match r:
    case True{}:
      op_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)
    case False{}:
      op_eoftext(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def op_eofmet(xmet: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match xmet:
    case True{}:
      {==}
    case False{}:
      op_eofredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, False{}})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, False{}, ph, pd, pt, hp, ip, pr, T)


def op_eoflost(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match l:
    case True{}:
      {==}
    case False{}:
      op_eofmet(xmet, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, ph, pd, pt, hp, ip, pr, T)


def op_eoffin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(xp)) == f : Bool})
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match f:
    case True{}:
      op_answer(Http.done(xp), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T, ev)
    case False{}:
      op_eoflost(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def op_latein(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hin:
    case True{}:
      {==}
    case False{}:
      {==}


def op_lateredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      op_latein(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)


def op_resolved(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), o) == L.chk_open(T, op(L.cst_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def op_resolvefailed(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +T: List<&2, L.CItem>)
  -> {L.chk_open(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), o) == L.chk_open(T, op(L.cst_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def op_ev(e: Conn.Ev, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +T: List<&2, L.CItem>)
  -> {L.chk_open(Con{L.CIEv{e}, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T)}, o) == L.chk_open(T, op(L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match e:
    case Conn.Opened{}:
      op_opened(ph, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, T)
    case Conn.OpenFailed{+m}:
      {==}
    case Conn.Sent{}:
      op_sent(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, T)
    case Conn.SendFailed{+m}:
      op_sendfailed(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, False{}, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, m, T)
    case Conn.Got{+d}:
      op_gotfin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d))), ka, to, mb, rd, q, o, Conn.set_got(k, d), xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d), d, T, {==})
    case Conn.Eof{}:
      op_eoffin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Conn.rx_p(Conn.rx_eof(Conn.Rx{xb, xhd, xp, xp0, xmet})))), ka, to, mb, rd, q, False{}, k, xb, xhd, Http.eof(xp), xp0, xmet, ph, pd, pt, hp, ip, pr, T, {==})
    case Conn.Late{}:
      op_lateredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, T)
    case Conn.Resolved{+ip2}:
      op_resolved(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip2, pr, T)
    case Conn.ResolveFailed{+m}:
      op_resolvefailed(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, m, T)


# ---------------------------------------------------------------------
# conn_send_open: the machine's open flag is the checker's, until Finish
# ---------------------------------------------------------------------

def op_over(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +f: Bool)
  -> {L.chk_open(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, True{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), f) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Conn.Opened{}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, True{})
        case Conn.OpenFailed{m}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, False{})
        case Conn.Sent{}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)
        case Conn.SendFailed{m}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, False{})
        case Conn.Got{d}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)
        case Conn.Eof{}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, False{})
        case Conn.Late{}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)
        case Conn.Resolved{i}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)
        case Conn.ResolveFailed{m}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)


def op_steps(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, s: Conn.State) -> {L.chk_open(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, s), op(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match s:
        case Conn.CState{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}:
          match v:
            case True{}:
              match x:
                case Conn.Rx{+xb, +xhd, +xp, +xp0, +xmet}:
                  op_over(Con{e, rest}, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, o)
            case False{}:
              match x:
                case Conn.Rx{+xb, +xhd, +xp, +xp0, +xmet}:
                  %Equal.sym(Bool, L.chk_open(Con{L.CIEv{e}, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))))}, op(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})),
                      L.chk_open(L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), op(L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))),
                      op_ev(e, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))))
                    : {_ == True{} : Bool}
                  op_steps(rest, ka, to, mb, rd, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))

def op_start(open: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +r: Conn.Req, +evs: List<&2, Conn.Ev>)
  -> {L.chk_open(L.ctimeline(Conn.CCfg{ka, to, mb, rd}, r, open, evs), open) == True{} : Bool}:
  match open:
    case True{}:
      op_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, True{})))
    case False{}:
      op_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, False{})))

def op_law(c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>) -> {L.chk_open(L.ctimeline(c, r, open, evs), open) == True{} : Bool}:
  match c:
    case Conn.CCfg{+ka, +to, +mb, +rd}:
      op_start(open, ka, to, mb, rd, r, evs)

def L.conn_send_open(c, r, open, evs):
  op_law(c, r, open, evs)

# ---------------------------------------------------------------------
# conn_live: one lemma per dispatcher (the invariant holds after a batch)
# ---------------------------------------------------------------------

def lv_sendpend(hp: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, True{}, sd, rv, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match hp:
    case True{}:
      {==}
    case False{}:
      {==}


def lv_opened(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, True{}, sd, rv, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      and_i(ph_ok(Conn.PResolve{}, rs, True{}, sd, rv, out), met_ok(xmet, Conn.PResolve{}), hP, hM)
    case Conn.POpen{}:
      lv_sendpend(hp, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, Conn.POpen{}, pd, pt, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)
    case Conn.PSend{}:
      and_i(ph_ok(Conn.PSend{}, rs, True{}, sd, rv, out), met_ok(xmet, Conn.PSend{}), hP, hM)
    case Conn.PRecv{}:
      and_i(ph_ok(Conn.PRecv{}, rs, True{}, sd, rv, out), met_ok(xmet, Conn.PRecv{}), hP, hM)


def lv_sent(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, True{}, rv, True{}) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, True{}, dn})) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      and_i(ph_ok(Conn.PResolve{}, rs, op, True{}, rv, True{}), met_ok(xmet, Conn.PResolve{}), hP, hM)
    case Conn.POpen{}:
      and_i(ph_ok(Conn.POpen{}, rs, op, True{}, rv, True{}), met_ok(xmet, Conn.POpen{}), hP, hM)
    case Conn.PSend{}:
      met_sr(xmet, hM)
    case Conn.PRecv{}:
      and_i(ph_ok(Conn.PRecv{}, rs, op, True{}, rv, True{}), met_ok(xmet, Conn.PRecv{}), hP, hM)


def lv_sendfailed(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, True{}, rv, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), wcmds(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match l:
    case True{}:
      met_popen(xmet)
    case False{}:
      {==}


def lv_answer(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hf: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, m) == True{} : Bool}, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), wcmds(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({inv(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), wcmds(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}, N.false_ne_true(hf))
    case Some{res}:
      match res:
        case Fail{e}:
          Empty.absurd({inv(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), wcmds(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}, N.false_ne_true(hf))
        case Done{pr}:
          match pr:
            case (+r0, +lo0):
              {==}

def lv_followopen(kept: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +hp2: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +ev: {Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o) == kept : Bool}, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), wcmds(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      {==}


def lv_followhost(same: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), wcmds(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match same:
    case True{}:
      lv_followopen(Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, nq, text, Conn.u_port(Conn.q_url(nq)), rs, op, sd, rv, out, dn, T, {==}, hP, hM)
    case False{}:
      {==}


def lv_followok(ok: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nt: Tgt.Target, +pu: Result<&2, &2, String, Tgt.Url>, +kk: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), wcmds(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match ok:
    case True{}:
      lv_followhost(Conn.same_host(Conn.u_host(Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)})), Conn.u_host(Conn.q_url(Conn.cur_req(k)))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}, Http.request(Conn.q_target(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_body(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_seq(q), Conn.q_name(q), Conn.c_ka(Conn.CCfg{ka, to, mb, rd})), rs, op, sd, rv, out, dn, T, hP, hM)
    case False{}:
      {==}


def lv_redirect(stop: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match stop:
    case True{}:
      {==}
    case False{}:
      lv_followok(Result.is_done(&2, &2, String, Tgt.Url, Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})))))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))))), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), rs, op, sd, rv, out, dn, T, hP, hM)


def lv_badof(body: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +good: Http.Parse, +msg: String, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), wcmds(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match body:
    case True{}:
      {==}
    case False{}:
      {==}


def lv_gotmore(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      and_i(ph_ok(Conn.PResolve{}, rs, op, sd, True{}, out), met_ok(xmet, Conn.PResolve{}), hP, hM)
    case Conn.POpen{}:
      and_i(ph_ok(Conn.POpen{}, rs, op, sd, True{}, out), met_ok(xmet, Conn.POpen{}), hP, hM)
    case Conn.PSend{}:
      and_i(ph_ok(Conn.PSend{}, rs, op, sd, True{}, out), met_ok(xmet, Conn.PSend{}), hP, hM)
    case Conn.PRecv{}:
      and_i(ph_ok(Conn.PRecv{}, rs, op, sd, True{}, out), met_ok(xmet, Conn.PRecv{}), hP, hM)


def lv_gotbad(b: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), wcmds(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match b:
    case True{}:
      lv_badof(Conn.p_body(Conn.upto(data, False{}, old, old)), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.upto(data, False{}, old, old), Conn.bad.msg(Conn.p_stat(Conn.upto(data, False{}, old, old)), Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Conn.fail_msg(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet})))), rs, op, sd, rv, out, dn, T, hP, hM)
    case False{}:
      lv_gotmore(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_gotdue(dd: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), wcmds(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match dd:
    case True{}:
      lv_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)
    case False{}:
      lv_gotbad(Conn.is_fail(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, old, data, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_gotfin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +p2: Http.Parse, +d: String, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(p2)) == f : Bool}, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), wcmds(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match f:
    case True{}:
      lv_answer(Http.done(p2), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, ev, hP, hM)
    case False{}:
      lv_gotdue(Conn.due(Conn.rx_feed(Conn.CCfg{ka, to, mb, rd}, Conn.Rx{xb, xhd, xp, xp0, xmet}, p2, d)), ka, to, mb, rd, q, o, k, Conn.rx_buf(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), Conn.rx_hd(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), p2, Conn.rx_p0(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), xmet, ph, pd, pt, hp, ip, pr, xp, d, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_eofnl(nl: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match nl:
    case True{}:
      {==}
    case False{}:
      {==}


def lv_eofempty(em: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match em:
    case True{}:
      {==}
    case False{}:
      lv_eofnl(String.ends_with(Conn.final_from(String.reverse(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet}))), "\n"), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_eoftext(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match hin:
    case True{}:
      {==}
    case False{}:
      lv_eofempty(String.is_empty(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_eofredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match r:
    case True{}:
      lv_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)
    case False{}:
      lv_eoftext(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_eofmet(xmet: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match xmet:
    case True{}:
      match ph:
        case Conn.PResolve{}:
          and_i(ph_ok(Conn.PResolve{}, rs, op, sd, True{}, out), met_ok(True{}, Conn.PResolve{}), hP, hM)
        case Conn.POpen{}:
          and_i(ph_ok(Conn.POpen{}, rs, op, sd, True{}, out), met_ok(True{}, Conn.POpen{}), hP, hM)
        case Conn.PSend{}:
          Empty.absurd({inv(L.cst_of(Conn.eof.met(True{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, True{}}, Conn.PSend{}, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.met(True{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, True{}}, Conn.PSend{}, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}, N.false_ne_true(hM))
        case Conn.PRecv{}:
          Empty.absurd({inv(L.cst_of(Conn.eof.met(True{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, True{}}, Conn.PRecv{}, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.met(True{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, True{}}, Conn.PRecv{}, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}, N.false_ne_true(hM))
    case False{}:
      lv_eofredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, False{}})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, False{}, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_eoflost(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match l:
    case True{}:
      met_popen(xmet)
    case False{}:
      lv_eofmet(xmet, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_eoffin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(xp)) == f : Bool}, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match f:
    case True{}:
      lv_answer(Http.done(xp), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, ev, hP, hM)
    case False{}:
      lv_eoflost(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_latein(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match hin:
    case True{}:
      {==}
    case False{}:
      {==}


def lv_lateredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, rs, op, sd, True{}, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      lv_latein(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, T, hP, hM)


def lv_resolved(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, True{}, op, sd, rv, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      met_popen(xmet)
    case Conn.POpen{}:
      and_i(ph_ok(Conn.POpen{}, True{}, op, sd, rv, out), met_ok(xmet, Conn.POpen{}), hP, hM)
    case Conn.PSend{}:
      and_i(ph_ok(Conn.PSend{}, True{}, op, sd, rv, out), met_ok(xmet, Conn.PSend{}), hP, hM)
    case Conn.PRecv{}:
      and_i(ph_ok(Conn.PRecv{}, True{}, op, sd, rv, out), met_ok(xmet, Conn.PRecv{}), hP, hM)


def lv_resolvefailed(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hP: {ph_ok(ph, True{}, op, sd, rv, out) == True{} : Bool}, +hM: {met_ok(xmet, ph) == True{} : Bool})
  -> {inv(L.cst_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), wcmds(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), L.Wait{rs, op, sd, rv, out, dn})) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      and_i(ph_ok(Conn.POpen{}, True{}, op, sd, rv, out), met_ok(xmet, Conn.POpen{}), hP, hM)
    case Conn.PSend{}:
      and_i(ph_ok(Conn.PSend{}, True{}, op, sd, rv, out), met_ok(xmet, Conn.PSend{}), hP, hM)
    case Conn.PRecv{}:
      and_i(ph_ok(Conn.PRecv{}, True{}, op, sd, rv, out), met_ok(xmet, Conn.PRecv{}), hP, hM)


def lv_ev(e: Conn.Ev, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +T: List<&2, L.CItem>, +hI: {Bool.and(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph)) == True{} : Bool})
  -> {inv(L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.w_ev(L.Wait{rs, op, sd, rv, out, dn}, e))) == True{} : Bool}:
  match e:
    case Conn.Opened{}:
      lv_opened(ph, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, rs, False{}, sd, rv, out, dn, T, up_op(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)), and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))
    case Conn.OpenFailed{+m}:
      {==}
    case Conn.Sent{}:
      lv_sent(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, rs, op, False{}, rv, dn, T, up_sent(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)), and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))
    case Conn.SendFailed{+m}:
      lv_sendfailed(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, False{}, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, m, rs, op, False{}, rv, out, dn, T, up_sd(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)), and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))
    case Conn.Got{+d}:
      lv_gotfin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d))), ka, to, mb, rd, q, o, Conn.set_got(k, d), xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d), d, rs, op, sd, False{}, out, dn, T, {==}, up_rv(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)), and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))
    case Conn.Eof{}:
      lv_eoffin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Conn.rx_p(Conn.rx_eof(Conn.Rx{xb, xhd, xp, xp0, xmet})))), ka, to, mb, rd, q, False{}, k, xb, xhd, Http.eof(xp), xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, False{}, out, dn, T, {==}, up_rv(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)), and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))
    case Conn.Late{}:
      lv_lateredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, False{}, out, dn, T, up_rv(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)), and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))
    case Conn.Resolved{+ip2}:
      lv_resolved(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip2, pr, False{}, op, sd, rv, out, dn, T, up_rs(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)), and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))
    case Conn.ResolveFailed{+m}:
      lv_resolvefailed(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, m, False{}, op, sd, rv, out, dn, T, up_rs(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)), and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))


# ---------------------------------------------------------------------
# conn_live: the walk over the timeline
# ---------------------------------------------------------------------

def pend_app(cs: List<&2, Conn.Cmd>, +T: List<&2, L.CItem>, +w: L.Wait)
  -> {L.chk_pending(List.append(&2, L.CItem, L.ccmds_items(cs), T), w) == L.chk_pending(T, wcmds(cs, w)) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+k, +rest}:
      pend_app(rest, T, L.w_cmd(w, k))

def or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      bool_absurd(b, True{}, e)

def or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# a phase's wait makes the request live
def live_of(ph: Conn.Phase, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +h: {ph_ok(ph, rs, op, sd, rv, out) == True{} : Bool})
  -> {L.w_live(L.Wait{rs, op, sd, rv, out, dn}) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      or_l(Bool.or(dn, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)), or_r(dn, rs, h))
    case Conn.POpen{}:
      or_r(Bool.or(dn, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)), or_l(Bool.or(op, sd), Bool.and(out, rv), or_l(op, sd, h)))
    case Conn.PSend{}:
      or_r(Bool.or(dn, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)), or_l(Bool.or(op, sd), Bool.and(out, rv), or_r(op, sd, h)))
    case Conn.PRecv{}:
      or_r(Bool.or(dn, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)), or_r(Bool.or(op, sd), Bool.and(out, rv), and_i(out, rv, and_r(rv, out, h), and_l(rv, out, h))))

# once finished, the request is done and stays so
def lv_over(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +x: Conn.Rx, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool)
  -> {L.chk_pending(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, True{}, k, x, ph, pd, pt, hp, ip, pr}), L.Wait{rs, op, sd, rv, out, True{}}) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Conn.Opened{}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, False{}, sd, rv, out)
        case Conn.OpenFailed{m}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, False{}, sd, rv, out)
        case Conn.Sent{}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, False{}, rv, True{})
        case Conn.SendFailed{m}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, False{}, rv, out)
        case Conn.Got{d}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, sd, False{}, out)
        case Conn.Eof{}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, sd, False{}, out)
        case Conn.Late{}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, sd, False{}, out)
        case Conn.Resolved{i}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, False{}, op, sd, rv, out)
        case Conn.ResolveFailed{m}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, False{}, op, sd, rv, out)

def inv_live(s: Conn.State, w: L.Wait, h: {inv(s, w) == True{} : Bool}) -> {L.w_live(w) == True{} : Bool}:
  match s:
    case Conn.CState{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}:
      match v:
        case True{}:
          match w:
            case L.Wait{+rs, +op, +sd, +rv, +out, +dn}:
              %Equal.sym(Bool, dn, True{}, h) : {L.w_live(L.Wait{rs, op, sd, rv, out, _}) == True{} : Bool}
              {==}
        case False{}:
          match w:
            case L.Wait{+rs, +op, +sd, +rv, +out, +dn}:
              live_of(ph, rs, op, sd, rv, out, dn, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(Conn.rx_met(x), ph), h))

def lv_steps(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, s: Conn.State, w: L.Wait, +h: {inv(s, w) == True{} : Bool})
  -> {L.chk_pending(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, s), w) == True{} : Bool}:
  match evs:
    case Nil{}:
      inv_live(s, w, h)
    case Con{+e, +rest}:
      match s:
        case Conn.CState{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}:
          match v:
            case True{}:
              match w:
                case L.Wait{+rs, +op, +sd, +rv, +out, +dn}:
                  %Equal.sym(Bool, dn, True{}, h) : {L.chk_pending(L.csteps(Con{e, rest}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, True{}, k, x, ph, pd, pt, hp, ip, pr}), L.Wait{rs, op, sd, rv, out, _}) == True{} : Bool}
                  lv_over(Con{e, rest}, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out)
            case False{}:
              match x:
                case Conn.Rx{+xb, +xhd, +xp, +xp0, +xmet}:
                  match w:
                    case L.Wait{+rs, +op, +sd, +rv, +out, +dn}:
                      %Equal.sym(Bool, L.w_live(L.Wait{rs, op, sd, rv, out, dn}), True{}, live_of(ph, rs, op, sd, rv, out, dn, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), h)))
                        : {Bool.and(_, L.chk_pending(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))), L.w_ev(L.Wait{rs, op, sd, rv, out, dn}, e))) == True{} : Bool}
                      %Equal.sym(Bool, L.chk_pending(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))), L.w_ev(L.Wait{rs, op, sd, rv, out, dn}, e)), L.chk_pending(L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), wcmds(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.w_ev(L.Wait{rs, op, sd, rv, out, dn}, e))), pend_app(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), L.w_ev(L.Wait{rs, op, sd, rv, out, dn}, e)))
                        : {Bool.and(True{}, _) == True{} : Bool}
                      lv_steps(rest, ka, to, mb, rd, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), wcmds(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), L.w_ev(L.Wait{rs, op, sd, rv, out, dn}, e)), lv_ev(e, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out, dn, L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), h))

def lv_start(open: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +r: Conn.Req, +evs: List<&2, Conn.Ev>)
  -> {L.chk_pending(L.ctimeline(Conn.CCfg{ka, to, mb, rd}, r, open, evs), L.Wait{False{}, False{}, False{}, False{}, False{}, False{}}) == True{} : Bool}:
  match open:
    case True{}:
      lv_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, True{})), L.Wait{False{}, False{}, True{}, False{}, False{}, False{}}, {==})
    case False{}:
      lv_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, False{})), L.Wait{False{}, True{}, False{}, False{}, False{}, False{}}, {==})

def lv_law(c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>)
  -> {L.chk_pending(L.ctimeline(c, r, open, evs), L.Wait{False{}, False{}, False{}, False{}, False{}, False{}}) == True{} : Bool}:
  match c:
    case Conn.CCfg{+ka, +to, +mb, +rd}:
      lv_start(open, ka, to, mb, rd, r, evs)

def L.conn_live(c, r, open, evs):
  lv_law(c, r, open, evs)

# ---------------------------------------------------------------------
# conn_answer: the checker after a batch (an_*), and the parse invariant (ai_*)
# ---------------------------------------------------------------------

def an_sendpend(hp: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hp:
    case True{}:
      {==}
    case False{}:
      {==}


def an_opened(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      an_sendpend(hp, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, Conn.POpen{}, pd, pt, ip, pr, hd, bf, ef, T)
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def an_sent(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def an_sendfailed(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), hd), a_bf(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), bf), a_ef(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), ef), ov(L.cst_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match l:
    case True{}:
      {==}
    case False{}:
      {==}


def an_answer(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hf: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, m) == True{} : Bool}, +hPB: {m == L.parse_buf(ef, mb, hd, bf) : Maybe<&1, Result<&1, &1, String, Http.Resp & String>>})
  -> {Bool.and(L.must_answer(Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T)), L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{})) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), hd), a_bf(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), bf), a_ef(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), ef), ov(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match m:
    case None{}:
      Empty.absurd({Bool.and(L.must_answer(Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{}))), T)), L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{})) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), hd), a_bf(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), bf), a_ef(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), ef), ov(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})))) : Bool}, N.false_ne_true(hf))
    case Some{res}:
      match res:
        case Fail{e}:
          Empty.absurd({Bool.and(L.must_answer(Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}}))), T)), L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{})) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), hd), a_bf(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), bf), a_ef(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), ef), ov(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})))) : Bool}, N.false_ne_true(hf))
        case Done{pr}:
          match pr:
            case (+r0, +lo0):
              %hPB : {Bool.and(Bool.or(Bool.not(L.final_resp(Conn.CCfg{ka, to, mb, rd}, _)), L.answer_of(ka, _, r0, Bool.and(Bool.and(Conn.r_keep(r0), ka), String.is_empty(lo0)))), Bool.and(L.answer_of(ka, _, r0, Bool.and(Bool.and(Conn.r_keep(r0), ka), String.is_empty(lo0))), Bool.and(Bool.or(Maybe.is_none(&2, Nat, rd), Bool.not(L.is_redirect(r0))), L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{})))) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{}) : Bool}
              %Equal.sym(Bool, L.answer_of(ka, Some{Done{(r0, lo0)}}, r0, Bool.and(Bool.and(Conn.r_keep(r0), ka), String.is_empty(lo0))), True{}, aok(ka, r0, lo0)) : {Bool.and(Bool.or(Bool.not(L.final_resp(Conn.CCfg{ka, to, mb, rd}, Some{Done{(r0, lo0)}})), _), Bool.and(_, Bool.and(Bool.or(Maybe.is_none(&2, Nat, rd), Bool.not(L.is_redirect(r0))), L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{})))) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{}) : Bool}
              %Equal.sym(Bool, Bool.or(Bool.not(L.final_resp(Conn.CCfg{ka, to, mb, rd}, Some{Done{(r0, lo0)}})), True{}), True{}, or_t(Bool.not(L.final_resp(Conn.CCfg{ka, to, mb, rd}, Some{Done{(r0, lo0)}})))) : {Bool.and(_, Bool.and(True{}, Bool.and(Bool.or(Maybe.is_none(&2, Nat, rd), Bool.not(L.is_redirect(r0))), L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{})))) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{}) : Bool}
              %Equal.sym(Bool, Bool.or(Maybe.is_none(&2, Nat, rd), Bool.not(L.is_redirect(r0))), True{}, rd_ok(rd, r0, hf)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(_, L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{})))) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{}) : Bool}
              {==}

def an_followopen(kept: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +hp2: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +ev: {Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o) == kept : Bool})
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), hd), a_bf(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), bf), a_ef(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), ef), ov(L.cst_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)))) : Bool}:
  match kept:
    case True{}:
      {==}
    case False{}:
      {==}


def an_followhost(same: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), hd), a_bf(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), bf), a_ef(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), ef), ov(L.cst_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)))) : Bool}:
  match same:
    case True{}:
      an_followopen(Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, nq, text, Conn.u_port(Conn.q_url(nq)), hd, bf, ef, T, {==})
    case False{}:
      {==}


def an_followok(ok: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nt: Tgt.Target, +pu: Result<&2, &2, String, Tgt.Url>, +kk: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), hd), a_bf(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), bf), a_ef(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), ef), ov(L.cst_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)))) : Bool}:
  match ok:
    case True{}:
      an_followhost(Conn.same_host(Conn.u_host(Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)})), Conn.u_host(Conn.q_url(Conn.cur_req(k)))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}, Http.request(Conn.q_target(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_body(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_seq(q), Conn.q_name(q), Conn.c_ka(Conn.CCfg{ka, to, mb, rd})), hd, bf, ef, T)
    case False{}:
      {==}


def an_redirect(stop: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match stop:
    case True{}:
      {==}
    case False{}:
      an_followok(Result.is_done(&2, &2, String, Tgt.Url, Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})))))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))))), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), hd, bf, ef, T)


def an_badof(body: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +good: Http.Parse, +msg: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), hd), a_bf(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), bf), a_ef(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), ef), ov(L.cst_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)))) : Bool}:
  match body:
    case True{}:
      {==}
    case False{}:
      {==}


def an_gotmore(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def an_gotbad(b: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), hd), a_bf(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), bf), a_ef(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), ef), ov(L.cst_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)))) : Bool}:
  match b:
    case True{}:
      an_badof(Conn.p_body(Conn.upto(data, False{}, old, old)), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.upto(data, False{}, old, old), Conn.bad.msg(Conn.p_stat(Conn.upto(data, False{}, old, old)), Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Conn.fail_msg(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet})))), hd, bf, ef, T)
    case False{}:
      an_gotmore(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, hd, bf, ef, T)


def an_gotdue(dd: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), hd), a_bf(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), bf), a_ef(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), ef), ov(L.cst_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)))) : Bool}:
  match dd:
    case True{}:
      an_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)
    case False{}:
      an_gotbad(Conn.is_fail(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, old, data, hd, bf, ef, T)


def an_gotfin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +p2: Http.Parse, +d: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(p2)) == f : Bool}, +hQ: {p2 == PE(mb, hd, bf, ef) : Http.Parse})
  -> {Bool.and(L.must_answer(Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d))), T)), L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{})) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), hd), a_bf(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), bf), a_ef(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), ef), ov(L.cst_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)))) : Bool}:
  match f:
    case True{}:
      an_answer(Http.done(p2), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, ev, Equal.trans(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, Http.done(p2), Http.done(PE(mb, hd, bf, ef)), L.parse_buf(ef, mb, hd, bf), Equal.cong(Http.Parse, Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, q => Http.done(q), p2, PE(mb, hd, bf, ef), hQ), Equal.sym(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, L.parse_buf(ef, mb, hd, bf), Http.done(PE(mb, hd, bf, ef)), pb_pe(ef, mb, hd, bf))))
    case False{}:
      %Equal.sym(Bool, L.final_resp(Conn.CCfg{ka, to, mb, rd}, L.parse_buf(ef, mb, hd, bf)), False{}, fr_eq(ka, to, mb, rd, hd, bf, ef, p2, False{}, hQ, ev))
        : {Bool.and(Bool.or(Bool.not(_), L.answers(Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, L.batch(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d))), T)))), L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.got.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{})) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.got.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), hd), a_bf(L.ccs_of(Conn.got.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), bf), a_ef(L.ccs_of(Conn.got.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), ef), ov(L.cst_of(Conn.got.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)))) : Bool}
      an_gotdue(Conn.due(Conn.rx_feed(Conn.CCfg{ka, to, mb, rd}, Conn.Rx{xb, xhd, xp, xp0, xmet}, p2, d)), ka, to, mb, rd, q, o, k, Conn.rx_buf(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), Conn.rx_hd(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), p2, Conn.rx_p0(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), xmet, ph, pd, pt, hp, ip, pr, xp, d, hd, bf, ef, T)


def an_eofnl(nl: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match nl:
    case True{}:
      {==}
    case False{}:
      {==}


def an_eofempty(em: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match em:
    case True{}:
      {==}
    case False{}:
      an_eofnl(String.ends_with(Conn.final_from(String.reverse(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet}))), "\n"), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)


def an_eoftext(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hin:
    case True{}:
      {==}
    case False{}:
      an_eofempty(String.is_empty(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)


def an_eofredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match r:
    case True{}:
      an_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)
    case False{}:
      an_eoftext(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)


def an_eofmet(xmet: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match xmet:
    case True{}:
      {==}
    case False{}:
      an_eofredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, False{}})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, False{}, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)


def an_eoflost(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match l:
    case True{}:
      {==}
    case False{}:
      an_eofmet(xmet, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)


def an_eoffin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(xp)) == f : Bool}, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> {Bool.and(L.must_answer(Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T)), L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{})) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match f:
    case True{}:
      an_answer(Http.done(xp), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, ev, Equal.trans(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, Http.done(xp), Http.done(PE(mb, hd, bf, ef)), L.parse_buf(ef, mb, hd, bf), Equal.cong(Http.Parse, Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, q => Http.done(q), xp, PE(mb, hd, bf, ef), hX), Equal.sym(Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, L.parse_buf(ef, mb, hd, bf), Http.done(PE(mb, hd, bf, ef)), pb_pe(ef, mb, hd, bf))))
    case False{}:
      %Equal.sym(Bool, L.final_resp(Conn.CCfg{ka, to, mb, rd}, L.parse_buf(ef, mb, hd, bf)), False{}, fr_eq(ka, to, mb, rd, hd, bf, ef, xp, False{}, hX, ev))
        : {Bool.and(Bool.or(Bool.not(_), L.answers(Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, L.batch(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T)))), L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.eof.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{})) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.eof.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.eof.fin(False{}, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}
      an_eoflost(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)


def an_latein(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match hin:
    case True{}:
      {==}
    case False{}:
      {==}


def an_lateredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      an_latein(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)


def an_resolved(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef), ov(L.cst_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def an_resolvefailed(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>)
  -> {L.chk_answer(List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m))), T), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), hd), a_bf(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), bf), a_ef(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), ef), ov(L.cst_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)))) : Bool}:
  match ph:
    case Conn.PResolve{}:
      {==}
    case Conn.POpen{}:
      {==}
    case Conn.PSend{}:
      {==}
    case Conn.PRecv{}:
      {==}


def an_ev(e: Conn.Ev, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> {L.chk_answer(Con{L.CIEv{e}, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), T)}, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}) == L.chk_answer(T, Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ev_bf(e, bf)), a_ef(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ev_ef(e, ef)), ov(L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))) : Bool}:
  match e:
    case Conn.Opened{}:
      an_opened(ph, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, hd, bf, ef, T)
    case Conn.OpenFailed{+m}:
      {==}
    case Conn.Sent{}:
      an_sent(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, hd, bf, ef, T)
    case Conn.SendFailed{+m}:
      an_sendfailed(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, False{}, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, m, hd, bf, ef, T)
    case Conn.Got{+d}:
      an_gotfin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d))), ka, to, mb, rd, q, o, Conn.set_got(k, d), xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d), d, hd, bf ++ d, ef, T, {==}, Equal.trans(Http.Parse, Http.feed(xp, d), Http.feed(PE(mb, hd, bf, ef), d), PE(mb, hd, bf ++ d, ef), Equal.cong(Http.Parse, Http.Parse, p => Http.feed(p, d), xp, PE(mb, hd, bf, ef), hX), pe_feed(ef, mb, hd, bf, d)))
    case Conn.Eof{}:
      an_eoffin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Conn.rx_p(Conn.rx_eof(Conn.Rx{xb, xhd, xp, xp0, xmet})))), ka, to, mb, rd, q, False{}, k, xb, xhd, Http.eof(xp), xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, True{}, T, {==}, Equal.trans(Http.Parse, Http.eof(xp), Http.eof(PE(mb, hd, bf, ef)), PE(mb, hd, bf, True{}), Equal.cong(Http.Parse, Http.Parse, p => Http.eof(p), xp, PE(mb, hd, bf, ef), hX), pe_eof(ef, mb, hd, bf)))
    case Conn.Late{}:
      an_lateredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T)
    case Conn.Resolved{+ip2}:
      an_resolved(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip2, pr, hd, bf, ef, T)
    case Conn.ResolveFailed{+m}:
      an_resolvefailed(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, m, hd, bf, ef, T)


def ai_sendpend(hp: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.send_pend(hp, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match hp:
    case True{}:
      {==}
    case False{}:
      {==}


def ai_opened(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.on_opened(ph, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, True{}, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match ph:
    case Conn.PResolve{}:
      hX
    case Conn.POpen{}:
      ai_sendpend(hp, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, Conn.POpen{}, pd, pt, ip, pr, hd, bf, ef, T, hX)
    case Conn.PSend{}:
      hX
    case Conn.PRecv{}:
      hX


def ai_sent(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.on_sent(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match ph:
    case Conn.PResolve{}:
      hX
    case Conn.POpen{}:
      hX
    case Conn.PSend{}:
      hX
    case Conn.PRecv{}:
      hX


def ai_sendfailed(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), mb, a_hd(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), hd), a_bf(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), bf), a_ef(L.ccs_of(Conn.on_send_failed(l, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), ef)):
  match l:
    case True{}:
      hX
    case False{}:
      Unit{}


def ai_answer(m: Maybe<&1, Result<&1, &1, String, Http.Resp & String>>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hf: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, m) == True{} : Bool})
  -> inv_a(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), mb, a_hd(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), hd), a_bf(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), bf), a_ef(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), ef)):
  match m:
    case None{}:
      Empty.absurd(inv_a(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), mb, a_hd(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), hd), a_bf(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), bf), a_ef(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, None{})), ef)), N.false_ne_true(hf))
    case Some{res}:
      match res:
        case Fail{e}:
          Empty.absurd(inv_a(L.cst_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), mb, a_hd(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), hd), a_bf(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), bf), a_ef(L.ccs_of(Conn.answer(Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Some{Fail{e}})), ef)), N.false_ne_true(hf))
        case Done{pr}:
          match pr:
            case (+r0, +lo0):
              Unit{}

def ai_followopen(kept: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +hp2: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +ev: {Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o) == kept : Bool}, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), mb, a_hd(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), hd), a_bf(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), bf), a_ef(L.ccs_of(Conn.follow.open(kept, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text, hp2)), ef)):
  match kept:
    case True{}:
      {==}
    case False{}:
      hX


def ai_followhost(same: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nq: Conn.Req, +text: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), mb, a_hd(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), hd), a_bf(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), bf), a_ef(L.ccs_of(Conn.follow.host(same, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nq, text)), ef)):
  match same:
    case True{}:
      ai_followopen(Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(Conn.CCfg{ka, to, mb, rd}), Http.done(Conn.rx_p0(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, nq, text, Conn.u_port(Conn.q_url(nq)), hd, bf, ef, T, {==}, hX)
    case False{}:
      hX


def ai_followok(ok: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +nt: Tgt.Target, +pu: Result<&2, &2, String, Tgt.Url>, +kk: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), mb, a_hd(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), hd), a_bf(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), bf), a_ef(L.ccs_of(Conn.follow.ok(ok, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, nt, pu, kk)), ef)):
  match ok:
    case True{}:
      ai_followhost(Conn.same_host(Conn.u_host(Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)})), Conn.u_host(Conn.q_url(Conn.cur_req(k)))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}, Http.request(Conn.q_target(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_url(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_body(Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(k)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(k))), Conn.q_seq(q), Conn.q_name(q)}), Conn.q_seq(q), Conn.q_name(q), Conn.c_ka(Conn.CCfg{ka, to, mb, rd})), hd, bf, ef, T, hX)
    case False{}:
      Unit{}


def ai_redirect(stop: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.redirect.of(stop, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match stop:
    case True{}:
      Unit{}
    case False{}:
      ai_followok(Result.is_done(&2, &2, String, Tgt.Url, Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})))))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))), Tgt.parse_url(Conn.tgt_url(Conn.redirect_target(Conn.u_host(Conn.q_url(q)), Conn.q_target(Conn.cur_req(k)), Conn.q_url(Conn.cur_req(k)), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), Conn.hd_loc(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}))))), Conn.hd_code(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), hd, bf, ef, T, hX)


def ai_badof(body: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +good: Http.Parse, +msg: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), mb, a_hd(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), hd), a_bf(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), bf), a_ef(L.ccs_of(Conn.bad.of(body, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, good, msg)), ef)):
  match body:
    case True{}:
      Unit{}
    case False{}:
      Unit{}


def ai_gotmore(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.got.more(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match ph:
    case Conn.PResolve{}:
      hX
    case Conn.POpen{}:
      hX
    case Conn.PSend{}:
      hX
    case Conn.PRecv{}:
      hX


def ai_gotbad(b: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), mb, a_hd(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), hd), a_bf(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), bf), a_ef(L.ccs_of(Conn.got.bad(b, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), ef)):
  match b:
    case True{}:
      ai_badof(Conn.p_body(Conn.upto(data, False{}, old, old)), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Conn.upto(data, False{}, old, old), Conn.bad.msg(Conn.p_stat(Conn.upto(data, False{}, old, old)), Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, Conn.fail_msg(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet})))), hd, bf, ef, T, hX)
    case False{}:
      ai_gotmore(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)


def ai_gotdue(dd: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +old: Http.Parse, +data: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), mb, a_hd(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), hd), a_bf(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), bf), a_ef(L.ccs_of(Conn.got.due(dd, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, old, data)), ef)):
  match dd:
    case True{}:
      ai_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)
    case False{}:
      ai_gotbad(Conn.is_fail(Http.done(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, old, data, hd, bf, ef, T, hX)


def ai_gotfin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +p2: Http.Parse, +d: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(p2)) == f : Bool}, +hQ: {p2 == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), mb, a_hd(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), hd), a_bf(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), bf), a_ef(L.ccs_of(Conn.got.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, p2, d)), ef)):
  match f:
    case True{}:
      ai_answer(Http.done(p2), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, ev)
    case False{}:
      ai_gotdue(Conn.due(Conn.rx_feed(Conn.CCfg{ka, to, mb, rd}, Conn.Rx{xb, xhd, xp, xp0, xmet}, p2, d)), ka, to, mb, rd, q, o, k, Conn.rx_buf(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), Conn.rx_hd(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), p2, Conn.rx_p0(Conn.rx_feed.hd(xhd, Conn.CCfg{ka, to, mb, rd}, xb, p2, xp0, xmet, d)), xmet, ph, pd, pt, hp, ip, pr, xp, d, hd, bf, ef, T, hQ)


def ai_eofnl(nl: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.text.nl(nl, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match nl:
    case True{}:
      Unit{}
    case False{}:
      Unit{}


def ai_eofempty(em: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.text.empty(em, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match em:
    case True{}:
      Unit{}
    case False{}:
      ai_eofnl(String.ends_with(Conn.final_from(String.reverse(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet}))), "\n"), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)


def ai_eoftext(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.text(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match hin:
    case True{}:
      Unit{}
    case False{}:
      ai_eofempty(String.is_empty(Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)


def ai_eofredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match r:
    case True{}:
      ai_redirect(Nat.is_ge(Conn.cur_hops(k), Conn.rd_limit(Conn.c_rd(Conn.CCfg{ka, to, mb, rd}))), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)
    case False{}:
      ai_eoftext(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)


def ai_eofmet(xmet: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.met(xmet, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match xmet:
    case True{}:
      hX
    case False{}:
      ai_eofredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, False{}})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, False{}, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)


def ai_eoflost(l: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.lost(l, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match l:
    case True{}:
      hX
    case False{}:
      ai_eofmet(xmet, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)


def ai_eoffin(f: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +ev: {Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(xp)) == f : Bool}, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.eof.fin(f, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match f:
    case True{}:
      ai_answer(Http.done(xp), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, ev)
    case False{}:
      ai_eoflost(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)


def ai_latein(hin: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.late.in(hin, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match hin:
    case True{}:
      Unit{}
    case False{}:
      Unit{}


def ai_lateredir(r: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.late.redir(r, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match r:
    case True{}:
      Unit{}
    case False{}:
      ai_latein(Conn.in_of(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet}), Conn.rx_buf(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)


def ai_resolved(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), bf), a_ef(L.ccs_of(Conn.on_resolved(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ef)):
  match ph:
    case Conn.PResolve{}:
      hX
    case Conn.POpen{}:
      hX
    case Conn.PSend{}:
      hX
    case Conn.PRecv{}:
      hX


def ai_resolvefailed(ph: Conn.Phase, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +m: String, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), mb, a_hd(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), hd), a_bf(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), bf), a_ef(L.ccs_of(Conn.on_resolve_failed(ph, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}, m)), ef)):
  match ph:
    case Conn.PResolve{}:
      Unit{}
    case Conn.POpen{}:
      hX
    case Conn.PSend{}:
      hX
    case Conn.PRecv{}:
      hX


def ai_ev(e: Conn.Ev, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool, +T: List<&2, L.CItem>, +hX: {xp == PE(mb, hd, bf, ef) : Http.Parse})
  -> inv_a(L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), mb, a_hd(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ev_bf(e, bf)), a_ef(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ev_ef(e, ef))):
  match e:
    case Conn.Opened{}:
      ai_opened(ph, ka, to, mb, rd, q, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)
    case Conn.OpenFailed{+m}:
      Unit{}
    case Conn.Sent{}:
      ai_sent(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)
    case Conn.SendFailed{+m}:
      ai_sendfailed(Conn.lost(Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), ka, to, mb, rd, q, False{}, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, m, hd, bf, ef, T, hX)
    case Conn.Got{+d}:
      ai_gotfin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d))), ka, to, mb, rd, q, o, Conn.set_got(k, d), xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, Http.feed(Conn.rx_p(Conn.Rx{xb, xhd, xp, xp0, xmet}), d), d, hd, bf ++ d, ef, T, {==}, Equal.trans(Http.Parse, Http.feed(xp, d), Http.feed(PE(mb, hd, bf, ef), d), PE(mb, hd, bf ++ d, ef), Equal.cong(Http.Parse, Http.Parse, p => Http.feed(p, d), xp, PE(mb, hd, bf, ef), hX), pe_feed(ef, mb, hd, bf, d)))
    case Conn.Eof{}:
      ai_eoffin(Conn.final_of(Conn.CCfg{ka, to, mb, rd}, Http.done(Conn.rx_p(Conn.rx_eof(Conn.Rx{xb, xhd, xp, xp0, xmet})))), ka, to, mb, rd, q, False{}, k, xb, xhd, Http.eof(xp), xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, True{}, T, {==}, Equal.trans(Http.Parse, Http.eof(xp), Http.eof(PE(mb, hd, bf, ef)), PE(mb, hd, bf, True{}), Equal.cong(Http.Parse, Http.Parse, p => Http.eof(p), xp, PE(mb, hd, bf, ef), hX), pe_eof(ef, mb, hd, bf)))
    case Conn.Late{}:
      ai_lateredir(Conn.hd_redir(Conn.rx_hd(Conn.Rx{xb, xhd, xp, xp0, xmet})), ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, T, hX)
    case Conn.Resolved{+ip2}:
      ai_resolved(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip2, pr, hd, bf, ef, T, hX)
    case Conn.ResolveFailed{+m}:
      ai_resolvefailed(ph, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, pd, pt, hp, ip, pr, m, hd, bf, ef, T, hX)


def an_over(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +x: Conn.Rx, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool)
  -> {L.chk_answer(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, True{}, k, x, ph, pd, pt, hp, ip, pr}), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, True{}) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Conn.Got{+d}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf ++ d, ef)
        case Conn.Eof{}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, True{})
        case Conn.Opened{}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, ef)
        case Conn.OpenFailed{m}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, ef)
        case Conn.Sent{}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, ef)
        case Conn.SendFailed{m}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, ef)
        case Conn.Late{}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, ef)
        case Conn.Resolved{i}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, ef)
        case Conn.ResolveFailed{m}:
          an_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, ef)

def an_steps(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, s: Conn.State, +hd: Bool, +bf: String, +ef: Bool, +hX: inv_a(s, mb, hd, bf, ef))
  -> {L.chk_answer(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, s), Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, ov(s)) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match s:
        case Conn.CState{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}:
          match v:
            case True{}:
              an_over(Con{e, rest}, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, hd, bf, ef)
            case False{}:
              match x:
                case Conn.Rx{+xb, +xhd, +xp, +xp0, +xmet}:
                  %Equal.sym(Bool, L.chk_answer(Con{L.CIEv{e}, List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))))}, Conn.CCfg{ka, to, mb, rd}, hd, bf, ef, False{}),
                      L.chk_answer(L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), Conn.CCfg{ka, to, mb, rd}, a_hd(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ev_bf(e, bf)), a_ef(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ev_ef(e, ef)), ov(L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})))),
                      an_ev(e, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), hX))
                    : {_ == True{} : Bool}
                  an_steps(rest, ka, to, mb, rd, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), a_hd(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), hd), a_bf(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ev_bf(e, bf)), a_ef(L.ccs_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})), ev_ef(e, ef)),
                    ai_ev(e, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, hd, bf, ef, L.csteps(rest, Conn.CCfg{ka, to, mb, rd}, L.cst_of(Conn.step.ev(e, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}))), hX))

def an_start(open: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +r: Conn.Req, +evs: List<&2, Conn.Ev>)
  -> {L.chk_answer(L.ctimeline(Conn.CCfg{ka, to, mb, rd}, r, open, evs), Conn.CCfg{ka, to, mb, rd}, False{}, "", False{}, False{}) == True{} : Bool}:
  match open:
    case True{}:
      an_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, True{})),
        String.starts_with(Http.request(Conn.q_target(r), Conn.q_url(r), Conn.q_body(r), Conn.q_seq(r), Conn.q_name(r), ka), "HEAD "), "", False{}, {==})
    case False{}:
      an_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, False{})), False{}, "", False{}, {==})

def an_law(c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>)
  -> {L.chk_answer(L.ctimeline(c, r, open, evs), c, False{}, "", False{}, False{}) == True{} : Bool}:
  match c:
    case Conn.CCfg{+ka, +to, +mb, +rd}:
      an_start(open, ka, to, mb, rd, r, evs)

def L.conn_answer(c, r, open, evs):
  an_law(c, r, open, evs)

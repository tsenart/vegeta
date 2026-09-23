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

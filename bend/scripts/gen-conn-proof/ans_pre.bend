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

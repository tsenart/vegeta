# Proofs of the results and targets laws: hit_to_csv, hit_to_json,
# hit_decode, url_parse, url_parse_edges, target_apply, targets_parse,
# targets_concat, targets_noise, targets_errors.
#
# lib/hit.bend and lib/target.bend copy LAWS' helpers under the same
# names; the *_h and *_t lemmas identify each copy with LAWS' def (the
# checker does not identify two defs' picks on an opaque condition).
#
# The targets parser is a fold of adv over the bytes (feed); a line and
# its newline move the state by trim_ws of the line (feed_nl2, line_rev),
# and LAWS' trim_ows is trim_ws on printable text (ows).
#
# Not proved here: hit_of_csv, hit_of_json, hit_stream_csv, hit_stream_json.
import Base
import ../LAWS.bend as L
import ../lib/hit.bend as Hit
import ../lib/target.bend as Tgt
import ../lib/hdr.bend as Hdr
import ../lib/csv.bend as Csv
import ../lib/civil.bend as Civil
import ../lib/dec.bend as Dec
import ../lib/b64.bend as B64
import ../lib/json.bend as Json
# for L.dec_show_canonical, L.dec_show_value and L.dec_read_accepts
import ./dec.bend as PDec
# for the codec writers onto a tail (str_into_e, enc_into)
import ./codec.bend as PC

# ---------------------------------------------------------------------
# Generic lemmas (Bool, U32 equality)
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

def or_f(p: Bool, -q: Bool, h: {Bool.or(p, q) == False{} : Bool}) -> {p == False{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(h))

def or_f2(p: Bool, -q: Bool, h: {Bool.or(p, q) == False{} : Bool}) -> {q == False{} : Bool}:
  match p:
    case False{}:
      h
    case True{}:
      Empty.absurd({q == False{} : Bool}, no_tf(h))

# ---------------------------------------------------------------------
# The lib's scans carry their verdict on the head as a flag; each *_c
# lemma unfolds one step back to the pick form of LAWS' helpers
# ---------------------------------------------------------------------

def hc_b(b: Bool, +kc: U32, +rest: String, +n: U32) -> {Bool.or(b, Tgt.has_char(rest, n)) == Tgt.has_char.go(SCon{Chr{kc}, rest}, n, b) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def hc_c(+kc: U32, +rest: String, +n: U32) -> {Bool.or(U32.is_eq(kc, n), Tgt.has_char(rest, n)) == Tgt.has_char(SCon{Chr{kc}, rest}, n) : Bool}:
  hc_b(U32.is_eq(kc, n), kc, rest, n)

def bef_b(b: Bool, +kc: U32, +rest: String, +n: U32) -> {Tgt.pick(String, b, SNil{}, SCon{Chr{kc}, Tgt.before(rest, n)}) == Tgt.before.go(SCon{Chr{kc}, rest}, n, b) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bef_c(+kc: U32, +rest: String, +n: U32) -> {Tgt.pick(String, U32.is_eq(kc, n), SNil{}, SCon{Chr{kc}, Tgt.before(rest, n)}) == Tgt.before(SCon{Chr{kc}, rest}, n) : String}:
  bef_b(U32.is_eq(kc, n), kc, rest, n)

def aft_b(b: Bool, +kc: U32, +rest: String, +n: U32) -> {Tgt.pick(String, b, rest, Tgt.after(rest, n)) == Tgt.after.go(SCon{Chr{kc}, rest}, n, b) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def aft_c(+kc: U32, +rest: String, +n: U32) -> {Tgt.pick(String, U32.is_eq(kc, n), rest, Tgt.after(rest, n)) == Tgt.after(SCon{Chr{kc}, rest}, n) : String}:
  aft_b(U32.is_eq(kc, n), kc, rest, n)

def tw_b(b: Bool, +k: U32, +r: String) -> {Tgt.pick(String, b, Tgt.trim_ws_l(r), SCon{Chr{k}, r}) == Tgt.trim_ws_l.go(SCon{Chr{k}, r}, b) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tw_c(+k: U32, +r: String) -> {Tgt.pick(String, Tgt.is_ws(k), Tgt.trim_ws_l(r), SCon{Chr{k}, r}) == Tgt.trim_ws_l(SCon{Chr{k}, r}) : String}:
  tw_b(Tgt.is_ws(k), k, r)

def auth_b(b: Bool, +k: U32, +r: String) -> {Tgt.pick(String, b, SNil{}, SCon{Chr{k}, Tgt.auth_of(r)}) == Tgt.auth_of.go(SCon{Chr{k}, r}, b) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def auth_c(+k: U32, +r: String) -> {Tgt.pick(String, Tgt.ends_auth(k), SNil{}, SCon{Chr{k}, Tgt.auth_of(r)}) == Tgt.auth_of(SCon{Chr{k}, r}) : String}:
  auth_b(Tgt.ends_auth(k), k, r)

def be_b(b: Bool, +k: U32, +r: String) -> {Tgt.pick(Maybe<&2, String>, b, Some{SCon{Chr{k}, String.take(r, 2n)}}, Tgt.bad_escape(r)) == Tgt.bad_escape.go(SCon{Chr{k}, r}, b) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def be_c(+k: U32, +r: String)
  -> {Tgt.pick(Maybe<&2, String>, Bool.and(U32.is_eq(k, 37), Bool.not(Bool.and(Tgt.is_hex(Tgt.byte_at(r, 0n)), Tgt.is_hex(Tgt.byte_at(r, 1n))))), Some{SCon{Chr{k}, String.take(r, 2n)}}, Tgt.bad_escape(r))
      == Tgt.bad_escape(SCon{Chr{k}, r}) : Maybe<&2, String>}:
  be_b(Bool.and(U32.is_eq(k, 37), Bool.not(Bool.and(Tgt.is_hex(Tgt.byte_at(r, 0n)), Tgt.is_hex(Tgt.byte_at(r, 1n))))), k, r)

def ur_b(b: Bool, +k: U32, +r: String) -> {Tgt.pick(Nat, b, 1n+Tgt.upper_run(r), 0n) == Tgt.upper_run.go(SCon{Chr{k}, r}, b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ur_c(+k: U32, +r: String) -> {Tgt.pick(Nat, Tgt.is_upper(k), 1n+Tgt.upper_run(r), 0n) == Tgt.upper_run(SCon{Chr{k}, r}) : Nat}:
  ur_b(Tgt.is_upper(k), k, r)

def htl_b(b: Bool, +k: U32, +r: String) -> {Hit.pick(String, b, Hit.trim_ows_l(r), SCon{Chr{k}, r}) == Hit.trim_ows_l.go(SCon{Chr{k}, r}, b) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def htl_c(+k: U32, +r: String) -> {Hit.pick(String, Hit.is_ows(k), Hit.trim_ows_l(r), SCon{Chr{k}, r}) == Hit.trim_ows_l(SCon{Chr{k}, r}) : String}:
  htl_b(Hit.is_ows(k), k, r)

def hcf_l(+kc: U32, +rest: String, +n: U32, +h: {Tgt.has_char(SCon{Chr{kc}, rest}, n) == False{} : Bool}) -> {U32.is_eq(kc, n) == False{} : Bool}:
  or_f(U32.is_eq(kc, n), Tgt.has_char(rest, n), Equal.trans(Bool, Bool.or(U32.is_eq(kc, n), Tgt.has_char(rest, n)), Tgt.has_char(SCon{Chr{kc}, rest}, n), False{}, hc_c(kc, rest, n), h))

def hcf_r(+kc: U32, +rest: String, +n: U32, +h: {Tgt.has_char(SCon{Chr{kc}, rest}, n) == False{} : Bool}) -> {Tgt.has_char(rest, n) == False{} : Bool}:
  or_f2(U32.is_eq(kc, n), Tgt.has_char(rest, n), Equal.trans(Bool, Bool.or(U32.is_eq(kc, n), Tgt.has_char(rest, n)), Tgt.has_char(SCon{Chr{kc}, rest}, n), False{}, hc_c(kc, rest, n), h))

# ---------------------------------------------------------------------
# target_apply
# ---------------------------------------------------------------------

def pick_tg(-A: Data, c: Bool, -a: A, -b: A, -x: A, -y: A, ea: {a == x : A}, eb: {b == y : A})
  -> {Tgt.pick(A, c, a, b) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def add_hdr_t(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> {Tgt.add_hdr(h, hs) == L.add_hdr(h, hs) : List<&2, Hdr.Header>}:
  match h:
    case Hdr.Header{+k, +vs}:
      match hs:
        case Nil{}:
          {==}
        case Con{g, +rest}:
          match g:
            case Hdr.Header{+gk, +gvs}:
              pick_tg(List<&2, Hdr.Header>, String.eq(gk, k),
                Con{Hdr.Header{gk, List.append(&2, String, gvs, vs)}, rest}, Con{Hdr.Header{gk, gvs}, Tgt.add_hdr(Hdr.Header{k, vs}, rest)},
                Con{Hdr.Header{gk, List.append(&2, String, gvs, vs)}, rest}, Con{Hdr.Header{gk, gvs}, L.add_hdr(Hdr.Header{k, vs}, rest)},
                {==}, Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, t => Con{Hdr.Header{gk, gvs}, t},
                  Tgt.add_hdr(Hdr.Header{k, vs}, rest), L.add_hdr(Hdr.Header{k, vs}, rest), add_hdr_t(Hdr.Header{k, vs}, rest)))

def add_hdrs_t(hs: List<&2, Hdr.Header>, +base: List<&2, Hdr.Header>) -> {Tgt.add_hdrs(hs, base) == L.add_hdrs(hs, base) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %add_hdr_t(h, base) : {Tgt.add_hdrs(rest, Tgt.add_hdr(h, base)) == L.add_hdrs(rest, _) : List<&2, Hdr.Header>}
      add_hdrs_t(rest, Tgt.add_hdr(h, base))

def L.target_apply(t, hs, body):
  match t:
    case Tgt.Target{+m, +u, +ths, +b}:
      %add_hdrs_t(ths, hs) : {Tgt.apply(Tgt.Target{m, u, ths, b}, hs, body) == Tgt.Target{m, u, _, Maybe.or(&2, String, b, body)} : Tgt.Target}
      {==}

# ---------------------------------------------------------------------
# hit_to_csv, hit_to_json: lib/hit.bend's copies of LAWS' helpers
# ---------------------------------------------------------------------

def pick_h(-A: Data, c: Bool, -a: A, -b: A, -x: A, -y: A, ea: {a == x : A}, eb: {b == y : A})
  -> {Hit.pick(A, c, a, b) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def tbo(a: Bool, +k: U32) -> {Hit.token_byte.of(a, k) == Bool.or(a, Hit.token_punct(k)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def all_token_h(s: String) -> {Hit.all_token(s) == L.all_token(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+kc}:
          %all_token_h(rest) : {Hit.all_token(SCon{Chr{kc}, rest}) == Bool.and(L.token_byte(kc), _) : Bool}
          %tbo(Hit.is_alnum(kc), kc) : {Hit.all_token(SCon{Chr{kc}, rest}) == Bool.and(_, Hit.all_token(rest)) : Bool}
          {==}

def token_h(+s: String) -> {Hit.token(s) == L.token(s) : Bool}:
  %all_token_h(s) : {Hit.token(s) == Bool.and(Bool.not(String.is_empty(s)), _) : Bool}
  {==}

def trim_ows_l_h(s: String) -> {Hit.trim_ows_l(s) == L.trim_ows_l(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+kc}:
          %htl_c(kc, rest) : {_ == L.trim_ows_l(SCon{Chr{kc}, rest}) : String}
          pick_h(String, Bool.or(U32.is_eq(kc, 32), U32.is_eq(kc, 9)), Hit.trim_ows_l(rest), SCon{Chr{kc}, rest}, L.trim_ows_l(rest), SCon{Chr{kc}, rest},
            trim_ows_l_h(rest), {==})

# generic string lemmas

def app_assoc(a: String, +b: String, +c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, +rest}:
      %app_assoc(rest, b, c) : {SCon{x, String.append(String.append(rest, b), c)} == SCon{x, _} : String}
      {==}

def rev_snoc(x: String, +c: Char, +acc: String) -> {String.reverse.go(String.append(x, SCon{c, SNil{}}), acc) == SCon{c, String.reverse.go(x, acc)} : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+d, +rest}:
      rev_snoc(rest, c, SCon{d, acc})

def rev_acc(r: String, +acc: String) -> {String.reverse.go(r, acc) == String.append(String.reverse.go(r, SNil{}), acc) : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      +r0 = String.reverse.go(rest, SNil{})
      Equal.trans(String, String.reverse.go(rest, SCon{c, acc}), String.append(r0, SCon{c, acc}), String.append(String.reverse.go(rest, SCon{c, SNil{}}), acc),
        rev_acc(rest, SCon{c, acc}),
        Equal.trans(String, String.append(r0, SCon{c, acc}), String.append(String.append(r0, SCon{c, SNil{}}), acc), String.append(String.reverse.go(rest, SCon{c, SNil{}}), acc),
          Equal.sym(String, String.append(String.append(r0, SCon{c, SNil{}}), acc), String.append(r0, SCon{c, acc}), app_assoc(r0, SCon{c, SNil{}}, acc)),
          Equal.cong(String, String, y => String.append(y, acc), String.append(r0, SCon{c, SNil{}}), String.reverse.go(rest, SCon{c, SNil{}}),
            Equal.sym(String, String.reverse.go(rest, SCon{c, SNil{}}), String.append(r0, SCon{c, SNil{}}), rev_acc(rest, SCon{c, SNil{}})))))

def ne_r(y: String, +acc: String, +h: {String.is_empty(acc) == False{} : Bool}) -> {String.is_empty(String.reverse.go(y, acc)) == False{} : Bool}:
  match y:
    case SNil{}:
      h
    case SCon{+c, +r}:
      ne_r(r, SCon{c, acc}, {==})

def ne_r0(y: String, +h: {String.is_empty(y) == False{} : Bool}) -> {String.is_empty(String.reverse(y)) == False{} : Bool}:
  match y:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(h))
    case SCon{+c, +r}:
      ne_r(r, SCon{c, SNil{}}, {==})

# the Hit copies of the trimming lemmas below (spaces and tabs)

def allws_o(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Hit.is_ows(Hit.code(c)), allws_o(rest))

def t_allws_o(y: String, +h: {allws_o(y) == True{} : Bool}) -> {Hit.trim_ows_l(y) == SNil{} : String}:
  match y:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Hit.is_ows(k), True{}, and_l(Hit.is_ows(k), allws_o(r), h))
            : {Hit.trim_ows_l.go(SCon{Chr{k}, r}, _) == SNil{} : String}
          t_allws_o(r, and_r(Hit.is_ows(k), allws_o(r), h))

def t_app_ws_o(a: String, +b: String, +h: {allws_o(a) == True{} : Bool}) -> {Hit.trim_ows_l(String.append(a, b)) == Hit.trim_ows_l(b) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Hit.is_ows(k), True{}, and_l(Hit.is_ows(k), allws_o(r), h))
            : {Hit.trim_ows_l.go(SCon{Chr{k}, String.append(r, b)}, _) == Hit.trim_ows_l(b) : String}
          t_app_ws_o(r, b, and_r(Hit.is_ows(k), allws_o(r), h))

def t_app_step_o(w: Bool, +k: U32, +r: String, +b: String, +ew: {Hit.is_ows(k) == w : Bool}, +h: {Bool.and(w, allws_o(r)) == False{} : Bool},
  ih: {allws_o(r) == False{} : Bool} -> {String.append(Hit.trim_ows_l(r), b) == Hit.trim_ows_l(String.append(r, b)) : String})
  -> {String.append(Hit.trim_ows_l.go(SCon{Chr{k}, r}, w), b) == Hit.trim_ows_l.go(SCon{Chr{k}, String.append(r, b)}, w) : String}:
  match w:
    case True{}:
      ih(h)
    case False{}:
      {==}

def t_app_nws_o(a: String, +b: String, +h: {allws_o(a) == False{} : Bool}) -> {String.append(Hit.trim_ows_l(a), b) == Hit.trim_ows_l(String.append(a, b)) : String}:
  match a:
    case SNil{}:
      Empty.absurd({b == Hit.trim_ows_l(b) : String}, no_tf(h))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          t_app_step_o(Hit.is_ows(k), k, r, b, {==}, h, hh => t_app_nws_o(r, b, hh))

def ne_t_step_o(w: Bool, +k: U32, +r: String, +ew: {Hit.is_ows(k) == w : Bool}, +h: {Bool.and(w, allws_o(r)) == False{} : Bool},
  ih: {allws_o(r) == False{} : Bool} -> {String.is_empty(Hit.trim_ows_l(r)) == False{} : Bool})
  -> {String.is_empty(Hit.trim_ows_l.go(SCon{Chr{k}, r}, w)) == False{} : Bool}:
  match w:
    case True{}:
      ih(h)
    case False{}:
      {==}

def ne_t_o(y: String, +h: {allws_o(y) == False{} : Bool}) -> {String.is_empty(Hit.trim_ows_l(y)) == False{} : Bool}:
  match y:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(h))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          ne_t_step_o(Hit.is_ows(k), k, r, {==}, h, hh => ne_t_o(r, hh))

def tr1_ws_o(w: Bool, +k: U32)
  -> {Hit.pick(String, Bool.and(True{}, w), SNil{}, SCon{Chr{k}, SNil{}}) == String.reverse(Hit.trim_ows_l.go(SCon{Chr{k}, SNil{}}, w)) : String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def tr1_step_o(b: Bool, +k: U32, +r: String, +eb: {allws_o(String.reverse(r)) == b : Bool})
  -> {Hit.pick(String, Bool.and(String.is_empty(String.reverse(Hit.trim_ows_l(String.reverse(r)))), Hit.is_ows(k)), SNil{}, SCon{Chr{k}, String.reverse(Hit.trim_ows_l(String.reverse(r)))})
      == String.reverse(Hit.trim_ows_l(String.append(String.reverse(r), SCon{Chr{k}, SNil{}}))) : String}:
  match b:
    case True{}:
      %Equal.sym(String, Hit.trim_ows_l(String.append(String.reverse(r), SCon{Chr{k}, SNil{}})), Hit.trim_ows_l(SCon{Chr{k}, SNil{}}), t_app_ws_o(String.reverse(r), SCon{Chr{k}, SNil{}}, eb))
        : {Hit.pick(String, Bool.and(String.is_empty(String.reverse(Hit.trim_ows_l(String.reverse(r)))), Hit.is_ows(k)), SNil{}, SCon{Chr{k}, String.reverse(Hit.trim_ows_l(String.reverse(r)))})
          == String.reverse(_) : String}
      %Equal.sym(String, Hit.trim_ows_l(String.reverse(r)), SNil{}, t_allws_o(String.reverse(r), eb))
        : {Hit.pick(String, Bool.and(String.is_empty(String.reverse(_)), Hit.is_ows(k)), SNil{}, SCon{Chr{k}, String.reverse(_)})
          == String.reverse(Hit.trim_ows_l(SCon{Chr{k}, SNil{}})) : String}
      tr1_ws_o(Hit.is_ows(k), k)
    case False{}:
      %t_app_nws_o(String.reverse(r), SCon{Chr{k}, SNil{}}, eb)
        : {Hit.pick(String, Bool.and(String.is_empty(String.reverse(Hit.trim_ows_l(String.reverse(r)))), Hit.is_ows(k)), SNil{}, SCon{Chr{k}, String.reverse(Hit.trim_ows_l(String.reverse(r)))})
          == String.reverse(_) : String}
      %Equal.sym(String, String.reverse(String.append(Hit.trim_ows_l(String.reverse(r)), SCon{Chr{k}, SNil{}})), SCon{Chr{k}, String.reverse(Hit.trim_ows_l(String.reverse(r)))},
          rev_snoc(Hit.trim_ows_l(String.reverse(r)), Chr{k}, SNil{}))
        : {Hit.pick(String, Bool.and(String.is_empty(String.reverse(Hit.trim_ows_l(String.reverse(r)))), Hit.is_ows(k)), SNil{}, SCon{Chr{k}, String.reverse(Hit.trim_ows_l(String.reverse(r)))})
          == _ : String}
      %Equal.sym(Bool, String.is_empty(String.reverse(Hit.trim_ows_l(String.reverse(r)))), False{},
          ne_r0(Hit.trim_ows_l(String.reverse(r)), ne_t_o(String.reverse(r), eb)))
        : {Hit.pick(String, Bool.and(_, Hit.is_ows(k)), SNil{}, SCon{Chr{k}, String.reverse(Hit.trim_ows_l(String.reverse(r)))})
          == SCon{Chr{k}, String.reverse(Hit.trim_ows_l(String.reverse(r)))} : String}
      {==}

def trr_rtr_o(x: String) -> {Hit.trim_ows_r(x) == String.reverse(Hit.trim_ows_l(String.reverse(x))) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +rtr = String.reverse(Hit.trim_ows_l(String.reverse(r)))
          %Equal.sym(String, Hit.trim_ows_r(r), rtr, trr_rtr_o(r))
            : {Hit.pick(String, Bool.and(String.is_empty(_), Hit.is_ows(k)), SNil{}, SCon{Chr{k}, _}) == String.reverse(Hit.trim_ows_l(String.reverse(SCon{Chr{k}, r}))) : String}
          %Equal.sym(String, String.reverse.go(r, SCon{Chr{k}, SNil{}}), String.append(String.reverse(r), SCon{Chr{k}, SNil{}}), rev_acc(r, SCon{Chr{k}, SNil{}}))
            : {Hit.pick(String, Bool.and(String.is_empty(rtr), Hit.is_ows(k)), SNil{}, SCon{Chr{k}, rtr}) == String.reverse(Hit.trim_ows_l(_)) : String}
          tr1_step_o(allws_o(String.reverse(r)), k, r, {==})

def trim_ows_h(+s: String) -> {Hit.trim_ows(s) == L.trim_ows(s) : String}:
  %trim_ows_l_h(s) : {Hit.trim_ows(s) == String.reverse(L.trim_ows_l(String.reverse(_))) : String}
  %trim_ows_l_h(String.reverse(Hit.trim_ows_l(s))) : {Hit.trim_ows(s) == String.reverse(_) : String}
  trr_rtr_o(Hit.trim_ows_l(s))

def nlc(b: Bool, +kc: U32, +x: String) -> {SCon{Chr{Hit.pick(U32, b, 32, kc)}, x} == L.pick(String, b, " ", SCon{Chr{kc}, SNil{}}) ++ x : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nl_to_space_h(s: String) -> {Hit.nl_to_space(s) == L.nl_to_space(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+kc}:
          %nl_to_space_h(rest) : {Hit.nl_to_space(SCon{Chr{kc}, rest}) == L.pick(String, Bool.or(U32.is_eq(kc, 10), U32.is_eq(kc, 13)), " ", SCon{Chr{kc}, SNil{}}) ++ _ : String}
          nlc(Bool.or(U32.is_eq(kc, 10), U32.is_eq(kc, 13)), kc, Hit.nl_to_space(rest))

# a header value in one copy (val_into): the blanks it starts with
# skipped (a1), then the bytes before its trailing blanks copied (a2)

# is_ows after nl_char is vblank
def ows_nl(b: Bool, +k: U32) -> {Hit.is_ows(Hit.pick(U32, b, 32, k)) == Bool.or(b, Hit.is_ows(k)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def a1_step(c: Bool, +k: U32, +rest: String, ih: {Hit.trim_ows_l(Hit.nl_to_space(rest)) == Hit.nl_to_space(Hit.skip_bl(rest)) : String})
  -> {Hit.trim_ows_l.go(SCon{Hit.nl_char(Chr{k}), Hit.nl_to_space(rest)}, c) == Hit.nl_to_space(Hit.skip_bl.go(SCon{Chr{k}, rest}, c)) : String}:
  match c:
    case True{}:
      ih
    case False{}:
      {==}

def a1(v: String) -> {Hit.trim_ows_l(Hit.nl_to_space(v)) == Hit.nl_to_space(Hit.skip_bl(v)) : String}:
  match v:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          +b = Bool.or(U32.is_eq(k, 10), U32.is_eq(k, 13))
          %Equal.sym(Bool, Hit.is_ows(Hit.pick(U32, b, 32, k)), Bool.or(b, Hit.is_ows(k)), ows_nl(b, k)) : {Hit.trim_ows_l.go(SCon{Hit.nl_char(Chr{k}), Hit.nl_to_space(rest)}, _) == Hit.nl_to_space(Hit.skip_bl(SCon{Chr{k}, rest})) : String}
          a1_step(Hit.vblank(k), k, rest, a1(rest))

def c_step(x: Bool, +m: Nat, +nc: Char, +r: String)
  -> {String.is_empty(Hit.pick(String, x, SNil{}, SCon{nc, r})) == Nat.is_eq(Hit.pick(Nat, x, 0n, 1n+m), 0n) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# the trimmed value is empty exactly when keep is 0
def a2c(u: String) -> {String.is_empty(Hit.trim_ows_r(Hit.nl_to_space(u))) == Nat.is_eq(Hit.keep(u), 0n) : Bool}:
  match u:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          +r = Hit.trim_ows_r(Hit.nl_to_space(rest))
          +m = Hit.keep(rest)
          +b = Bool.or(U32.is_eq(k, 10), U32.is_eq(k, 13))
          %Equal.sym(Bool, String.is_empty(r), Nat.is_eq(m, 0n), a2c(rest))
            : {String.is_empty(Hit.pick(String, Bool.and(_, Hit.is_ows(Hit.code(Hit.nl_char(Chr{k})))), SNil{}, SCon{Hit.nl_char(Chr{k}), r}))
               == Nat.is_eq(Hit.keep(SCon{Chr{k}, rest}), 0n) : Bool}
          %Equal.sym(Bool, Hit.is_ows(Hit.pick(U32, b, 32, k)), Bool.or(b, Hit.is_ows(k)), ows_nl(b, k))
            : {String.is_empty(Hit.pick(String, Bool.and(Nat.is_eq(m, 0n), _), SNil{}, SCon{Hit.nl_char(Chr{k}), r}))
               == Nat.is_eq(Hit.keep(SCon{Chr{k}, rest}), 0n) : Bool}
          c_step(Bool.and(Nat.is_eq(m, 0n), Hit.vblank(k)), m, Hit.nl_char(Chr{k}), r)

def a2_step(x: Bool, +m: Nat, +c: Char, +rest: String, +r: String, +t: String, ih: {String.append(r, t) == Hit.copy_nl(m, rest, t) : String})
  -> {String.append(Hit.pick(String, x, SNil{}, SCon{Hit.nl_char(c), r}), t) == Hit.copy_nl(Hit.pick(Nat, x, 0n, 1n+m), SCon{c, rest}, t) : String}:
  match x:
    case True{}:
      {==}
    case False{}:
      %ih : {SCon{Hit.nl_char(c), String.append(r, t)} == SCon{Hit.nl_char(c), _} : String}
      {==}

def a2(u: String, +t: String) -> {String.append(Hit.trim_ows_r(Hit.nl_to_space(u)), t) == Hit.copy_nl(Hit.keep(u), u, t) : String}:
  match u:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          +r = Hit.trim_ows_r(Hit.nl_to_space(rest))
          +m = Hit.keep(rest)
          +b = Bool.or(U32.is_eq(k, 10), U32.is_eq(k, 13))
          %Equal.sym(Bool, String.is_empty(r), Nat.is_eq(m, 0n), a2c(rest))
            : {String.append(Hit.pick(String, Bool.and(_, Hit.is_ows(Hit.code(Hit.nl_char(Chr{k})))), SNil{}, SCon{Hit.nl_char(Chr{k}), r}), t)
               == Hit.copy_nl(Hit.keep(SCon{Chr{k}, rest}), SCon{Chr{k}, rest}, t) : String}
          %Equal.sym(Bool, Hit.is_ows(Hit.pick(U32, b, 32, k)), Bool.or(b, Hit.is_ows(k)), ows_nl(b, k))
            : {String.append(Hit.pick(String, Bool.and(Nat.is_eq(m, 0n), _), SNil{}, SCon{Hit.nl_char(Chr{k}), r}), t)
               == Hit.copy_nl(Hit.keep(SCon{Chr{k}, rest}), SCon{Chr{k}, rest}, t) : String}
          a2_step(Bool.and(Nat.is_eq(m, 0n), Hit.vblank(k)), m, Chr{k}, rest, r, t, a2(rest, t))

def val_l(+v: String, +t: String) -> {Hit.val_into(v, t) == String.append(Hit.trim_ows(Hit.nl_to_space(v)), t) : String}:
  %Equal.sym(String, Hit.trim_ows_l(Hit.nl_to_space(v)), Hit.nl_to_space(Hit.skip_bl(v)), a1(v))
    : {Hit.val_into(v, t) == String.append(Hit.trim_ows_r(_), t) : String}
  Equal.sym(String, String.append(Hit.trim_ows_r(Hit.nl_to_space(Hit.skip_bl(v))), t), Hit.val_into(v, t), a2(Hit.skip_bl(v), t))

# the header block is written front to back: lines_into(k, vs, t) is
# hdr_lines(k, vs) ++ t, hdrs_into(hs, t) is hdrs_text(hs) ++ t
def lines_l(+k: String, vs: List<&2, String>, +t: String) -> {Hit.lines_into(k, vs, t) == L.hdr_lines(k, vs) ++ t : String}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      +lv = L.trim_ows(L.nl_to_space(v))
      +r = "\r\n" ++ L.hdr_lines(k, rest)
      +x = ": " ++ (lv ++ r)
      %Equal.sym(String, String.append(String.append(k, x), t), String.append(k, String.append(x, t)), app_assoc(k, x, t))
        : {Hit.lines_into(k, Con{v, rest}, t) == _ : String}
      %Equal.sym(String, String.append(String.append(lv, r), t), String.append(lv, String.append(r, t)), app_assoc(lv, r, t))
        : {Hit.lines_into(k, Con{v, rest}, t) == k ++ SCon{':', SCon{' ', _}} : String}
      %lines_l(k, rest, t)
        : {Hit.lines_into(k, Con{v, rest}, t) == k ++ SCon{':', SCon{' ', lv ++ SCon{'\r', SCon{'\n', _}}}} : String}
      %nl_to_space_h(v)
        : {Hit.lines_into(k, Con{v, rest}, t) == k ++ SCon{':', SCon{' ', L.trim_ows(_) ++ SCon{'\r', SCon{'\n', Hit.lines_into(k, rest, t)}}}} : String}
      %trim_ows_h(Hit.nl_to_space(v))
        : {Hit.lines_into(k, Con{v, rest}, t) == k ++ SCon{':', SCon{' ', _ ++ SCon{'\r', SCon{'\n', Hit.lines_into(k, rest, t)}}}} : String}
      %val_l(v, SCon{'\r', SCon{'\n', Hit.lines_into(k, rest, t)}})
        : {Hit.lines_into(k, Con{v, rest}, t) == k ++ SCon{':', SCon{' ', _}} : String}
      {==}

def ti_b(b: Bool, +k: String, +vs: List<&2, String>, +t: String)
  -> {Hit.text_into(b, k, vs, t) == L.pick(String, b, L.hdr_lines(k, vs), "") ++ t : String}:
  match b:
    case True{}:
      lines_l(k, vs, t)
    case False{}:
      {==}

def hdrs_l(hs: List<&2, Hdr.Header>, +t: String) -> {Hit.hdrs_into(hs, t) == L.hdrs_text(hs) ++ t : String}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +rest}:
      match h:
        case Hdr.Header{+k, +vs}:
          +p = L.pick(String, L.token(k), L.hdr_lines(k, vs), "")
          %Equal.sym(String, String.append(String.append(p, L.hdrs_text(rest)), t), String.append(p, String.append(L.hdrs_text(rest), t)),
              app_assoc(p, L.hdrs_text(rest), t))
            : {Hit.hdrs_into(Con{Hdr.Header{k, vs}, rest}, t) == _ : String}
          %hdrs_l(rest, t) : {Hit.hdrs_into(Con{Hdr.Header{k, vs}, rest}, t) == p ++ _ : String}
          %token_h(k) : {Hit.hdrs_into(Con{Hdr.Header{k, vs}, rest}, t) == L.pick(String, _, L.hdr_lines(k, vs), "") ++ Hit.hdrs_into(rest, t) : String}
          ti_b(Hit.token(k), k, vs, Hit.hdrs_into(rest, t))

def ins_b(b: Bool, +h: Hdr.Header, +x: Hdr.Header, +rest: List<&2, Hdr.Header>)
  -> {Hit.pick(List<&2, Hdr.Header>, b, Con{h, Con{x, rest}}, Con{x, Hit.insert_hdr(h, rest)}) == Hit.insert_hdr.go(Con{x, rest}, h, b) : List<&2, Hdr.Header>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# str_lt is String.is_lt: a case on each byte's comparison
def rec_ord(-h1: Char, -h2: Char, r: (String & String) & Cmp)
  -> {Cmp.is_lt(String.order.fin(String.cmp.rec(h1, h2, r))) == Cmp.is_lt(String.order.fin(r)) : Bool}:
  match r:
    case (xy, c):
      match xy:
        case (x, y):
          {==}

def lt_c(c: Cmp, +ka: U32, +kb: U32, +ra: String, +rb: String, ih: {Hit.str_lt(ra, rb) == String.is_lt(ra, rb) : Bool})
  -> {Hit.lt.go(SCon{Chr{ka}, ra}, SCon{Chr{kb}, rb}, Hit.pick(Nat, Cmp.is_lt(c), 0n, Hit.pick(Nat, Cmp.is_eq(c), 2n, 1n)))
      == Cmp.is_lt(String.order.fin(String.cmp.fin(ra, rb, ((Chr{ka}, Chr{kb}), c)))) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      %Equal.sym(Bool, Cmp.is_lt(String.order.fin(String.cmp.rec(Chr{ka}, Chr{kb}, String.cmp(ra, rb)))), Cmp.is_lt(String.order.fin(String.cmp(ra, rb))),
          rec_ord(Chr{ka}, Chr{kb}, String.cmp(ra, rb)))
        : {Hit.str_lt(ra, rb) == _ : Bool}
      ih
    case GT{}:
      {==}

def lt_is(a: String, +b: String) -> {Hit.str_lt(a, b) == String.is_lt(a, b) : Bool}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{+cb, +rb}:
          {==}
    case SCon{ca, +ra}:
      match ca:
        case Chr{+ka}:
          match b:
            case SNil{}:
              {==}
            case SCon{cb, +rb}:
              match cb:
                case Chr{+kb}:
                  lt_c(U32.cmp(ka, kb), ka, kb, ra, rb, lt_is(ra, rb))

def insert_hdr_h(+h: Hdr.Header, hs: List<&2, Hdr.Header>) -> {Hit.insert_hdr(h, hs) == L.insert_hdr(h, hs) : List<&2, Hdr.Header>}:
  match h:
    case Hdr.Header{+k, +vs}:
      match hs:
        case Nil{}:
          {==}
        case Con{x, +rest}:
          match x:
            case Hdr.Header{+xk, +xvs}:
              %Equal.sym(Bool, Hit.str_lt(k, xk), String.is_lt(k, xk), lt_is(k, xk))
                : {Hit.insert_hdr.go(Con{Hdr.Header{xk, xvs}, rest}, Hdr.Header{k, vs}, _) == L.insert_hdr(Hdr.Header{k, vs}, Con{Hdr.Header{xk, xvs}, rest}) : List<&2, Hdr.Header>}
              %ins_b(String.is_lt(k, xk), Hdr.Header{k, vs}, Hdr.Header{xk, xvs}, rest)
                : {_ == L.insert_hdr(Hdr.Header{k, vs}, Con{Hdr.Header{xk, xvs}, rest}) : List<&2, Hdr.Header>}
              pick_h(List<&2, Hdr.Header>, String.is_lt(k, xk),
                Con{Hdr.Header{k, vs}, Con{Hdr.Header{xk, xvs}, rest}}, Con{Hdr.Header{xk, xvs}, Hit.insert_hdr(Hdr.Header{k, vs}, rest)},
                Con{Hdr.Header{k, vs}, Con{Hdr.Header{xk, xvs}, rest}}, Con{Hdr.Header{xk, xvs}, L.insert_hdr(Hdr.Header{k, vs}, rest)},
                {==}, Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, t => Con{Hdr.Header{xk, xvs}, t},
                  Hit.insert_hdr(Hdr.Header{k, vs}, rest), L.insert_hdr(Hdr.Header{k, vs}, rest), insert_hdr_h(Hdr.Header{k, vs}, rest)))

def sort_hdrs_h(hs: List<&2, Hdr.Header>) -> {Hit.sort_hdrs(hs) == L.sort_hdrs(hs) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +rest}:
      %sort_hdrs_h(rest) : {Hit.insert_hdr(h, Hit.sort_hdrs(rest)) == L.insert_hdr(h, _) : List<&2, Hdr.Header>}
      insert_hdr_h(h, Hit.sort_hdrs(rest))

def hdr_block_h(+m: Maybe<&2, List<&2, Hdr.Header>>) -> {Hit.hdr_block(m) == L.hdr_block(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+hs}:
      %sort_hdrs_h(hs) : {Hit.hdrs_into(Hit.sort_hdrs(hs), "\r\n") == L.hdrs_text(_) ++ "\r\n" : String}
      hdrs_l(Hit.sort_hdrs(hs), "\r\n")

# to_csv writes the row front to back; its two base64 fields are
# encoded in place (PC.fb)
def L.hit_to_csv(h):
  match h:
    case Hit.Hit{+attack, +seq, +code, +ts, +lat, +bout, +bin, +err, +body, +method, +url, +hdrs}:
      +hh = {Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} : Hit.Hit}
      +f6 = {[Civil.unix_nanos(ts), Dec.show(code), Dec.show(lat), Dec.show(bout), Dec.show(bin), err] : List<&2, String>}
      +f4 = {[attack, Dec.show(seq), method, url] : List<&2, String>}
      %hdr_block_h(hdrs) : {Hit.to_csv(hh)
        == Csv.row([Civil.unix_nanos(ts), Dec.show(code), Dec.show(lat), Dec.show(bout), Dec.show(bin), err,
             B64.encode(L.body_or_empty(body)), attack, Dec.show(seq), method, url, B64.encode(_)]) : String}
      %PC.fb(Hit.hdr_block(hdrs), "\n")
        : {Hit.to_csv(hh) == Hit.csv_into(f6, Csv.field_into(B64.encode(L.body_or_empty(body)), SCon{',', Hit.csv_into(f4, _)})) : String}
      %PC.fb(L.body_or_empty(body), SCon{',', Hit.csv_into(f4, Hit.b64_field_into(Hit.hdr_block(hdrs), "\n"))})
        : {Hit.to_csv(hh) == Hit.csv_into(f6, _) : String}
      {==}

# JSON is written front to back too: each *_into is its LAWS text ++ t
# (PC.str_into_e and PC.enc_into for the codecs)

def list_l(vs: List<&2, String>, +t: String) -> {Hit.json_list_into(vs, t) == L.json_list(vs) ++ t : String}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      match rest:
        case Nil{}:
          PC.str_into_e(v, t)
        case Con{+w, +more}:
          +j = L.json_list(Con{w, more})
          %Equal.sym(String, (Json.str(v) ++ ("," ++ j)) ++ t, Json.str(v) ++ (("," ++ j) ++ t), app_assoc(Json.str(v), "," ++ j, t))
            : {Hit.json_list_into(Con{v, Con{w, more}}, t) == _ : String}
          %list_l(Con{w, more}, t) : {Hit.json_list_into(Con{v, Con{w, more}}, t) == Json.str(v) ++ SCon{',', _} : String}
          PC.str_into_e(v, SCon{',', Hit.json_list_into(Con{w, more}, t)})

def item_l(+k: String, +vs: List<&2, String>, +t: String)
  -> {Hit.json_item_into(Hdr.Header{k, vs}, t) == (Json.str(k) ++ ":[" ++ L.json_list(vs) ++ "]") ++ t : String}:
  +j = L.json_list(vs)
  %Equal.sym(String, (Json.str(k) ++ (":[" ++ (j ++ "]"))) ++ t, Json.str(k) ++ ((":[" ++ (j ++ "]")) ++ t), app_assoc(Json.str(k), ":[" ++ (j ++ "]"), t))
    : {Hit.json_item_into(Hdr.Header{k, vs}, t) == _ : String}
  %Equal.sym(String, (j ++ "]") ++ t, j ++ ("]" ++ t), app_assoc(j, "]", t))
    : {Hit.json_item_into(Hdr.Header{k, vs}, t) == Json.str(k) ++ SCon{':', SCon{'[', _}} : String}
  %list_l(vs, SCon{']', t}) : {Hit.json_item_into(Hdr.Header{k, vs}, t) == Json.str(k) ++ SCon{':', SCon{'[', _}} : String}
  PC.str_into_e(k, SCon{':', SCon{'[', Hit.json_list_into(vs, SCon{']', t})}})

def items_l(hs: List<&2, Hdr.Header>, +t: String) -> {Hit.json_items_into(hs, t) == L.json_hdrs(hs) ++ t : String}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +rest}:
      match h:
        case Hdr.Header{+k, +vs}:
          match rest:
            case Nil{}:
              item_l(k, vs, t)
            case Con{+g, +more}:
              +x = Json.str(k) ++ ":[" ++ L.json_list(vs) ++ "]"
              +j = L.json_hdrs(Con{g, more})
              %Equal.sym(String, (x ++ ("," ++ j)) ++ t, x ++ (("," ++ j) ++ t), app_assoc(x, "," ++ j, t))
                : {Hit.json_items_into(Con{Hdr.Header{k, vs}, Con{g, more}}, t) == _ : String}
              %items_l(Con{g, more}, t) : {Hit.json_items_into(Con{Hdr.Header{k, vs}, Con{g, more}}, t) == x ++ SCon{',', _} : String}
              item_l(k, vs, SCon{',', Hit.json_items_into(Con{g, more}, t)})

def jh_l(+m: Maybe<&2, List<&2, Hdr.Header>>, +t: String) -> {Hit.json_hdrs_into(m, t) == L.json_hdrs_of(m) ++ t : String}:
  match m:
    case None{}:
      {==}
    case Some{+hs}:
      +j = L.json_hdrs(L.sort_hdrs(hs))
      %Equal.sym(String, (j ++ "}") ++ t, j ++ ("}" ++ t), app_assoc(j, "}", t))
        : {Hit.json_hdrs_into(Some{hs}, t) == SCon{Chr{123}, _} : String}
      %sort_hdrs_h(hs) : {Hit.json_hdrs_into(Some{hs}, t) == SCon{Chr{123}, L.json_hdrs(_) ++ SCon{Chr{125}, t}} : String}
      %items_l(Hit.sort_hdrs(hs), SCon{Chr{125}, t}) : {Hit.json_hdrs_into(Some{hs}, t) == SCon{Chr{123}, _} : String}
      {==}

def jb_l(+m: Maybe<&2, String>, +t: String) -> {Hit.json_body_into(m, t) == L.json_body(m) ++ t : String}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      +e = B64.encode(x)
      %Equal.sym(String, (e ++ "\"") ++ t, e ++ ("\"" ++ t), app_assoc(e, "\"", t))
        : {Hit.json_body_into(Some{x}, t) == SCon{'"', _} : String}
      %PC.enc_into(x, SCon{'"', t}) : {Hit.json_body_into(Some{x}, t) == SCon{'"', _} : String}
      {==}

# show_into(n, t) is Dec.show(n) ++ t
def sg(f: Nat, +st: Bool, +n: Nat, +acc: String, +t: String)
  -> {Dec.show.go(f, st, n, acc ++ t) == Dec.show.go(f, st, n, acc) ++ t : String}:
  match f:
    case 0n:
      {==}
    case 1n+(+g):
      match st:
        case True{}:
          {==}
        case False{}:
          sg(g, Nat.is_lt(n, 10n), Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}, t)

# json_text piece by piece, from the end: p ++ (lib piece) is p ++ (LAWS piece)
def js_s(+p: String, +s: String, +a: String, +b: String, e: {a == b : String})
  -> {p ++ Json.str_into(s, a) == p ++ Json.str(s) ++ b : String}:
  %e : {p ++ Json.str_into(s, a) == p ++ Json.str(s) ++ _ : String}
  %PC.str_into_e(s, a) : {p ++ Json.str_into(s, a) == p ++ _ : String}
  {==}

def js_n(+p: String, +n: Nat, +a: String, +b: String, e: {a == b : String})
  -> {p ++ Hit.show_into(n, a) == p ++ Dec.show(n) ++ b : String}:
  %e : {p ++ Hit.show_into(n, a) == p ++ Dec.show(n) ++ _ : String}
  %sg(1n+n, False{}, n, "", a) : {p ++ Hit.show_into(n, a) == p ++ _ : String}
  {==}

def js_t(+p: String, +x: String, +a: String, +b: String, e: {a == b : String})
  -> {p ++ x ++ a == p ++ x ++ b : String}:
  %e : {p ++ x ++ a == p ++ x ++ _ : String}
  {==}

def js_b(+p: String, +m: Maybe<&2, String>, +a: String, +b: String, e: {a == b : String})
  -> {p ++ Hit.json_body_into(m, a) == p ++ L.json_body(m) ++ b : String}:
  %e : {p ++ Hit.json_body_into(m, a) == p ++ L.json_body(m) ++ _ : String}
  %jb_l(m, a) : {p ++ Hit.json_body_into(m, a) == p ++ _ : String}
  {==}

def js_h(+p: String, +m: Maybe<&2, List<&2, Hdr.Header>>)
  -> {p ++ Hit.json_hdrs_into(m, "}\n") == p ++ L.json_hdrs_of(m) ++ "}\n" : String}:
  %jh_l(m, "}\n") : {p ++ Hit.json_hdrs_into(m, "}\n") == p ++ _ : String}
  {==}

def L.hit_to_json(h):
  match h:
    case Hit.Hit{+attack, +seq, +code, +ts, +lat, +bout, +bin, +err, +body, +method, +url, +hdrs}:
      +l12 = ",\"headers\":" ++ Hit.json_hdrs_into(hdrs, "}\n")
      +r12 = ",\"headers\":" ++ L.json_hdrs_of(hdrs) ++ "}\n"
      +l11 = ",\"url\":" ++ Json.str_into(url, l12)
      +r11 = ",\"url\":" ++ Json.str(url) ++ r12
      +l10 = ",\"method\":" ++ Json.str_into(method, l11)
      +r10 = ",\"method\":" ++ Json.str(method) ++ r11
      +l9 = ",\"body\":" ++ Hit.json_body_into(body, l10)
      +r9 = ",\"body\":" ++ L.json_body(body) ++ r10
      +l8 = ",\"error\":" ++ Json.str_into(err, l9)
      +r8 = ",\"error\":" ++ Json.str(err) ++ r9
      +l7 = ",\"bytes_in\":" ++ Hit.show_into(bin, l8)
      +r7 = ",\"bytes_in\":" ++ Dec.show(bin) ++ r8
      +l6 = ",\"bytes_out\":" ++ Hit.show_into(bout, l7)
      +r6 = ",\"bytes_out\":" ++ Dec.show(bout) ++ r7
      +l5 = "\",\"latency\":" ++ Hit.show_into(lat, l6)
      +r5 = "\",\"latency\":" ++ Dec.show(lat) ++ r6
      +l4 = ",\"timestamp\":\"" ++ Civil.rfc3339(ts) ++ l5
      +r4 = ",\"timestamp\":\"" ++ Civil.rfc3339(ts) ++ r5
      +l3 = ",\"code\":" ++ Hit.show_into(code, l4)
      +r3 = ",\"code\":" ++ Dec.show(code) ++ r4
      +l2 = ",\"seq\":" ++ Hit.show_into(seq, l3)
      +r2 = ",\"seq\":" ++ Dec.show(seq) ++ r3
      +e12 = js_h(",\"headers\":", hdrs)
      +e11 = js_s(",\"url\":", url, l12, r12, e12)
      +e10 = js_s(",\"method\":", method, l11, r11, e11)
      +e9 = js_b(",\"body\":", body, l10, r10, e10)
      +e8 = js_s(",\"error\":", err, l9, r9, e9)
      +e7 = js_n(",\"bytes_in\":", bin, l8, r8, e8)
      +e6 = js_n(",\"bytes_out\":", bout, l7, r7, e7)
      +e5 = js_n("\",\"latency\":", lat, l6, r6, e6)
      +e4 = js_t(",\"timestamp\":\"", Civil.rfc3339(ts), l5, r5, e5)
      +e3 = js_n(",\"code\":", code, l4, r4, e4)
      +e2 = js_n(",\"seq\":", seq, l3, r3, e3)
      js_s("{\"attack\":", attack, l2, r2, e2)

# ---------------------------------------------------------------------
# url_parse_edges
# ---------------------------------------------------------------------

def all_host_t(s: String) -> {Tgt.all_host(s) == L.all_host(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+kc}:
          %all_host_t(rest) : {Tgt.all_host(SCon{Chr{kc}, rest}) == Bool.and(L.is_host_char(kc), _) : Bool}
          {==}

# k is not n when P holds of k but not of n
def ne_of(P: U32 -> Bool, b: Bool, +k: U32, +n: U32, +e: {U32.is_eq(k, n) == b : Bool},
  hn: {P(n) == False{} : Bool}, h: {P(k) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, True{}, P(n), False{},
        Equal.trans(Bool, True{}, P(k), P(n), Equal.sym(Bool, P(k), True{}, h),
          Equal.cong(U32, Bool, x => P(x), k, n, u32_eq(k, n, e))), hn)

def host_ne(b: Bool, +k: U32, +n: U32, +e: {U32.is_eq(k, n) == b : Bool},
  hn: {Tgt.is_host_char(n) == False{} : Bool}, h: {Tgt.is_host_char(k) == True{} : Bool}) -> {b == False{} : Bool}:
  ne_of(x => Tgt.is_host_char(x), b, k, n, e, hn, h)

def ends_auth_f(+k: U32, +h: {Tgt.is_host_char(k) == True{} : Bool}) -> {Tgt.ends_auth(k) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(k, 47), False{}, host_ne(U32.is_eq(k, 47), k, 47, {==}, {==}, h))
    : {Bool.or(_, Bool.or(U32.is_eq(k, 63), U32.is_eq(k, 35))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_eq(k, 63), False{}, host_ne(U32.is_eq(k, 63), k, 63, {==}, {==}, h))
    : {Bool.or(False{}, Bool.or(_, U32.is_eq(k, 35))) == False{} : Bool}
  host_ne(U32.is_eq(k, 35), k, 35, {==}, {==}, h)

def auth_host(s: String, +h: {Tgt.all_host(s) == True{} : Bool}) -> {s == Tgt.auth_of(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +hk = and_l(Tgt.is_host_char(k), Tgt.all_host(rest), h)
          %Equal.sym(Bool, Tgt.ends_auth(k), False{}, ends_auth_f(k, hk))
            : {SCon{Chr{k}, rest} == Tgt.auth_of.go(SCon{Chr{k}, rest}, _) : String}
          %auth_host(rest, and_r(Tgt.is_host_char(k), Tgt.all_host(rest), h))
            : {SCon{Chr{k}, rest} == SCon{Chr{k}, _} : String}
          {==}

def before_host(s: String, +h: {Tgt.all_host(s) == True{} : Bool}) -> {s == Tgt.before(s, 58) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +hk = and_l(Tgt.is_host_char(k), Tgt.all_host(rest), h)
          %Equal.sym(Bool, U32.is_eq(k, 58), False{}, host_ne(U32.is_eq(k, 58), k, 58, {==}, {==}, hk))
            : {SCon{Chr{k}, rest} == Tgt.before.go(SCon{Chr{k}, rest}, 58, _) : String}
          %before_host(rest, and_r(Tgt.is_host_char(k), Tgt.all_host(rest), h))
            : {SCon{Chr{k}, rest} == SCon{Chr{k}, _} : String}
          {==}

def colon_host(s: String, +h: {Tgt.all_host(s) == True{} : Bool}) -> {False{} == Tgt.has_char(s, 58) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +hk = and_l(Tgt.is_host_char(k), Tgt.all_host(rest), h)
          %Equal.sym(Bool, U32.is_eq(k, 58), False{}, host_ne(U32.is_eq(k, 58), k, 58, {==}, {==}, hk))
            : {False{} == Tgt.has_char.go(SCon{Chr{k}, rest}, 58, _) : Bool}
          colon_host(rest, and_r(Tgt.is_host_char(k), Tgt.all_host(rest), h))

def drop_len(s: String) -> {SNil{} == String.drop(s, String.length(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      drop_len(rest)

# the host alone: path "/", no port
def url_rest_host(+host: String, +hne: {String.is_empty(host) == False{} : Bool}, +hall: {Tgt.all_host(host) == True{} : Bool})
  -> {Tgt.url_rest(host) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}:
  %auth_host(host, hall)
    : {Tgt.url_host(Bool.and(Bool.not(String.is_empty(Tgt.before(_, 58))), Tgt.all_host(Tgt.before(_, 58))), Tgt.before(_, 58), _,
        Tgt.path_of(String.drop(host, String.length(_)))) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  %before_host(host, hall)
    : {Tgt.url_host(Bool.and(Bool.not(String.is_empty(_)), Tgt.all_host(_)), _, host,
        Tgt.path_of(String.drop(host, String.length(host)))) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  %drop_len(host)
    : {Tgt.url_host(Bool.and(Bool.not(String.is_empty(host)), Tgt.all_host(host)), host, host,
        Tgt.path_of(_)) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  %Equal.sym(Bool, String.is_empty(host), False{}, hne)
    : {Tgt.url_host(Bool.and(Bool.not(_), Tgt.all_host(host)), host, host, "/") == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  %Equal.sym(Bool, Tgt.all_host(host), True{}, hall)
    : {Tgt.url_host(Bool.and(True{}, _), host, host, "/") == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  %colon_host(host, hall)
    : {Tgt.url_port(Bool.and(_, Bool.not(String.is_empty(Tgt.after(host, 58)))), host, Tgt.after(host, 58), "/") == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  {==}

def sw_nil(s: String) -> {True{} == String.starts_with(s, "") : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      {==}

def drop0(s: String) -> {s == String.drop(s, 0n) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      {==}

def edge_http(+host: String, +ok: {Tgt.url_rest(host) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>})
  -> {Tgt.parse_url("http://" ++ host) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}:
  %sw_nil(host) : {Tgt.parse_url.of(_, False{}, "http://" ++ host) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  %drop0(host) : {Tgt.url_rest(_) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}
  ok

def edge_https(+rest: String) -> {Tgt.parse_url("https://" ++ rest) == Fail{"https is not supported"} : Result<&2, &2, String, Tgt.Url>}:
  %sw_nil(rest) : {Tgt.parse_url.of(False{}, _, "https://" ++ rest) == Fail{"https is not supported"} : Result<&2, &2, String, Tgt.Url>}
  {==}

def host_ok(+host: String, +h: {Bool.and(Bool.not(String.is_empty(host)), L.all_host(host)) == True{} : Bool})
  -> {Tgt.url_rest(host) == Done{Tgt.Url{"http", host, None{}, "/"}} : Result<&2, &2, String, Tgt.Url>}:
  url_rest_host(host,
    not_t(String.is_empty(host), and_l(Bool.not(String.is_empty(host)), L.all_host(host), h)),
    Equal.trans(Bool, Tgt.all_host(host), L.all_host(host), True{}, all_host_t(host), and_r(Bool.not(String.is_empty(host)), L.all_host(host), h)))

def L.url_parse_edges(host, rest, h):
  (edge_http(host, host_ok(host, h)), edge_https(rest))

# ---------------------------------------------------------------------
# U32 order: a >= b > c puts a above c
# ---------------------------------------------------------------------

def gt_b(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      False{}
    case GT{}:
      True{}

def no_gt(-c: Cmp, e: {c == GT{} : Cmp}, h: {gt_b(c) == False{} : Bool}) -> Empty:
  no_ft(Equal.trans(Bool, False{}, gt_b(c), True{}, Equal.sym(Bool, gt_b(c), False{}, h), Equal.cong(Cmp, Bool, x => gt_b(x), c, GT{}, e)))

def ge_of_fin(-ab: Bool, -bb: Bool, t: Cmp, h: {Cmp.is_ge(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) -> {Cmp.is_ge(t) == True{} : Bool}:
  match t:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case EQ{}:
      {==}
    case GT{}:
      {==}

def wgt_t(ab: Bool, t: Cmp, h1: {Cmp.is_ge(Word.cmp.fin(ab, True{}, t)) == True{} : Bool}) -> {Word.cmp.fin(ab, False{}, t) == GT{} : Cmp}:
  match ab t:
    case _ LT{}:
      Empty.absurd({LT{} == GT{} : Cmp}, no_ft(h1))
    case _ GT{}:
      {==}
    case True{} EQ{}:
      {==}
    case False{} EQ{}:
      Empty.absurd({EQ{} == GT{} : Cmp}, no_ft(h1))

def wgt_eq(+ab: Bool, -ta: Cmp, -tc: Cmp, +t: Cmp, et: {ta == t : Cmp}, ec: {tc == t : Cmp},
  h1: {Cmp.is_ge(Word.cmp.fin(ab, True{}, ta)) == True{} : Bool}) -> {Word.cmp.fin(ab, False{}, tc) == GT{} : Cmp}:
  %Equal.sym(Cmp, tc, t, ec) : {Word.cmp.fin(ab, False{}, _) == GT{} : Cmp}
  wgt_t(ab, t, Equal.trans(Bool, Cmp.is_ge(Word.cmp.fin(ab, True{}, t)), Cmp.is_ge(Word.cmp.fin(ab, True{}, ta)), True{},
    Equal.cong(Cmp, Bool, x => Cmp.is_ge(Word.cmp.fin(ab, True{}, x)), t, ta, Equal.sym(Cmp, ta, t, et)), h1))

def bits_l(bb: Bool, cb: Bool, h: {Bool.cmp(bb, cb) == GT{} : Cmp}) -> {bb == True{} : Bool}:
  match bb cb:
    case True{} _:
      {==}
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, no_gt(EQ{}, h, {==}))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, no_gt(LT{}, h, {==}))

def bits_r(bb: Bool, cb: Bool, h: {Bool.cmp(bb, cb) == GT{} : Cmp}) -> {cb == False{} : Bool}:
  match bb cb:
    case _ False{}:
      {==}
    case True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, no_gt(EQ{}, h, {==}))
    case False{} True{}:
      Empty.absurd({True{} == False{} : Bool}, no_gt(LT{}, h, {==}))

def wstep(+p: Nat, +at: Word(p), +bt: Word(p), +ct: Word(p), +ab: Bool, +bb: Bool, +cb: Bool, +ta: Cmp, tb: Cmp, +tc: Cmp,
  +ea: {Word.cmp(p, at, bt) == ta : Cmp}, +eb: {Word.cmp(p, bt, ct) == tb : Cmp}, +ec: {Word.cmp(p, at, ct) == tc : Cmp},
  +h1: {Cmp.is_ge(Word.cmp.fin(ab, bb, ta)) == True{} : Bool}, +h2: {Word.cmp.fin(bb, cb, tb) == GT{} : Cmp},
  ih: {Cmp.is_ge(Word.cmp(p, at, bt)) == True{} : Bool} -> {Word.cmp(p, bt, ct) == GT{} : Cmp} -> {Word.cmp(p, at, ct) == GT{} : Cmp})
  -> {Word.cmp.fin(ab, cb, tc) == GT{} : Cmp}:
  match tb:
    case LT{}:
      Empty.absurd({Word.cmp.fin(ab, cb, tc) == GT{} : Cmp}, no_gt(LT{}, h2, {==}))
    case GT{}:
      +g = ih(Equal.trans(Bool, Cmp.is_ge(Word.cmp(p, at, bt)), Cmp.is_ge(ta), True{}, Equal.cong(Cmp, Bool, x => Cmp.is_ge(x), Word.cmp(p, at, bt), ta, ea), ge_of_fin(ab, bb, ta, h1)), eb)
      %Equal.sym(Cmp, tc, GT{}, Equal.trans(Cmp, tc, Word.cmp(p, at, ct), GT{}, Equal.sym(Cmp, Word.cmp(p, at, ct), tc, ec), g))
        : {Word.cmp.fin(ab, cb, _) == GT{} : Cmp}
      {==}
    case EQ{}:
      +w = weq(p, bt, ct, Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, bt, ct), EQ{}, eb))
      +eac = Equal.trans(Cmp, ta, Word.cmp(p, at, bt), tc, Equal.sym(Cmp, Word.cmp(p, at, bt), ta, ea),
        Equal.trans(Cmp, Word.cmp(p, at, bt), Word.cmp(p, at, ct), tc, Equal.cong(Word(p), Cmp, x => Word.cmp(p, at, x), bt, ct, w), ec))
      +hb = bits_l(bb, cb, h2)
      +hc = bits_r(bb, cb, h2)
      %Equal.sym(Bool, cb, False{}, hc) : {Word.cmp.fin(ab, _, tc) == GT{} : Cmp}
      wgt_eq(ab, ta, tc, ta, {==}, Equal.sym(Cmp, ta, tc, eac),
        Equal.trans(Bool, Cmp.is_ge(Word.cmp.fin(ab, True{}, ta)), Cmp.is_ge(Word.cmp.fin(ab, bb, ta)), True{},
          Equal.cong(Bool, Bool, x => Cmp.is_ge(Word.cmp.fin(ab, x, ta)), True{}, bb, Equal.sym(Bool, bb, True{}, hb)), h1))

def wgt(n: Nat, a: Word(n), b: Word(n), c: Word(n), +h1: {Cmp.is_ge(Word.cmp(n, a, b)) == True{} : Bool}, +h2: {Word.cmp(n, b, c) == GT{} : Cmp})
  -> {Word.cmp(n, a, c) == GT{} : Cmp}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          Empty.absurd({EQ{} == GT{} : Cmp}, no_gt(EQ{}, h2, {==}))
    case 1n+(+p):
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          wstep(p, at, bt, ct, ab, bb, cb, Word.cmp(p, at, bt), Word.cmp(p, bt, ct), Word.cmp(p, at, ct), {==}, {==}, {==}, h1, h2,
            x => y => wgt(p, at, bt, ct, x, y))

def lt_b(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def no_lt(-c: Cmp, e: {c == LT{} : Cmp}, h: {lt_b(c) == False{} : Bool}) -> Empty:
  no_ft(Equal.trans(Bool, False{}, lt_b(c), True{}, Equal.sym(Bool, lt_b(c), False{}, h), Equal.cong(Cmp, Bool, x => lt_b(x), c, LT{}, e)))

def le_of_fin(-ab: Bool, -bb: Bool, t: Cmp, h: {Cmp.is_le(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) -> {Cmp.is_le(t) == True{} : Bool}:
  match t:
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case EQ{}:
      {==}
    case LT{}:
      {==}

def wlt_t(ab: Bool, t: Cmp, h1: {Cmp.is_le(Word.cmp.fin(ab, False{}, t)) == True{} : Bool}) -> {Word.cmp.fin(ab, True{}, t) == LT{} : Cmp}:
  match ab t:
    case _ GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, no_ft(h1))
    case _ LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, no_ft(h1))

def wlt_eq(+ab: Bool, -ta: Cmp, -tc: Cmp, +t: Cmp, et: {ta == t : Cmp}, ec: {tc == t : Cmp},
  h1: {Cmp.is_le(Word.cmp.fin(ab, False{}, ta)) == True{} : Bool}) -> {Word.cmp.fin(ab, True{}, tc) == LT{} : Cmp}:
  %Equal.sym(Cmp, tc, t, ec) : {Word.cmp.fin(ab, True{}, _) == LT{} : Cmp}
  wlt_t(ab, t, Equal.trans(Bool, Cmp.is_le(Word.cmp.fin(ab, False{}, t)), Cmp.is_le(Word.cmp.fin(ab, False{}, ta)), True{},
    Equal.cong(Cmp, Bool, x => Cmp.is_le(Word.cmp.fin(ab, False{}, x)), t, ta, Equal.sym(Cmp, ta, t, et)), h1))

def bitl_l(bb: Bool, cb: Bool, h: {Bool.cmp(bb, cb) == LT{} : Cmp}) -> {bb == False{} : Bool}:
  match bb cb:
    case False{} _:
      {==}
    case True{} True{}:
      Empty.absurd({True{} == False{} : Bool}, no_lt(EQ{}, h, {==}))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, no_lt(GT{}, h, {==}))

def bitl_r(bb: Bool, cb: Bool, h: {Bool.cmp(bb, cb) == LT{} : Cmp}) -> {cb == True{} : Bool}:
  match bb cb:
    case _ True{}:
      {==}
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, no_lt(EQ{}, h, {==}))
    case True{} False{}:
      Empty.absurd({False{} == True{} : Bool}, no_lt(GT{}, h, {==}))

def wlstep(+p: Nat, +at: Word(p), +bt: Word(p), +ct: Word(p), +ab: Bool, +bb: Bool, +cb: Bool, +ta: Cmp, tb: Cmp, +tc: Cmp,
  +ea: {Word.cmp(p, at, bt) == ta : Cmp}, +eb: {Word.cmp(p, bt, ct) == tb : Cmp}, +ec: {Word.cmp(p, at, ct) == tc : Cmp},
  +h1: {Cmp.is_le(Word.cmp.fin(ab, bb, ta)) == True{} : Bool}, +h2: {Word.cmp.fin(bb, cb, tb) == LT{} : Cmp},
  ih: {Cmp.is_le(Word.cmp(p, at, bt)) == True{} : Bool} -> {Word.cmp(p, bt, ct) == LT{} : Cmp} -> {Word.cmp(p, at, ct) == LT{} : Cmp})
  -> {Word.cmp.fin(ab, cb, tc) == LT{} : Cmp}:
  match tb:
    case GT{}:
      Empty.absurd({Word.cmp.fin(ab, cb, tc) == LT{} : Cmp}, no_lt(GT{}, h2, {==}))
    case LT{}:
      +g = ih(Equal.trans(Bool, Cmp.is_le(Word.cmp(p, at, bt)), Cmp.is_le(ta), True{}, Equal.cong(Cmp, Bool, x => Cmp.is_le(x), Word.cmp(p, at, bt), ta, ea), le_of_fin(ab, bb, ta, h1)), eb)
      %Equal.sym(Cmp, tc, LT{}, Equal.trans(Cmp, tc, Word.cmp(p, at, ct), LT{}, Equal.sym(Cmp, Word.cmp(p, at, ct), tc, ec), g))
        : {Word.cmp.fin(ab, cb, _) == LT{} : Cmp}
      {==}
    case EQ{}:
      +w = weq(p, bt, ct, Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, bt, ct), EQ{}, eb))
      +eac = Equal.trans(Cmp, ta, Word.cmp(p, at, bt), tc, Equal.sym(Cmp, Word.cmp(p, at, bt), ta, ea),
        Equal.trans(Cmp, Word.cmp(p, at, bt), Word.cmp(p, at, ct), tc, Equal.cong(Word(p), Cmp, x => Word.cmp(p, at, x), bt, ct, w), ec))
      +hb = bitl_l(bb, cb, h2)
      +hc = bitl_r(bb, cb, h2)
      %Equal.sym(Bool, cb, True{}, hc) : {Word.cmp.fin(ab, _, tc) == LT{} : Cmp}
      wlt_eq(ab, ta, tc, ta, {==}, Equal.sym(Cmp, ta, tc, eac),
        Equal.trans(Bool, Cmp.is_le(Word.cmp.fin(ab, False{}, ta)), Cmp.is_le(Word.cmp.fin(ab, bb, ta)), True{},
          Equal.cong(Bool, Bool, x => Cmp.is_le(Word.cmp.fin(ab, x, ta)), False{}, bb, Equal.sym(Bool, bb, False{}, hb)), h1))

def wlt(n: Nat, a: Word(n), b: Word(n), c: Word(n), +h1: {Cmp.is_le(Word.cmp(n, a, b)) == True{} : Bool}, +h2: {Word.cmp(n, b, c) == LT{} : Cmp})
  -> {Word.cmp(n, a, c) == LT{} : Cmp}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          Empty.absurd({EQ{} == LT{} : Cmp}, no_lt(EQ{}, h2, {==}))
    case 1n+(+p):
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          wlstep(p, at, bt, ct, ab, bb, cb, Word.cmp(p, at, bt), Word.cmp(p, bt, ct), Word.cmp(p, at, ct), {==}, {==}, {==}, h1, h2,
            x => y => wlt(p, at, bt, ct, x, y))

# a >= b > c: a > c
def u32_gt2(a: U32, b: U32, c: U32, +h1: {U32.is_ge(a, b) == True{} : Bool}, +h2: {U32.cmp(b, c) == GT{} : Cmp})
  -> {U32.cmp(a, c) == GT{} : Cmp}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      wgt(32n, x, y, z, h1, h2)

# a <= b < c: a < c
def u32_lt2(a: U32, b: U32, c: U32, +h1: {U32.is_le(a, b) == True{} : Bool}, +h2: {U32.cmp(b, c) == LT{} : Cmp})
  -> {U32.cmp(a, c) == LT{} : Cmp}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      wlt(32n, x, y, z, h1, h2)

# a >= b and b > c: a > c, so not a < c
def u32_gt(a: U32, b: U32, c: U32, +h1: {U32.is_ge(a, b) == True{} : Bool}, +h2: {U32.cmp(b, c) == GT{} : Cmp})
  -> {U32.is_lt(a, c) == False{} : Bool}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      %Equal.sym(Cmp, Word.cmp(32n, x, z), GT{}, wgt(32n, x, y, z, h1, h2)) : {Cmp.is_lt(_) == False{} : Bool}
      {==}

# ---------------------------------------------------------------------
# String.eq is equality
# ---------------------------------------------------------------------

def rec_fin(-h1: Char, -h2: Char, rr: (String & String) & Cmp) -> {String.eq.fin(String.cmp.rec(h1, h2, rr)) == String.eq.fin(rr) : Bool}:
  match rr:
    case (ab, r):
      match ab:
        case (a, b):
          {==}

def seq_step(+t1: String, +t2: String, +x: U32, +y: U32, c: Cmp, +e: {U32.cmp(x, y) == c : Cmp},
  +h: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c))) == True{} : Bool},
  ih: {String.eq(t1, t2) == True{} : Bool} -> {t1 == t2 : String}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}:
  match c:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, no_ft(h))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String}, no_ft(h))
    case EQ{}:
      +et = ih(Equal.trans(Bool, String.eq(t1, t2), String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), True{},
        Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))), String.eq(t1, t2), rec_fin(Chr{x}, Chr{y}, String.cmp(t1, t2))), h))
      +ex = u32_eq(x, y, Equal.cong(Cmp, Bool, z => Cmp.is_eq(z), U32.cmp(x, y), EQ{}, e))
      %et : {SCon{Chr{x}, t1} == SCon{Chr{y}, _} : String}
      %ex : {SCon{Chr{x}, t1} == SCon{Chr{_}, t1} : String}
      {==}

def str_eq(a: String, b: String, +h: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{c, t}:
          Empty.absurd({SNil{} == SCon{c, t} : String}, no_ft(h))
    case SCon{c1, +t1}:
      match c1:
        case Chr{+x}:
          match b:
            case SNil{}:
              Empty.absurd({SCon{Chr{x}, t1} == SNil{} : String}, no_ft(h))
            case SCon{c2, +t2}:
              match c2:
                case Chr{+y}:
                  seq_step(t1, t2, x, y, U32.cmp(x, y), {==}, h, hh => str_eq(t1, t2, hh))

# ---------------------------------------------------------------------
# url_parse
# ---------------------------------------------------------------------

def app_nil(s: String) -> {s == String.append(s, SNil{}) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %app_nil(rest) : {SCon{c, rest} == SCon{c, _} : String}
      {==}

# the authority of a host followed by more: the host, then the rest's
def auth_app(a: String, +y: String, +h: {Tgt.all_host(a) == True{} : Bool}) -> {String.append(a, Tgt.auth_of(y)) == Tgt.auth_of(String.append(a, y)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +hk = and_l(Tgt.is_host_char(k), Tgt.all_host(rest), h)
          %Equal.sym(Bool, Tgt.ends_auth(k), False{}, ends_auth_f(k, hk))
            : {SCon{Chr{k}, String.append(rest, Tgt.auth_of(y))} == Tgt.auth_of.go(SCon{Chr{k}, String.append(rest, y)}, _) : String}
          %auth_app(rest, y, and_r(Tgt.is_host_char(k), Tgt.all_host(rest), h))
            : {SCon{Chr{k}, String.append(rest, Tgt.auth_of(y))} == SCon{Chr{k}, _} : String}
          {==}

def before_app(a: String, +y: String, +h: {Tgt.all_host(a) == True{} : Bool}) -> {String.append(a, Tgt.before(y, 58)) == Tgt.before(String.append(a, y), 58) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +hk = and_l(Tgt.is_host_char(k), Tgt.all_host(rest), h)
          %Equal.sym(Bool, U32.is_eq(k, 58), False{}, host_ne(U32.is_eq(k, 58), k, 58, {==}, {==}, hk))
            : {SCon{Chr{k}, String.append(rest, Tgt.before(y, 58))} == Tgt.before.go(SCon{Chr{k}, String.append(rest, y)}, 58, _) : String}
          %before_app(rest, y, and_r(Tgt.is_host_char(k), Tgt.all_host(rest), h))
            : {SCon{Chr{k}, String.append(rest, Tgt.before(y, 58))} == SCon{Chr{k}, _} : String}
          {==}

def after_app(a: String, +y: String, +h: {Tgt.all_host(a) == True{} : Bool}) -> {Tgt.after(y, 58) == Tgt.after(String.append(a, y), 58) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +hk = and_l(Tgt.is_host_char(k), Tgt.all_host(rest), h)
          %Equal.sym(Bool, U32.is_eq(k, 58), False{}, host_ne(U32.is_eq(k, 58), k, 58, {==}, {==}, hk))
            : {Tgt.after(y, 58) == Tgt.after.go(SCon{Chr{k}, String.append(rest, y)}, 58, _) : String}
          after_app(rest, y, and_r(Tgt.is_host_char(k), Tgt.all_host(rest), h))

def has_app(a: String, +y: String, +h: {Tgt.all_host(a) == True{} : Bool}) -> {Tgt.has_char(y, 58) == Tgt.has_char(String.append(a, y), 58) : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +hk = and_l(Tgt.is_host_char(k), Tgt.all_host(rest), h)
          %Equal.sym(Bool, U32.is_eq(k, 58), False{}, host_ne(U32.is_eq(k, 58), k, 58, {==}, {==}, hk))
            : {Tgt.has_char(y, 58) == Tgt.has_char.go(SCon{Chr{k}, String.append(rest, y)}, 58, _) : Bool}
          has_app(rest, y, and_r(Tgt.is_host_char(k), Tgt.all_host(rest), h))

def drop_app(a: String, +y: String) -> {y == String.drop(String.append(a, y), String.length(a)) : String}:
  match a:
    case SNil{}:
      drop0(y)
    case SCon{+c, +rest}:
      drop_app(rest, y)

def drop_app2(a: String, +b: String, +y: String) -> {y == String.drop(String.append(a, String.append(b, y)), String.length(String.append(a, b))) : String}:
  match a:
    case SNil{}:
      drop_app(b, y)
    case SCon{+c, +rest}:
      drop_app2(rest, b, y)

# digits hold no '/', '?' or '#'
def dig_ne(+k: U32, +n: U32, +hn: {L.is_digit(Chr{n}) == False{} : Bool}, +h: {L.is_digit(Chr{k}) == True{} : Bool}) -> {U32.is_eq(k, n) == False{} : Bool}:
  ne_of(x => L.is_digit(Chr{x}), U32.is_eq(k, n), k, n, {==}, hn, h)

def auth_dig(d: String, +p: String, +h: {L.all_digits.go(d) == True{} : Bool}) -> {d == Tgt.auth_of(String.append(d, SCon{Chr{47}, p})) : String}:
  match d:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          +hk = and_l(L.is_digit(Chr{k}), L.all_digits.go(rest), h)
          %Equal.sym(Bool, U32.is_eq(k, 47), False{}, dig_ne(k, 47, {==}, hk))
            : {SCon{Chr{k}, rest} == Tgt.auth_of.go(SCon{Chr{k}, String.append(rest, SCon{Chr{47}, p})}, Bool.or(_, Bool.or(U32.is_eq(k, 63), U32.is_eq(k, 35)))) : String}
          %Equal.sym(Bool, U32.is_eq(k, 63), False{}, dig_ne(k, 63, {==}, hk))
            : {SCon{Chr{k}, rest} == Tgt.auth_of.go(SCon{Chr{k}, String.append(rest, SCon{Chr{47}, p})}, Bool.or(False{}, Bool.or(_, U32.is_eq(k, 35)))) : String}
          %Equal.sym(Bool, U32.is_eq(k, 35), False{}, dig_ne(k, 35, {==}, hk))
            : {SCon{Chr{k}, rest} == Tgt.auth_of.go(SCon{Chr{k}, String.append(rest, SCon{Chr{47}, p})}, Bool.or(False{}, Bool.or(False{}, _))) : String}
          %auth_dig(rest, p, and_r(L.is_digit(Chr{k}), L.all_digits.go(rest), h))
            : {SCon{Chr{k}, rest} == SCon{Chr{k}, _} : String}
          {==}

def digits_go(d: String, h: {L.all_digits(d) == True{} : Bool}) -> {L.all_digits.go(d) == True{} : Bool}:
  match d:
    case SNil{}:
      Empty.absurd({True{} == True{} : Bool}, no_ft(h))
    case SCon{+c, +rest}:
      h

def digits_ne(d: String, h: {L.all_digits(d) == True{} : Bool}) -> {False{} == String.is_empty(d) : Bool}:
  match d:
    case SNil{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case SCon{+c, +rest}:
      {==}

def bef35(p: String, +h: {L.all_path(p) == True{} : Bool}) -> {p == Tgt.before(p, 35) : String}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          +h1 = and_l(Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35))), L.all_path(rest), h)
          +h35 = not_t(U32.is_eq(k, 35), and_r(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35)), h1))
          %Equal.sym(Bool, U32.is_eq(k, 35), False{}, h35)
            : {SCon{Chr{k}, rest} == Tgt.before.go(SCon{Chr{k}, rest}, 35, _) : String}
          %bef35(rest, and_r(Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35))), L.all_path(rest), h))
            : {SCon{Chr{k}, rest} == SCon{Chr{k}, _} : String}
          {==}

def ctl_path(p: String, +h: {L.all_path(p) == True{} : Bool}) -> {False{} == Tgt.has_ctl(p) : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          +h1 = and_l(Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35))), L.all_path(rest), h)
          +hr = and_l(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35)), h1)
          +hge = and_l(U32.is_ge(k, 33), U32.is_le(k, 126), hr)
          %Equal.sym(Bool, U32.is_lt(k, 32), False{}, u32_gt(k, 33, 32, hge, {==}))
            : {False{} == Bool.or(Bool.or(_, U32.is_eq(k, 127)), Tgt.has_ctl(rest)) : Bool}
          %Equal.sym(Bool, U32.is_eq(k, 127), False{}, ne_of(x => L.in_range32(x, 33, 126), U32.is_eq(k, 127), k, 127, {==}, {==}, hr))
            : {False{} == Bool.or(Bool.or(False{}, _), Tgt.has_ctl(rest)) : Bool}
          ctl_path(rest, and_r(Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35))), L.all_path(rest), h))

def and_f(x: Bool) -> {False{} == Bool.and(x, False{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def hex2b(+j: U32, r2: String, +h: {Bool.and(L.is_hex(j), L.is_hex(L.byte_at(r2, 0n))) == True{} : Bool})
  -> {Bool.and(Tgt.is_hex(j), Tgt.is_hex(Tgt.byte_at(Tgt.before(r2, 63), 0n))) == True{} : Bool}:
  match r2:
    case SNil{}:
      Empty.absurd({Bool.and(Tgt.is_hex(j), False{}) == True{} : Bool}, no_ft(Equal.trans(Bool, False{}, Bool.and(L.is_hex(j), False{}), True{}, and_f(L.is_hex(j)), h)))
    case SCon{c, +r3}:
      match c:
        case Chr{+i}:
          +hi = and_r(L.is_hex(j), L.is_hex(i), h)
          %Equal.sym(Bool, U32.is_eq(i, 63), False{}, ne_of(x => L.is_hex(x), U32.is_eq(i, 63), i, 63, {==}, {==}, hi))
            : {Bool.and(Tgt.is_hex(j), Tgt.is_hex(Tgt.byte_at(Tgt.before.go(SCon{Chr{i}, r3}, 63, _), 0n))) == True{} : Bool}
          h

# the two hex digits after a '%' survive cutting at '?'
def hex2(r: String, +h: {Bool.and(L.is_hex(L.byte_at(r, 0n)), L.is_hex(L.byte_at(r, 1n))) == True{} : Bool})
  -> {Bool.and(Tgt.is_hex(Tgt.byte_at(Tgt.before(r, 63), 0n)), Tgt.is_hex(Tgt.byte_at(Tgt.before(r, 63), 1n))) == True{} : Bool}:
  match r:
    case SNil{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case SCon{c, +r2}:
      match c:
        case Chr{+j}:
          +hj = and_l(L.is_hex(j), L.is_hex(L.byte_at(r2, 0n)), h)
          %Equal.sym(Bool, U32.is_eq(j, 63), False{}, ne_of(x => L.is_hex(x), U32.is_eq(j, 63), j, 63, {==}, {==}, hj))
            : {Bool.and(Tgt.is_hex(Tgt.byte_at(Tgt.before.go(SCon{Chr{j}, r2}, 63, _), 0n)),
                Tgt.is_hex(Tgt.byte_at(Tgt.before.go(SCon{Chr{j}, r2}, 63, _), 1n))) == True{} : Bool}
          hex2b(j, r2, h)

def pstep2(b37: Bool, +k: U32, +r: String,
  +hh: {Bool.or(Bool.not(b37), Bool.and(L.is_hex(L.byte_at(r, 0n)), L.is_hex(L.byte_at(r, 1n)))) == True{} : Bool},
  +ih: {None{} == Tgt.bad_escape(Tgt.before(r, 63)) : Maybe<&2, String>})
  -> {None{} == Tgt.bad_escape.go(SCon{Chr{k}, Tgt.before(r, 63)}, Bool.and(b37, Bool.not(Bool.and(Tgt.is_hex(Tgt.byte_at(Tgt.before(r, 63), 0n)), Tgt.is_hex(Tgt.byte_at(Tgt.before(r, 63), 1n)))))) : Maybe<&2, String>}:
  match b37:
    case False{}:
      ih
    case True{}:
      %Equal.sym(Bool, Bool.and(Tgt.is_hex(Tgt.byte_at(Tgt.before(r, 63), 0n)), Tgt.is_hex(Tgt.byte_at(Tgt.before(r, 63), 1n))), True{}, hex2(r, hh))
        : {None{} == Tgt.bad_escape.go(SCon{Chr{k}, Tgt.before(r, 63)}, Bool.and(True{}, Bool.not(_))) : Maybe<&2, String>}
      ih

def pstep(b63: Bool, +k: U32, +r: String, +e37: {U32.is_eq(k, 37) == U32.is_eq(k, 37) : Bool},
  +hh: {Bool.or(Bool.not(U32.is_eq(k, 37)), Bool.and(L.is_hex(L.byte_at(r, 0n)), L.is_hex(L.byte_at(r, 1n)))) == True{} : Bool},
  +ih: {None{} == Tgt.bad_escape(Tgt.before(r, 63)) : Maybe<&2, String>})
  -> {None{} == Tgt.bad_escape(Tgt.before.go(SCon{Chr{k}, r}, 63, b63)) : Maybe<&2, String>}:
  match b63:
    case True{}:
      {==}
    case False{}:
      pstep2(U32.is_eq(k, 37), k, r, hh, ih)

def pct(p: String, +h: {L.pct_ok.go(String.length(p), p) == True{} : Bool}) -> {None{} == Tgt.bad_escape(Tgt.before(p, 63)) : Maybe<&2, String>}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +a = Bool.or(Bool.not(U32.is_eq(k, 37)), Bool.and(L.is_hex(L.byte_at(r, 0n)), L.is_hex(L.byte_at(r, 1n))))
          +hr = Equal.trans(Bool, L.pct_ok.go(String.length(r), r), L.pct_ok.go(String.length(r), String.drop(r, 0n)), True{},
            Equal.cong(String, Bool, x => L.pct_ok.go(String.length(r), x), r, String.drop(r, 0n), drop0(r)),
            and_r(a, L.pct_ok.go(String.length(r), String.drop(r, 0n)), h))
          pstep(U32.is_eq(k, 63), k, r, {==}, and_l(a, L.pct_ok.go(String.length(r), String.drop(r, 0n)), h), pct(r, hr))

def ur_f(+r: String, +auth: String) -> Result<&2, &2, String, Tgt.Url>:
  Tgt.url_host(Bool.and(Bool.not(String.is_empty(Tgt.before(auth, 58))), Tgt.all_host(Tgt.before(auth, 58))), Tgt.before(auth, 58), auth,
    Tgt.path_of(String.drop(r, String.length(auth))))

def ur_g(+r: String, +h: String, +auth: String) -> Result<&2, &2, String, Tgt.Url>:
  Tgt.url_host(Bool.and(Bool.not(String.is_empty(h)), Tgt.all_host(h)), h, auth, Tgt.path_of(String.drop(r, String.length(auth))))

# after the host and its port text: the port decides
def rest_main(+host: String, +pt: String, +p: String,
  +hne: {String.is_empty(host) == False{} : Bool}, +hall: {Tgt.all_host(host) == True{} : Bool},
  +hpath: {L.all_path(p) == True{} : Bool}, +hpct: {L.pct_ok.go(String.length(p), p) == True{} : Bool},
  +hauth: {pt == Tgt.auth_of(String.append(pt, SCon{Chr{47}, p})) : String}, +hbef: {SNil{} == Tgt.before(pt, 58) : String})
  -> {Tgt.url_rest(String.append(host, String.append(pt, SCon{Chr{47}, p})))
      == Tgt.url_port(Bool.and(Tgt.has_char(String.append(host, pt), 58), Bool.not(String.is_empty(Tgt.after(String.append(host, pt), 58)))),
           host, Tgt.after(String.append(host, pt), 58), SCon{Chr{47}, p}) : Result<&2, &2, String, Tgt.Url>}:
  +r = String.append(host, String.append(pt, SCon{Chr{47}, p}))
  +a = String.append(host, pt)
  +rhs = Tgt.url_port(Bool.and(Tgt.has_char(a, 58), Bool.not(String.is_empty(Tgt.after(a, 58)))), host, Tgt.after(a, 58), SCon{Chr{47}, p})
  +e1 = Equal.trans(String, a, String.append(host, Tgt.auth_of(String.append(pt, SCon{Chr{47}, p}))), Tgt.auth_of(r),
    Equal.cong(String, String, x => String.append(host, x), pt, Tgt.auth_of(String.append(pt, SCon{Chr{47}, p})), hauth),
    auth_app(host, String.append(pt, SCon{Chr{47}, p}), hall))
  +e2 = Equal.trans(String, host, String.append(host, SNil{}), Tgt.before(a, 58), app_nil(host),
    Equal.trans(String, String.append(host, SNil{}), String.append(host, Tgt.before(pt, 58)), Tgt.before(a, 58),
      Equal.cong(String, String, x => String.append(host, x), SNil{}, Tgt.before(pt, 58), hbef),
      before_app(host, pt, hall)))
  +e3 = Equal.trans(String, SCon{Chr{47}, p}, SCon{Chr{47}, Tgt.before(p, 35)}, Tgt.path_of(String.drop(r, String.length(a))),
    Equal.cong(String, String, x => SCon{Chr{47}, x}, p, Tgt.before(p, 35), bef35(p, hpath)),
    Equal.cong(String, String, x => Tgt.path_of(x), SCon{Chr{47}, p}, String.drop(r, String.length(a)), drop_app2(host, pt, SCon{Chr{47}, p})))
  +ec = Equal.sym(Bool, Bool.and(Bool.not(String.is_empty(host)), Tgt.all_host(host)), True{},
    Equal.trans(Bool, Bool.and(Bool.not(String.is_empty(host)), Tgt.all_host(host)), Bool.and(Bool.not(False{}), Tgt.all_host(host)), True{},
      Equal.cong(Bool, Bool, x => Bool.and(Bool.not(x), Tgt.all_host(host)), String.is_empty(host), False{}, hne), hall))
  %e1 : {ur_f(r, _) == rhs : Result<&2, &2, String, Tgt.Url>}
  %e2 : {ur_g(r, _, a) == rhs : Result<&2, &2, String, Tgt.Url>}
  %e3 : {Tgt.url_host(Bool.and(Bool.not(String.is_empty(host)), Tgt.all_host(host)), host, a, _) == rhs : Result<&2, &2, String, Tgt.Url>}
  %ec : {Tgt.url_host(_, host, a, SCon{Chr{47}, p}) == rhs : Result<&2, &2, String, Tgt.Url>}
  %ctl_path(p, hpath) : {Tgt.url_path(Bool.or(False{}, _), host, a, SCon{Chr{47}, p}) == rhs : Result<&2, &2, String, Tgt.Url>}
  %pct(p, hpct) : {Tgt.url_esc(_, host, a, SCon{Chr{47}, p}) == rhs : Result<&2, &2, String, Tgt.Url>}
  {==}

def http_pre(+x: String, -r: Result<&2, &2, String, Tgt.Url>, +ok: {Tgt.url_rest(x) == r : Result<&2, &2, String, Tgt.Url>})
  -> {Tgt.parse_url("http://" ++ x) == r : Result<&2, &2, String, Tgt.Url>}:
  %sw_nil(x) : {Tgt.parse_url.of(_, False{}, "http://" ++ x) == r : Result<&2, &2, String, Tgt.Url>}
  %drop0(x) : {Tgt.url_rest(_) == r : Result<&2, &2, String, Tgt.Url>}
  ok

def url_none(+host: String, +p: String,
  +hne: {String.is_empty(host) == False{} : Bool}, +hall: {Tgt.all_host(host) == True{} : Bool},
  +hpath: {L.all_path(p) == True{} : Bool}, +hpct: {L.pct_ok.go(String.length(p), p) == True{} : Bool})
  -> {Tgt.url_rest(String.append(host, String.append(SNil{}, SCon{Chr{47}, p}))) == Done{Tgt.Url{"http", host, None{}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}:
  +a = String.append(host, SNil{})
  %Equal.sym(Result<&2, &2, String, Tgt.Url>, Tgt.url_rest(String.append(host, String.append(SNil{}, SCon{Chr{47}, p}))),
      Tgt.url_port(Bool.and(Tgt.has_char(a, 58), Bool.not(String.is_empty(Tgt.after(a, 58)))), host, Tgt.after(a, 58), SCon{Chr{47}, p}),
      rest_main(host, SNil{}, p, hne, hall, hpath, hpct, {==}, {==}))
    : {_ == Done{Tgt.Url{"http", host, None{}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  %has_app(host, SNil{}, hall)
    : {Tgt.url_port(Bool.and(_, Bool.not(String.is_empty(Tgt.after(String.append(host, SNil{}), 58)))), host, Tgt.after(String.append(host, SNil{}), 58), SCon{Chr{47}, p})
       == Done{Tgt.Url{"http", host, None{}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  {==}

def url_some(+host: String, +n: Nat, +p: String,
  +hne: {String.is_empty(host) == False{} : Bool}, +hall: {Tgt.all_host(host) == True{} : Bool},
  +hpath: {L.all_path(p) == True{} : Bool}, +hpct: {L.pct_ok.go(String.length(p), p) == True{} : Bool},
  +hport: {L.port_ok(Some{n}) == True{} : Bool})
  -> {Tgt.url_rest(String.append(host, String.append(":" ++ Dec.show(n), SCon{Chr{47}, p}))) == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}:
  +d = Dec.show(n)
  +pt = ":" ++ d
  +hd = and_l(L.all_digits(d), Bool.or(String.eq(d, "0"), Bool.not(String.starts_with(d, "0"))), L.dec_show_canonical(n))
  +ha = Equal.cong(String, String, x => SCon{Chr{58}, x}, d, Tgt.auth_of(String.append(d, SCon{Chr{47}, p})), auth_dig(d, p, digits_go(d, hd)))
  +a = String.append(host, pt)
  %Equal.sym(Result<&2, &2, String, Tgt.Url>, Tgt.url_rest(String.append(host, String.append(pt, SCon{Chr{47}, p}))),
      Tgt.url_port(Bool.and(Tgt.has_char(a, 58), Bool.not(String.is_empty(Tgt.after(a, 58)))), host, Tgt.after(a, 58), SCon{Chr{47}, p}),
      rest_main(host, pt, p, hne, hall, hpath, hpct, ha, {==}))
    : {_ == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  %has_app(host, pt, hall)
    : {Tgt.url_port(Bool.and(_, Bool.not(String.is_empty(Tgt.after(String.append(host, pt), 58)))), host, Tgt.after(String.append(host, pt), 58), SCon{Chr{47}, p}) == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  %after_app(host, pt, hall)
    : {Tgt.url_port(Bool.and(True{}, Bool.not(String.is_empty(_))), host, _, SCon{Chr{47}, p}) == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  %digits_ne(d, hd)
    : {Tgt.url_port(Bool.and(True{}, Bool.not(_)), host, d, SCon{Chr{47}, p}) == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  %digits_ne(d, hd)
    : {Tgt.url_port.read(Tgt.pick(Maybe<&2, Nat>, _, Some{80n}, Dec.read(d)), host, d, SCon{Chr{47}, p}) == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  %Equal.sym(Maybe<&2, Nat>, Dec.read(d), Some{L.digits_value(d)}, L.dec_read_accepts(d, hd))
    : {Tgt.url_port.read(_, host, d, SCon{Chr{47}, p}) == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  %Equal.sym(Nat, L.digits_value(d), n, L.dec_show_value(n))
    : {Tgt.url_port.read(Some{_}, host, d, SCon{Chr{47}, p}) == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  %Equal.sym(Bool, L.port_ok(Some{n}), True{}, hport)
    : {Tgt.url_port.of(_, host, n, d, SCon{Chr{47}, p}) == Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}
  {==}

def sw_true(b: Bool, -t: String, h: {String.starts_with.if(t, SNil{}, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))

def url_port_case(+host: String, port: Maybe<&2, Nat>, +p: String,
  +hne: {String.is_empty(host) == False{} : Bool}, +hall: {Tgt.all_host(host) == True{} : Bool},
  +hpath: {L.all_path(p) == True{} : Bool}, +hpct: {L.pct_ok.go(String.length(p), p) == True{} : Bool},
  +hport: {L.port_ok(port) == True{} : Bool})
  -> {Tgt.parse_url("http://" ++ host ++ L.port_text(port) ++ SCon{Chr{47}, p}) == Done{Tgt.Url{"http", host, port, SCon{Chr{47}, p}}} : Result<&2, &2, String, Tgt.Url>}:
  match port:
    case None{}:
      http_pre(String.append(host, String.append(SNil{}, SCon{Chr{47}, p})), Done{Tgt.Url{"http", host, None{}, SCon{Chr{47}, p}}},
        url_none(host, p, hne, hall, hpath, hpct))
    case Some{+n}:
      http_pre(String.append(host, String.append(":" ++ Dec.show(n), SCon{Chr{47}, p})), Done{Tgt.Url{"http", host, Some{n}, SCon{Chr{47}, p}}},
        url_some(host, n, p, hne, hall, hpath, hpct, hport))

def url_path_case(+host: String, +port: Maybe<&2, Nat>, path: String,
  +hne: {String.is_empty(host) == False{} : Bool}, +hall: {Tgt.all_host(host) == True{} : Bool}, +hport: {L.port_ok(port) == True{} : Bool},
  +hsw: {String.starts_with(path, "/") == True{} : Bool}, +hpath: {L.all_path(path) == True{} : Bool}, +hpct: {L.pct_ok(path) == True{} : Bool})
  -> {Tgt.parse_url("http://" ++ host ++ L.port_text(port) ++ path) == Done{Tgt.Url{"http", host, port, path}} : Result<&2, &2, String, Tgt.Url>}:
  match path:
    case SNil{}:
      Empty.absurd({Tgt.parse_url("http://" ++ host ++ L.port_text(port) ++ SNil{}) == Done{Tgt.Url{"http", host, port, SNil{}}} : Result<&2, &2, String, Tgt.Url>}, no_ft(hsw))
    case SCon{c, +p}:
      match c:
        case Chr{+k}:
          +ek = u32_eq(k, 47, sw_true(U32.is_eq(k, 47), p, hsw))
          +a1 = Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35)))
          +hp = and_r(a1, L.all_path(p), hpath)
          +a2 = Bool.or(Bool.not(U32.is_eq(k, 37)), Bool.and(L.is_hex(L.byte_at(p, 0n)), L.is_hex(L.byte_at(p, 1n))))
          +hq = Equal.trans(Bool, L.pct_ok.go(String.length(p), p), L.pct_ok.go(String.length(p), String.drop(p, 0n)), True{},
            Equal.cong(String, Bool, x => L.pct_ok.go(String.length(p), x), p, String.drop(p, 0n), drop0(p)),
            and_r(a2, L.pct_ok.go(String.length(p), String.drop(p, 0n)), hpct))
          %Equal.sym(U32, k, 47, ek)
            : {Tgt.parse_url("http://" ++ host ++ L.port_text(port) ++ SCon{Chr{_}, p}) == Done{Tgt.Url{"http", host, port, SCon{Chr{_}, p}}} : Result<&2, &2, String, Tgt.Url>}
          url_port_case(host, port, p, hne, hall, hp, hq, hport)

def url_all(+scheme: String, +host: String, +port: Maybe<&2, Nat>, +path: String, +h: {L.url_ok(Tgt.Url{scheme, host, port, path}) == True{} : Bool})
  -> {Tgt.parse_url(L.url_text(Tgt.Url{scheme, host, port, path})) == Done{Tgt.Url{scheme, host, port, path}} : Result<&2, &2, String, Tgt.Url>}:
  +c6 = Bool.and(L.all_path(path), L.pct_ok(path))
  +c5 = Bool.and(String.starts_with(path, "/"), c6)
  +c4 = Bool.and(L.port_ok(port), c5)
  +c3 = Bool.and(Bool.not(String.is_empty(host)), L.all_host(host))
  +c2 = Bool.and(c3, c4)
  +es = str_eq(scheme, "http", and_l(String.eq(scheme, "http"), c2, h))
  +h2 = and_r(String.eq(scheme, "http"), c2, h)
  +h3 = and_l(c3, c4, h2)
  +h4 = and_r(c3, c4, h2)
  +h5 = and_r(L.port_ok(port), c5, h4)
  +h6 = and_r(String.starts_with(path, "/"), c6, h5)
  +hne = not_t(String.is_empty(host), and_l(Bool.not(String.is_empty(host)), L.all_host(host), h3))
  +hall = Equal.trans(Bool, Tgt.all_host(host), L.all_host(host), True{}, all_host_t(host), and_r(Bool.not(String.is_empty(host)), L.all_host(host), h3))
  %Equal.sym(String, scheme, "http", es)
    : {Tgt.parse_url(L.url_text(Tgt.Url{scheme, host, port, path})) == Done{Tgt.Url{_, host, port, path}} : Result<&2, &2, String, Tgt.Url>}
  url_path_case(host, port, path, hne, hall, and_l(L.port_ok(port), c5, h4), and_l(String.starts_with(path, "/"), c6, h5),
    and_l(L.all_path(path), L.pct_ok(path), h6), and_r(L.all_path(path), L.pct_ok(path), h6))

def L.url_parse(u, h):
  match u:
    case Tgt.Url{+scheme, +host, +port, +path}:
      url_all(scheme, host, port, path, h)

# ---------------------------------------------------------------------
# hit_decode: a JSON line starts with '{'; a CSV record with a digit or
# a quote
# ---------------------------------------------------------------------

def first_dig(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      L.is_digit(c)

def fd_app(d: String, -y: String, h: {first_dig(d) == True{} : Bool}) -> {first_dig(String.append(d, y)) == True{} : Bool}:
  match d:
    case SNil{}:
      Empty.absurd({first_dig(y) == True{} : Bool}, no_ft(h))
    case SCon{+c, +rest}:
      h

def fd_all(d: String, h: {L.all_digits(d) == True{} : Bool}) -> {first_dig(d) == True{} : Bool}:
  match d:
    case SNil{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case SCon{+c, +rest}:
      and_l(L.is_digit(c), L.all_digits.go(rest), h)

def fd_show(+n: Nat) -> {first_dig(Dec.show(n)) == True{} : Bool}:
  fd_all(Dec.show(n), and_l(L.all_digits(Dec.show(n)), Bool.or(String.eq(Dec.show(n), "0"), Bool.not(String.starts_with(Dec.show(n), "0"))), L.dec_show_canonical(n)))

def fd_pick(b: Bool, +x: Nat, +y: Nat, +n: Nat) -> {first_dig(Civil.pick(String, b, Dec.show(x), Dec.show(y) ++ Dec.pad(9n, n))) == True{} : Bool}:
  match b:
    case True{}:
      fd_show(x)
    case False{}:
      fd_app(Dec.show(y), Dec.pad(9n, n), fd_show(y))

# the CSV timestamp starts with a digit
def fd_nanos(+t: Civil.Time) -> {first_dig(Civil.unix_nanos(t)) == True{} : Bool}:
  +s = Nat.add(Civil.time_sec(t), Nat.div(Civil.time_nsec(t), Civil.sec()))
  +n = Nat.mod(Civil.time_nsec(t), Civil.sec())
  fd_pick(Nat.is_eq(s, 0n), n, s, n)

# a string starting with a byte that is not blank and not '{' is not JSON
def nj_chr(+k: U32, +t: String, +hb: {Hit.blank(True{}, k) == False{} : Bool}, +h1: {U32.is_eq(k, 123) == False{} : Bool})
  -> {Hit.first_is(Hit.skip_ws(SCon{Chr{k}, t}), 123) == False{} : Bool}:
  %Equal.sym(Bool, Hit.blank(True{}, k), False{}, hb)
    : {Hit.first_is(Hit.skip.go(SCon{Chr{k}, t}, Bool.not(_), True{}, String.drop(SCon{Chr{k}, t}, Hit.pick(Nat, _, 1n, 0n))), 123) == False{} : Bool}
  h1

def blank_f(+k: U32, e32: {U32.is_eq(k, 32) == False{} : Bool}, e9: {U32.is_eq(k, 9) == False{} : Bool},
  e13: {U32.is_eq(k, 13) == False{} : Bool}, e10: {U32.is_eq(k, 10) == False{} : Bool}) -> {Hit.blank(True{}, k) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(k, 32), False{}, e32) : {Bool.or(Bool.or(_, U32.is_eq(k, 9)), Bool.or(U32.is_eq(k, 13), Bool.and(True{}, U32.is_eq(k, 10)))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_eq(k, 9), False{}, e9) : {Bool.or(Bool.or(False{}, _), Bool.or(U32.is_eq(k, 13), Bool.and(True{}, U32.is_eq(k, 10)))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_eq(k, 13), False{}, e13) : {Bool.or(Bool.or(False{}, False{}), Bool.or(_, Bool.and(True{}, U32.is_eq(k, 10)))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_eq(k, 10), False{}, e10) : {Bool.or(Bool.or(False{}, False{}), Bool.or(False{}, Bool.and(True{}, _))) == False{} : Bool}
  {==}

def nj_dig(d: String, +t: String, h: {first_dig(d) == True{} : Bool}) -> {Hit.first_is(Hit.skip_ws(String.append(d, t)), 123) == False{} : Bool}:
  match d:
    case SNil{}:
      Empty.absurd({Hit.first_is(Hit.skip_ws(t), 123) == False{} : Bool}, no_ft(h))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +hd = h
          +hb = blank_f(k, dig_ne(k, 32, {==}, hd), dig_ne(k, 9, {==}, hd), dig_ne(k, 13, {==}, hd), dig_ne(k, 10, {==}, hd))
          nj_chr(k, String.append(r, t), hb, dig_ne(k, 123, {==}, hd))

def nj_f(b: Bool, +u: String, +T: String, +rest: String, +hu: {first_dig(u) == True{} : Bool})
  -> {Hit.first_is(Hit.skip_ws(String.append(Csv.field.of(b, u, T), rest)), 123) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, String.append(String.append(u, T), rest), String.append(u, String.append(T, rest)), app_assoc(u, T, rest))
        : {Hit.first_is(Hit.skip_ws(_), 123) == False{} : Bool}
      nj_dig(u, String.append(T, rest), hu)

# a CSV record whose first field starts with a digit is not JSON (the
# first field is written bare, or quoted)
def row_nj(+u: String, +g: String, +more: List<&2, String>, +rest: String, +hu: {first_dig(u) == True{} : Bool})
  -> {Hit.first_is(Hit.skip_ws(String.append(Csv.row(Con{u, Con{g, more}}), rest)), 123) == False{} : Bool}:
  nj_f(Csv.needs_quotes(u), u, SCon{',', Csv.row_into(Con{g, more})}, rest, hu)

def dec_nj(+x: String, +e: {Hit.first_is(Hit.skip_ws(x), 123) == False{} : Bool}) -> {Hit.decode(x) == Hit.of_csv(x) : Maybe<&1, Hit.Hit & String>}:
  %Equal.sym(Bool, Hit.first_is(Hit.skip_ws(x), 123), False{}, e) : {Hit.decode.of(_, x) == Hit.of_csv(x) : Maybe<&1, Hit.Hit & String>}
  {==}

def dec_csv(+attack: String, +seq: Nat, +code: Nat, +ts: Civil.Time, +lat: Nat, +bout: Nat, +bin: Nat, +err: String,
  +body: Maybe<&2, String>, +method: String, +url: String, +hdrs: Maybe<&2, List<&2, Hdr.Header>>, +rest: String)
  -> {Hit.decode(Hit.to_csv(Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs}) ++ rest)
      == Hit.of_csv(Hit.to_csv(Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs}) ++ rest) : Maybe<&1, Hit.Hit & String>}:
  +hh = {Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs} : Hit.Hit}
  %Equal.sym(String, Hit.to_csv(hh), L.csv_text(hh), L.hit_to_csv(hh))
    : {Hit.decode(_ ++ rest) == Hit.of_csv(_ ++ rest) : Maybe<&1, Hit.Hit & String>}
  dec_nj(L.csv_text(hh) ++ rest,
    row_nj(Civil.unix_nanos(ts), Dec.show(code), [Dec.show(lat), Dec.show(bout), Dec.show(bin), err,
      B64.encode(L.body_or_empty(body)), attack, Dec.show(seq), method, url, B64.encode(L.hdr_block(hdrs))], rest, fd_nanos(ts)))

def dec_js(+x: String, +e: {Hit.first_is(Hit.skip_ws(x), 123) == True{} : Bool}) -> {Hit.decode(x) == Hit.of_json(x) : Maybe<&1, Hit.Hit & String>}:
  %Equal.sym(Bool, Hit.first_is(Hit.skip_ws(x), 123), True{}, e) : {Hit.decode.of(_, x) == Hit.of_json(x) : Maybe<&1, Hit.Hit & String>}
  {==}

def L.hit_decode(h, rest):
  match h:
    case Hit.Hit{+attack, +seq, +code, +ts, +lat, +bout, +bin, +err, +body, +method, +url, +hdrs}:
      (dec_js(Hit.to_json(Hit.Hit{attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs}) ++ rest, {==}),
       dec_csv(attack, seq, code, ts, lat, bout, bin, err, body, method, url, hdrs, rest))

# ---------------------------------------------------------------------
# Trimming (lib/target.bend): the parser trims a line read backwards;
# trim_ws, line_of and LAWS' trim_ows all strip both ends
# ---------------------------------------------------------------------

def allws(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Tgt.is_ws(Tgt.code(c)), allws(rest))

def rev_rev(l: String, +a: String, +b: String) -> {String.reverse.go(String.reverse.go(l, a), b) == String.reverse.go(a, String.append(l, b)) : String}:
  match l:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      rev_rev(rest, SCon{c, a}, b)

def rr(+l: String) -> {l == String.reverse(String.reverse(l)) : String}:
  Equal.trans(String, l, String.append(l, SNil{}), String.reverse(String.reverse(l)), app_nil(l),
    Equal.sym(String, String.reverse(String.reverse(l)), String.append(l, SNil{}), rev_rev(l, SNil{}, SNil{})))

def t_allws(y: String, +h: {allws(y) == True{} : Bool}) -> {Tgt.trim_ws_l(y) == SNil{} : String}:
  match y:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_ws(k), True{}, and_l(Tgt.is_ws(k), allws(r), h))
            : {Tgt.trim_ws_l.go(SCon{Chr{k}, r}, _) == SNil{} : String}
          t_allws(r, and_r(Tgt.is_ws(k), allws(r), h))

def t_app_ws(a: String, +b: String, +h: {allws(a) == True{} : Bool}) -> {Tgt.trim_ws_l(String.append(a, b)) == Tgt.trim_ws_l(b) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_ws(k), True{}, and_l(Tgt.is_ws(k), allws(r), h))
            : {Tgt.trim_ws_l.go(SCon{Chr{k}, String.append(r, b)}, _) == Tgt.trim_ws_l(b) : String}
          t_app_ws(r, b, and_r(Tgt.is_ws(k), allws(r), h))

def t_app_step(w: Bool, +k: U32, +r: String, +b: String, +ew: {Tgt.is_ws(k) == w : Bool}, +h: {Bool.and(w, allws(r)) == False{} : Bool},
  ih: {allws(r) == False{} : Bool} -> {String.append(Tgt.trim_ws_l(r), b) == Tgt.trim_ws_l(String.append(r, b)) : String})
  -> {String.append(Tgt.trim_ws_l.go(SCon{Chr{k}, r}, w), b) == Tgt.trim_ws_l.go(SCon{Chr{k}, String.append(r, b)}, w) : String}:
  match w:
    case True{}:
      ih(h)
    case False{}:
      {==}

def t_app_nws(a: String, +b: String, +h: {allws(a) == False{} : Bool}) -> {String.append(Tgt.trim_ws_l(a), b) == Tgt.trim_ws_l(String.append(a, b)) : String}:
  match a:
    case SNil{}:
      Empty.absurd({b == Tgt.trim_ws_l(b) : String}, no_tf(h))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          t_app_step(Tgt.is_ws(k), k, r, b, {==}, h, hh => t_app_nws(r, b, hh))

def t_idem_step(w: Bool, +k: U32, +r: String, +ew: {Tgt.is_ws(k) == w : Bool}, ih: {Tgt.trim_ws_l(Tgt.trim_ws_l(r)) == Tgt.trim_ws_l(r) : String})
  -> {Tgt.trim_ws_l(Tgt.trim_ws_l.go(SCon{Chr{k}, r}, w)) == Tgt.trim_ws_l.go(SCon{Chr{k}, r}, w) : String}:
  match w:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Tgt.is_ws(k), False{}, ew) : {Tgt.trim_ws_l.go(SCon{Chr{k}, r}, _) == SCon{Chr{k}, r} : String}
      {==}

def t_idem(y: String) -> {Tgt.trim_ws_l(Tgt.trim_ws_l(y)) == Tgt.trim_ws_l(y) : String}:
  match y:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          t_idem_step(Tgt.is_ws(k), k, r, {==}, t_idem(r))


def ne_t_step(w: Bool, +k: U32, +r: String, +ew: {Tgt.is_ws(k) == w : Bool}, +h: {Bool.and(w, allws(r)) == False{} : Bool},
  ih: {allws(r) == False{} : Bool} -> {String.is_empty(Tgt.trim_ws_l(r)) == False{} : Bool})
  -> {String.is_empty(Tgt.trim_ws_l.go(SCon{Chr{k}, r}, w)) == False{} : Bool}:
  match w:
    case True{}:
      ih(h)
    case False{}:
      {==}

def ne_t(y: String, +h: {allws(y) == False{} : Bool}) -> {String.is_empty(Tgt.trim_ws_l(y)) == False{} : Bool}:
  match y:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(h))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          ne_t_step(Tgt.is_ws(k), k, r, {==}, h, hh => ne_t(r, hh))

def tr1_ws(w: Bool, +k: U32)
  -> {Tgt.pick(String, Bool.and(True{}, w), SNil{}, SCon{Chr{k}, SNil{}}) == String.reverse(Tgt.trim_ws_l.go(SCon{Chr{k}, SNil{}}, w)) : String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def tr1_step(b: Bool, +k: U32, +r: String, +eb: {allws(String.reverse(r)) == b : Bool})
  -> {Tgt.pick(String, Bool.and(String.is_empty(String.reverse(Tgt.trim_ws_l(String.reverse(r)))), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, String.reverse(Tgt.trim_ws_l(String.reverse(r)))})
      == String.reverse(Tgt.trim_ws_l(String.append(String.reverse(r), SCon{Chr{k}, SNil{}}))) : String}:
  match b:
    case True{}:
      %Equal.sym(String, Tgt.trim_ws_l(String.append(String.reverse(r), SCon{Chr{k}, SNil{}})), Tgt.trim_ws_l(SCon{Chr{k}, SNil{}}), t_app_ws(String.reverse(r), SCon{Chr{k}, SNil{}}, eb))
        : {Tgt.pick(String, Bool.and(String.is_empty(String.reverse(Tgt.trim_ws_l(String.reverse(r)))), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, String.reverse(Tgt.trim_ws_l(String.reverse(r)))})
          == String.reverse(_) : String}
      %Equal.sym(String, Tgt.trim_ws_l(String.reverse(r)), SNil{}, t_allws(String.reverse(r), eb))
        : {Tgt.pick(String, Bool.and(String.is_empty(String.reverse(_)), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, String.reverse(_)})
          == String.reverse(Tgt.trim_ws_l(SCon{Chr{k}, SNil{}})) : String}
      tr1_ws(Tgt.is_ws(k), k)
    case False{}:
      %t_app_nws(String.reverse(r), SCon{Chr{k}, SNil{}}, eb)
        : {Tgt.pick(String, Bool.and(String.is_empty(String.reverse(Tgt.trim_ws_l(String.reverse(r)))), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, String.reverse(Tgt.trim_ws_l(String.reverse(r)))})
          == String.reverse(_) : String}
      %Equal.sym(String, String.reverse(String.append(Tgt.trim_ws_l(String.reverse(r)), SCon{Chr{k}, SNil{}})), SCon{Chr{k}, String.reverse(Tgt.trim_ws_l(String.reverse(r)))},
          rev_snoc(Tgt.trim_ws_l(String.reverse(r)), Chr{k}, SNil{}))
        : {Tgt.pick(String, Bool.and(String.is_empty(String.reverse(Tgt.trim_ws_l(String.reverse(r)))), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, String.reverse(Tgt.trim_ws_l(String.reverse(r)))})
          == _ : String}
      %Equal.sym(Bool, String.is_empty(String.reverse(Tgt.trim_ws_l(String.reverse(r)))), False{},
          ne_r0(Tgt.trim_ws_l(String.reverse(r)), ne_t(String.reverse(r), eb)))
        : {Tgt.pick(String, Bool.and(_, Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, String.reverse(Tgt.trim_ws_l(String.reverse(r)))})
          == SCon{Chr{k}, String.reverse(Tgt.trim_ws_l(String.reverse(r)))} : String}
      {==}

# the right trim is the left trim of the reverse, reversed
def trr_rtr(x: String) -> {Tgt.trim_ws_r(x) == String.reverse(Tgt.trim_ws_l(String.reverse(x))) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +rtr = String.reverse(Tgt.trim_ws_l(String.reverse(r)))
          %Equal.sym(String, Tgt.trim_ws_r(r), rtr, trr_rtr(r))
            : {Tgt.pick(String, Bool.and(String.is_empty(_), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, _}) == String.reverse(Tgt.trim_ws_l(String.reverse(SCon{Chr{k}, r}))) : String}
          %Equal.sym(String, String.reverse.go(r, SCon{Chr{k}, SNil{}}), String.append(String.reverse(r), SCon{Chr{k}, SNil{}}), rev_acc(r, SCon{Chr{k}, SNil{}}))
            : {Tgt.pick(String, Bool.and(String.is_empty(rtr), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, rtr}) == String.reverse(Tgt.trim_ws_l(_)) : String}
          tr1_step(allws(String.reverse(r)), k, r, {==})

def emp_eq(s: String, h: {String.is_empty(s) == True{} : Bool}) -> {s == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, r}:
      Empty.absurd({SCon{c, r} == SNil{} : String}, no_ft(h))

def and_t(x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def comm_e(e: Bool, +k: U32, +r: String, +ee: {String.is_empty(Tgt.trim_ws_r(r)) == e : Bool}, +ew: {Tgt.is_ws(k) == True{} : Bool},
  +ih: {Tgt.trim_ws_l(Tgt.trim_ws_r(r)) == Tgt.trim_ws_r(Tgt.trim_ws_l(r)) : String})
  -> {Tgt.trim_ws_l(Tgt.pick(String, e, SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)})) == Tgt.trim_ws_r(Tgt.trim_ws_l(r)) : String}:
  match e:
    case True{}:
      +ez = emp_eq(Tgt.trim_ws_r(r), ee)
      Equal.trans(String, SNil{}, Tgt.trim_ws_l(Tgt.trim_ws_r(r)), Tgt.trim_ws_r(Tgt.trim_ws_l(r)),
        Equal.cong(String, String, x => Tgt.trim_ws_l(x), SNil{}, Tgt.trim_ws_r(r), Equal.sym(String, Tgt.trim_ws_r(r), SNil{}, ez)), ih)
    case False{}:
      %Equal.sym(Bool, Tgt.is_ws(k), True{}, ew)
        : {Tgt.trim_ws_l.go(SCon{Chr{k}, Tgt.trim_ws_r(r)}, _) == Tgt.trim_ws_r(Tgt.trim_ws_l(r)) : String}
      ih

def comm_w(w: Bool, +k: U32, +r: String, +ew: {Tgt.is_ws(k) == w : Bool},
  +ih: {Tgt.trim_ws_l(Tgt.trim_ws_r(r)) == Tgt.trim_ws_r(Tgt.trim_ws_l(r)) : String})
  -> {Tgt.trim_ws_l(Tgt.trim_ws_r(SCon{Chr{k}, r})) == Tgt.trim_ws_r(Tgt.trim_ws_l(SCon{Chr{k}, r})) : String}:
  match w:
    case True{}:
      %Equal.sym(Bool, Tgt.is_ws(k), True{}, ew)
        : {Tgt.trim_ws_l(Tgt.pick(String, Bool.and(String.is_empty(Tgt.trim_ws_r(r)), _), SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)}))
           == Tgt.trim_ws_r(Tgt.trim_ws_l.go(SCon{Chr{k}, r}, _)) : String}
      %Equal.sym(Bool, Bool.and(String.is_empty(Tgt.trim_ws_r(r)), True{}), String.is_empty(Tgt.trim_ws_r(r)), and_t(String.is_empty(Tgt.trim_ws_r(r))))
        : {Tgt.trim_ws_l(Tgt.pick(String, _, SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)})) == Tgt.trim_ws_r(Tgt.trim_ws_l(r)) : String}
      comm_e(String.is_empty(Tgt.trim_ws_r(r)), k, r, {==}, ew, ih)
    case False{}:
      %Equal.sym(Bool, Tgt.is_ws(k), False{}, ew)
        : {Tgt.trim_ws_l(Tgt.pick(String, Bool.and(String.is_empty(Tgt.trim_ws_r(r)), _), SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)}))
           == Tgt.trim_ws_r(Tgt.trim_ws_l.go(SCon{Chr{k}, r}, _)) : String}
      %Equal.sym(Bool, Tgt.is_ws(k), False{}, ew)
        : {Tgt.trim_ws_l(Tgt.pick(String, Bool.and(String.is_empty(Tgt.trim_ws_r(r)), False{}), SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)}))
           == Tgt.pick(String, Bool.and(String.is_empty(Tgt.trim_ws_r(r)), _), SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)}) : String}
      %and_f(String.is_empty(Tgt.trim_ws_r(r)))
        : {Tgt.trim_ws_l(Tgt.pick(String, _, SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)}))
           == Tgt.pick(String, _, SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)}) : String}
      %Equal.sym(Bool, Tgt.is_ws(k), False{}, ew)
        : {Tgt.trim_ws_l.go(SCon{Chr{k}, Tgt.trim_ws_r(r)}, _) == SCon{Chr{k}, Tgt.trim_ws_r(r)} : String}
      {==}

# trimming the left and the right commute
def comm(l: String) -> {Tgt.trim_ws_l(Tgt.trim_ws_r(l)) == Tgt.trim_ws_r(Tgt.trim_ws_l(l)) : String}:
  match l:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          comm_w(Tgt.is_ws(k), k, r, {==}, comm(r))

# the parser's line is trim_ws of the text read
def line_rev(+l: String) -> {Tgt.line_of(String.reverse(l)) == Tgt.trim_ws(l) : String}:
  %trr_rtr(l) : {Tgt.trim_ws_l(_) == Tgt.trim_ws(l) : String}
  comm(l)

# ---------------------------------------------------------------------
# The targets parser: run is a fold of adv over the bytes
# ---------------------------------------------------------------------

def feed(s: String, r: Tgt.Ln) -> Tgt.Ln:
  match s:
    case SNil{}:
      r
    case SCon{+c, +rest}:
      feed(rest, Tgt.adv(U32.is_eq(Tgt.code(c), 10), c, r))

def run_feed(s: String, +r: Tgt.Ln) -> {Tgt.run(s, r) == Tgt.ln_end(feed(s, r)) : Tgt.St}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      run_feed(rest, Tgt.adv(U32.is_eq(Tgt.code(c), 10), c, r))

def feed_app(a: String, +b: String, +r: Tgt.Ln) -> {feed(String.append(a, b), r) == feed(b, feed(a, r)) : Tgt.Ln}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      feed_app(rest, b, Tgt.adv(U32.is_eq(Tgt.code(c), 10), c, r))

def rev_app(a: String, +b: String, +acc: String) -> {String.reverse.go(String.append(a, b), acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      rev_app(rest, b, SCon{c, acc})

# bytes without a newline only extend the line
def feed_line(a: String, +cur: String, +st: Tgt.St, +h: {Tgt.has_char(a, 10) == False{} : Bool})
  -> {feed(a, Tgt.Ln{cur, st}) == Tgt.Ln{String.reverse.go(a, cur), st} : Tgt.Ln}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, 10), False{}, hcf_l(k, rest, 10, h))
            : {feed(rest, Tgt.adv(_, Chr{k}, Tgt.Ln{cur, st})) == Tgt.Ln{String.reverse.go(rest, SCon{Chr{k}, cur}), st} : Tgt.Ln}
          feed_line(rest, SCon{Chr{k}, cur}, st, hcf_r(k, rest, 10, h))

# a line and its newline move the state by the trimmed line
def feed_nl(+a: String, +st: Tgt.St, +h: {Tgt.has_char(a, 10) == False{} : Bool})
  -> {feed(String.append(a, SCon{Chr{10}, SNil{}}), Tgt.Ln{SNil{}, st}) == Tgt.Ln{SNil{}, Tgt.step(st, Tgt.trim_ws(a))} : Tgt.Ln}:
  %Equal.sym(Tgt.Ln, feed(String.append(a, SCon{Chr{10}, SNil{}}), Tgt.Ln{SNil{}, st}), feed(SCon{Chr{10}, SNil{}}, feed(a, Tgt.Ln{SNil{}, st})),
      feed_app(a, SCon{Chr{10}, SNil{}}, Tgt.Ln{SNil{}, st}))
    : {_ == Tgt.Ln{SNil{}, Tgt.step(st, Tgt.trim_ws(a))} : Tgt.Ln}
  %Equal.sym(Tgt.Ln, feed(a, Tgt.Ln{SNil{}, st}), Tgt.Ln{String.reverse(a), st}, feed_line(a, SNil{}, st, h))
    : {feed(SCon{Chr{10}, SNil{}}, _) == Tgt.Ln{SNil{}, Tgt.step(st, Tgt.trim_ws(a))} : Tgt.Ln}
  %Equal.sym(String, Tgt.line_of(String.reverse(a)), Tgt.trim_ws(a), line_rev(a))
    : {Tgt.Ln{SNil{}, Tgt.step(st, _)} == Tgt.Ln{SNil{}, Tgt.step(st, Tgt.trim_ws(a))} : Tgt.Ln}
  {==}

def all_nws(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(Bool.not(Tgt.is_ws(Tgt.code(c))), all_nws(rest))

def ne_app(a: String, -x: String, h: {String.is_empty(x) == False{} : Bool}) -> {String.is_empty(String.append(a, x)) == False{} : Bool}:
  match a:
    case SNil{}:
      h
    case SCon{c, r}:
      {==}

def ne_trr_step(w: Bool, +k: U32, +r: String, +ew: {Tgt.is_ws(k) == w : Bool}, +h: {Bool.and(w, allws(r)) == False{} : Bool},
  ih: {allws(r) == False{} : Bool} -> {String.is_empty(Tgt.trim_ws_r(r)) == False{} : Bool})
  -> {String.is_empty(Tgt.trim_ws_r(SCon{Chr{k}, r})) == False{} : Bool}:
  match w:
    case True{}:
      %Equal.sym(Bool, String.is_empty(Tgt.trim_ws_r(r)), False{}, ih(h))
        : {String.is_empty(Tgt.pick(String, Bool.and(_, Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)})) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Tgt.is_ws(k), False{}, ew)
        : {String.is_empty(Tgt.pick(String, Bool.and(String.is_empty(Tgt.trim_ws_r(r)), _), SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)})) == False{} : Bool}
      %and_f(String.is_empty(Tgt.trim_ws_r(r)))
        : {String.is_empty(Tgt.pick(String, _, SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)})) == False{} : Bool}
      {==}

def ne_trr(b: String, +h: {allws(b) == False{} : Bool}) -> {String.is_empty(Tgt.trim_ws_r(b)) == False{} : Bool}:
  match b:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(h))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          ne_trr_step(Tgt.is_ws(k), k, r, {==}, h, hh => ne_trr(r, hh))

def trr_app(a: String, +b: String, +h: {allws(b) == False{} : Bool}) -> {String.append(a, Tgt.trim_ws_r(b)) == Tgt.trim_ws_r(String.append(a, b)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %trr_app(r, b, h)
            : {SCon{Chr{k}, String.append(r, Tgt.trim_ws_r(b))} == Tgt.pick(String, Bool.and(String.is_empty(_), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, _}) : String}
          %Equal.sym(Bool, String.is_empty(String.append(r, Tgt.trim_ws_r(b))), False{}, ne_app(r, Tgt.trim_ws_r(b), ne_trr(b, h)))
            : {SCon{Chr{k}, String.append(r, Tgt.trim_ws_r(b))} == Tgt.pick(String, Bool.and(_, Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, String.append(r, Tgt.trim_ws_r(b))}) : String}
          {==}

def trr_id(s: String, +h: {all_nws(s) == True{} : Bool}) -> {s == Tgt.trim_ws_r(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +hk = not_t(Tgt.is_ws(k), and_l(Bool.not(Tgt.is_ws(k)), all_nws(r), h))
          %trr_id(r, and_r(Bool.not(Tgt.is_ws(k)), all_nws(r), h))
            : {SCon{Chr{k}, r} == Tgt.pick(String, Bool.and(String.is_empty(_), Tgt.is_ws(k)), SNil{}, SCon{Chr{k}, _}) : String}
          %Equal.sym(Bool, Tgt.is_ws(k), False{}, hk)
            : {SCon{Chr{k}, r} == Tgt.pick(String, Bool.and(String.is_empty(r), _), SNil{}, SCon{Chr{k}, r}) : String}
          %and_f(String.is_empty(r))
            : {SCon{Chr{k}, r} == Tgt.pick(String, _, SNil{}, SCon{Chr{k}, r}) : String}
          {==}

def trr_idem(+x: String) -> {Tgt.trim_ws_r(Tgt.trim_ws_r(x)) == Tgt.trim_ws_r(x) : String}:
  +rx = String.reverse(x)
  %Equal.sym(String, Tgt.trim_ws_r(x), String.reverse(Tgt.trim_ws_l(rx)), trr_rtr(x))
    : {Tgt.trim_ws_r(_) == _ : String}
  %Equal.sym(String, Tgt.trim_ws_r(String.reverse(Tgt.trim_ws_l(rx))), String.reverse(Tgt.trim_ws_l(String.reverse(String.reverse(Tgt.trim_ws_l(rx))))),
      trr_rtr(String.reverse(Tgt.trim_ws_l(rx))))
    : {_ == String.reverse(Tgt.trim_ws_l(rx)) : String}
  %rr(Tgt.trim_ws_l(rx)) : {String.reverse(Tgt.trim_ws_l(_)) == String.reverse(Tgt.trim_ws_l(rx)) : String}
  %Equal.sym(String, Tgt.trim_ws_l(Tgt.trim_ws_l(rx)), Tgt.trim_ws_l(rx), t_idem(rx)) : {String.reverse(_) == String.reverse(Tgt.trim_ws_l(rx)) : String}
  {==}

# ---------------------------------------------------------------------
# Printable bytes: white space there is the space alone
# ---------------------------------------------------------------------

def or_ff(x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def and_tt(-x: Bool, -y: Bool, hx: {x == True{} : Bool}, hy: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, hx) : {Bool.and(_, y) == True{} : Bool}
  hy

# in 32..126 the range 9..13 is out
def ws_pr(+k: U32, +h: {L.in_range32(k, 32, 126) == True{} : Bool}) -> {Tgt.is_ws(k) == U32.is_eq(k, 32) : Bool}:
  +hge = and_l(U32.is_ge(k, 32), U32.is_le(k, 126), h)
  +g = u32_gt2(k, 32, 13, hge, {==})
  %Equal.sym(Cmp, U32.cmp(k, 13), GT{}, g) : {Bool.or(U32.is_eq(k, 32), Bool.and(U32.is_ge(k, 9), Cmp.is_le(_))) == U32.is_eq(k, 32) : Bool}
  %and_f(U32.is_ge(k, 9)) : {Bool.or(U32.is_eq(k, 32), _) == U32.is_eq(k, 32) : Bool}
  or_ff(U32.is_eq(k, 32))

def ows_pr(+k: U32, +h: {L.in_range32(k, 32, 126) == True{} : Bool}) -> {Bool.or(U32.is_eq(k, 32), U32.is_eq(k, 9)) == U32.is_eq(k, 32) : Bool}:
  %Equal.sym(Bool, U32.is_eq(k, 9), False{}, ne_of(x => L.in_range32(x, 32, 126), U32.is_eq(k, 9), k, 9, {==}, {==}, h))
    : {Bool.or(U32.is_eq(k, 32), _) == U32.is_eq(k, 32) : Bool}
  or_ff(U32.is_eq(k, 32))

def ot(s: String, +h: {L.printable(s) == True{} : Bool}) -> {Tgt.trim_ws_l(s) == L.trim_ows_l(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +hk = and_l(L.in_range32(k, 32, 126), L.printable(r), h)
          %Equal.sym(Bool, Tgt.is_ws(k), U32.is_eq(k, 32), ws_pr(k, hk)) : {Tgt.trim_ws_l.go(SCon{Chr{k}, r}, _) == L.trim_ows_l(SCon{Chr{k}, r}) : String}
          %Equal.sym(Bool, Bool.or(U32.is_eq(k, 32), U32.is_eq(k, 9)), U32.is_eq(k, 32), ows_pr(k, hk)) : {Tgt.trim_ws_l.go(SCon{Chr{k}, r}, U32.is_eq(k, 32)) == L.pick(String, _, L.trim_ows_l(r), SCon{Chr{k}, r}) : String}
          %tw_b(U32.is_eq(k, 32), k, r) : {_ == L.pick(String, U32.is_eq(k, 32), L.trim_ows_l(r), SCon{Chr{k}, r}) : String}
          pick_tg(String, U32.is_eq(k, 32), Tgt.trim_ws_l(r), SCon{Chr{k}, r}, L.trim_ows_l(r), SCon{Chr{k}, r},
            ot(r, and_r(L.in_range32(k, 32, 126), L.printable(r), h)), {==})

def pr_t_step(b: Bool, +k: U32, +r: String, +h: {L.printable(SCon{Chr{k}, r}) == True{} : Bool},
  ih: {L.printable(r) == True{} : Bool} -> {L.printable(Tgt.trim_ws_l(r)) == True{} : Bool})
  -> {L.printable(Tgt.trim_ws_l.go(SCon{Chr{k}, r}, b)) == True{} : Bool}:
  match b:
    case True{}:
      ih(and_r(L.in_range32(k, 32, 126), L.printable(r), h))
    case False{}:
      h

def pr_t(s: String, +h: {L.printable(s) == True{} : Bool}) -> {L.printable(Tgt.trim_ws_l(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          pr_t_step(Tgt.is_ws(k), k, r, h, hh => pr_t(r, hh))

def pr_rev(s: String, +acc: String, +h1: {L.printable(s) == True{} : Bool}, +h2: {L.printable(acc) == True{} : Bool})
  -> {L.printable(String.reverse.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      h2
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          pr_rev(r, SCon{Chr{k}, acc}, and_r(L.in_range32(k, 32, 126), L.printable(r), h1),
            and_tt(L.in_range32(k, 32, 126), L.printable(acc), and_l(L.in_range32(k, 32, 126), L.printable(r), h1), h2))

# LAWS' trim_ows is trim_ws on printable text
def ows(+s: String, +h: {L.printable(s) == True{} : Bool}) -> {L.trim_ows(s) == Tgt.trim_ws(s) : String}:
  +ts = Tgt.trim_ws_l(s)
  +hts = pr_t(s, h)
  +hr = pr_rev(ts, SNil{}, hts, {==})
  %ot(s, h) : {String.reverse(L.trim_ows_l(String.reverse(_))) == Tgt.trim_ws(s) : String}
  %ot(String.reverse(ts), hr) : {String.reverse(_) == Tgt.trim_ws(s) : String}
  Equal.sym(String, Tgt.trim_ws_r(ts), String.reverse(Tgt.trim_ws_l(String.reverse(ts))), trr_rtr(ts))

# ---------------------------------------------------------------------
# Visible bytes (33..126): no white space, no newline
# ---------------------------------------------------------------------

def vis(+k: U32) -> Bool:
  L.in_range32(k, 33, 126)

def all_vis(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +rest}:
      Bool.and(vis(Tgt.code(c)), all_vis(rest))

# a sub-range a..b of 33..126 (a > 33, b < 126)
def sub_vis(+k: U32, +a: U32, +b: U32, +h: {L.in_range32(k, a, b) == True{} : Bool},
  +ha: {U32.cmp(a, 33) == GT{} : Cmp}, +hb: {U32.cmp(b, 126) == LT{} : Cmp}) -> {vis(k) == True{} : Bool}:
  +g = u32_gt2(k, a, 33, and_l(U32.is_ge(k, a), U32.is_le(k, b), h), ha)
  +l = u32_lt2(k, b, 126, and_r(U32.is_ge(k, a), U32.is_le(k, b), h), hb)
  %Equal.sym(Cmp, U32.cmp(k, 33), GT{}, g) : {Bool.and(Cmp.is_ge(_), U32.is_le(k, 126)) == True{} : Bool}
  %Equal.sym(Cmp, U32.cmp(k, 126), LT{}, l) : {Bool.and(True{}, Cmp.is_le(_)) == True{} : Bool}
  {==}

# a byte equal to a visible constant n is visible
def eq_vis(+k: U32, +n: U32, +e: {U32.is_eq(k, n) == True{} : Bool}, +hn: {vis(n) == True{} : Bool}) -> {vis(k) == True{} : Bool}:
  Equal.trans(Bool, vis(k), vis(n), True{}, Equal.cong(U32, Bool, x => vis(x), k, n, u32_eq(k, n, e)), hn)

def or_cases(a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, -G: Type, ka: {a == True{} : Bool} -> G, kb: {b == True{} : Bool} -> G) -> G:
  match a:
    case True{}:
      ka({==})
    case False{}:
      kb(h)

def alnum_vis(+k: U32, +h: {L.is_alnum(k) == True{} : Bool}) -> {vis(k) == True{} : Bool}:
  or_cases(L.in_range32(k, 48, 57), Bool.or(L.in_range32(k, 65, 90), L.in_range32(k, 97, 122)), h, {vis(k) == True{} : Bool},
    h1 => sub_vis(k, 48, 57, h1, {==}, {==}),
    h2 => or_cases(L.in_range32(k, 65, 90), L.in_range32(k, 97, 122), h2, {vis(k) == True{} : Bool},
      h3 => sub_vis(k, 65, 90, h3, {==}, {==}),
      h4 => sub_vis(k, 97, 122, h4, {==}, {==})))

def host_vis(+k: U32, +h: {L.is_host_char(k) == True{} : Bool}) -> {vis(k) == True{} : Bool}:
  or_cases(L.is_alnum(k), Bool.or(U32.is_eq(k, 46), Bool.or(U32.is_eq(k, 45), U32.is_eq(k, 95))), h, {vis(k) == True{} : Bool},
    h1 => alnum_vis(k, h1),
    h2 => or_cases(U32.is_eq(k, 46), Bool.or(U32.is_eq(k, 45), U32.is_eq(k, 95)), h2, {vis(k) == True{} : Bool},
      h3 => eq_vis(k, 46, h3, {==}),
      h4 => or_cases(U32.is_eq(k, 45), U32.is_eq(k, 95), h4, {vis(k) == True{} : Bool},
        h5 => eq_vis(k, 45, h5, {==}),
        h6 => eq_vis(k, 95, h6, {==}))))

# a byte of a literal of visible bytes is visible
def lit_vis(s: String, +k: U32, +hs: {all_vis(s) == True{} : Bool}, +h: {L.has_char(s, k) == True{} : Bool}) -> {vis(k) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({vis(k) == True{} : Bool}, no_ft(h))
    case SCon{c, +r}:
      match c:
        case Chr{+j}:
          or_cases(U32.is_eq(j, k), L.has_char(r, k), h, {vis(k) == True{} : Bool},
            h1 => Equal.trans(Bool, vis(k), vis(j), True{}, Equal.cong(U32, Bool, x => vis(x), k, j, Equal.sym(U32, j, k, u32_eq(j, k, h1))),
              and_l(vis(j), all_vis(r), hs)),
            h2 => lit_vis(r, k, and_r(vis(j), all_vis(r), hs), h2))

def token_vis(+k: U32, +h: {L.token_byte(k) == True{} : Bool}) -> {vis(k) == True{} : Bool}:
  or_cases(L.is_alnum(k), L.has_char("!#$%&'*+-.^_`|~", k), h, {vis(k) == True{} : Bool},
    h1 => alnum_vis(k, h1),
    h2 => lit_vis("!#$%&'*+-.^_`|~", k, {==}, h2))

def upper_vis(+k: U32, +h: {L.is_upper(k) == True{} : Bool}) -> {vis(k) == True{} : Bool}:
  sub_vis(k, 65, 90, h, {==}, {==})

def path_vis(+k: U32, +h: {Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35))) == True{} : Bool}) -> {vis(k) == True{} : Bool}:
  and_l(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35)), h)

def digit_vis(+k: U32, +h: {L.is_digit(Chr{k}) == True{} : Bool}) -> {vis(k) == True{} : Bool}:
  sub_vis(k, 48, 57, h, {==}, {==})

def vis_app(a: String, +b: String, +ha: {all_vis(a) == True{} : Bool}, +hb: {all_vis(b) == True{} : Bool}) -> {all_vis(String.append(a, b)) == True{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          and_tt(vis(k), all_vis(String.append(r, b)), and_l(vis(k), all_vis(r), ha), vis_app(r, b, and_r(vis(k), all_vis(r), ha), hb))

def vis_host(s: String, +h: {L.all_host(s) == True{} : Bool}) -> {all_vis(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          and_tt(vis(k), all_vis(r), host_vis(k, and_l(L.is_host_char(k), L.all_host(r), h)), vis_host(r, and_r(L.is_host_char(k), L.all_host(r), h)))

def vis_path(s: String, +h: {L.all_path(s) == True{} : Bool}) -> {all_vis(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          and_tt(vis(k), all_vis(r), path_vis(k, and_l(Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35))), L.all_path(r), h)), vis_path(r, and_r(Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35))), L.all_path(r), h)))

def vis_upper(s: String, +h: {L.all_upper(s) == True{} : Bool}) -> {all_vis(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          and_tt(vis(k), all_vis(r), upper_vis(k, and_l(L.is_upper(k), L.all_upper(r), h)), vis_upper(r, and_r(L.is_upper(k), L.all_upper(r), h)))

def vis_token(s: String, +h: {L.all_token(s) == True{} : Bool}) -> {all_vis(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          and_tt(vis(k), all_vis(r), token_vis(k, and_l(L.token_byte(k), L.all_token(r), h)), vis_token(r, and_r(L.token_byte(k), L.all_token(r), h)))

def vis_digits(s: String, +h: {L.all_digits.go(s) == True{} : Bool}) -> {all_vis(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          and_tt(vis(k), all_vis(r), digit_vis(k, and_l(L.is_digit(Chr{k}), L.all_digits.go(r), h)), vis_digits(r, and_r(L.is_digit(Chr{k}), L.all_digits.go(r), h)))

def vis_ws(+k: U32, +h: {vis(k) == True{} : Bool}) -> {Tgt.is_ws(k) == False{} : Bool}:
  +g = u32_gt2(k, 33, 13, and_l(U32.is_ge(k, 33), U32.is_le(k, 126), h), {==})
  %Equal.sym(Bool, U32.is_eq(k, 32), False{}, ne_of(x => vis(x), U32.is_eq(k, 32), k, 32, {==}, {==}, h))
    : {Bool.or(_, Bool.and(U32.is_ge(k, 9), U32.is_le(k, 13))) == False{} : Bool}
  %Equal.sym(Cmp, U32.cmp(k, 13), GT{}, g) : {Bool.and(U32.is_ge(k, 9), Cmp.is_le(_)) == False{} : Bool}
  Equal.sym(Bool, False{}, Bool.and(U32.is_ge(k, 9), False{}), and_f(U32.is_ge(k, 9)))

def vis_nws(s: String, +h: {all_vis(s) == True{} : Bool}) -> {all_nws(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_ws(k), False{}, vis_ws(k, and_l(vis(k), all_vis(r), h)))
            : {Bool.and(Bool.not(_), all_nws(r)) == True{} : Bool}
          vis_nws(r, and_r(vis(k), all_vis(r), h))

def vis_nallws(s: String, +h: {all_vis(s) == True{} : Bool}, +hne: {String.is_empty(s) == False{} : Bool}) -> {allws(s) == False{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(hne))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_ws(k), False{}, vis_ws(k, and_l(vis(k), all_vis(r), h)))
            : {Bool.and(_, allws(r)) == False{} : Bool}
          {==}

# no byte n in a visible text when n is not visible
def vis_no(s: String, +n: U32, +hn: {vis(n) == False{} : Bool}, +h: {all_vis(s) == True{} : Bool}) -> {Tgt.has_char(s, n) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, n), False{}, ne_of(x => vis(x), U32.is_eq(k, n), k, n, {==}, hn, and_l(vis(k), all_vis(r), h)))
            : {Tgt.has_char.go(SCon{Chr{k}, r}, n, _) == False{} : Bool}
          vis_no(r, n, hn, and_r(vis(k), all_vis(r), h))

def vis_noctl(s: String, +h: {all_vis(s) == True{} : Bool}) -> {Tgt.has_ctl(s) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +hk = and_l(vis(k), all_vis(r), h)
          %Equal.sym(Bool, U32.is_lt(k, 32), False{}, u32_gt(k, 33, 32, and_l(U32.is_ge(k, 33), U32.is_le(k, 126), hk), {==}))
            : {Bool.or(Bool.or(_, U32.is_eq(k, 127)), Tgt.has_ctl(r)) == False{} : Bool}
          %Equal.sym(Bool, U32.is_eq(k, 127), False{}, ne_of(x => vis(x), U32.is_eq(k, 127), k, 127, {==}, {==}, hk))
            : {Bool.or(Bool.or(False{}, _), Tgt.has_ctl(r)) == False{} : Bool}
          vis_noctl(r, and_r(vis(k), all_vis(r), h))

def bef_gen(a: String, +y: String, +n: U32, +h: {Tgt.has_char(a, n) == False{} : Bool}) -> {String.append(a, Tgt.before(y, n)) == Tgt.before(String.append(a, y), n) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, n), False{}, hcf_l(k, r, n, h))
            : {SCon{Chr{k}, String.append(r, Tgt.before(y, n))} == Tgt.before.go(SCon{Chr{k}, String.append(r, y)}, n, _) : String}
          %bef_gen(r, y, n, hcf_r(k, r, n, h))
            : {SCon{Chr{k}, String.append(r, Tgt.before(y, n))} == SCon{Chr{k}, _} : String}
          {==}

def aft_gen(a: String, +y: String, +n: U32, +h: {Tgt.has_char(a, n) == False{} : Bool}) -> {Tgt.after(y, n) == Tgt.after(String.append(a, y), n) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, n), False{}, hcf_l(k, r, n, h))
            : {Tgt.after(y, n) == Tgt.after.go(SCon{Chr{k}, String.append(r, y)}, n, _) : String}
          aft_gen(r, y, n, hcf_r(k, r, n, h))

def or_true(x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def bcmp_refl(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wcmp_refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match a:
        case WCon{+ab, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, wcmp_refl(p, at)) : {Word.cmp.fin(ab, ab, _) == EQ{} : Cmp}
          bcmp_refl(ab)

def u32_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+x}:
      %Equal.sym(Cmp, Word.cmp(32n, x, x), EQ{}, wcmp_refl(32n, x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def hc_mid(a: String, +n: U32, +z: String) -> {Tgt.has_char(String.append(a, SCon{Chr{n}, z}), n) == True{} : Bool}:
  match a:
    case SNil{}:
      %Equal.sym(Bool, U32.is_eq(n, n), True{}, u32_refl(n)) : {Tgt.has_char.go(SCon{Chr{n}, z}, n, _) == True{} : Bool}
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %hc_c(k, String.append(r, SCon{Chr{n}, z}), n) : {_ == True{} : Bool}
          %Equal.sym(Bool, Tgt.has_char(String.append(r, SCon{Chr{n}, z}), n), True{}, hc_mid(r, n, z))
            : {Bool.or(U32.is_eq(k, n), _) == True{} : Bool}
          or_true(U32.is_eq(k, n))

# ---------------------------------------------------------------------
# A target's URL: visible, and ParseRequestURI accepts it
# ---------------------------------------------------------------------

def host_no(s: String, +n: U32, +hn: {Tgt.is_host_char(n) == False{} : Bool}, +h: {Tgt.all_host(s) == True{} : Bool}) -> {Tgt.has_char(s, n) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, n), False{}, host_ne(U32.is_eq(k, n), k, n, {==}, hn, and_l(Tgt.is_host_char(k), Tgt.all_host(r), h)))
            : {Tgt.has_char.go(SCon{Chr{k}, r}, n, _) == False{} : Bool}
          host_no(r, n, hn, and_r(Tgt.is_host_char(k), Tgt.all_host(r), h))

def dig_no(s: String, +n: U32, +hn: {L.is_digit(Chr{n}) == False{} : Bool}, +h: {L.all_digits.go(s) == True{} : Bool}) -> {Tgt.has_char(s, n) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, n), False{}, dig_ne(k, n, hn, and_l(L.is_digit(Chr{k}), L.all_digits.go(r), h)))
            : {Tgt.has_char.go(SCon{Chr{k}, r}, n, _) == False{} : Bool}
          dig_no(r, n, hn, and_r(L.is_digit(Chr{k}), L.all_digits.go(r), h))

def ruri_main(+host: String, +pt: String, +p: String,
  +hv: {all_vis(String.append(host, String.append(pt, SCon{Chr{47}, p}))) == True{} : Bool},
  +hall: {Tgt.all_host(host) == True{} : Bool},
  +hp63: {Tgt.has_char(pt, 63) == False{} : Bool}, +hp47: {Tgt.has_char(pt, 47) == False{} : Bool},
  +hpct: {L.pct_ok.go(String.length(p), p) == True{} : Bool})
  -> {Tgt.req_uri_err("http://" ++ String.append(host, String.append(pt, SCon{Chr{47}, p}))) == None{} : Maybe<&2, String>}:
  +x = String.append(host, String.append(pt, SCon{Chr{47}, p}))
  +u = "http://" ++ x
  +q = Tgt.before(p, 63)
  +b = Tgt.before(x, 63)
  +b2 = String.append(host, String.append(pt, SCon{Chr{47}, q}))
  +eb = Equal.trans(String, b2, String.append(host, Tgt.before(String.append(pt, SCon{Chr{47}, p}), 63)), b,
    Equal.cong(String, String, y => String.append(host, y), String.append(pt, SCon{Chr{47}, q}), Tgt.before(String.append(pt, SCon{Chr{47}, p}), 63),
      bef_gen(pt, SCon{Chr{47}, p}, 63, hp63)),
    bef_gen(host, String.append(pt, SCon{Chr{47}, p}), 63, host_no(host, 63, {==}, hall)))
  +e47 = Equal.trans(String, String.append(host, String.append(pt, SNil{})), String.append(host, Tgt.before(String.append(pt, SCon{Chr{47}, q}), 47)), Tgt.before(b2, 47),
    Equal.cong(String, String, y => String.append(host, y), String.append(pt, SNil{}), Tgt.before(String.append(pt, SCon{Chr{47}, q}), 47),
      bef_gen(pt, SCon{Chr{47}, q}, 47, hp47)),
    bef_gen(host, String.append(pt, SCon{Chr{47}, q}), 47, host_no(host, 47, {==}, hall)))
  %Equal.sym(Bool, Tgt.has_ctl(u), False{}, vis_noctl(u, hv)) : {Tgt.req_uri.ctl(_, u) == None{} : Maybe<&2, String>}
  %sw_nil(b) : {Tgt.req_uri.auth(Bool.and(True{}, _), u, SCon{Chr{47}, SCon{Chr{47}, b}}) == None{} : Maybe<&2, String>}
  %drop0(b) : {Tgt.req_uri.path(u, String.drop(_, String.length(Tgt.before(_, 47)))) == None{} : Maybe<&2, String>}
  %eb : {Tgt.req_uri.path(u, String.drop(_, String.length(Tgt.before(_, 47)))) == None{} : Maybe<&2, String>}
  %e47 : {Tgt.req_uri.path(u, String.drop(b2, String.length(_))) == None{} : Maybe<&2, String>}
  %app_nil(pt) : {Tgt.req_uri.path(u, String.drop(b2, String.length(String.append(host, _)))) == None{} : Maybe<&2, String>}
  %drop_app2(host, pt, SCon{Chr{47}, q}) : {Tgt.req_uri.path(u, _) == None{} : Maybe<&2, String>}
  %pct(p, hpct) : {Tgt.req_uri.esc(_, u) == None{} : Maybe<&2, String>}
  {==}

def uf_port(+host: String, port: Maybe<&2, Nat>, +p: String,
  +hall: {Tgt.all_host(host) == True{} : Bool}, +hl: {L.all_host(host) == True{} : Bool},
  +hp: {L.all_path(p) == True{} : Bool}, +hq: {L.pct_ok.go(String.length(p), p) == True{} : Bool})
  -> {all_vis(String.append(host, String.append(L.port_text(port), SCon{Chr{47}, p}))) == True{} : Bool}
     & {Tgt.req_uri_err("http://" ++ String.append(host, String.append(L.port_text(port), SCon{Chr{47}, p}))) == None{} : Maybe<&2, String>}:
  match port:
    case None{}:
      +hv = vis_app(host, SCon{Chr{47}, p}, vis_host(host, hl), vis_path(p, hp))
      (hv, ruri_main(host, SNil{}, p, hv, hall, {==}, {==}, hq))
    case Some{+n}:
      +d = Dec.show(n)
      +hdg = digits_go(d, and_l(L.all_digits(d), Bool.or(String.eq(d, "0"), Bool.not(String.starts_with(d, "0"))), L.dec_show_canonical(n)))
      +hv = vis_app(host, String.append(":" ++ d, SCon{Chr{47}, p}), vis_host(host, hl),
        vis_app(":" ++ d, SCon{Chr{47}, p}, vis_digits(d, hdg), vis_path(p, hp)))
      (hv, ruri_main(host, ":" ++ d, p, hv, hall, dig_no(d, 63, {==}, hdg), dig_no(d, 47, {==}, hdg), hq))

def uf_path(+host: String, +port: Maybe<&2, Nat>, path: String,
  +hall: {Tgt.all_host(host) == True{} : Bool}, +hl: {L.all_host(host) == True{} : Bool},
  +hsw: {String.starts_with(path, "/") == True{} : Bool}, +hpath: {L.all_path(path) == True{} : Bool}, +hpct: {L.pct_ok(path) == True{} : Bool})
  -> {all_vis(String.append(host, String.append(L.port_text(port), path))) == True{} : Bool}
     & {Tgt.req_uri_err("http://" ++ String.append(host, String.append(L.port_text(port), path))) == None{} : Maybe<&2, String>}:
  match path:
    case SNil{}:
      Empty.absurd({all_vis(String.append(host, String.append(L.port_text(port), SNil{}))) == True{} : Bool}
        & {Tgt.req_uri_err("http://" ++ String.append(host, String.append(L.port_text(port), SNil{}))) == None{} : Maybe<&2, String>}, no_ft(hsw))
    case SCon{c, +p}:
      match c:
        case Chr{+k}:
          +ek = u32_eq(k, 47, sw_true(U32.is_eq(k, 47), p, hsw))
          +a1 = Bool.and(L.in_range32(k, 33, 126), Bool.not(U32.is_eq(k, 35)))
          +hp = and_r(a1, L.all_path(p), hpath)
          +a2 = Bool.or(Bool.not(U32.is_eq(k, 37)), Bool.and(L.is_hex(L.byte_at(p, 0n)), L.is_hex(L.byte_at(p, 1n))))
          +hq = Equal.trans(Bool, L.pct_ok.go(String.length(p), p), L.pct_ok.go(String.length(p), String.drop(p, 0n)), True{},
            Equal.cong(String, Bool, x => L.pct_ok.go(String.length(p), x), p, String.drop(p, 0n), drop0(p)),
            and_r(a2, L.pct_ok.go(String.length(p), String.drop(p, 0n)), hpct))
          %Equal.sym(U32, k, 47, ek)
            : {all_vis(String.append(host, String.append(L.port_text(port), SCon{Chr{_}, p}))) == True{} : Bool}
              & {Tgt.req_uri_err("http://" ++ String.append(host, String.append(L.port_text(port), SCon{Chr{_}, p}))) == None{} : Maybe<&2, String>}
          uf_port(host, port, p, hall, hl, hp, hq)

def url_facts(+scheme: String, +host: String, +port: Maybe<&2, Nat>, +path: String, +h: {L.url_ok(Tgt.Url{scheme, host, port, path}) == True{} : Bool})
  -> {all_vis(String.append(host, String.append(L.port_text(port), path))) == True{} : Bool}
     & {Tgt.req_uri_err("http://" ++ String.append(host, String.append(L.port_text(port), path))) == None{} : Maybe<&2, String>}:
  +c6 = Bool.and(L.all_path(path), L.pct_ok(path))
  +c5 = Bool.and(String.starts_with(path, "/"), c6)
  +c4 = Bool.and(L.port_ok(port), c5)
  +c3 = Bool.and(Bool.not(String.is_empty(host)), L.all_host(host))
  +c2 = Bool.and(c3, c4)
  +h2 = and_r(String.eq(scheme, "http"), c2, h)
  +h3 = and_l(c3, c4, h2)
  +h4 = and_r(c3, c4, h2)
  +h5 = and_r(L.port_ok(port), c5, h4)
  +h6 = and_r(String.starts_with(path, "/"), c6, h5)
  +hl = and_r(Bool.not(String.is_empty(host)), L.all_host(host), h3)
  +hall = Equal.trans(Bool, Tgt.all_host(host), L.all_host(host), True{}, all_host_t(host), hl)
  uf_path(host, port, path, hall, hl, and_l(String.starts_with(path, "/"), c6, h5),
    and_l(L.all_path(path), L.pct_ok(path), h6), and_r(L.all_path(path), L.pct_ok(path), h6))

def us_facts(+u: String, r: Result<&2, &2, String, Tgt.Url>, +h: {L.url_str_of(u, r) == True{} : Bool})
  -> {all_vis(u) == True{} : Bool} & {Tgt.req_uri_err(u) == None{} : Maybe<&2, String>}:
  match r:
    case Fail{e}:
      Empty.absurd({all_vis(u) == True{} : Bool} & {Tgt.req_uri_err(u) == None{} : Maybe<&2, String>}, no_ft(h))
    case Done{v}:
      match v:
        case Tgt.Url{+scheme, +host, +port, +path}:
          +e = str_eq(L.url_text(Tgt.Url{scheme, host, port, path}), u, and_r(L.url_ok(Tgt.Url{scheme, host, port, path}), String.eq(L.url_text(Tgt.Url{scheme, host, port, path}), u), h))
          %e : {all_vis(_) == True{} : Bool} & {Tgt.req_uri_err(_) == None{} : Maybe<&2, String>}
          url_facts(scheme, host, port, path, and_l(L.url_ok(Tgt.Url{scheme, host, port, path}), String.eq(L.url_text(Tgt.Url{scheme, host, port, path}), u), h))

def us_ne(+u: String, r: Result<&2, &2, String, Tgt.Url>, +h: {L.url_str_of(u, r) == True{} : Bool}) -> {String.is_empty(u) == False{} : Bool}:
  match r:
    case Fail{e}:
      Empty.absurd({String.is_empty(u) == False{} : Bool}, no_ft(h))
    case Done{v}:
      match v:
        case Tgt.Url{+scheme, +host, +port, +path}:
          +e = str_eq(L.url_text(Tgt.Url{scheme, host, port, path}), u, and_r(L.url_ok(Tgt.Url{scheme, host, port, path}), String.eq(L.url_text(Tgt.Url{scheme, host, port, path}), u), h))
          %e : {String.is_empty(_) == False{} : Bool}
          {==}

def pair_l(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def pair_r(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case (a, b):
      b

def hc_app(a: String, +b: String, +n: U32, +ha: {Tgt.has_char(a, n) == False{} : Bool}, +hb: {Tgt.has_char(b, n) == False{} : Bool})
  -> {Tgt.has_char(String.append(a, b), n) == False{} : Bool}:
  match a:
    case SNil{}:
      hb
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, n), False{}, hcf_l(k, r, n, ha))
            : {Tgt.has_char.go(SCon{Chr{k}, String.append(r, b)}, n, _) == False{} : Bool}
          hc_app(r, b, n, hcf_r(k, r, n, ha), hb)

# a line starting with a visible byte is trimmed on the left
def t_vis(a: String, +y: String, +h: {all_vis(a) == True{} : Bool}, +hne: {String.is_empty(a) == False{} : Bool})
  -> {String.append(a, y) == Tgt.trim_ws_l(String.append(a, y)) : String}:
  match a:
    case SNil{}:
      Empty.absurd({y == Tgt.trim_ws_l(y) : String}, no_tf(hne))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_ws(k), False{}, vis_ws(k, and_l(vis(k), all_vis(r), h)))
            : {SCon{Chr{k}, String.append(r, y)} == Tgt.trim_ws_l.go(SCon{Chr{k}, String.append(r, y)}, _) : String}
          {==}

def ur_len(m: String, +y: String, +h: {L.all_upper(m) == True{} : Bool}, +hy: {Tgt.upper_run(y) == 0n : Nat})
  -> {Tgt.upper_run(String.append(m, y)) == String.length(m) : Nat}:
  match m:
    case SNil{}:
      hy
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_upper(k), True{}, and_l(L.is_upper(k), L.all_upper(r), h))
            : {Tgt.upper_run.go(SCon{Chr{k}, String.append(r, y)}, _) == 1n+String.length(r) : Nat}
          %Equal.sym(Nat, Tgt.upper_run(String.append(r, y)), String.length(r), ur_len(r, y, and_r(L.is_upper(k), L.all_upper(r), h), hy))
            : {1n+_ == 1n+String.length(r) : Nat}
          {==}

def len_lt(m: String, +c: Char, +u: String) -> {Nat.is_lt(String.length(m), String.length(String.append(m, SCon{c, u}))) == True{} : Bool}:
  match m:
    case SNil{}:
      {==}
    case SCon{+d, +r}:
      len_lt(r, c, u)

def ba_len(m: String, +c: Char, +u: String) -> {Tgt.byte_at(String.append(m, SCon{c, u}), String.length(m)) == Tgt.code(c) : U32}:
  match m:
    case SNil{}:
      {==}
    case SCon{+d, +r}:
      ba_len(r, c, u)

def sm_req(m: String, +u: String, +h: {L.all_upper(m) == True{} : Bool}, +hne: {String.is_empty(m) == False{} : Bool})
  -> {Tgt.starts_method(String.append(m, SCon{Chr{32}, u})) == True{} : Bool}:
  match m:
    case SNil{}:
      Empty.absurd({Tgt.starts_method(SCon{Chr{32}, u}) == True{} : Bool}, no_tf(hne))
    case SCon{+c, +r}:
      +l = String.append(SCon{c, r}, SCon{Chr{32}, u})
      %Equal.sym(Nat, Tgt.upper_run(l), String.length(SCon{c, r}), ur_len(SCon{c, r}, SCon{Chr{32}, u}, h, {==}))
        : {Tgt.starts_method.of(_, l) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_lt(String.length(SCon{c, r}), String.length(l)), True{}, len_lt(SCon{c, r}, Chr{32}, u))
        : {Bool.and(Nat.is_gt(String.length(SCon{c, r}), 0n), Bool.and(_, Tgt.is_re_space(Tgt.byte_at(l, String.length(SCon{c, r}))))) == True{} : Bool}
      %Equal.sym(U32, Tgt.byte_at(l, String.length(SCon{c, r})), 32, ba_len(SCon{c, r}, Chr{32}, u))
        : {Bool.and(Nat.is_gt(String.length(SCon{c, r}), 0n), Bool.and(True{}, Tgt.is_re_space(_))) == True{} : Bool}
      {==}

# a line, its newline and more: the state moves by the trimmed line
def feed_nl2(+l: String, +w: String, +st: Tgt.St, +h: {Tgt.has_char(l, 10) == False{} : Bool})
  -> {feed(String.append(l, SCon{Chr{10}, w}), Tgt.Ln{SNil{}, st}) == feed(w, Tgt.Ln{SNil{}, Tgt.step(st, Tgt.trim_ws(l))}) : Tgt.Ln}:
  %Equal.sym(Tgt.Ln, feed(String.append(l, SCon{Chr{10}, w}), Tgt.Ln{SNil{}, st}), feed(SCon{Chr{10}, w}, feed(l, Tgt.Ln{SNil{}, st})),
      feed_app(l, SCon{Chr{10}, w}, Tgt.Ln{SNil{}, st}))
    : {_ == feed(w, Tgt.Ln{SNil{}, Tgt.step(st, Tgt.trim_ws(l))}) : Tgt.Ln}
  %Equal.sym(Tgt.Ln, feed(l, Tgt.Ln{SNil{}, st}), Tgt.Ln{String.reverse(l), st}, feed_line(l, SNil{}, st, h))
    : {feed(SCon{Chr{10}, w}, _) == feed(w, Tgt.Ln{SNil{}, Tgt.step(st, Tgt.trim_ws(l))}) : Tgt.Ln}
  %Equal.sym(String, Tgt.line_of(String.reverse(l)), Tgt.trim_ws(l), line_rev(l))
    : {feed(w, Tgt.Ln{SNil{}, Tgt.step(st, _)}) == feed(w, Tgt.Ln{SNil{}, Tgt.step(st, Tgt.trim_ws(l))}) : Tgt.Ln}
  {==}

# the request line "M U"
def req_step(m: String, +u: String, +acc: List<&2, Tgt.Target>,
  +hvm: {all_vis(m) == True{} : Bool}, +hup: {L.all_upper(m) == True{} : Bool}, +hne: {String.is_empty(m) == False{} : Bool},
  +hvu: {all_vis(u) == True{} : Bool}, +hru: {Tgt.req_uri_err(u) == None{} : Maybe<&2, String>})
  -> {Tgt.step(Tgt.SSeek{acc}, String.append(m, SCon{Chr{32}, u})) == Tgt.SPeek{Tgt.Target{m, u, [], None{}}, acc} : Tgt.St}:
  match m:
    case SNil{}:
      Empty.absurd({Tgt.step(Tgt.SSeek{acc}, SCon{Chr{32}, u}) == Tgt.SPeek{Tgt.Target{SNil{}, u, [], None{}}, acc} : Tgt.St}, no_tf(hne))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +l = String.append(SCon{Chr{k}, r}, SCon{Chr{32}, u})
          %Equal.sym(Bool, U32.is_eq(k, 35), False{}, ne_of(x => L.is_upper(x), U32.is_eq(k, 35), k, 35, {==}, {==}, and_l(L.is_upper(k), L.all_upper(r), hup)))
            : {Tgt.seek.of(Bool.or(False{}, _), l, acc) == Tgt.SPeek{Tgt.Target{SCon{Chr{k}, r}, u, [], None{}}, acc} : Tgt.St}
          %Equal.sym(Bool, Tgt.has_char(l, 32), True{}, hc_mid(SCon{Chr{k}, r}, 32, u))
            : {Tgt.req_line(_, l, acc) == Tgt.SPeek{Tgt.Target{SCon{Chr{k}, r}, u, [], None{}}, acc} : Tgt.St}
          %Equal.sym(Bool, Tgt.starts_method(l), True{}, sm_req(SCon{Chr{k}, r}, u, hup, hne))
            : {Tgt.req_line.meth(_, l, acc) == Tgt.SPeek{Tgt.Target{SCon{Chr{k}, r}, u, [], None{}}, acc} : Tgt.St}
          %aft_gen(SCon{Chr{k}, r}, SCon{Chr{32}, u}, 32, vis_no(SCon{Chr{k}, r}, 32, {==}, hvm))
            : {Tgt.req_line.url(Tgt.req_uri_err(_), Tgt.before(l, 32), _, acc) == Tgt.SPeek{Tgt.Target{SCon{Chr{k}, r}, u, [], None{}}, acc} : Tgt.St}
          %bef_gen(SCon{Chr{k}, r}, SCon{Chr{32}, u}, 32, vis_no(SCon{Chr{k}, r}, 32, {==}, hvm))
            : {Tgt.req_line.url(Tgt.req_uri_err(u), _, u, acc) == Tgt.SPeek{Tgt.Target{SCon{Chr{k}, r}, u, [], None{}}, acc} : Tgt.St}
          %app_nil(SCon{Chr{k}, r}) : {Tgt.req_line.url(Tgt.req_uri_err(u), _, u, acc) == Tgt.SPeek{Tgt.Target{SCon{Chr{k}, r}, u, [], None{}}, acc} : Tgt.St}
          %Equal.sym(Maybe<&2, String>, Tgt.req_uri_err(u), None{}, hru) : {Tgt.req_line.url(_, SCon{Chr{k}, r}, u, acc) == Tgt.SPeek{Tgt.Target{SCon{Chr{k}, r}, u, [], None{}}, acc} : Tgt.St}
          {==}

# the request line is trimmed
def req_trim(+m: String, +u: String, +hvm: {all_vis(m) == True{} : Bool}, +hne: {String.is_empty(m) == False{} : Bool},
  +hvu: {all_vis(u) == True{} : Bool}, +hnu: {String.is_empty(u) == False{} : Bool})
  -> {Tgt.trim_ws(String.append(m, SCon{Chr{32}, u})) == String.append(m, SCon{Chr{32}, u}) : String}:
  +l = String.append(m, SCon{Chr{32}, u})
  +nu = vis_nallws(u, hvu, hnu)
  %t_vis(m, SCon{Chr{32}, u}, hvm, hne) : {Tgt.trim_ws_r(_) == l : String}
  %trr_app(m, SCon{Chr{32}, u}, nu) : {_ == l : String}
  %trr_app(SCon{Chr{32}, SNil{}}, u, nu) : {String.append(m, _) == l : String}
  %trr_id(u, vis_nws(u, hvu)) : {String.append(m, SCon{Chr{32}, _}) == l : String}
  {==}

# ---------------------------------------------------------------------
# Header lines "k: v"
# ---------------------------------------------------------------------

def mk(p: Bool, +t: Tgt.Target, +acc: List<&2, Tgt.Target>) -> Tgt.St:
  match p:
    case True{}:
      Tgt.SPeek{t, acc}
    case False{}:
      Tgt.SHdr{t, acc}

def step_mk(p: Bool, +t: Tgt.Target, +acc: List<&2, Tgt.Target>, +l: String,
  +hne: {String.is_empty(l) == False{} : Bool}, +hsm: {Tgt.starts_method(l) == False{} : Bool})
  -> {Tgt.step(mk(p, t, acc), l) == Tgt.hdr(l, t, acc) : Tgt.St}:
  match p:
    case True{}:
      %Equal.sym(Bool, String.is_empty(l), False{}, hne) : {Tgt.peek.of(Bool.or(_, Tgt.starts_method(l)), l, t, acc) == Tgt.hdr(l, t, acc) : Tgt.St}
      %Equal.sym(Bool, Tgt.starts_method(l), False{}, hsm) : {Tgt.peek.of(_, l, t, acc) == Tgt.hdr(l, t, acc) : Tgt.St}
      {==}
    case False{}:
      {==}

def step_blank(p: Bool, +t: Tgt.Target, +acc: List<&2, Tgt.Target>) -> {Tgt.step(mk(p, t, acc), SNil{}) == Tgt.SSeek{Con{t, acc}} : Tgt.St}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def nm(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          Tgt.pick(Bool, Tgt.is_upper(k), nm(r), Bool.not(Tgt.is_re_space(k)))

def nm_step(w: Bool, +k: U32, +r: String, +ew: {Tgt.is_upper(k) == w : Bool}, +h: {Tgt.pick(Bool, w, nm(r), Bool.not(Tgt.is_re_space(k))) == True{} : Bool},
  ih: {nm(r) == True{} : Bool} -> {Bool.and(Nat.is_lt(Tgt.upper_run(r), String.length(r)), Tgt.is_re_space(Tgt.byte_at(r, Tgt.upper_run(r)))) == False{} : Bool})
  -> {Bool.and(Nat.is_lt(Tgt.upper_run(SCon{Chr{k}, r}), String.length(SCon{Chr{k}, r})), Tgt.is_re_space(Tgt.byte_at(SCon{Chr{k}, r}, Tgt.upper_run(SCon{Chr{k}, r})))) == False{} : Bool}:
  match w:
    case True{}:
      %Equal.sym(Bool, Tgt.is_upper(k), True{}, ew)
        : {Bool.and(Nat.is_lt(Tgt.upper_run.go(SCon{Chr{k}, r}, _), 1n+String.length(r)), Tgt.is_re_space(Tgt.byte_at(SCon{Chr{k}, r}, Tgt.upper_run.go(SCon{Chr{k}, r}, _)))) == False{} : Bool}
      ih(h)
    case False{}:
      %Equal.sym(Bool, Tgt.is_upper(k), False{}, ew)
        : {Bool.and(Nat.is_lt(Tgt.upper_run.go(SCon{Chr{k}, r}, _), 1n+String.length(r)), Tgt.is_re_space(Tgt.byte_at(SCon{Chr{k}, r}, Tgt.upper_run.go(SCon{Chr{k}, r}, _)))) == False{} : Bool}
      not_t(Tgt.is_re_space(k), h)

def nm_run(s: String, +h: {nm(s) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(Tgt.upper_run(s), String.length(s)), Tgt.is_re_space(Tgt.byte_at(s, Tgt.upper_run(s)))) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          nm_step(Tgt.is_upper(k), k, r, {==}, h, hh => nm_run(r, hh))

def nm_sm(+s: String, +h: {nm(s) == True{} : Bool}) -> {Tgt.starts_method(s) == False{} : Bool}:
  %Equal.sym(Bool, Bool.and(Nat.is_lt(Tgt.upper_run(s), String.length(s)), Tgt.is_re_space(Tgt.byte_at(s, Tgt.upper_run(s)))), False{}, nm_run(s, h))
    : {Bool.and(Nat.is_gt(Tgt.upper_run(s), 0n), _) == False{} : Bool}
  Equal.sym(Bool, False{}, Bool.and(Nat.is_gt(Tgt.upper_run(s), 0n), False{}), and_f(Nat.is_gt(Tgt.upper_run(s), 0n)))

def vis_rs(+k: U32, +h: {vis(k) == True{} : Bool}) -> {Tgt.is_re_space(k) == False{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(k, 32), False{}, ne_of(x => vis(x), U32.is_eq(k, 32), k, 32, {==}, {==}, h))
    : {Bool.or(_, Bool.or(U32.is_eq(k, 9), Bool.or(U32.is_eq(k, 10), Bool.or(U32.is_eq(k, 12), U32.is_eq(k, 13))))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_eq(k, 9), False{}, ne_of(x => vis(x), U32.is_eq(k, 9), k, 9, {==}, {==}, h))
    : {Bool.or(False{}, Bool.or(_, Bool.or(U32.is_eq(k, 10), Bool.or(U32.is_eq(k, 12), U32.is_eq(k, 13))))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_eq(k, 10), False{}, ne_of(x => vis(x), U32.is_eq(k, 10), k, 10, {==}, {==}, h))
    : {Bool.or(False{}, Bool.or(False{}, Bool.or(_, Bool.or(U32.is_eq(k, 12), U32.is_eq(k, 13))))) == False{} : Bool}
  %Equal.sym(Bool, U32.is_eq(k, 12), False{}, ne_of(x => vis(x), U32.is_eq(k, 12), k, 12, {==}, {==}, h))
    : {Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, Bool.or(_, U32.is_eq(k, 13))))) == False{} : Bool}
  ne_of(x => vis(x), U32.is_eq(k, 13), k, 13, {==}, {==}, h)

def nm_vis_step(w: Bool, +k: U32, +r: String, +y: String, +ew: {Tgt.is_upper(k) == w : Bool}, +hk: {vis(k) == True{} : Bool},
  ih: {nm(String.append(r, y)) == True{} : Bool})
  -> {Tgt.pick(Bool, w, nm(String.append(r, y)), Bool.not(Tgt.is_re_space(k))) == True{} : Bool}:
  match w:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Tgt.is_re_space(k), False{}, vis_rs(k, hk)) : {Bool.not(_) == True{} : Bool}
      {==}

def nm_vis(a: String, +y: String, +h: {all_vis(a) == True{} : Bool}, +hy: {nm(y) == True{} : Bool}) -> {nm(String.append(a, y)) == True{} : Bool}:
  match a:
    case SNil{}:
      hy
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          nm_vis_step(Tgt.is_upper(k), k, r, y, {==}, and_l(vis(k), all_vis(r), h), nm_vis(r, y, and_r(vis(k), all_vis(r), h), hy))

def tok_no(s: String, +n: U32, +hn: {L.token_byte(n) == False{} : Bool}, +h: {L.all_token(s) == True{} : Bool}) -> {Tgt.has_char(s, n) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, n), False{}, ne_of(x => L.token_byte(x), U32.is_eq(k, n), k, n, {==}, hn, and_l(L.token_byte(k), L.all_token(r), h)))
            : {Tgt.has_char.go(SCon{Chr{k}, r}, n, _) == False{} : Bool}
          tok_no(r, n, hn, and_r(L.token_byte(k), L.all_token(r), h))

def pr_no(s: String, +n: U32, +hn: {L.in_range32(n, 32, 126) == False{} : Bool}, +h: {L.printable(s) == True{} : Bool}) -> {Tgt.has_char(s, n) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, n), False{}, ne_of(x => L.in_range32(x, 32, 126), U32.is_eq(k, n), k, n, {==}, hn, and_l(L.in_range32(k, 32, 126), L.printable(r), h)))
            : {Tgt.has_char.go(SCon{Chr{k}, r}, n, _) == False{} : Bool}
          pr_no(r, n, hn, and_r(L.in_range32(k, 32, 126), L.printable(r), h))

def t_vis1(s: String, +h: {all_vis(s) == True{} : Bool}) -> {s == Tgt.trim_ws_l(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_ws(k), False{}, vis_ws(k, and_l(vis(k), all_vis(r), h)))
            : {SCon{Chr{k}, r} == Tgt.trim_ws_l.go(SCon{Chr{k}, r}, _) : String}
          {==}

def tw_vis(+s: String, +h: {all_vis(s) == True{} : Bool}) -> {Tgt.trim_ws(s) == s : String}:
  %t_vis1(s, h) : {Tgt.trim_ws_r(_) == s : String}
  Equal.sym(String, s, Tgt.trim_ws_r(s), trr_id(s, vis_nws(s, h)))

def ne_app2(a: String, -y: String, h: {String.is_empty(a) == False{} : Bool}) -> {String.is_empty(String.append(a, y)) == False{} : Bool}:
  match a:
    case SNil{}:
      Empty.absurd({String.is_empty(y) == False{} : Bool}, no_tf(h))
    case SCon{c, r}:
      {==}

def swf(b: Bool, +r: String, h: {String.starts_with.if(r, SNil{}, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, True{}, String.starts_with(r, SNil{}), False{}, sw_nil(r), h)

# a trimmed value that is not empty holds something else than white space
def nav_b(b: Bool, +v: String, +eb: {allws(v) == b : Bool}, +htv: {Tgt.trim_ws(v) == v : String}, +hne: {String.is_empty(v) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +ev = Equal.trans(String, v, Tgt.trim_ws(v), SNil{}, Equal.sym(String, Tgt.trim_ws(v), v, htv),
        Equal.cong(String, String, x => Tgt.trim_ws_r(x), Tgt.trim_ws_l(v), SNil{}, t_allws(v, eb)))
      Empty.absurd({True{} == False{} : Bool},
        no_tf(Equal.trans(Bool, True{}, String.is_empty(v), False{}, Equal.cong(String, Bool, x => String.is_empty(x), SNil{}, v, Equal.sym(String, v, SNil{}, ev)), hne)))

def trr_v(+v: String, +htv: {Tgt.trim_ws(v) == v : String}) -> {v == Tgt.trim_ws_r(v) : String}:
  +tv = Tgt.trim_ws_l(v)
  Equal.sym(String, Tgt.trim_ws_r(v), v,
    Equal.trans(String, Tgt.trim_ws_r(v), Tgt.trim_ws_r(Tgt.trim_ws_r(tv)), v,
      Equal.cong(String, String, x => Tgt.trim_ws_r(x), v, Tgt.trim_ws_r(tv), Equal.sym(String, Tgt.trim_ws(v), v, htv)),
      Equal.trans(String, Tgt.trim_ws_r(Tgt.trim_ws_r(tv)), Tgt.trim_ws_r(tv), v, trr_idem(tv), htv)))

# the header line "k: v" is trimmed
def hl_trim(+k: String, +v: String, +hvk: {all_vis(k) == True{} : Bool}, +hkne: {String.is_empty(k) == False{} : Bool},
  +htv: {Tgt.trim_ws(v) == v : String}, +hvne: {String.is_empty(v) == False{} : Bool})
  -> {Tgt.trim_ws(String.append(k, SCon{Chr{58}, SCon{Chr{32}, v}})) == String.append(k, SCon{Chr{58}, SCon{Chr{32}, v}}) : String}:
  +l = String.append(k, SCon{Chr{58}, SCon{Chr{32}, v}})
  %t_vis(k, SCon{Chr{58}, SCon{Chr{32}, v}}, hvk, hkne) : {Tgt.trim_ws_r(_) == l : String}
  %trr_app(k, SCon{Chr{58}, SCon{Chr{32}, v}}, {==}) : {_ == l : String}
  %trr_app(SCon{Chr{58}, SCon{Chr{32}, SNil{}}}, v, nav_b(allws(v), v, {==}, htv, hvne)) : {String.append(k, _) == l : String}
  %trr_v(v, htv) : {String.append(k, SCon{Chr{58}, SCon{Chr{32}, _}}) == l : String}
  {==}

def hdr_kv(k: String, +v: String, +t: Tgt.Target, +acc: List<&2, Tgt.Target>,
  +htok: {L.all_token(k) == True{} : Bool}, +hvk: {all_vis(k) == True{} : Bool}, +hkne: {String.is_empty(k) == False{} : Bool},
  +hs35: {String.starts_with(k, "#") == False{} : Bool}, +hs64: {String.starts_with(k, "@") == False{} : Bool},
  +htv: {Tgt.trim_ws(v) == v : String}, +hvne: {String.is_empty(v) == False{} : Bool})
  -> {Tgt.hdr(String.append(k, SCon{Chr{58}, SCon{Chr{32}, v}}), t, acc) == Tgt.SHdr{Tgt.with_hdr(t, k, v), acc} : Tgt.St}:
  match k:
    case SNil{}:
      Empty.absurd({Tgt.hdr(SCon{Chr{58}, SCon{Chr{32}, v}}, t, acc) == Tgt.SHdr{Tgt.with_hdr(t, SNil{}, v), acc} : Tgt.St}, no_tf(hkne))
    case SCon{c, +r}:
      match c:
        case Chr{+j}:
          +kk = String.append(SCon{Chr{j}, SNil{}}, r)
          +l = String.append(kk, SCon{Chr{58}, SCon{Chr{32}, v}})
          %Equal.sym(Bool, U32.is_eq(j, 35), False{}, swf(U32.is_eq(j, 35), r, hs35))
            : {Tgt.hdr.comment(_, l, t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          %Equal.sym(Bool, U32.is_eq(j, 64), False{}, swf(U32.is_eq(j, 64), r, hs64))
            : {Tgt.hdr.body(_, l, t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          %Equal.sym(Bool, Tgt.has_char(l, 58), True{}, hc_mid(kk, 58, SCon{Chr{32}, v}))
            : {Tgt.hdr.colon(_, l, t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          %bef_gen(kk, SCon{Chr{58}, SCon{Chr{32}, v}}, 58, tok_no(kk, 58, {==}, htok))
            : {Tgt.hdr.kv(Bool.and(Bool.not(String.is_empty(Tgt.trim_ws(_))), Bool.not(String.is_empty(Tgt.trim_ws(Tgt.after(l, 58))))), l,
                 Tgt.trim_ws(_), Tgt.trim_ws(Tgt.after(l, 58)), t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          %app_nil(kk)
            : {Tgt.hdr.kv(Bool.and(Bool.not(String.is_empty(Tgt.trim_ws(_))), Bool.not(String.is_empty(Tgt.trim_ws(Tgt.after(l, 58))))), l,
                 Tgt.trim_ws(_), Tgt.trim_ws(Tgt.after(l, 58)), t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          %Equal.sym(String, Tgt.trim_ws(kk), kk, tw_vis(kk, hvk))
            : {Tgt.hdr.kv(Bool.and(Bool.not(String.is_empty(_)), Bool.not(String.is_empty(Tgt.trim_ws(Tgt.after(l, 58))))), l,
                 _, Tgt.trim_ws(Tgt.after(l, 58)), t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          %aft_gen(kk, SCon{Chr{58}, SCon{Chr{32}, v}}, 58, tok_no(kk, 58, {==}, htok))
            : {Tgt.hdr.kv(Bool.and(Bool.not(String.is_empty(kk)), Bool.not(String.is_empty(Tgt.trim_ws(_)))), l,
                 kk, Tgt.trim_ws(_), t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          %Equal.sym(String, Tgt.trim_ws(v), v, htv)
            : {Tgt.hdr.kv(Bool.and(Bool.not(String.is_empty(kk)), Bool.not(String.is_empty(_))), l,
                 kk, _, t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          %Equal.sym(Bool, String.is_empty(v), False{}, hvne)
            : {Tgt.hdr.kv(Bool.and(Bool.not(String.is_empty(kk)), Bool.not(_)), l, kk, v, t, acc) == Tgt.SHdr{Tgt.with_hdr(t, kk, v), acc} : Tgt.St}
          {==}

# a header line moves a target being read to its next header
def feed_hl(+p: Bool, +t: Tgt.Target, +acc: List<&2, Tgt.Target>, +k: String, +v: String, +w: String,
  +htok: {L.all_token(k) == True{} : Bool}, +hkne: {String.is_empty(k) == False{} : Bool},
  +hs35: {String.starts_with(k, "#") == False{} : Bool}, +hs64: {String.starts_with(k, "@") == False{} : Bool},
  +hpr: {L.printable(v) == True{} : Bool}, +htv: {Tgt.trim_ws(v) == v : String}, +hvne: {String.is_empty(v) == False{} : Bool})
  -> {feed(String.append(k, SCon{Chr{58}, SCon{Chr{32}, String.append(v, SCon{Chr{10}, w})}}), Tgt.Ln{SNil{}, mk(p, t, acc)})
      == feed(w, Tgt.Ln{SNil{}, mk(False{}, Tgt.with_hdr(t, k, v), acc)}) : Tgt.Ln}:
  +l = String.append(k, SCon{Chr{58}, SCon{Chr{32}, v}})
  +hvk = vis_token(k, htok)
  +rhs = feed(w, Tgt.Ln{SNil{}, mk(False{}, Tgt.with_hdr(t, k, v), acc)})
  %app_assoc(k, SCon{Chr{58}, SCon{Chr{32}, v}}, SCon{Chr{10}, w}) : {feed(_, Tgt.Ln{SNil{}, mk(p, t, acc)}) == rhs : Tgt.Ln}
  %Equal.sym(Tgt.Ln, feed(String.append(l, SCon{Chr{10}, w}), Tgt.Ln{SNil{}, mk(p, t, acc)}), feed(w, Tgt.Ln{SNil{}, Tgt.step(mk(p, t, acc), Tgt.trim_ws(l))}),
      feed_nl2(l, w, mk(p, t, acc), hc_app(k, SCon{Chr{58}, SCon{Chr{32}, v}}, 10, vis_no(k, 10, {==}, hvk), pr_no(v, 10, {==}, hpr))))
    : {_ == rhs : Tgt.Ln}
  %Equal.sym(String, Tgt.trim_ws(l), l, hl_trim(k, v, hvk, hkne, htv, hvne))
    : {feed(w, Tgt.Ln{SNil{}, Tgt.step(mk(p, t, acc), _)}) == rhs : Tgt.Ln}
  %Equal.sym(Tgt.St, Tgt.step(mk(p, t, acc), l), Tgt.hdr(l, t, acc),
      step_mk(p, t, acc, l, ne_app2(k, SCon{Chr{58}, SCon{Chr{32}, v}}, hkne), nm_sm(l, nm_vis(k, SCon{Chr{58}, SCon{Chr{32}, v}}, hvk, {==}))))
    : {feed(w, Tgt.Ln{SNil{}, _}) == rhs : Tgt.Ln}
  %Equal.sym(Tgt.St, Tgt.hdr(l, t, acc), Tgt.SHdr{Tgt.with_hdr(t, k, v), acc}, hdr_kv(k, v, t, acc, htok, hvk, hkne, hs35, hs64, htv, hvne))
    : {feed(w, Tgt.Ln{SNil{}, _}) == rhs : Tgt.Ln}
  {==}

def wv(vs: List<&2, String>, +t: Tgt.Target, +k: String) -> Tgt.Target:
  match vs:
    case Nil{}:
      t
    case Con{+v, +rest}:
      wv(rest, Tgt.with_hdr(t, k, v), k)

def pv(vs: List<&2, String>, +p: Bool) -> Bool:
  match vs:
    case Nil{}:
      p
    case Con{v, rest}:
      False{}

def wh(hs: List<&2, Hdr.Header>, +t: Tgt.Target) -> Tgt.Target:
  match hs:
    case Nil{}:
      t
    case Con{+h, +rest}:
      wh(rest, wv(L.hdr_vals(h), t, L.hdr_key(h)))

def ph(hs: List<&2, Hdr.Header>, +p: Bool) -> Bool:
  match hs:
    case Nil{}:
      p
    case Con{+h, +rest}:
      ph(rest, pv(L.hdr_vals(h), p))

def pv_f(vs: List<&2, String>) -> {pv(vs, False{}) == False{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case Con{v, rest}:
      {==}

# the value lines of one header
def feed_vl(vs: List<&2, String>, +p: Bool, +t: Tgt.Target, +acc: List<&2, Tgt.Target>, +k: String,
  +hk: {L.tgt_key_ok(k) == True{} : Bool}, +hv: {L.tgt_vals_ok(vs) == True{} : Bool})
  -> {feed(L.tgt_val_lines(k, vs), Tgt.Ln{SNil{}, mk(p, t, acc)}) == Tgt.Ln{SNil{}, mk(pv(vs, p), wv(vs, t, k), acc)} : Tgt.Ln}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      +c1 = Bool.and(L.printable(v), Bool.not(String.is_empty(v)))
      +c2 = Bool.and(String.eq(L.trim_ows(v), v), L.tgt_vals_ok(rest))
      +h1 = and_l(c1, c2, hv)
      +h2 = and_r(c1, c2, hv)
      +hpr = and_l(L.printable(v), Bool.not(String.is_empty(v)), h1)
      +hvne = not_t(String.is_empty(v), and_r(L.printable(v), Bool.not(String.is_empty(v)), h1))
      +htv = Equal.trans(String, Tgt.trim_ws(v), L.trim_ows(v), v, Equal.sym(String, L.trim_ows(v), Tgt.trim_ws(v), ows(v, hpr)),
        str_eq(L.trim_ows(v), v, and_l(String.eq(L.trim_ows(v), v), L.tgt_vals_ok(rest), h2)))
      +tk = L.token(k)
      +nk = Bool.not(Bool.or(String.starts_with(k, "#"), String.starts_with(k, "@")))
      +htk = and_l(tk, nk, hk)
      +hor = not_t(Bool.or(String.starts_with(k, "#"), String.starts_with(k, "@")), and_r(tk, nk, hk))
      +htok = and_r(Bool.not(String.is_empty(k)), L.all_token(k), htk)
      +hkne = not_t(String.is_empty(k), and_l(Bool.not(String.is_empty(k)), L.all_token(k), htk))
      Equal.trans(Tgt.Ln, feed(L.tgt_val_lines(k, Con{v, rest}), Tgt.Ln{SNil{}, mk(p, t, acc)}),
        feed(L.tgt_val_lines(k, rest), Tgt.Ln{SNil{}, mk(False{}, Tgt.with_hdr(t, k, v), acc)}),
        Tgt.Ln{SNil{}, mk(False{}, wv(rest, Tgt.with_hdr(t, k, v), k), acc)},
        feed_hl(p, t, acc, k, v, L.tgt_val_lines(k, rest), htok, hkne,
          or_f(String.starts_with(k, "#"), String.starts_with(k, "@"), hor), or_f2(String.starts_with(k, "#"), String.starts_with(k, "@"), hor),
          hpr, htv, hvne),
        Equal.trans(Tgt.Ln, feed(L.tgt_val_lines(k, rest), Tgt.Ln{SNil{}, mk(False{}, Tgt.with_hdr(t, k, v), acc)}),
          Tgt.Ln{SNil{}, mk(pv(rest, False{}), wv(rest, Tgt.with_hdr(t, k, v), k), acc)},
          Tgt.Ln{SNil{}, mk(False{}, wv(rest, Tgt.with_hdr(t, k, v), k), acc)},
          feed_vl(rest, False{}, Tgt.with_hdr(t, k, v), acc, k, hk, and_r(String.eq(L.trim_ows(v), v), L.tgt_vals_ok(rest), h2)),
          Equal.cong(Bool, Tgt.Ln, x => Tgt.Ln{SNil{}, mk(x, wv(rest, Tgt.with_hdr(t, k, v), k), acc)}, pv(rest, False{}), False{}, pv_f(rest))))

def lnz(+st: Tgt.St) -> Tgt.Ln:
  Tgt.Ln{SNil{}, st}

# the header lines of a target
def feed_hls(hs: List<&2, Hdr.Header>, +p: Bool, +t: Tgt.Target, +acc: List<&2, Tgt.Target>, +h: {L.tgt_hdrs_ok(hs) == True{} : Bool})
  -> {feed(L.tgt_hdr_lines(hs), Tgt.Ln{SNil{}, mk(p, t, acc)}) == Tgt.Ln{SNil{}, mk(ph(hs, p), wh(hs, t), acc)} : Tgt.Ln}:
  match hs:
    case Nil{}:
      {==}
    case Con{hd, +rest}:
      match hd:
        case Hdr.Header{+k, +vs}:
          +c3 = Bool.and(L.tgt_vals_ok(vs), L.tgt_hdrs_ok(rest))
          +c2 = Bool.and(Bool.not(List.is_empty(&2, String, vs)), c3)
          +h2 = and_r(L.tgt_key_ok(k), c2, h)
          +h3 = and_r(Bool.not(List.is_empty(&2, String, vs)), c3, h2)
          +vl = L.tgt_val_lines(k, vs)
          +hl = L.tgt_hdr_lines(rest)
          +r0 = lnz(mk(p, t, acc))
          +r1 = lnz(mk(pv(vs, p), wv(vs, t, k), acc))
          Equal.trans(Tgt.Ln, feed(String.append(vl, hl), r0), feed(hl, feed(vl, r0)), Tgt.Ln{SNil{}, mk(ph(rest, pv(vs, p)), wh(rest, wv(vs, t, k)), acc)},
            feed_app(vl, hl, r0),
            Equal.trans(Tgt.Ln, feed(hl, feed(vl, r0)), feed(hl, r1), Tgt.Ln{SNil{}, mk(ph(rest, pv(vs, p)), wh(rest, wv(vs, t, k)), acc)},
              Equal.cong(Tgt.Ln, Tgt.Ln, x => feed(hl, x), feed(vl, r0), r1, feed_vl(vs, p, t, acc, k, and_l(L.tgt_key_ok(k), c2, h), and_l(L.tgt_vals_ok(vs), L.tgt_hdrs_ok(rest), h3))),
              feed_hls(rest, pv(vs, p), wv(vs, t, k), acc, and_r(L.tgt_vals_ok(vs), L.tgt_hdrs_ok(rest), h3))))

# ---------------------------------------------------------------------
# The headers read back: add_hdr over the value lines rebuilds them
# ---------------------------------------------------------------------

def u32_crefl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{+w}:
      wcmp_refl(32n, w)

def seq_refl(+x: U32, +t: String, c: Cmp, +e: {U32.cmp(x, x) == c : Cmp}, +ih: {String.eq(t, t) == True{} : Bool})
  -> {String.eq.fin(String.cmp.fin(t, t, ((Chr{x}, Chr{x}), c))) == True{} : Bool}:
  match c:
    case EQ{}:
      Equal.trans(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{x}, String.cmp(t, t))), String.eq(t, t), True{},
        rec_fin(Chr{x}, Chr{x}, String.cmp(t, t)), ih)
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, no_lt(EQ{}, Equal.trans(Cmp, EQ{}, U32.cmp(x, x), LT{}, Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_crefl(x)), e), {==}))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, no_gt(EQ{}, Equal.trans(Cmp, EQ{}, U32.cmp(x, x), GT{}, Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_crefl(x)), e), {==}))

def str_refl(s: String) -> {String.eq(s, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          seq_refl(x, t, U32.cmp(x, x), {==}, str_refl(t))

def seq_sym_b(c: Bool, +a: String, +b: String, +ec: {String.eq(b, a) == c : Bool}, +h: {String.eq(a, b) == False{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      +e = str_eq(b, a, ec)
      Empty.absurd({True{} == False{} : Bool},
        no_tf(Equal.trans(Bool, True{}, String.eq(a, b), False{},
          Equal.trans(Bool, True{}, String.eq(a, a), String.eq(a, b), Equal.sym(Bool, String.eq(a, a), True{}, str_refl(a)),
            Equal.cong(String, Bool, x => String.eq(a, x), a, b, Equal.sym(String, b, a, e))), h)))

def seq_sym_f(+a: String, +b: String, +h: {String.eq(a, b) == False{} : Bool}) -> {String.eq(b, a) == False{} : Bool}:
  seq_sym_b(String.eq(b, a), a, b, {==}, h)

def addv(vs: List<&2, String>, +hs: List<&2, Hdr.Header>, +k: String) -> List<&2, Hdr.Header>:
  match vs:
    case Nil{}:
      hs
    case Con{+v, +rest}:
      addv(rest, Tgt.add_hdr(Hdr.Header{k, [v]}, hs), k)

def addh(hs: List<&2, Hdr.Header>, +base: List<&2, Hdr.Header>) -> List<&2, Hdr.Header>:
  match hs:
    case Nil{}:
      base
    case Con{+h, +rest}:
      addh(rest, addv(L.hdr_vals(h), base, L.hdr_key(h)))

def wv_t(vs: List<&2, String>, +m: String, +u: String, +hs: List<&2, Hdr.Header>, +b: Maybe<&2, String>, +k: String)
  -> {wv(vs, Tgt.Target{m, u, hs, b}, k) == Tgt.Target{m, u, addv(vs, hs, k), b} : Tgt.Target}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +rest}:
      wv_t(rest, m, u, Tgt.add_hdr(Hdr.Header{k, [v]}, hs), b, k)

def wh_t(hs: List<&2, Hdr.Header>, +m: String, +u: String, +base: List<&2, Hdr.Header>, +b: Maybe<&2, String>)
  -> {wh(hs, Tgt.Target{m, u, base, b}) == Tgt.Target{m, u, addh(hs, base), b} : Tgt.Target}:
  match hs:
    case Nil{}:
      {==}
    case Con{hd, +rest}:
      match hd:
        case Hdr.Header{+k, +vs}:
          %Equal.sym(Tgt.Target, wv(vs, Tgt.Target{m, u, base, b}, k), Tgt.Target{m, u, addv(vs, base, k), b}, wv_t(vs, m, u, base, b, k))
            : {wh(rest, _) == Tgt.Target{m, u, addh(rest, addv(vs, base, k)), b} : Tgt.Target}
          wh_t(rest, m, u, addv(vs, base, k), b)

# a name not in the list is added at its end
def ah1(base: List<&2, Hdr.Header>, +k: String, +vs: List<&2, String>, +h: {L.has_key(k, base) == False{} : Bool})
  -> {Tgt.add_hdr(Hdr.Header{k, vs}, base) == List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs}]) : List<&2, Hdr.Header>}:
  match base:
    case Nil{}:
      {==}
    case Con{g, +r}:
      match g:
        case Hdr.Header{+gk, +gvs}:
          %Equal.sym(Bool, String.eq(gk, k), False{}, or_f(String.eq(gk, k), L.has_key(k, r), h))
            : {Tgt.pick(List<&2, Hdr.Header>, _, Con{Hdr.Header{gk, List.append(&2, String, gvs, vs)}, r}, Con{Hdr.Header{gk, gvs}, Tgt.add_hdr(Hdr.Header{k, vs}, r)})
               == Con{Hdr.Header{gk, gvs}, List.append(&2, Hdr.Header, r, [Hdr.Header{k, vs}])} : List<&2, Hdr.Header>}
          %Equal.sym(List<&2, Hdr.Header>, Tgt.add_hdr(Hdr.Header{k, vs}, r), List.append(&2, Hdr.Header, r, [Hdr.Header{k, vs}]), ah1(r, k, vs, or_f2(String.eq(gk, k), L.has_key(k, r), h)))
            : {Con{Hdr.Header{gk, gvs}, _} == Con{Hdr.Header{gk, gvs}, List.append(&2, Hdr.Header, r, [Hdr.Header{k, vs}])} : List<&2, Hdr.Header>}
          {==}

# a value for the name at the end goes to it
def ah2(base: List<&2, Hdr.Header>, +k: String, +vs0: List<&2, String>, +v: String, +h: {L.has_key(k, base) == False{} : Bool})
  -> {Tgt.add_hdr(Hdr.Header{k, [v]}, List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs0}]))
      == List.append(&2, Hdr.Header, base, [Hdr.Header{k, List.append(&2, String, vs0, [v])}]) : List<&2, Hdr.Header>}:
  match base:
    case Nil{}:
      %Equal.sym(Bool, String.eq(k, k), True{}, str_refl(k))
        : {Tgt.pick(List<&2, Hdr.Header>, _, Con{Hdr.Header{k, List.append(&2, String, vs0, [v])}, Nil{}}, Con{Hdr.Header{k, vs0}, Tgt.add_hdr(Hdr.Header{k, [v]}, Nil{})})
           == [Hdr.Header{k, List.append(&2, String, vs0, [v])}] : List<&2, Hdr.Header>}
      {==}
    case Con{g, +r}:
      match g:
        case Hdr.Header{+gk, +gvs}:
          +tail = List.append(&2, Hdr.Header, r, [Hdr.Header{k, vs0}])
          %Equal.sym(Bool, String.eq(gk, k), False{}, or_f(String.eq(gk, k), L.has_key(k, r), h))
            : {Tgt.pick(List<&2, Hdr.Header>, _, Con{Hdr.Header{gk, List.append(&2, String, gvs, [v])}, tail}, Con{Hdr.Header{gk, gvs}, Tgt.add_hdr(Hdr.Header{k, [v]}, tail)})
               == Con{Hdr.Header{gk, gvs}, List.append(&2, Hdr.Header, r, [Hdr.Header{k, List.append(&2, String, vs0, [v])}])} : List<&2, Hdr.Header>}
          %Equal.sym(List<&2, Hdr.Header>, Tgt.add_hdr(Hdr.Header{k, [v]}, tail), List.append(&2, Hdr.Header, r, [Hdr.Header{k, List.append(&2, String, vs0, [v])}]),
              ah2(r, k, vs0, v, or_f2(String.eq(gk, k), L.has_key(k, r), h)))
            : {Con{Hdr.Header{gk, gvs}, _} == Con{Hdr.Header{gk, gvs}, List.append(&2, Hdr.Header, r, [Hdr.Header{k, List.append(&2, String, vs0, [v])}])} : List<&2, Hdr.Header>}
          {==}

def lnil_s(xs: List<&2, String>) -> {xs == List.append(&2, String, xs, Nil{}) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %lnil_s(r) : {Con{x, r} == Con{x, _} : List<&2, String>}
      {==}

def lassoc_s(a: List<&2, String>, +b: List<&2, String>, +c: List<&2, String>)
  -> {List.append(&2, String, List.append(&2, String, a, b), c) == List.append(&2, String, a, List.append(&2, String, b, c)) : List<&2, String>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %lassoc_s(r, b, c) : {Con{x, List.append(&2, String, List.append(&2, String, r, b), c)} == Con{x, _} : List<&2, String>}
      {==}

def lnil_h(xs: List<&2, Hdr.Header>) -> {List.append(&2, Hdr.Header, xs, Nil{}) == xs : List<&2, Hdr.Header>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.cong(List<&2, Hdr.Header>, List<&2, Hdr.Header>, y => Con{x, y}, List.append(&2, Hdr.Header, r, Nil{}), r, lnil_h(r))

def lassoc_h(a: List<&2, Hdr.Header>, +b: List<&2, Hdr.Header>, +c: List<&2, Hdr.Header>)
  -> {List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, a, b), c) == List.append(&2, Hdr.Header, a, List.append(&2, Hdr.Header, b, c)) : List<&2, Hdr.Header>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %lassoc_h(r, b, c) : {Con{x, List.append(&2, Hdr.Header, List.append(&2, Hdr.Header, r, b), c)} == Con{x, _} : List<&2, Hdr.Header>}
      {==}

def addv_end(vr: List<&2, String>, +base: List<&2, Hdr.Header>, +k: String, +vs0: List<&2, String>, +h: {L.has_key(k, base) == False{} : Bool})
  -> {addv(vr, List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs0}]), k) == List.append(&2, Hdr.Header, base, [Hdr.Header{k, List.append(&2, String, vs0, vr)}]) : List<&2, Hdr.Header>}:
  match vr:
    case Nil{}:
      %lnil_s(vs0) : {List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs0}]) == List.append(&2, Hdr.Header, base, [Hdr.Header{k, _}]) : List<&2, Hdr.Header>}
      {==}
    case Con{+v, +r}:
      %Equal.sym(List<&2, Hdr.Header>, Tgt.add_hdr(Hdr.Header{k, [v]}, List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs0}])),
          List.append(&2, Hdr.Header, base, [Hdr.Header{k, List.append(&2, String, vs0, [v])}]), ah2(base, k, vs0, v, h))
        : {addv(r, _, k) == List.append(&2, Hdr.Header, base, [Hdr.Header{k, List.append(&2, String, vs0, Con{v, r})}]) : List<&2, Hdr.Header>}
      %lassoc_s(vs0, [v], r)
        : {addv(r, List.append(&2, Hdr.Header, base, [Hdr.Header{k, List.append(&2, String, vs0, [v])}]), k) == List.append(&2, Hdr.Header, base, [Hdr.Header{k, _}]) : List<&2, Hdr.Header>}
      addv_end(r, base, k, List.append(&2, String, vs0, [v]), h)

def addv_new(vs: List<&2, String>, +base: List<&2, Hdr.Header>, +k: String, +h: {L.has_key(k, base) == False{} : Bool},
  +hne: {Bool.not(List.is_empty(&2, String, vs)) == True{} : Bool})
  -> {addv(vs, base, k) == List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs}]) : List<&2, Hdr.Header>}:
  match vs:
    case Nil{}:
      Empty.absurd({base == List.append(&2, Hdr.Header, base, [Hdr.Header{k, Nil{}}]) : List<&2, Hdr.Header>}, no_ft(hne))
    case Con{+v, +r}:
      %Equal.sym(List<&2, Hdr.Header>, Tgt.add_hdr(Hdr.Header{k, [v]}, base), List.append(&2, Hdr.Header, base, [Hdr.Header{k, [v]}]), ah1(base, k, [v], h))
        : {addv(r, _, k) == List.append(&2, Hdr.Header, base, [Hdr.Header{k, Con{v, r}}]) : List<&2, Hdr.Header>}
      addv_end(r, base, k, [v], h)

def hk_app(a: List<&2, Hdr.Header>, +b: List<&2, Hdr.Header>, +k: String, +ha: {L.has_key(k, a) == False{} : Bool}, +hb: {L.has_key(k, b) == False{} : Bool})
  -> {L.has_key(k, List.append(&2, Hdr.Header, a, b)) == False{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+g, +r}:
      %Equal.sym(Bool, String.eq(L.hdr_key(g), k), False{}, or_f(String.eq(L.hdr_key(g), k), L.has_key(k, r), ha))
        : {Bool.or(_, L.has_key(k, List.append(&2, Hdr.Header, r, b))) == False{} : Bool}
      hk_app(r, b, k, or_f2(String.eq(L.hdr_key(g), k), L.has_key(k, r), ha), hb)

def nokey(hs: List<&2, Hdr.Header>, +base: List<&2, Hdr.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, +r}:
      Bool.and(Bool.not(L.has_key(L.hdr_key(h), base)), nokey(r, base))

def nokey_nil(hs: List<&2, Hdr.Header>) -> {nokey(hs, Nil{}) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +r}:
      nokey_nil(r)

def nokey_step(rest: List<&2, Hdr.Header>, +base: List<&2, Hdr.Header>, +k: String, +vs: List<&2, String>,
  +hn: {nokey(rest, base) == True{} : Bool}, +hd: {L.has_key(k, rest) == False{} : Bool})
  -> {nokey(rest, List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs}])) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{g, +r}:
      match g:
        case Hdr.Header{+gk, +gvs}:
          +a = Bool.not(L.has_key(gk, base))
          +hb = not_t(L.has_key(gk, base), and_l(a, nokey(r, base), hn))
          +e1 = or_f(String.eq(gk, k), L.has_key(k, r), hd)
          +hk = hk_app(base, [Hdr.Header{k, vs}], gk, hb,
            Equal.trans(Bool, Bool.or(String.eq(k, gk), False{}), String.eq(k, gk), False{}, or_ff(String.eq(k, gk)), seq_sym_f(gk, k, e1)))
          %Equal.sym(Bool, L.has_key(gk, List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs}])), False{}, hk)
            : {Bool.and(Bool.not(_), nokey(r, List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs}]))) == True{} : Bool}
          nokey_step(r, base, k, vs, and_r(a, nokey(r, base), hn), or_f2(String.eq(gk, k), L.has_key(k, r), hd))

def addh_main(hs: List<&2, Hdr.Header>, +base: List<&2, Hdr.Header>,
  +hd: {L.hdr_names_distinct(hs) == True{} : Bool}, +hn: {nokey(hs, base) == True{} : Bool}, +hv: {L.tgt_hdrs_ok(hs) == True{} : Bool})
  -> {addh(hs, base) == List.append(&2, Hdr.Header, base, hs) : List<&2, Hdr.Header>}:
  match hs:
    case Nil{}:
      Equal.sym(List<&2, Hdr.Header>, List.append(&2, Hdr.Header, base, Nil{}), base, lnil_h(base))
    case Con{g, +rest}:
      match g:
        case Hdr.Header{+k, +vs}:
          +c3 = Bool.and(L.tgt_vals_ok(vs), L.tgt_hdrs_ok(rest))
          +c2 = Bool.and(Bool.not(List.is_empty(&2, String, vs)), c3)
          +h2 = and_r(L.tgt_key_ok(k), c2, hv)
          +a = Bool.not(L.has_key(k, rest))
          +hk = not_t(L.has_key(k, base), and_l(Bool.not(L.has_key(k, base)), nokey(rest, base), hn))
          %Equal.sym(List<&2, Hdr.Header>, addv(vs, base, k), List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs}]),
              addv_new(vs, base, k, hk, and_l(Bool.not(List.is_empty(&2, String, vs)), c3, h2)))
            : {addh(rest, _) == List.append(&2, Hdr.Header, base, Con{Hdr.Header{k, vs}, rest}) : List<&2, Hdr.Header>}
          %lassoc_h(base, [Hdr.Header{k, vs}], rest)
            : {addh(rest, List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs}])) == _ : List<&2, Hdr.Header>}
          addh_main(rest, List.append(&2, Hdr.Header, base, [Hdr.Header{k, vs}]), and_r(a, L.hdr_names_distinct(rest), hd),
            nokey_step(rest, base, k, vs, and_r(Bool.not(L.has_key(k, base)), nokey(rest, base), hn), not_t(L.has_key(k, rest), and_l(a, L.hdr_names_distinct(rest), hd))),
            and_r(L.tgt_vals_ok(vs), L.tgt_hdrs_ok(rest), and_r(Bool.not(List.is_empty(&2, String, vs)), c3, h2)))

# ---------------------------------------------------------------------
# The body line, and a whole target
# ---------------------------------------------------------------------

def bst(b: Maybe<&2, String>, +p: Bool, +t: Tgt.Target, +acc: List<&2, Tgt.Target>) -> Tgt.St:
  match b:
    case None{}:
      mk(p, t, acc)
    case Some{+q}:
      Tgt.SSeek{Con{Tgt.with_body(t, q), acc}}

def feed_body(b: Maybe<&2, String>, +p: Bool, +t: Tgt.Target, +acc: List<&2, Tgt.Target>, +hb: {L.body_path_ok(b) == True{} : Bool})
  -> {feed(L.body_line(b), lnz(mk(p, t, acc))) == lnz(bst(b, p, t, acc)) : Tgt.Ln}:
  match b:
    case None{}:
      {==}
    case Some{+q}:
      +c1 = Bool.and(L.printable(q), Bool.not(String.is_empty(q)))
      +h1 = and_l(c1, String.eq(L.trim_ows(q), q), hb)
      +hpr = and_l(L.printable(q), Bool.not(String.is_empty(q)), h1)
      +hqne = not_t(String.is_empty(q), and_r(L.printable(q), Bool.not(String.is_empty(q)), h1))
      +htv = Equal.trans(String, Tgt.trim_ws(q), L.trim_ows(q), q, Equal.sym(String, L.trim_ows(q), Tgt.trim_ws(q), ows(q, hpr)),
        str_eq(L.trim_ows(q), q, and_r(c1, String.eq(L.trim_ows(q), q), hb)))
      +rhs = lnz(Tgt.SSeek{Con{Tgt.with_body(t, q), acc}})
      %Equal.sym(Tgt.Ln, feed(String.append(SCon{Chr{64}, q}, SCon{Chr{10}, SNil{}}), lnz(mk(p, t, acc))),
          feed(SNil{}, lnz(Tgt.step(mk(p, t, acc), Tgt.trim_ws(SCon{Chr{64}, q})))),
          feed_nl2(SCon{Chr{64}, q}, SNil{}, mk(p, t, acc), pr_no(q, 10, {==}, hpr)))
        : {_ == rhs : Tgt.Ln}
      %trr_app(SCon{Chr{64}, SNil{}}, q, nav_b(allws(q), q, {==}, htv, hqne))
        : {lnz(Tgt.step(mk(p, t, acc), _)) == rhs : Tgt.Ln}
      %trr_v(q, htv) : {lnz(Tgt.step(mk(p, t, acc), SCon{Chr{64}, _})) == rhs : Tgt.Ln}
      %Equal.sym(Tgt.St, Tgt.step(mk(p, t, acc), SCon{Chr{64}, q}), Tgt.hdr(SCon{Chr{64}, q}, t, acc), step_mk(p, t, acc, SCon{Chr{64}, q}, {==}, {==}))
        : {lnz(_) == rhs : Tgt.Ln}
      %drop0(q) : {lnz(Tgt.SSeek{Con{Tgt.with_body(t, _), acc}}) == rhs : Tgt.Ln}
      {==}

def bst_blank(b: Maybe<&2, String>, +p: Bool, +m: String, +u: String, +hs: List<&2, Hdr.Header>, +acc: List<&2, Tgt.Target>)
  -> {Tgt.step(bst(b, p, Tgt.Target{m, u, hs, None{}}, acc), SNil{}) == Tgt.SSeek{Con{Tgt.Target{m, u, hs, b}, acc}} : Tgt.St}:
  match b:
    case None{}:
      step_blank(p, Tgt.Target{m, u, hs, None{}}, acc)
    case Some{+q}:
      {==}

def mkt(+m: String, +u: String) -> Tgt.Target:
  Tgt.Target{m, u, [], None{}}

# a target's text, read from a state looking for one
def tgt_core(+m: String, +u: String, +hs: List<&2, Hdr.Header>, +b: Maybe<&2, String>, +acc: List<&2, Tgt.Target>,
  +h: {L.target_ok(Tgt.Target{m, u, hs, b}) == True{} : Bool})
  -> {feed(L.target_text(Tgt.Target{m, u, hs, b}), lnz(Tgt.SSeek{acc})) == lnz(bst(b, ph(hs, True{}), Tgt.Target{m, u, hs, None{}}, acc)) : Tgt.Ln}:
  +cm = L.method_ok(m)
  +c4 = Bool.and(L.tgt_hdrs_ok(hs), L.hdr_names_distinct(hs))
  +c3 = Bool.and(c4, L.body_path_ok(b))
  +c2 = Bool.and(L.url_str_ok(u), c3)
  +hm = and_l(cm, c2, h)
  +h2 = and_r(cm, c2, h)
  +hu = and_l(L.url_str_ok(u), c3, h2)
  +h3 = and_r(L.url_str_ok(u), c3, h2)
  +h4 = and_l(c4, L.body_path_ok(b), h3)
  +hb = and_r(c4, L.body_path_ok(b), h3)
  +hhs = and_l(L.tgt_hdrs_ok(hs), L.hdr_names_distinct(hs), h4)
  +hd = and_r(L.tgt_hdrs_ok(hs), L.hdr_names_distinct(hs), h4)
  +hup = and_r(Bool.not(String.is_empty(m)), L.all_upper(m), hm)
  +hmne = not_t(String.is_empty(m), and_l(Bool.not(String.is_empty(m)), L.all_upper(m), hm))
  +hvm = vis_upper(m, hup)
  +hvu = pair_l({all_vis(u) == True{} : Bool}, {Tgt.req_uri_err(u) == None{} : Maybe<&2, String>}, us_facts(u, Tgt.parse_url(u), hu))
  +hru = pair_r({all_vis(u) == True{} : Bool}, {Tgt.req_uri_err(u) == None{} : Maybe<&2, String>}, us_facts(u, Tgt.parse_url(u), hu))
  +hune = us_ne(u, Tgt.parse_url(u), hu)
  +l = String.append(m, SCon{Chr{32}, u})
  +hl = L.tgt_hdr_lines(hs)
  +bl = L.body_line(b)
  +w = String.append(hl, bl)
  +rhs = lnz(bst(b, ph(hs, True{}), Tgt.Target{m, u, hs, None{}}, acc))
  %app_assoc(m, SCon{Chr{32}, u}, SCon{Chr{10}, w}) : {feed(_, lnz(Tgt.SSeek{acc})) == rhs : Tgt.Ln}
  %Equal.sym(Tgt.Ln, feed(String.append(l, SCon{Chr{10}, w}), lnz(Tgt.SSeek{acc})), feed(w, lnz(Tgt.step(Tgt.SSeek{acc}, Tgt.trim_ws(l)))),
      feed_nl2(l, w, Tgt.SSeek{acc}, hc_app(m, SCon{Chr{32}, u}, 10, vis_no(m, 10, {==}, hvm), vis_no(u, 10, {==}, hvu))))
    : {_ == rhs : Tgt.Ln}
  %Equal.sym(String, Tgt.trim_ws(l), l, req_trim(m, u, hvm, hmne, hvu, hune))
    : {feed(w, lnz(Tgt.step(Tgt.SSeek{acc}, _))) == rhs : Tgt.Ln}
  %Equal.sym(Tgt.St, Tgt.step(Tgt.SSeek{acc}, l), Tgt.SPeek{mkt(m, u), acc}, req_step(m, u, acc, hvm, hup, hmne, hvu, hru))
    : {feed(w, lnz(_)) == rhs : Tgt.Ln}
  %Equal.sym(Tgt.Ln, feed(w, lnz(mk(True{}, mkt(m, u), acc))), feed(bl, feed(hl, lnz(mk(True{}, mkt(m, u), acc)))), feed_app(hl, bl, lnz(mk(True{}, mkt(m, u), acc))))
    : {_ == rhs : Tgt.Ln}
  %Equal.sym(Tgt.Ln, feed(hl, lnz(mk(True{}, mkt(m, u), acc))), lnz(mk(ph(hs, True{}), wh(hs, mkt(m, u)), acc)), feed_hls(hs, True{}, mkt(m, u), acc, hhs))
    : {feed(bl, _) == rhs : Tgt.Ln}
  %Equal.sym(Tgt.Target, wh(hs, mkt(m, u)), Tgt.Target{m, u, addh(hs, Nil{}), None{}}, wh_t(hs, m, u, Nil{}, None{}))
    : {feed(bl, lnz(mk(ph(hs, True{}), _, acc))) == rhs : Tgt.Ln}
  %Equal.sym(List<&2, Hdr.Header>, addh(hs, Nil{}), hs, addh_main(hs, Nil{}, hd, nokey_nil(hs), hhs))
    : {feed(bl, lnz(mk(ph(hs, True{}), Tgt.Target{m, u, _, None{}}, acc))) == rhs : Tgt.Ln}
  feed_body(b, ph(hs, True{}), Tgt.Target{m, u, hs, None{}}, acc, hb)

# ---------------------------------------------------------------------
# targets_parse, targets_concat
# ---------------------------------------------------------------------

def tgt_end(t: Tgt.Target, +acc: List<&2, Tgt.Target>, +h: {L.target_ok(t) == True{} : Bool})
  -> {Tgt.ln_end(feed(L.target_text(t), lnz(Tgt.SSeek{acc}))) == Tgt.SSeek{Con{t, acc}} : Tgt.St}:
  match t:
    case Tgt.Target{+m, +u, +hs, +b}:
      %Equal.sym(Tgt.Ln, feed(L.target_text(Tgt.Target{m, u, hs, b}), lnz(Tgt.SSeek{acc})), lnz(bst(b, ph(hs, True{}), Tgt.Target{m, u, hs, None{}}, acc)),
          tgt_core(m, u, hs, b, acc, h))
        : {Tgt.ln_end(_) == Tgt.SSeek{Con{Tgt.Target{m, u, hs, b}, acc}} : Tgt.St}
      bst_blank(b, ph(hs, True{}), m, u, hs, acc)

def tgt_nl(t: Tgt.Target, +acc: List<&2, Tgt.Target>, +z: String, +h: {L.target_ok(t) == True{} : Bool})
  -> {feed(String.append(L.target_text(t), SCon{Chr{10}, z}), lnz(Tgt.SSeek{acc})) == feed(z, lnz(Tgt.SSeek{Con{t, acc}})) : Tgt.Ln}:
  match t:
    case Tgt.Target{+m, +u, +hs, +b}:
      +tt = L.target_text(Tgt.Target{m, u, hs, b})
      %Equal.sym(Tgt.Ln, feed(String.append(tt, SCon{Chr{10}, z}), lnz(Tgt.SSeek{acc})), feed(SCon{Chr{10}, z}, feed(tt, lnz(Tgt.SSeek{acc}))),
          feed_app(tt, SCon{Chr{10}, z}, lnz(Tgt.SSeek{acc})))
        : {_ == feed(z, lnz(Tgt.SSeek{Con{Tgt.Target{m, u, hs, b}, acc}})) : Tgt.Ln}
      %Equal.sym(Tgt.Ln, feed(tt, lnz(Tgt.SSeek{acc})), lnz(bst(b, ph(hs, True{}), Tgt.Target{m, u, hs, None{}}, acc)), tgt_core(m, u, hs, b, acc, h))
        : {feed(SCon{Chr{10}, z}, _) == feed(z, lnz(Tgt.SSeek{Con{Tgt.Target{m, u, hs, b}, acc}})) : Tgt.Ln}
      %Equal.sym(Tgt.St, Tgt.step(bst(b, ph(hs, True{}), Tgt.Target{m, u, hs, None{}}, acc), SNil{}), Tgt.SSeek{Con{Tgt.Target{m, u, hs, b}, acc}},
          bst_blank(b, ph(hs, True{}), m, u, hs, acc))
        : {feed(z, Tgt.Ln{SNil{}, _}) == feed(z, lnz(Tgt.SSeek{Con{Tgt.Target{m, u, hs, b}, acc}})) : Tgt.Ln}
      {==}

# the targets of a text, read from a state looking for one
def tgts_end(ts: List<&2, Tgt.Target>, +acc: List<&2, Tgt.Target>, +h: {L.targets_ok(ts) == True{} : Bool})
  -> {Tgt.ln_end(feed(L.targets_text(ts), lnz(Tgt.SSeek{acc}))) == Tgt.SSeek{List.reverse.go(&2, Tgt.Target, ts, acc)} : Tgt.St}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      match rest:
        case Nil{}:
          tgt_end(t, acc, and_l(L.target_ok(t), True{}, h))
        case Con{+u, +more}:
          %Equal.sym(Tgt.Ln, feed(String.append(L.target_text(t), SCon{Chr{10}, L.targets_text(Con{u, more})}), lnz(Tgt.SSeek{acc})),
              feed(L.targets_text(Con{u, more}), lnz(Tgt.SSeek{Con{t, acc}})),
              tgt_nl(t, acc, L.targets_text(Con{u, more}), and_l(L.target_ok(t), L.targets_ok(Con{u, more}), h)))
            : {Tgt.ln_end(_) == Tgt.SSeek{List.reverse.go(&2, Tgt.Target, Con{u, more}, Con{t, acc})} : Tgt.St}
          tgts_end(Con{u, more}, Con{t, acc}, and_r(L.target_ok(t), L.targets_ok(Con{u, more}), h))

# the targets of a text, a newline and more
def tgts_nl(ts: List<&2, Tgt.Target>, +acc: List<&2, Tgt.Target>, +z: String, +h: {L.targets_ok(ts) == True{} : Bool})
  -> {feed(String.append(L.targets_text(ts), SCon{Chr{10}, z}), lnz(Tgt.SSeek{acc})) == feed(z, lnz(Tgt.SSeek{List.reverse.go(&2, Tgt.Target, ts, acc)})) : Tgt.Ln}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      match rest:
        case Nil{}:
          tgt_nl(t, acc, z, and_l(L.target_ok(t), True{}, h))
        case Con{+u, +more}:
          +tt = L.target_text(t)
          +r2 = L.targets_text(Con{u, more})
          %Equal.sym(String, String.append(String.append(tt, SCon{Chr{10}, r2}), SCon{Chr{10}, z}), String.append(tt, SCon{Chr{10}, String.append(r2, SCon{Chr{10}, z})}),
              app_assoc(tt, SCon{Chr{10}, r2}, SCon{Chr{10}, z}))
            : {feed(_, lnz(Tgt.SSeek{acc})) == feed(z, lnz(Tgt.SSeek{List.reverse.go(&2, Tgt.Target, Con{u, more}, Con{t, acc})})) : Tgt.Ln}
          %Equal.sym(Tgt.Ln, feed(String.append(tt, SCon{Chr{10}, String.append(r2, SCon{Chr{10}, z})}), lnz(Tgt.SSeek{acc})),
              feed(String.append(r2, SCon{Chr{10}, z}), lnz(Tgt.SSeek{Con{t, acc}})),
              tgt_nl(t, acc, String.append(r2, SCon{Chr{10}, z}), and_l(L.target_ok(t), L.targets_ok(Con{u, more}), h)))
            : {_ == feed(z, lnz(Tgt.SSeek{List.reverse.go(&2, Tgt.Target, Con{u, more}, Con{t, acc})})) : Tgt.Ln}
          tgts_nl(Con{u, more}, Con{t, acc}, z, and_r(L.target_ok(t), L.targets_ok(Con{u, more}), h))

def lrev_rev(l: List<&2, Tgt.Target>, +a: List<&2, Tgt.Target>, +b: List<&2, Tgt.Target>)
  -> {List.reverse.go(&2, Tgt.Target, List.reverse.go(&2, Tgt.Target, l, a), b) == List.reverse.go(&2, Tgt.Target, a, List.append(&2, Tgt.Target, l, b)) : List<&2, Tgt.Target>}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      lrev_rev(r, Con{x, a}, b)

def lnil_t(xs: List<&2, Tgt.Target>) -> {List.append(&2, Tgt.Target, xs, Nil{}) == xs : List<&2, Tgt.Target>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.cong(List<&2, Tgt.Target>, List<&2, Tgt.Target>, y => Con{x, y}, List.append(&2, Tgt.Target, r, Nil{}), r, lnil_t(r))

def lrr(+ts: List<&2, Tgt.Target>) -> {List.reverse(&2, Tgt.Target, List.reverse.go(&2, Tgt.Target, ts, Nil{})) == ts : List<&2, Tgt.Target>}:
  Equal.trans(List<&2, Tgt.Target>, List.reverse(&2, Tgt.Target, List.reverse.go(&2, Tgt.Target, ts, Nil{})), List.append(&2, Tgt.Target, ts, Nil{}), ts,
    lrev_rev(ts, Nil{}, Nil{}), lnil_t(ts))

def tp(+ts: List<&2, Tgt.Target>, +h: {L.targets_ok(ts) == True{} : Bool})
  -> {Tgt.parse_all(L.targets_text(ts)) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}:
  %Equal.sym(Tgt.St, Tgt.run(L.targets_text(ts), lnz(Tgt.SSeek{[]})), Tgt.ln_end(feed(L.targets_text(ts), lnz(Tgt.SSeek{[]}))), run_feed(L.targets_text(ts), lnz(Tgt.SSeek{[]})))
    : {Tgt.finish(_) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.ln_end(feed(L.targets_text(ts), lnz(Tgt.SSeek{[]}))), Tgt.SSeek{List.reverse.go(&2, Tgt.Target, ts, Nil{})}, tgts_end(ts, Nil{}, h))
    : {Tgt.finish(_) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(List<&2, Tgt.Target>, List.reverse(&2, Tgt.Target, List.reverse.go(&2, Tgt.Target, ts, Nil{})), ts, lrr(ts))
    : {Done{_} == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  {==}

def L.targets_parse(ts, h):
  tp(ts, h)

def tok_l(a: List<&2, Tgt.Target>, +b: List<&2, Tgt.Target>, +h: {L.targets_ok(List.append(&2, Tgt.Target, a, b)) == True{} : Bool}) -> {L.targets_ok(a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+t, +r}:
      and_tt(L.target_ok(t), L.targets_ok(r), and_l(L.target_ok(t), L.targets_ok(List.append(&2, Tgt.Target, r, b)), h),
        tok_l(r, b, and_r(L.target_ok(t), L.targets_ok(List.append(&2, Tgt.Target, r, b)), h)))

def tok_r(a: List<&2, Tgt.Target>, +b: List<&2, Tgt.Target>, +h: {L.targets_ok(List.append(&2, Tgt.Target, a, b)) == True{} : Bool}) -> {L.targets_ok(b) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+t, +r}:
      tok_r(r, b, and_r(L.target_ok(t), L.targets_ok(List.append(&2, Tgt.Target, r, b)), h))

def tc(+a: List<&2, Tgt.Target>, +b: List<&2, Tgt.Target>, +h: {L.targets_ok(List.append(&2, Tgt.Target, a, b)) == True{} : Bool})
  -> {Tgt.parse_all(L.targets_text(a) ++ "\n" ++ L.targets_text(b)) == Done{List.append(&2, Tgt.Target, a, b)} : Result<&2, &2, String, List<&2, Tgt.Target>>}:
  +s = String.append(L.targets_text(a), SCon{Chr{10}, L.targets_text(b)})
  +ra = List.reverse.go(&2, Tgt.Target, a, Nil{})
  %Equal.sym(Tgt.St, Tgt.run(s, lnz(Tgt.SSeek{[]})), Tgt.ln_end(feed(s, lnz(Tgt.SSeek{[]}))), run_feed(s, lnz(Tgt.SSeek{[]})))
    : {Tgt.finish(_) == Done{List.append(&2, Tgt.Target, a, b)} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.Ln, feed(s, lnz(Tgt.SSeek{[]})), feed(L.targets_text(b), lnz(Tgt.SSeek{ra})), tgts_nl(a, Nil{}, L.targets_text(b), tok_l(a, b, h)))
    : {Tgt.finish(Tgt.ln_end(_)) == Done{List.append(&2, Tgt.Target, a, b)} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.ln_end(feed(L.targets_text(b), lnz(Tgt.SSeek{ra}))), Tgt.SSeek{List.reverse.go(&2, Tgt.Target, b, ra)}, tgts_end(b, ra, tok_r(a, b, h)))
    : {Tgt.finish(_) == Done{List.append(&2, Tgt.Target, a, b)} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(List<&2, Tgt.Target>, List.reverse.go(&2, Tgt.Target, List.reverse.go(&2, Tgt.Target, b, ra), Nil{}), List.reverse.go(&2, Tgt.Target, ra, List.append(&2, Tgt.Target, b, Nil{})), lrev_rev(b, ra, Nil{})) : {Done{_} == Done{List.append(&2, Tgt.Target, a, b)} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(List<&2, Tgt.Target>, List.reverse.go(&2, Tgt.Target, ra, List.append(&2, Tgt.Target, b, Nil{})), List.reverse.go(&2, Tgt.Target, Nil{}, List.append(&2, Tgt.Target, a, List.append(&2, Tgt.Target, b, Nil{}))),
      lrev_rev(a, Nil{}, List.append(&2, Tgt.Target, b, Nil{}))) : {Done{_} == Done{List.append(&2, Tgt.Target, a, b)} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(List<&2, Tgt.Target>, List.append(&2, Tgt.Target, b, Nil{}), b, lnil_t(b))
    : {Done{List.append(&2, Tgt.Target, a, _)} == Done{List.append(&2, Tgt.Target, a, b)} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  {==}

def L.targets_concat(a, b, h):
  tc(a, b, h)

# ---------------------------------------------------------------------
# targets_noise
# ---------------------------------------------------------------------

def has_char_tg(s: String, +k: U32) -> {Tgt.has_char(s, k) == L.has_char(s, k) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+kc}:
          %hc_c(kc, rest, k) : {_ == L.has_char(SCon{Chr{kc}, rest}, k) : Bool}
          %has_char_tg(rest, k) : {Bool.or(U32.is_eq(kc, k), Tgt.has_char(rest, k)) == Bool.or(U32.is_eq(kc, k), _) : Bool}
          {==}

def skip_of(x: String, +h: {Bool.or(String.is_empty(x), String.starts_with(x, "#")) == True{} : Bool})
  -> {Bool.or(String.is_empty(x), Tgt.first_is(x, 35)) == True{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          sw_true(U32.is_eq(k, 35), r, h)

def noise_skip(ns: List<&2, String>, +acc: List<&2, Tgt.Target>, +z: String, +h: {L.all_noise(ns) == True{} : Bool})
  -> {feed(String.append(L.noise_text(ns), z), lnz(Tgt.SSeek{acc})) == feed(z, lnz(Tgt.SSeek{acc})) : Tgt.Ln}:
  match ns:
    case Nil{}:
      {==}
    case Con{+l, +r}:
      +a1 = Bool.and(L.printable(l), Bool.not(L.has_char(l, 10)))
      +a2 = Bool.or(String.is_empty(L.trim_ows(l)), String.starts_with(L.trim_ows(l), "#"))
      +hn = and_l(L.noise_ok(l), L.all_noise(r), h)
      +h1 = and_l(a1, a2, hn)
      +hpr = and_l(L.printable(l), Bool.not(L.has_char(l, 10)), h1)
      +hnl = Equal.trans(Bool, Tgt.has_char(l, 10), L.has_char(l, 10), False{}, has_char_tg(l, 10), not_t(L.has_char(l, 10), and_r(L.printable(l), Bool.not(L.has_char(l, 10)), h1)))
      +tw = Tgt.trim_ws(l)
      +hsk = skip_of(tw, Equal.trans(Bool, Bool.or(String.is_empty(tw), String.starts_with(tw, "#")), a2, True{},
        Equal.cong(String, Bool, x => Bool.or(String.is_empty(x), String.starts_with(x, "#")), tw, L.trim_ows(l), Equal.sym(String, L.trim_ows(l), tw, ows(l, hpr))),
        and_r(a1, a2, hn)))
      +nr = L.noise_text(r)
      %Equal.sym(String, String.append(String.append(l, SCon{Chr{10}, nr}), z), String.append(l, SCon{Chr{10}, String.append(nr, z)}), app_assoc(l, SCon{Chr{10}, nr}, z))
        : {feed(_, lnz(Tgt.SSeek{acc})) == feed(z, lnz(Tgt.SSeek{acc})) : Tgt.Ln}
      %Equal.sym(Tgt.Ln, feed(String.append(l, SCon{Chr{10}, String.append(nr, z)}), lnz(Tgt.SSeek{acc})),
          feed(String.append(nr, z), lnz(Tgt.step(Tgt.SSeek{acc}, tw))), feed_nl2(l, String.append(nr, z), Tgt.SSeek{acc}, hnl))
        : {_ == feed(z, lnz(Tgt.SSeek{acc})) : Tgt.Ln}
      %Equal.sym(Bool, Bool.or(String.is_empty(tw), Tgt.first_is(tw, 35)), True{}, hsk)
        : {feed(String.append(nr, z), lnz(Tgt.seek.of(_, tw, acc))) == feed(z, lnz(Tgt.SSeek{acc})) : Tgt.Ln}
      noise_skip(r, acc, z, and_r(L.noise_ok(l), L.all_noise(r), h))

def tn(+ns: List<&2, String>, +ts: List<&2, Tgt.Target>, +h0: {L.targets_ok(ts) == True{} : Bool}, +h1: {L.all_noise(ns) == True{} : Bool})
  -> {Tgt.parse_all(L.noise_text(ns) ++ L.targets_text(ts)) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}:
  +s = String.append(L.noise_text(ns), L.targets_text(ts))
  %Equal.sym(Tgt.St, Tgt.run(s, lnz(Tgt.SSeek{[]})), Tgt.ln_end(feed(s, lnz(Tgt.SSeek{[]}))), run_feed(s, lnz(Tgt.SSeek{[]})))
    : {Tgt.finish(_) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.Ln, feed(s, lnz(Tgt.SSeek{[]})), feed(L.targets_text(ts), lnz(Tgt.SSeek{[]})), noise_skip(ns, Nil{}, L.targets_text(ts), h1))
    : {Tgt.finish(Tgt.ln_end(_)) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.ln_end(feed(L.targets_text(ts), lnz(Tgt.SSeek{[]}))), Tgt.SSeek{List.reverse.go(&2, Tgt.Target, ts, Nil{})}, tgts_end(ts, Nil{}, h0))
    : {Tgt.finish(_) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(List<&2, Tgt.Target>, List.reverse(&2, Tgt.Target, List.reverse.go(&2, Tgt.Target, ts, Nil{})), ts, lrr(ts))
    : {Done{_} == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  {==}

def L.targets_noise(ns, ts, h0, h1):
  tn(ns, ts, h0, h1)

# ---------------------------------------------------------------------
# targets_errors: LAWS' starts_method is the parser's on printable text
# ---------------------------------------------------------------------

def sub0(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_succ(x: Nat, y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, 1n+y) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+xp:
      match y:
        case 0n:
          Empty.absurd({Nat.is_le(1n+xp, 1n) == True{} : Bool}, no_ft(h))
        case 1n+yp:
          le_succ(xp, yp, h)

def sub_succ0(a: Nat) -> {Nat.sub(1n+a, 0n) == 1n+Nat.sub(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_succ(b: Nat, +a: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match b:
    case 0n:
      sub_succ0(a)
    case 1n+bp:
      match a:
        case 0n:
          Empty.absurd({Nat.sub(1n, 1n+bp) == 1n+Nat.sub(0n, 1n+bp) : Nat}, no_ft(h))
        case 1n+ap:
          sub_succ(bp, ap, h)

def le_du_step(w: Bool, +c: Char, +r: String, +ih: {Nat.is_le(String.length(L.drop_upper(r)), String.length(r)) == True{} : Bool})
  -> {Nat.is_le(String.length(L.pick(String, w, L.drop_upper(r), SCon{c, r})), 1n+String.length(r)) == True{} : Bool}:
  match w:
    case True{}:
      le_succ(String.length(L.drop_upper(r)), String.length(r), ih)
    case False{}:
      le_refl(String.length(r))

def le_du(s: String) -> {Nat.is_le(String.length(L.drop_upper(s)), String.length(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          le_du_step(L.is_upper(k), Chr{k}, r, le_du(r))

def swif_eq(b: Bool, +r: String) -> {String.starts_with.if(r, SNil{}, b) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.sym(Bool, True{}, String.starts_with(r, SNil{}), sw_nil(r))

def rs_pr(+j: U32, +h: {L.in_range32(j, 32, 126) == True{} : Bool}) -> {Tgt.is_re_space(j) == U32.is_eq(j, 32) : Bool}:
  %Equal.sym(Bool, U32.is_eq(j, 9), False{}, ne_of(x => L.in_range32(x, 32, 126), U32.is_eq(j, 9), j, 9, {==}, {==}, h))
    : {Bool.or(U32.is_eq(j, 32), Bool.or(_, Bool.or(U32.is_eq(j, 10), Bool.or(U32.is_eq(j, 12), U32.is_eq(j, 13))))) == U32.is_eq(j, 32) : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 10), False{}, ne_of(x => L.in_range32(x, 32, 126), U32.is_eq(j, 10), j, 10, {==}, {==}, h))
    : {Bool.or(U32.is_eq(j, 32), Bool.or(False{}, Bool.or(_, Bool.or(U32.is_eq(j, 12), U32.is_eq(j, 13))))) == U32.is_eq(j, 32) : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 12), False{}, ne_of(x => L.in_range32(x, 32, 126), U32.is_eq(j, 12), j, 12, {==}, {==}, h))
    : {Bool.or(U32.is_eq(j, 32), Bool.or(False{}, Bool.or(False{}, Bool.or(_, U32.is_eq(j, 13))))) == U32.is_eq(j, 32) : Bool}
  %Equal.sym(Bool, U32.is_eq(j, 13), False{}, ne_of(x => L.in_range32(x, 32, 126), U32.is_eq(j, 13), j, 13, {==}, {==}, h))
    : {Bool.or(U32.is_eq(j, 32), Bool.or(False{}, Bool.or(False{}, Bool.or(False{}, _)))) == U32.is_eq(j, 32) : Bool}
  or_ff(U32.is_eq(j, 32))

def xr_step(w: Bool, +j: U32, +r: String, +ew: {Tgt.is_upper(j) == w : Bool}, +hj: {L.in_range32(j, 32, 126) == True{} : Bool},
  +ih: {Bool.and(Nat.is_lt(Tgt.upper_run(r), String.length(r)), Tgt.is_re_space(Tgt.byte_at(r, Tgt.upper_run(r)))) == String.starts_with(L.drop_upper(r), " ") : Bool})
  -> {Bool.and(Nat.is_lt(Tgt.upper_run.go(SCon{Chr{j}, r}, w), 1n+String.length(r)), Tgt.is_re_space(Tgt.byte_at(SCon{Chr{j}, r}, Tgt.upper_run.go(SCon{Chr{j}, r}, w))))
      == String.starts_with(L.pick(String, w, L.drop_upper(r), SCon{Chr{j}, r}), " ") : Bool}:
  match w:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Tgt.is_re_space(j), U32.is_eq(j, 32), rs_pr(j, hj)) : {_ == String.starts_with.if(r, SNil{}, U32.is_eq(j, 32)) : Bool}
      Equal.sym(Bool, String.starts_with.if(r, SNil{}, U32.is_eq(j, 32)), U32.is_eq(j, 32), swif_eq(U32.is_eq(j, 32), r))

def xr(r: String, +h: {L.printable(r) == True{} : Bool})
  -> {Bool.and(Nat.is_lt(Tgt.upper_run(r), String.length(r)), Tgt.is_re_space(Tgt.byte_at(r, Tgt.upper_run(r)))) == String.starts_with(L.drop_upper(r), " ") : Bool}:
  match r:
    case SNil{}:
      {==}
    case SCon{c, +rr2}:
      match c:
        case Chr{+j}:
          xr_step(Tgt.is_upper(j), j, rr2, {==}, and_l(L.in_range32(j, 32, 126), L.printable(rr2), h), xr(rr2, and_r(L.in_range32(j, 32, 126), L.printable(rr2), h)))

def sm_step(w: Bool, +k: U32, +r: String, +hr: {L.printable(r) == True{} : Bool})
  -> {Tgt.starts_method.of(Tgt.upper_run.go(SCon{Chr{k}, r}, w), SCon{Chr{k}, r})
      == Bool.and(Bool.not(String.is_empty(String.take(SCon{Chr{k}, r}, Nat.sub(1n+String.length(r), String.length(L.pick(String, w, L.drop_upper(r), SCon{Chr{k}, r})))))),
           String.starts_with(L.pick(String, w, L.drop_upper(r), SCon{Chr{k}, r}), " ")) : Bool}:
  match w:
    case False{}:
      %Equal.sym(Nat, Nat.sub(String.length(r), String.length(r)), 0n, sub_self(String.length(r)))
        : {False{} == Bool.and(Bool.not(String.is_empty(String.take(SCon{Chr{k}, r}, _))), String.starts_with(SCon{Chr{k}, r}, " ")) : Bool}
      {==}
    case True{}:
      %Equal.sym(Nat, Nat.sub(1n+String.length(r), String.length(L.drop_upper(r))), 1n+Nat.sub(String.length(r), String.length(L.drop_upper(r))),
          sub_succ(String.length(L.drop_upper(r)), String.length(r), le_du(r)))
        : {Tgt.starts_method.of(1n+Tgt.upper_run(r), SCon{Chr{k}, r}) == Bool.and(Bool.not(String.is_empty(String.take(SCon{Chr{k}, r}, _))), String.starts_with(L.drop_upper(r), " ")) : Bool}
      xr(r, hr)

def smeq(tl: String, +h: {L.printable(tl) == True{} : Bool}) -> {Tgt.starts_method(tl) == L.starts_method(tl) : Bool}:
  match tl:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          sm_step(Tgt.is_upper(k), k, r, and_r(L.in_range32(k, 32, 126), L.printable(r), h))

def pr_nws(s: String, +hpr: {L.printable(s) == True{} : Bool}, +hns: {L.has_char(s, 32) == False{} : Bool}) -> {all_nws(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +hk = and_l(L.in_range32(k, 32, 126), L.printable(r), hpr)
          %Equal.sym(Bool, Tgt.is_ws(k), U32.is_eq(k, 32), ws_pr(k, hk)) : {Bool.and(Bool.not(_), all_nws(r)) == True{} : Bool}
          %Equal.sym(Bool, U32.is_eq(k, 32), False{}, or_f(U32.is_eq(k, 32), L.has_char(r, 32), hns)) : {Bool.and(Bool.not(_), all_nws(r)) == True{} : Bool}
          pr_nws(r, and_r(L.in_range32(k, 32, 126), L.printable(r), hpr), or_f2(U32.is_eq(k, 32), L.has_char(r, 32), hns))

def t_nws(a: String, +y: String, +h: {all_nws(a) == True{} : Bool}, +hne: {String.is_empty(a) == False{} : Bool})
  -> {String.append(a, y) == Tgt.trim_ws_l(String.append(a, y)) : String}:
  match a:
    case SNil{}:
      Empty.absurd({y == Tgt.trim_ws_l(y) : String}, no_tf(hne))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_ws(k), False{}, not_t(Tgt.is_ws(k), and_l(Bool.not(Tgt.is_ws(k)), all_nws(r), h)))
            : {SCon{Chr{k}, String.append(r, y)} == Tgt.trim_ws_l.go(SCon{Chr{k}, String.append(r, y)}, _) : String}
          {==}

def nav2_b(b: Bool, +v: String, +eb: {allws(v) == b : Bool}, +h: {String.is_empty(Tgt.trim_ws(v)) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(
        Equal.trans(Bool, True{}, String.is_empty(Tgt.trim_ws(v)), False{},
          Equal.cong(String, Bool, x => String.is_empty(Tgt.trim_ws_r(x)), SNil{}, Tgt.trim_ws_l(v), Equal.sym(String, Tgt.trim_ws_l(v), SNil{}, t_allws(v, eb))), h)))

def nav2(+v: String, +h: {String.is_empty(Tgt.trim_ws(v)) == False{} : Bool}) -> {allws(v) == False{} : Bool}:
  nav2_b(allws(v), v, {==}, h)

def t_nws1(s: String, +h: {all_nws(s) == True{} : Bool}) -> {s == Tgt.trim_ws_l(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Tgt.is_ws(k), False{}, not_t(Tgt.is_ws(k), and_l(Bool.not(Tgt.is_ws(k)), all_nws(r), h)))
            : {SCon{Chr{k}, r} == Tgt.trim_ws_l.go(SCon{Chr{k}, r}, _) : String}
          {==}

# a line of one token is a bad target
def e1_step(tok: String, +hns: {L.has_char(tok, 32) == False{} : Bool}, +hne: {String.is_empty(tok) == False{} : Bool},
  +hsw: {String.starts_with(tok, "#") == False{} : Bool})
  -> {Tgt.step(Tgt.SSeek{[]}, tok) == Tgt.SFail{"bad target: " ++ tok} : Tgt.St}:
  match tok:
    case SNil{}:
      Empty.absurd({Tgt.step(Tgt.SSeek{[]}, SNil{}) == Tgt.SFail{"bad target: " ++ SNil{}} : Tgt.St}, no_tf(hne))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, 35), False{}, swf(U32.is_eq(k, 35), r, hsw))
            : {Tgt.seek.of(Bool.or(False{}, _), SCon{Chr{k}, r}, []) == Tgt.SFail{"bad target: " ++ SCon{Chr{k}, r}} : Tgt.St}
          %Equal.sym(Bool, Tgt.has_char(SCon{Chr{k}, r}, 32), False{}, Equal.trans(Bool, Tgt.has_char(SCon{Chr{k}, r}, 32), L.has_char(SCon{Chr{k}, r}, 32), False{}, has_char_tg(SCon{Chr{k}, r}, 32), hns))
            : {Tgt.req_line(_, SCon{Chr{k}, r}, []) == Tgt.SFail{"bad target: " ++ SCon{Chr{k}, r}} : Tgt.St}
          {==}

def e1(+tok: String, +h0: {Bool.and(Bool.and(L.printable(tok), Bool.not(L.has_char(tok, 32))), Bool.and(Bool.not(String.is_empty(tok)), Bool.not(String.starts_with(tok, "#")))) == True{} : Bool})
  -> {Tgt.parse_all(tok ++ "\n") == Fail{"bad target: " ++ tok} : Result<&2, &2, String, List<&2, Tgt.Target>>}:
  +a1 = Bool.and(L.printable(tok), Bool.not(L.has_char(tok, 32)))
  +a2 = Bool.and(Bool.not(String.is_empty(tok)), Bool.not(String.starts_with(tok, "#")))
  +h1 = and_l(a1, a2, h0)
  +h2 = and_r(a1, a2, h0)
  +hpr = and_l(L.printable(tok), Bool.not(L.has_char(tok, 32)), h1)
  +hns = not_t(L.has_char(tok, 32), and_r(L.printable(tok), Bool.not(L.has_char(tok, 32)), h1))
  +hne = not_t(String.is_empty(tok), and_l(Bool.not(String.is_empty(tok)), Bool.not(String.starts_with(tok, "#")), h2))
  +hsw = not_t(String.starts_with(tok, "#"), and_r(Bool.not(String.is_empty(tok)), Bool.not(String.starts_with(tok, "#")), h2))
  +hnw = pr_nws(tok, hpr, hns)
  +s = String.append(tok, SCon{Chr{10}, SNil{}})
  %Equal.sym(Tgt.St, Tgt.run(s, lnz(Tgt.SSeek{[]})), Tgt.ln_end(feed(s, lnz(Tgt.SSeek{[]}))), run_feed(s, lnz(Tgt.SSeek{[]})))
    : {Tgt.finish(_) == Fail{"bad target: " ++ tok} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.Ln, feed(s, lnz(Tgt.SSeek{[]})), feed(SNil{}, lnz(Tgt.step(Tgt.SSeek{[]}, Tgt.trim_ws(tok)))), feed_nl2(tok, SNil{}, Tgt.SSeek{[]}, pr_no(tok, 10, {==}, hpr)))
    : {Tgt.finish(Tgt.ln_end(_)) == Fail{"bad target: " ++ tok} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %t_nws1(tok, hnw) : {Tgt.finish(Tgt.step(Tgt.step(Tgt.SSeek{[]}, Tgt.trim_ws_r(_)), SNil{})) == Fail{"bad target: " ++ tok} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %trr_id(tok, hnw) : {Tgt.finish(Tgt.step(Tgt.step(Tgt.SSeek{[]}, _), SNil{})) == Fail{"bad target: " ++ tok} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.step(Tgt.SSeek{[]}, tok), Tgt.SFail{"bad target: " ++ tok}, e1_step(tok, hns, hne, hsw))
    : {Tgt.finish(Tgt.step(_, SNil{})) == Fail{"bad target: " ++ tok} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  {==}

def nm_m_step(w: Bool, +k: U32, +r: String, +y: String, +ew: {Tgt.is_upper(k) == w : Bool},
  +hk: {L.in_range32(k, 32, 126) == True{} : Bool}, +hk32: {U32.is_eq(k, 32) == False{} : Bool},
  +hnu: {Bool.and(w, L.all_upper(r)) == False{} : Bool},
  ih: {L.all_upper(r) == False{} : Bool} -> {nm(String.append(r, y)) == True{} : Bool})
  -> {Tgt.pick(Bool, w, nm(String.append(r, y)), Bool.not(Tgt.is_re_space(k))) == True{} : Bool}:
  match w:
    case True{}:
      ih(hnu)
    case False{}:
      %Equal.sym(Bool, Tgt.is_re_space(k), U32.is_eq(k, 32), rs_pr(k, hk)) : {Bool.not(_) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(k, 32), False{}, hk32) : {Bool.not(_) == True{} : Bool}
      {==}

# a first token that is not all upper-case stops the method scan inside it
def nm_m(m: String, +y: String, +hpr: {L.printable(m) == True{} : Bool}, +hns: {L.has_char(m, 32) == False{} : Bool}, +hnu: {L.all_upper(m) == False{} : Bool})
  -> {nm(String.append(m, y)) == True{} : Bool}:
  match m:
    case SNil{}:
      Empty.absurd({nm(y) == True{} : Bool}, no_tf(hnu))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          nm_m_step(Tgt.is_upper(k), k, r, y, {==}, and_l(L.in_range32(k, 32, 126), L.printable(r), hpr), or_f(U32.is_eq(k, 32), L.has_char(r, 32), hns), hnu,
            hh => nm_m(r, y, and_r(L.in_range32(k, 32, 126), L.printable(r), hpr), or_f2(U32.is_eq(k, 32), L.has_char(r, 32), hns), hh))

def e2_step(m: String, +r2: String, +hpr: {L.printable(m) == True{} : Bool}, +hns: {L.has_char(m, 32) == False{} : Bool},
  +hnu: {L.all_upper(m) == False{} : Bool}, +hne: {String.is_empty(m) == False{} : Bool}, +hsw: {String.starts_with(m, "#") == False{} : Bool})
  -> {Tgt.step(Tgt.SSeek{[]}, String.append(m, SCon{Chr{32}, r2})) == Tgt.SFail{"bad method: " ++ m} : Tgt.St}:
  match m:
    case SNil{}:
      Empty.absurd({Tgt.step(Tgt.SSeek{[]}, SCon{Chr{32}, r2}) == Tgt.SFail{"bad method: " ++ SNil{}} : Tgt.St}, no_tf(hne))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          +mm = String.append(SCon{Chr{k}, SNil{}}, r)
          +l = String.append(mm, SCon{Chr{32}, r2})
          +hns2 = Equal.trans(Bool, Tgt.has_char(mm, 32), L.has_char(mm, 32), False{}, has_char_tg(mm, 32), hns)
          %Equal.sym(Bool, U32.is_eq(k, 35), False{}, swf(U32.is_eq(k, 35), r, hsw))
            : {Tgt.seek.of(Bool.or(False{}, _), l, []) == Tgt.SFail{"bad method: " ++ mm} : Tgt.St}
          %Equal.sym(Bool, Tgt.has_char(l, 32), True{}, hc_mid(mm, 32, r2))
            : {Tgt.req_line(_, l, []) == Tgt.SFail{"bad method: " ++ mm} : Tgt.St}
          %Equal.sym(Bool, Tgt.starts_method(l), False{}, nm_sm(l, nm_m(mm, SCon{Chr{32}, r2}, hpr, hns, hnu)))
            : {Tgt.req_line.meth(_, l, []) == Tgt.SFail{"bad method: " ++ mm} : Tgt.St}
          %bef_gen(mm, SCon{Chr{32}, r2}, 32, hns2)
            : {Tgt.SFail{"bad method: " ++ _} == Tgt.SFail{"bad method: " ++ mm} : Tgt.St}
          %app_nil(mm) : {Tgt.SFail{"bad method: " ++ _} == Tgt.SFail{"bad method: " ++ mm} : Tgt.St}
          {==}

def e2(+m: String, +rest: String,
  +h1: {Bool.and(Bool.and(L.printable(m), Bool.not(L.has_char(m, 32))), Bool.and(Bool.not(String.is_empty(m)), Bool.not(L.all_upper(m)))) == True{} : Bool},
  +h2: {Bool.and(Bool.and(L.printable(rest), Bool.not(String.is_empty(L.trim_ows(rest)))), Bool.not(String.starts_with(m, "#"))) == True{} : Bool})
  -> {Tgt.parse_all(m ++ " " ++ rest ++ "\n") == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}:
  +a1 = Bool.and(L.printable(m), Bool.not(L.has_char(m, 32)))
  +a2 = Bool.and(Bool.not(String.is_empty(m)), Bool.not(L.all_upper(m)))
  +b1 = Bool.and(L.printable(rest), Bool.not(String.is_empty(L.trim_ows(rest))))
  +g1 = and_l(a1, a2, h1)
  +g2 = and_r(a1, a2, h1)
  +k1 = and_l(b1, Bool.not(String.starts_with(m, "#")), h2)
  +hpr = and_l(L.printable(m), Bool.not(L.has_char(m, 32)), g1)
  +hns = not_t(L.has_char(m, 32), and_r(L.printable(m), Bool.not(L.has_char(m, 32)), g1))
  +hne = not_t(String.is_empty(m), and_l(Bool.not(String.is_empty(m)), Bool.not(L.all_upper(m)), g2))
  +hnu = not_t(L.all_upper(m), and_r(Bool.not(String.is_empty(m)), Bool.not(L.all_upper(m)), g2))
  +hsw = not_t(String.starts_with(m, "#"), and_r(b1, Bool.not(String.starts_with(m, "#")), h2))
  +hpr2 = and_l(L.printable(rest), Bool.not(String.is_empty(L.trim_ows(rest))), k1)
  +hte = Equal.trans(Bool, String.is_empty(Tgt.trim_ws(rest)), String.is_empty(L.trim_ows(rest)), False{},
    Equal.cong(String, Bool, x => String.is_empty(x), Tgt.trim_ws(rest), L.trim_ows(rest), Equal.sym(String, L.trim_ows(rest), Tgt.trim_ws(rest), ows(rest, hpr2))),
    not_t(String.is_empty(L.trim_ows(rest)), and_r(L.printable(rest), Bool.not(String.is_empty(L.trim_ows(rest))), k1)))
  +nar = nav2(rest, hte)
  +l = String.append(m, SCon{Chr{32}, rest})
  +s = String.append(l, SCon{Chr{10}, SNil{}})
  %app_assoc(m, SCon{Chr{32}, rest}, SCon{Chr{10}, SNil{}})
    : {Tgt.parse_all(_) == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.run(s, lnz(Tgt.SSeek{[]})), Tgt.ln_end(feed(s, lnz(Tgt.SSeek{[]}))), run_feed(s, lnz(Tgt.SSeek{[]})))
    : {Tgt.finish(_) == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.Ln, feed(s, lnz(Tgt.SSeek{[]})), feed(SNil{}, lnz(Tgt.step(Tgt.SSeek{[]}, Tgt.trim_ws(l)))),
      feed_nl2(l, SNil{}, Tgt.SSeek{[]}, hc_app(m, SCon{Chr{32}, rest}, 10, pr_no(m, 10, {==}, hpr), pr_no(rest, 10, {==}, hpr2))))
    : {Tgt.finish(Tgt.ln_end(_)) == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %t_nws(m, SCon{Chr{32}, rest}, pr_nws(m, hpr, hns), hne)
    : {Tgt.finish(Tgt.step(Tgt.step(Tgt.SSeek{[]}, Tgt.trim_ws_r(_)), SNil{})) == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %trr_app(m, SCon{Chr{32}, rest}, nar)
    : {Tgt.finish(Tgt.step(Tgt.step(Tgt.SSeek{[]}, _), SNil{})) == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %trr_app(SCon{Chr{32}, SNil{}}, rest, nar)
    : {Tgt.finish(Tgt.step(Tgt.step(Tgt.SSeek{[]}, String.append(m, _)), SNil{})) == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.step(Tgt.SSeek{[]}, String.append(m, SCon{Chr{32}, Tgt.trim_ws_r(rest)})), Tgt.SFail{"bad method: " ++ m},
      e2_step(m, Tgt.trim_ws_r(rest), hpr, hns, hnu, hne, hsw))
    : {Tgt.finish(Tgt.step(_, SNil{})) == Fail{"bad method: " ++ m} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  {==}

def hc_t_step(w: Bool, +k: U32, +r: String, +n: U32, +h: {Tgt.has_char(SCon{Chr{k}, r}, n) == False{} : Bool},
  ih: {Tgt.has_char(r, n) == False{} : Bool} -> {Tgt.has_char(Tgt.trim_ws_l(r), n) == False{} : Bool})
  -> {Tgt.has_char(Tgt.trim_ws_l.go(SCon{Chr{k}, r}, w), n) == False{} : Bool}:
  match w:
    case True{}:
      ih(hcf_r(k, r, n, h))
    case False{}:
      h

def hc_t(s: String, +n: U32, +h: {Tgt.has_char(s, n) == False{} : Bool}) -> {Tgt.has_char(Tgt.trim_ws_l(s), n) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          hc_t_step(Tgt.is_ws(k), k, r, n, h, hh => hc_t(r, n, hh))

def hc_trr_step(b: Bool, +k: U32, +r: String, +n: U32, +h: {Tgt.has_char(SCon{Chr{k}, r}, n) == False{} : Bool},
  +ih: {Tgt.has_char(Tgt.trim_ws_r(r), n) == False{} : Bool})
  -> {Tgt.has_char(Tgt.pick(String, b, SNil{}, SCon{Chr{k}, Tgt.trim_ws_r(r)}), n) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(k, n), False{}, hcf_l(k, r, n, h))
        : {Tgt.has_char.go(SCon{Chr{k}, Tgt.trim_ws_r(r)}, n, _) == False{} : Bool}
      ih

def hc_trr(s: String, +n: U32, +h: {Tgt.has_char(s, n) == False{} : Bool}) -> {Tgt.has_char(Tgt.trim_ws_r(s), n) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          hc_trr_step(Bool.and(String.is_empty(Tgt.trim_ws_r(r)), Tgt.is_ws(k)), k, r, n, h, hc_trr(r, n, hcf_r(k, r, n, h)))

def pr_trim(+l: String, +h: {L.printable(l) == True{} : Bool}) -> {L.printable(Tgt.trim_ws(l)) == True{} : Bool}:
  +tl = Tgt.trim_ws_l(l)
  +ht = pr_t(l, h)
  %Equal.sym(String, Tgt.trim_ws_r(tl), String.reverse(Tgt.trim_ws_l(String.reverse(tl))), trr_rtr(tl)) : {L.printable(_) == True{} : Bool}
  pr_rev(Tgt.trim_ws_l(String.reverse(tl)), SNil{}, pr_t(String.reverse(tl), pr_rev(tl, SNil{}, ht, {==})), {==})

def e3_step(tl: String, +t: Tgt.Target, +acc: List<&2, Tgt.Target>,
  +hne: {String.is_empty(tl) == False{} : Bool}, +h35: {String.starts_with(tl, "#") == False{} : Bool},
  +h64: {String.starts_with(tl, "@") == False{} : Bool}, +h58: {Tgt.has_char(tl, 58) == False{} : Bool})
  -> {Tgt.hdr(tl, t, acc) == Tgt.SFail{"bad header: " ++ tl} : Tgt.St}:
  match tl:
    case SNil{}:
      Empty.absurd({Tgt.hdr(SNil{}, t, acc) == Tgt.SFail{"bad header: " ++ SNil{}} : Tgt.St}, no_tf(hne))
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, 35), False{}, swf(U32.is_eq(k, 35), r, h35))
            : {Tgt.hdr.comment(_, SCon{Chr{k}, r}, t, acc) == Tgt.SFail{"bad header: " ++ SCon{Chr{k}, r}} : Tgt.St}
          %Equal.sym(Bool, U32.is_eq(k, 64), False{}, swf(U32.is_eq(k, 64), r, h64))
            : {Tgt.hdr.body(_, SCon{Chr{k}, r}, t, acc) == Tgt.SFail{"bad header: " ++ SCon{Chr{k}, r}} : Tgt.St}
          %Equal.sym(Bool, Tgt.has_char(SCon{Chr{k}, r}, 58), False{}, h58)
            : {Tgt.hdr.colon(_, SCon{Chr{k}, r}, t, acc) == Tgt.SFail{"bad header: " ++ SCon{Chr{k}, r}} : Tgt.St}
          {==}

def mkn(+m: String, +u: String, +hs: List<&2, Hdr.Header>) -> Tgt.Target:
  Tgt.Target{m, u, hs, None{}}

def e3_none(+m: String, +u: String, +hs: List<&2, Hdr.Header>, +l: String,
  +ht: {L.target_ok(Tgt.Target{m, u, hs, None{}}) == True{} : Bool},
  +h4: {Bool.and(Bool.and(L.printable(l), Bool.not(L.has_char(l, 58))), Bool.and(Bool.not(String.is_empty(L.trim_ows(l))),
     Bool.not(Bool.or(Bool.or(String.starts_with(L.trim_ows(l), "#"), String.starts_with(L.trim_ows(l), "@")), L.starts_method(L.trim_ows(l)))))) == True{} : Bool})
  -> {Tgt.parse_all(L.target_text(Tgt.Target{m, u, hs, None{}}) ++ l ++ "\n") == Fail{"bad header: " ++ L.trim_ows(l)} : Result<&2, &2, String, List<&2, Tgt.Target>>}:
  +to = L.trim_ows(l)
  +a1 = Bool.and(L.printable(l), Bool.not(L.has_char(l, 58)))
  +o3 = Bool.or(Bool.or(String.starts_with(to, "#"), String.starts_with(to, "@")), L.starts_method(to))
  +a2 = Bool.and(Bool.not(String.is_empty(to)), Bool.not(o3))
  +g1 = and_l(a1, a2, h4)
  +g2 = and_r(a1, a2, h4)
  +hpr = and_l(L.printable(l), Bool.not(L.has_char(l, 58)), g1)
  +h58 = not_t(L.has_char(l, 58), and_r(L.printable(l), Bool.not(L.has_char(l, 58)), g1))
  +hte = not_t(String.is_empty(to), and_l(Bool.not(String.is_empty(to)), Bool.not(o3), g2))
  +hor = not_t(o3, and_r(Bool.not(String.is_empty(to)), Bool.not(o3), g2))
  +hor2 = or_f(Bool.or(String.starts_with(to, "#"), String.starts_with(to, "@")), L.starts_method(to), hor)
  +hsmL = or_f2(Bool.or(String.starts_with(to, "#"), String.starts_with(to, "@")), L.starts_method(to), hor)
  +tl = Tgt.trim_ws(l)
  +eo = ows(l, hpr)
  +hne = Equal.trans(Bool, String.is_empty(tl), String.is_empty(to), False{}, Equal.cong(String, Bool, x => String.is_empty(x), tl, to, Equal.sym(String, to, tl, eo)), hte)
  +h35 = Equal.trans(Bool, String.starts_with(tl, "#"), String.starts_with(to, "#"), False{}, Equal.cong(String, Bool, x => String.starts_with(x, "#"), tl, to, Equal.sym(String, to, tl, eo)),
    or_f(String.starts_with(to, "#"), String.starts_with(to, "@"), hor2))
  +h64 = Equal.trans(Bool, String.starts_with(tl, "@"), String.starts_with(to, "@"), False{}, Equal.cong(String, Bool, x => String.starts_with(x, "@"), tl, to, Equal.sym(String, to, tl, eo)),
    or_f2(String.starts_with(to, "#"), String.starts_with(to, "@"), hor2))
  +hsm = Equal.trans(Bool, Tgt.starts_method(tl), L.starts_method(tl), False{}, smeq(tl, pr_trim(l, hpr)),
    Equal.trans(Bool, L.starts_method(tl), L.starts_method(to), False{}, Equal.cong(String, Bool, x => L.starts_method(x), tl, to, Equal.sym(String, to, tl, eo)), hsmL))
  +hc = hc_trr(Tgt.trim_ws_l(l), 58, hc_t(l, 58, Equal.trans(Bool, Tgt.has_char(l, 58), L.has_char(l, 58), False{}, has_char_tg(l, 58), h58)))
  +t = mkn(m, u, hs)
  +tt = L.target_text(t)
  +y = String.append(l, SCon{Chr{10}, SNil{}})
  +s = String.append(tt, y)
  +p = ph(hs, True{})
  %Equal.sym(String, to, tl, eo) : {Tgt.parse_all(s) == Fail{"bad header: " ++ _} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.run(s, lnz(Tgt.SSeek{[]})), Tgt.ln_end(feed(s, lnz(Tgt.SSeek{[]}))), run_feed(s, lnz(Tgt.SSeek{[]})))
    : {Tgt.finish(_) == Fail{"bad header: " ++ tl} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.Ln, feed(s, lnz(Tgt.SSeek{[]})), feed(y, feed(tt, lnz(Tgt.SSeek{[]}))), feed_app(tt, y, lnz(Tgt.SSeek{[]})))
    : {Tgt.finish(Tgt.ln_end(_)) == Fail{"bad header: " ++ tl} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.Ln, feed(tt, lnz(Tgt.SSeek{[]})), lnz(bst(None{}, p, t, [])), tgt_core(m, u, hs, None{}, [], ht))
    : {Tgt.finish(Tgt.ln_end(feed(y, _))) == Fail{"bad header: " ++ tl} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.Ln, feed(y, lnz(mk(p, t, []))), feed(SNil{}, lnz(Tgt.step(mk(p, t, []), tl))), feed_nl2(l, SNil{}, mk(p, t, []), pr_no(l, 10, {==}, hpr)))
    : {Tgt.finish(Tgt.ln_end(_)) == Fail{"bad header: " ++ tl} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.step(mk(p, t, []), tl), Tgt.hdr(tl, t, []), step_mk(p, t, [], tl, hne, hsm))
    : {Tgt.finish(Tgt.step(_, SNil{})) == Fail{"bad header: " ++ tl} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  %Equal.sym(Tgt.St, Tgt.hdr(tl, t, []), Tgt.SFail{"bad header: " ++ tl}, e3_step(tl, t, [], hne, h35, h64, hc))
    : {Tgt.finish(Tgt.step(_, SNil{})) == Fail{"bad header: " ++ tl} : Result<&2, &2, String, List<&2, Tgt.Target>>}
  {==}

def e3(t: Tgt.Target, +l: String,
  +h3: {Bool.and(L.target_ok(t), Maybe.is_none(&2, String, L.tgt_body(t))) == True{} : Bool},
  +h4: {Bool.and(Bool.and(L.printable(l), Bool.not(L.has_char(l, 58))), Bool.and(Bool.not(String.is_empty(L.trim_ows(l))),
     Bool.not(Bool.or(Bool.or(String.starts_with(L.trim_ows(l), "#"), String.starts_with(L.trim_ows(l), "@")), L.starts_method(L.trim_ows(l)))))) == True{} : Bool})
  -> {Tgt.parse_all(L.target_text(t) ++ l ++ "\n") == Fail{"bad header: " ++ L.trim_ows(l)} : Result<&2, &2, String, List<&2, Tgt.Target>>}:
  match t:
    case Tgt.Target{+m, +u, +hs, b}:
      match b:
        case None{}:
          e3_none(m, u, hs, l, and_l(L.target_ok(Tgt.Target{m, u, hs, None{}}), True{}, h3), h4)
        case Some{q}:
          Empty.absurd({Tgt.parse_all(L.target_text(Tgt.Target{m, u, hs, Some{q}}) ++ l ++ "\n") == Fail{"bad header: " ++ L.trim_ows(l)} : Result<&2, &2, String, List<&2, Tgt.Target>>},
            no_ft(Equal.trans(Bool, False{}, Bool.and(L.target_ok(Tgt.Target{m, u, hs, Some{q}}), False{}), True{}, and_f(L.target_ok(Tgt.Target{m, u, hs, Some{q}})), h3)))

def L.targets_errors(tok, m, rest, t, l, h0, h1, h2, h3, h4):
  (e1(tok, h0), (e2(m, rest, h1, h2), e3(t, l, h3, h4)))

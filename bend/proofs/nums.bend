# Laws with big closed constants (report_text, report_hist,
# civil_unix_nanos, met_floats), and the
# lemmas that carry 10^9-sized constants symbolically (shift, pad_dw,
# pad9_len).
#
# The checker compares by weak head normal form and has no native
# arithmetic: a Nat literal is one node, equal to the same literal in one
# step, but anything that computes with it (Nat.mul, Nat.div, Big.of, a
# comparison against a computed Nat) walks it one unit at a time. Two
# copies of one closed term (lib's and LAWS') are separate objects, so
# comparing them evaluates both. So:
# - a big literal must only ever be passed along, or compared with the
#   same literal, inside a call stuck on a variable;
# - a closed constant that is compared must be cheap to evaluate: lib's
#   F64.of_big takes an exact path for Bigs of up to three limbs, so
#   F64.of_nat(100n) is F64{25, 2, False} in a few steps (round's 2^30
#   steps never finished);
# - a fact that depends on a big literal's value (10^9 has nine zeros)
#   costs as many steps as the value, so no proof can check it: prove it
#   for pow10(k) with k a variable, and meet the literal only through an
#   equation that rewrites it in one step.
import Base
import ../LAWS.bend as L
import ../lib/dec.bend as Dec
import ../lib/big.bend as Big
import ../lib/f64.bend as F64
import ../lib/dur.bend as Dur
import ../lib/report.bend as Rep
import ../lib/metrics.bend as Met
import ../lib/tab.bend as Tab
import ../lib/civil.bend as Civil
import ../lib/hit.bend as Hit
import ./metrics.bend as PMet
import ./big.bend as PBig
import ./nat.bend as PNat

# ---------------------------------------------------------------------
# report_text
# ---------------------------------------------------------------------

def cong2(f: String -> String -> String, -a1: String, -a2: String, -b1: String, -b2: String, e1: {a1 == a2 : String}, e2: {b1 == b2 : String})
  -> {f(a1, b1) == f(a2, b2) : String}:
  %e1 : {f(a1, b1) == f(_, b2) : String}
  %e2 : {f(a1, b1) == f(a1, _) : String}
  {==}

def code_items_same(cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>) -> {Rep.code_items(cs) == L.code_items(cs) : String}:
  match cs:
    case Nil{}:
      {==}
    case Con{p, +rest}:
      match p:
        case (k, v):
          %code_items_same(rest) : {Rep.code_items(Con{(k, v), rest}) == Dec.show(k) ++ ":" ++ Dec.show(v) ++ "  " ++ _ : String}
          {==}

def error_lines_same(es: List<&2, String>) -> {Rep.error_lines(es) == L.error_lines(es) : String}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      %error_lines_same(rest) : {Rep.error_lines(Con{e, rest}) == e ++ "\n" ++ _ : String}
      {==}

def codes_text_same(+cs: List<&2, Sigma<&2, &2, Nat, _ => Nat>>)
  -> {Rep.code_items(Rep.codes_by_text(cs)) == L.code_items(L.codes_by_text(cs)) : String}:
  %PMet.by_text_same(cs) : {Rep.code_items(Rep.codes_by_text(cs)) == L.code_items(_) : String}
  code_items_same(Rep.codes_by_text(cs))

# LAWS' text_src with the status codes and the errors as holes
def ttpl(+s: Met.Summary, codes: String, errs: String) -> String:
  "Requests\t[total, rate, throughput]\t" ++ Dec.show(L.s_requests(s)) ++ ", " ++ L.fixed2(L.s_rate(s)) ++ ", " ++ L.fixed2(L.s_throughput(s)) ++ "\n"
  ++ "Duration\t[total, attack, wait]\t" ++ L.dur(Nat.add(L.s_duration(s), L.s_wait(s))) ++ ", " ++ L.dur(L.s_duration(s)) ++ ", " ++ L.dur(L.s_wait(s)) ++ "\n"
  ++ "Latencies\t[min, mean, 50, 90, 95, 99, max]\t" ++ L.dur(L.s_lat_min(s)) ++ ", " ++ L.dur(L.s_lat_mean(s)) ++ ", " ++ L.dur(L.s_p50(s)) ++ ", "
     ++ L.dur(L.s_p90(s)) ++ ", " ++ L.dur(L.s_p95(s)) ++ ", " ++ L.dur(L.s_p99(s)) ++ ", " ++ L.dur(L.s_lat_max(s)) ++ "\n"
  ++ "Bytes In\t[total, mean]\t" ++ Big.show(L.s_bytes_in(s)) ++ ", " ++ L.fixed2(L.s_in_mean(s)) ++ "\n"
  ++ "Bytes Out\t[total, mean]\t" ++ Big.show(L.s_bytes_out(s)) ++ ", " ++ L.fixed2(L.s_out_mean(s)) ++ "\n"
  ++ "Success\t[ratio]\t" ++ L.fixed2(F64.mul(L.s_ratio(s), F64.of_nat(100n))) ++ "%\n"
  ++ "Status Codes\t[code:count]\t" ++ codes ++ "\nError Set:\n" ++ errs

def L.report_text(s):
  match s:
    case Met.Summary{+req, +ok, +cs, +es, +lt, +lm, +lmin, +lmax, +p50, +p90, +p95, +p99, +bi, +bo, +im, +om, +rate, +thr, +ratio, +e, +l, +n, +du, +w, +b, +h}:
      +S = {Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, h} : Met.Summary}
      cong2(u => m => Tab.render(ttpl(S, u, m)), Rep.code_items(Rep.codes_by_text(cs)), L.code_items(L.codes_by_text(cs)),
        Rep.error_lines(es), L.error_lines(es), codes_text_same(cs), error_lines_same(es))

# ---------------------------------------------------------------------
# report_hist
# ---------------------------------------------------------------------

# LAWS' row with the rows after as a hole
def row(+b: Nat, +cs: List<&2, Nat>, +total: Nat, up: String, more: String) -> String:
  +n = L.head_or(0n, cs)
  +ratio = F64.div(F64.of_nat(n), F64.of_nat(total))
  "[" ++ Dur.show(b) ++ ",\t" ++ up ++ "]\t"
    ++ Dec.show(n) ++ "\t" ++ L.fixed2(F64.mul(ratio, F64.of_nat(100n))) ++ "%\t"
    ++ String.repeat("#", F64.trunc(F64.mul(ratio, F64.of_nat(75n)))) ++ "\n"
    ++ more

def upper_same(bs: List<&2, Nat>) -> {Rep.upper_bound(bs) == L.upper_bound(bs) : String}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      {==}

# one row each side, its upper bound and the rows after it as holes (a
# row's text holds nested F64 steps: each comparison of one costs ~1 s)
def rows_same(bs: List<&2, Nat>, +cs: List<&2, Nat>, +total: Nat) -> {Rep.hist_rows(bs, cs, total) == L.hist_rows(bs, cs, total) : String}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      cong2(u => m => row(b, cs, total, u, m), Rep.upper_bound(rest), L.upper_bound(rest),
        Rep.hist_rows(rest, List.drop(&2, Nat, cs, 1n), total), L.hist_rows(rest, List.drop(&2, Nat, cs, 1n), total),
        upper_same(rest), rows_same(rest, List.drop(&2, Nat, cs, 1n), total))

def L.report_hist(s, h):
  match s:
    case Met.Summary{+req, +ok, +cs, +es, +lt, +lm, +lmin, +lmax, +p50, +p90, +p95, +p99, +bi, +bo, +im, +om, +rate, +thr, +ratio, +e, +l, +n, +du, +w, +b, +hi}:
      %rows_same(b, hi, req) : {Rep.hist(Met.Summary{req, ok, cs, es, lt, lm, lmin, lmax, p50, p90, p95, p99, bi, bo, im, om, rate, thr, ratio, e, l, n, du, w, b, hi})
        == Tab.render("Bucket\t\t#\t%\tHistogram\n" ++ _) : String}
      {==}

# ---------------------------------------------------------------------
# Decimal text of s 10^k + n: the technique for 10^9-sized constants.
# A literal's value is out of reach, so a law about 10^9 is proved for
# pow10(k) with k a variable (these lemmas), and meets the literal only
# through an equation (a hypothesis {sec() == pow10(k)}), which rewrites
# the literal in one step.
# ---------------------------------------------------------------------

# the k low digits of n, zero-filled
def dw(j: Nat, +n: Nat) -> String:
  match j:
    case 0n:
      ""
    case 1n++i:
      String.append(dw(i, Nat.div(n, 10n)), SCon{Dec.digit_chr(Nat.mod(n, 10n)), SNil{}})

def app_nil(a: String) -> {String.append(a, "") == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %app_nil(t) : {SCon{c, String.append(t, "")} == SCon{c, _} : String}
      {==}

def app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %app_assoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

def len_snoc(a: String, -c: Char) -> {String.length(String.append(a, SCon{c, SNil{}})) == 1n+String.length(a) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %len_snoc(t, c) : {1n+String.length(String.append(t, SCon{c, SNil{}})) == 1n+_ : Nat}
      {==}

def rep_snoc(i: Nat) -> {String.append(String.repeat("0", i), "0") == String.append("0", String.repeat("0", i)) : String}:
  match i:
    case 0n:
      {==}
    case 1n++p:
      %rep_snoc(p) : {SCon{'0', String.append(String.repeat("0", p), "0")} == SCon{'0', _} : String}
      {==}

def dw_zero(j: Nat) -> {dw(j, 0n) == String.repeat("0", j) : String}:
  match j:
    case 0n:
      {==}
    case 1n++i:
      %Equal.sym(String, dw(i, 0n), String.repeat("0", i), dw_zero(i)) : {String.append(_, "0") == String.append("0", String.repeat("0", i)) : String}
      rep_snoc(i)

def gt_add_l(x: Nat, -y: Nat, +h: {Nat.is_gt(x, 0n) == True{} : Bool}) -> {Nat.is_gt(Nat.add(x, y), 0n) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_gt(y, 0n) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n++p:
      {==}

def pow_pos(j: Nat) -> {Nat.is_gt(Nat.pow(10n, j), 0n) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n++i:
      gt_add_l(Nat.pow(10n, i), Nat.mul(9n, Nat.pow(10n, i)), pow_pos(i))

def mul_pos(s: Nat, +p: Nat, +hs: {Nat.is_gt(s, 0n) == True{} : Bool}, +hp: {Nat.is_gt(p, 0n) == True{} : Bool})
  -> {Nat.is_gt(Nat.mul(s, p), 0n) == True{} : Bool}:
  match s:
    case 0n:
      Empty.absurd({Nat.is_gt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(hs))
    case 1n++q:
      gt_add_l(p, Nat.mul(q, p), hp)

# n < 1 + m: n / (1 + m) is 0 and n mod (1 + m) is n
def dm_small(n: Nat, m: Nat, +d: Nat, +r: Nat, +h: {Nat.is_lt(n, 1n+m) == True{} : Bool})
  -> {Nat.divmod.go(n, m, d, r) == (d, Nat.add(n, r)) : Nat & Nat}:
  match n:
    case 0n:
      {==}
    case 1n++np:
      match m:
        case 0n:
          Empty.absurd({Nat.divmod.go(1n+np, 0n, d, r) == (d, Nat.add(1n+np, r)) : Nat & Nat}, PNat.lt_zero(np, h))
        case 1n++mp:
          %Equal.sym(Nat, 1n+Nat.add(np, r), Nat.add(np, 1n+r), PNat.add_succ(np, r)) : {Nat.divmod.go(np, mp, d, 1n+r) == (d, _) : Nat & Nat}
          dm_small(np, mp, d, 1n+r, h)

def div_small(+n: Nat, +m: Nat, +h: {Nat.is_lt(n, 1n+m) == True{} : Bool}) -> {Nat.div(n, 1n+m) == 0n : Nat}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(n, m, 0n, 0n), (0n, Nat.add(n, 0n)), dm_small(n, m, 0n, 0n, h)) : {Nat.div.fin(_) == 0n : Nat}
  {==}

def mod_small(+n: Nat, +m: Nat, +h: {Nat.is_lt(n, 1n+m) == True{} : Bool}) -> {Nat.mod(n, 1n+m) == n : Nat}:
  %Equal.sym(Nat & Nat, Nat.divmod.go(n, m, 0n, 0n), (0n, Nat.add(n, 0n)), dm_small(n, m, 0n, 0n, h)) : {Nat.mod.fin(_) == n : Nat}
  Equal.sym(Nat, n, Nat.add(n, 0n), PNat.add_zero(n))

# r + 10 q (q > 0, r < 10) is q's digits, then r
def snoc(+q: Nat, +r: Nat, +hr: {Nat.is_lt(r, 10n) == True{} : Bool}, +hq: {Nat.is_gt(q, 0n) == True{} : Bool})
  -> {Dec.show(Nat.add(r, Nat.mul(10n, q))) == String.append(Dec.show(q), SCon{Dec.digit_chr(r), SNil{}}) : String}:
  +m = Nat.add(r, Nat.mul(10n, q))
  +a = {SCon{Dec.digit_chr(r), SNil{}} : String}
  +f1 = PBig.fuel(m, Nat.add(1n+q, m), m, "", PBig.le_refl(m), PBig.le_add_l(m, 1n+q))
  +s1 = PBig.show_step(Nat.add(1n+q, m), m, q, r, "", {==}, hr, hq)
  +lq = PBig.le_rw_r(q, Nat.add(m, q), Nat.add(q, m), PNat.add_comm(m, q), PBig.le_add_l(q, m))
  +f2 = PBig.fuel(Nat.add(q, m), q, q, a, lq, PBig.le_refl(q))
  +ga = PBig.go_app(1n+q, False{}, q, "", a)
  Equal.trans(String, Dec.show(m), Dec.show.go(1n+Nat.add(1n+q, m), False{}, m, ""), String.append(Dec.show(q), a), f1,
    Equal.trans(String, Dec.show.go(1n+Nat.add(1n+q, m), False{}, m, ""), Dec.show.go(Nat.add(1n+q, m), False{}, q, a), String.append(Dec.show(q), a), s1,
      Equal.trans(String, Dec.show.go(1n+Nat.add(q, m), False{}, q, a), Dec.show.go(1n+q, False{}, q, a), String.append(Dec.show(q), a), f2,
        Equal.sym(String, String.append(Dec.show(q), a), Dec.show.go(1n+q, False{}, q, a), ga))))

# s (10 P) + n == n mod 10 + 10 (s P + n / 10)
def split10(+s: Nat, +p: Nat, +n: Nat)
  -> {Nat.add(Nat.mul(s, Nat.mul(10n, p)), n) == Nat.add(Nat.mod(n, 10n), Nat.mul(10n, Nat.add(Nat.mul(s, p), Nat.div(n, 10n)))) : Nat}:
  +a = Nat.mul(s, p)
  +b = Nat.div(n, 10n)
  +r = Nat.mod(n, 10n)
  +rhs = Nat.add(r, Nat.mul(10n, Nat.add(a, b)))
  %PBig.recomb(n, 9n) : {Nat.add(Nat.mul(s, Nat.mul(10n, p)), _) == rhs : Nat}
  %PBig.mul_assoc(s, 10n, p) : {Nat.add(_, Nat.add(r, Nat.mul(10n, b))) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(s, 10n), Nat.mul(10n, s), PNat.mul_comm(s, 10n)) : {Nat.add(Nat.mul(_, p), Nat.add(r, Nat.mul(10n, b))) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(10n, s), p), Nat.mul(10n, a), PBig.mul_assoc(10n, s, p)) : {Nat.add(_, Nat.add(r, Nat.mul(10n, b))) == rhs : Nat}
  %Equal.sym(Nat, Nat.mul(10n, Nat.add(a, b)), Nat.add(Nat.mul(10n, a), Nat.mul(10n, b)), PBig.mul_dist_l(10n, a, b))
    : {Nat.add(Nat.mul(10n, a), Nat.add(r, Nat.mul(10n, b))) == Nat.add(r, _) : Nat}
  PNat.add_swap(Nat.mul(10n, a), r, Nat.mul(10n, b))

# the text of s 10^j + n (s > 0, n < 10^j) is s's, then n's j low digits
def shift(j: Nat, +s: Nat, +n: Nat, +hs: {Nat.is_gt(s, 0n) == True{} : Bool}, +hn: {Nat.is_lt(n, Nat.pow(10n, j)) == True{} : Bool})
  -> {Dec.show(Nat.add(Nat.mul(s, Nat.pow(10n, j)), n)) == String.append(Dec.show(s), dw(j, n)) : String}:
  match j:
    case 0n:
      match n:
        case 0n:
          %Equal.sym(Nat, Nat.mul(s, 1n), s, PBig.mul_one(s)) : {Dec.show(Nat.add(_, 0n)) == String.append(Dec.show(s), "") : String}
          %PNat.add_zero(s) : {Dec.show(_) == String.append(Dec.show(s), "") : String}
          Equal.sym(String, String.append(Dec.show(s), ""), Dec.show(s), app_nil(Dec.show(s)))
        case 1n++np:
          Empty.absurd({Dec.show(Nat.add(Nat.mul(s, 1n), 1n+np)) == String.append(Dec.show(s), "") : String}, PNat.lt_zero(np, hn))
    case 1n++i:
      +p = Nat.pow(10n, i)
      +q = Nat.add(Nat.mul(s, p), Nat.div(n, 10n))
      +r = Nat.mod(n, 10n)
      +d = {SCon{Dec.digit_chr(r), SNil{}} : String}
      +w = dw(i, Nat.div(n, 10n))
      +rhs = String.append(Dec.show(s), String.append(w, d))
      +hq = gt_add_l(Nat.mul(s, p), Nat.div(n, 10n), mul_pos(s, p, hs, pow_pos(i)))
      %Equal.sym(Nat, Nat.add(Nat.mul(s, Nat.mul(10n, p)), n), Nat.add(r, Nat.mul(10n, q)), split10(s, p, n))
        : {Dec.show(_) == rhs : String}
      %Equal.sym(String, Dec.show(Nat.add(r, Nat.mul(10n, q))), String.append(Dec.show(q), d), snoc(q, r, PNat.mod_lt(n, 9n), hq)) : {_ == rhs : String}
      %Equal.sym(String, Dec.show(q), String.append(Dec.show(s), w), shift(i, s, Nat.div(n, 10n), hs, PBig.dbound(n, p, hn))) : {String.append(_, d) == rhs : String}
      app_assoc(Dec.show(s), w, d)

def go_true(f: Nat, +m: Nat, +acc: String) -> {Dec.show.go(f, True{}, m, acc) == acc : String}:
  match f:
    case 0n:
      {==}
    case 1n++g:
      {==}

def show_lt10(+n: Nat, +h: {Nat.is_lt(n, 10n) == True{} : Bool}) -> {Dec.show(n) == SCon{Dec.digit_chr(Nat.mod(n, 10n)), SNil{}} : String}:
  +a = {SCon{Dec.digit_chr(Nat.mod(n, 10n)), SNil{}} : String}
  %Equal.sym(Bool, Nat.is_lt(n, 10n), True{}, h) : {Dec.show.go(n, _, Nat.div(n, 10n), a) == a : String}
  go_true(n, Nat.div(n, 10n), a)

# n >= 10: n / 10 > 0
def qpos(q: Nat, +n: Nat, +e: {Nat.add(Nat.mod(n, 10n), Nat.mul(10n, q)) == n : Nat}, +hl: {False{} == Nat.is_lt(n, 10n) : Bool})
  -> {Nat.is_gt(q, 0n) == True{} : Bool}:
  match q:
    case 0n:
      +r = Nat.mod(n, 10n)
      +e2 = Equal.trans(Nat, r, Nat.add(r, 0n), n, PNat.add_zero(r), e)
      +lt = Equal.trans(Bool, Nat.is_lt(n, 10n), Nat.is_lt(r, 10n), True{},
        Equal.cong(Nat, Bool, x => Nat.is_lt(x, 10n), n, r, Equal.sym(Nat, r, n, e2)), PNat.mod_lt(n, 9n))
      Empty.absurd({Nat.is_gt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(n, 10n), True{}, hl, lt)))
    case 1n++p:
      {==}

def pad_of(c: Bool, +i: Nat, +n: Nat, +hc: {c == Nat.is_lt(n, 10n) : Bool},
  +ih: {Dec.pad(1n+i, Nat.div(n, 10n)) == dw(1n+i, Nat.div(n, 10n)) : String})
  -> {Dec.pad(2n+i, n) == dw(2n+i, n) : String}:
  match c:
    case True{}:
      +d = {SCon{Dec.digit_chr(Nat.mod(n, 10n)), SNil{}} : String}
      +h = Equal.sym(Bool, True{}, Nat.is_lt(n, 10n), hc)
      %Equal.sym(String, Dec.show(n), d, show_lt10(n, h))
        : {String.append(String.repeat("0", Nat.sub(2n+i, String.length(_))), _) == dw(2n+i, n) : String}
      %Equal.sym(Nat, Nat.div(n, 10n), 0n, div_small(n, 9n, h)) : {String.append(String.repeat("0", 1n+i), d) == String.append(dw(1n+i, _), d) : String}
      %Equal.sym(String, dw(1n+i, 0n), String.repeat("0", 1n+i), dw_zero(1n+i)) : {String.append(String.repeat("0", 1n+i), d) == String.append(_, d) : String}
      {==}
    case False{}:
      +d = {SCon{Dec.digit_chr(Nat.mod(n, 10n)), SNil{}} : String}
      +q = Nat.div(n, 10n)
      +sq = Dec.show(q)
      +y = String.append(sq, d)
      +er = PBig.recomb(n, 9n)
      +yy = Nat.add(Nat.mod(n, 10n), Nat.mul(10n, q))
      +sn = Equal.trans(String, Dec.show(n), Dec.show(yy), y, Equal.cong(Nat, String, x => Dec.show(x), n, yy, Equal.sym(Nat, yy, n, er)),
        snoc(q, Nat.mod(n, 10n), PNat.mod_lt(n, 9n), qpos(q, n, er, hc)))
      %Equal.sym(String, Dec.show(n), y, sn) : {String.append(String.repeat("0", Nat.sub(2n+i, String.length(_))), _) == dw(2n+i, n) : String}
      %Equal.sym(Nat, String.length(y), 1n+String.length(sq), len_snoc(sq, Dec.digit_chr(Nat.mod(n, 10n))))
        : {String.append(String.repeat("0", Nat.sub(2n+i, _)), y) == dw(2n+i, n) : String}
      %app_assoc(String.repeat("0", Nat.sub(1n+i, String.length(sq))), sq, d) : {_ == dw(2n+i, n) : String}
      %Equal.sym(String, Dec.pad(1n+i, q), dw(1n+i, q), ih) : {String.append(_, d) == dw(2n+i, n) : String}
      {==}

# n < 10^(1+j): pad(1 + j, n) is n's 1 + j low digits
def pad_dw(j: Nat, +n: Nat, +hn: {Nat.is_lt(n, Nat.pow(10n, 1n+j)) == True{} : Bool}) -> {Dec.pad(1n+j, n) == dw(1n+j, n) : String}:
  match j:
    case 0n:
      %Equal.sym(String, Dec.show(n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), SNil{}}, show_lt10(n, hn))
        : {String.append(String.repeat("0", Nat.sub(1n, String.length(_))), _) == dw(1n, n) : String}
      {==}
    case 1n++i:
      pad_of(Nat.is_lt(n, 10n), i, n, {==}, pad_dw(i, Nat.div(n, 10n), PBig.dbound(n, Nat.pow(10n, 1n+i), hn)))

# ---------------------------------------------------------------------
# pad's width (hit_of_csv reads nine nanosecond digits back): with
# nsec_ok's digit count, no 10^9 is ever built
# ---------------------------------------------------------------------

def len_app(a: String, -b: String) -> {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %len_app(t, b) : {1n+String.length(String.append(t, b)) == 1n+_ : Nat}
      {==}

def len_rep(m: Nat) -> {String.length(String.repeat("0", m)) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      %len_rep(p) : {1n+String.length(String.repeat("0", p)) == 1n+_ : Nat}
      {==}

def sub_add(l: Nat, w: Nat, +h: {Nat.is_le(l, w) == True{} : Bool}) -> {Nat.add(Nat.sub(w, l), l) == w : Nat}:
  match l:
    case 0n:
      match w:
        case 0n:
          {==}
        case 1n++wp:
          Equal.sym(Nat, 1n+wp, Nat.add(1n+wp, 0n), PNat.add_zero(1n+wp))
    case 1n++lp:
      match w:
        case 0n:
          Empty.absurd({Nat.add(0n, 1n+lp) == 0n : Nat}, PNat.false_ne_true(h))
        case 1n++wp:
          %PNat.add_succ(Nat.sub(wp, lp), lp) : {_ == 1n+wp : Nat}
          %sub_add(lp, wp, h) : {1n+Nat.add(Nat.sub(wp, lp), lp) == 1n+_ : Nat}
          {==}

def lt_le(l: Nat, m: Nat, +h: {Nat.is_lt(l, 1n+m) == True{} : Bool}) -> {Nat.is_le(l, m) == True{} : Bool}:
  match l:
    case 0n:
      PBig.le_zero(m)
    case 1n++lp:
      match m:
        case 0n:
          Empty.absurd({Nat.is_le(1n+lp, 0n) == True{} : Bool}, PNat.lt_zero(lp, h))
        case 1n++mp:
          lt_le(lp, mp, h)

# pad never truncates: a text of at most w digits pads to exactly w
def pad_len(+w: Nat, +n: Nat, +h: {Nat.is_le(String.length(Dec.show(n)), w) == True{} : Bool}) -> {String.length(Dec.pad(w, n)) == w : Nat}:
  +l = String.length(Dec.show(n))
  +z = String.repeat("0", Nat.sub(w, l))
  %Equal.sym(Nat, String.length(String.append(z, Dec.show(n))), Nat.add(String.length(z), l), len_app(z, Dec.show(n))) : {_ == w : Nat}
  %Equal.sym(Nat, String.length(z), Nat.sub(w, l), len_rep(Nat.sub(w, l))) : {Nat.add(_, l) == w : Nat}
  sub_add(l, w, h)

def pad9_len(+n: Nat, +h: {L.nsec_ok(n) == True{} : Bool}) -> {String.length(Dec.pad(9n, n)) == 9n : Nat}:
  pad_len(9n, n, lt_le(String.length(Dec.show(n)), 9n, h))

# ---------------------------------------------------------------------
# civil_unix_nanos: lib tells "below a second" by nsec_ok's digit count,
# so no carry is divided out of 10^9
# ---------------------------------------------------------------------

def unix_pick(c: Bool, +a: String, +b: String) -> {Civil.pick(String, c, a, b) == L.pick(String, c, a, b) : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def L.civil_unix_nanos(t, h):
  match t:
    case Civil.Time{+s, +ns, +off}:
      +e = Equal.sym(Bool, Civil.nsec_fits(ns), True{}, h)
      %e : {Civil.pick(String, Nat.is_eq(Nat.add(s, Civil.ns_carry.of(_, ns)), 0n), Dec.show(Civil.ns_low.of(_, ns)),
              String.append(Dec.show(Nat.add(s, Civil.ns_carry.of(_, ns))), Dec.pad(9n, Civil.ns_low.of(_, ns))))
            == L.pick(String, Nat.is_eq(s, 0n), Dec.show(ns), String.append(Dec.show(s), Dec.pad(9n, ns))) : String}
      %PNat.add_zero(s) : {Civil.pick(String, Nat.is_eq(_, 0n), Dec.show(ns), String.append(Dec.show(_), Dec.pad(9n, ns)))
            == L.pick(String, Nat.is_eq(s, 0n), Dec.show(ns), String.append(Dec.show(s), Dec.pad(9n, ns))) : String}
      unix_pick(Nat.is_eq(s, 0n), Dec.show(ns), String.append(Dec.show(s), Dec.pad(9n, ns)))

# ---------------------------------------------------------------------
# met_floats: seconds() divides by the literal f64_1e9 (lib's sec_f64 is
# the same literal), so no closed Big.of(10^9) is ever compared
# ---------------------------------------------------------------------

def per_sec_same(c: Bool, +x: F64.F64, +d: Nat) -> {Met.per_sec(c, x, d) == L.pick(F64.F64, c, F64.div(x, L.seconds(d)), x) : F64.F64}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the float fields of a summary, by the accumulator's counts
def fl_type(+a: Met.Acc, +n: Nat, +k: Nat) -> Type:
  +s = Met.close(a)
  {L.s_rate(s) == L.pick(F64.F64, Nat.is_gt(L.s_duration(s), 0n), F64.div(F64.of_nat(n), L.seconds(L.s_duration(s))), F64.of_nat(n)) : F64.F64}
  & {L.s_throughput(s) == L.pick(F64.F64, Nat.is_gt(L.s_duration(s), 0n), F64.div(F64.of_nat(k), L.seconds(Nat.add(L.s_duration(s), L.s_wait(s)))), F64.of_nat(k)) : F64.F64}
  & {L.s_ratio(s) == F64.div(F64.of_nat(k), F64.of_nat(n)) : F64.F64}
  & {L.s_in_mean(s) == F64.div(F64.of_big(L.s_bytes_in(s)), F64.of_nat(n)) : F64.F64}
  & {L.s_out_mean(s) == F64.div(F64.of_big(L.s_bytes_out(s)), F64.of_nat(n)) : F64.F64}
  & {L.s_lat_mean(s) == F64.trunc(F64.div(F64.of_big(L.s_lat_total(s)), F64.of_nat(n))) : Nat}

def fl(a: Met.Acc, hx: {PMet.is_ext(PMet.a_x(a)) == True{} : Bool}, +n: Nat, +k: Nat,
  +en: {PMet.a_n(a) == n : Nat}, +ek: {PMet.a_ok(a) == k : Nat}) -> fl_type(a, n, k):
  match a:
    case Met.Acc{+bs, +an, +ok, +cs, +es, +l, +i, +o, x, +t}:
      match x:
        case Met.NoExt{}:
          Empty.absurd(fl_type(Met.Acc{bs, an, ok, cs, es, l, i, o, Met.NoExt{}, t}, n, k), PMet.no_ft(hx))
        case Met.Ext{+lmin, +lmax, +es1, +en1, +ls1, +ln1, +xs1, +xn1}:
          +a2 = {Met.Acc{bs, an, ok, cs, es, l, i, o, Met.Ext{lmin, lmax, es1, en1, ls1, ln1, xs1, xn1}, t} : Met.Acc}
          +d = Met.span_ns(es1, en1, ls1, ln1)
          +w = Met.span_ns(ls1, ln1, xs1, xn1)
          %en : fl_type(a2, _, k)
          %ek : fl_type(a2, an, _)
          (per_sec_same(Nat.is_gt(d, 0n), F64.of_nat(an), d),
           (per_sec_same(Nat.is_gt(d, 0n), F64.of_nat(ok), Nat.add(d, w)), ({==}, ({==}, ({==}, {==})))))

def L.met_floats(bs, h, hs):
  +E = Met.empty(bs)
  +A = L.acc_all(Con{h, hs}, E)
  +nn = List.length(&2, Hit.Hit, Con{h, hs})
  +nk = L.n_ok(Con{h, hs})
  fl(A, PMet.sum_x(bs, h, hs), nn, nk,
    Equal.sym(Nat, Nat.add(PMet.a_n(E), nn), PMet.a_n(A), PMet.f_n(Con{h, hs}, E)),
    Equal.sym(Nat, Nat.add(PMet.a_ok(E), nk), PMet.a_ok(A), PMet.f_ok(Con{h, hs}, E)))

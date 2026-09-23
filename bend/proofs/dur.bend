# Proofs of the duration laws (dur_*).
#
# lib/dur.bend states show and round with the same structure as LAWS'
# go_dur and round_go; its picks are its own, so each is related to LAWS'
# pick by the lemmas below (a pick stuck on a symbolic condition does not
# unfold, so equal-looking terms from the two files are not convertible).
import Base
import ../LAWS.bend as L
import ../lib/dec.bend as Dec
import ../lib/big.bend as Big
import ../lib/dur.bend as Dur
import ./nat.bend as PNat

def pickN(c: Bool, +a: Nat, +b: Nat, +a2: Nat, +b2: Nat, +ea: {a == a2 : Nat}, +eb: {b == b2 : Nat})
  -> {Dur.pick(Nat, c, a, b) == L.pick(Nat, c, a2, b2) : Nat}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def pickS(c: Bool, +a: String, +b: String, +a2: String, +b2: String, +ea: {a == a2 : String}, +eb: {b == b2 : String})
  -> {Dur.pick(String, c, a, b) == L.pick(String, c, a2, b2) : String}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def mul_cong_l(-x: Nat, -y: Nat, -b: Nat, e: {x == y : Nat}) -> {Nat.mul(x, b) == Nat.mul(y, b) : Nat}:
  %e : {Nat.mul(x, b) == Nat.mul(_, b) : Nat}
  {==}

def app_cong_l(-x: String, -y: String, -t: String, e: {x == y : String}) -> {String.append(x, t) == String.append(y, t) : String}:
  %e : {String.append(x, t) == String.append(_, t) : String}
  {==}

def app_cong_r(-a: String, -x: String, -y: String, e: {x == y : String}) -> {String.append(a, x) == String.append(a, y) : String}:
  %e : {String.append(a, x) == String.append(a, _) : String}
  {==}

def app_cong_both(-a: String, -a2: String, -b: String, -b2: String, ea: {a == a2 : String}, eb: {b == b2 : String})
  -> {String.append(a, b) == String.append(a2, b2) : String}:
  %ea : {String.append(a, b) == String.append(_, b2) : String}
  %eb : {String.append(a, b) == String.append(a, _) : String}
  {==}

# ---------------------------------------------------------------------
# dur_round
# ---------------------------------------------------------------------

def round_to_same(+n: Nat, +f: Nat, +b: Nat) -> {Dur.round_to(n, f, b) == L.round_to(n, f, b) : Nat}:
  +q = Nat.div(n, b)
  +a = Nat.mod(q, f)
  +c = Nat.mod(n, b)
  +up = Bool.or(Nat.is_ge(Nat.mul(2n, a), f), Bool.and(Nat.is_eq(Nat.add(Nat.mul(2n, a), 1n), f), Nat.is_ge(Nat.mul(2n, c), b)))
  +x = Nat.add(Nat.sub(q, a), f)
  +y = Nat.sub(q, a)
  mul_cong_l(Dur.pick(Nat, up, x, y), L.pick(Nat, up, x, y), b, pickN(up, x, y, x, y, {==}, {==}))

def L.dur_round(n):
  pickN(Nat.is_ge(Nat.div(n, 1000000000n), 3600n), Dur.round_to(n, 60n, 1000000000n), Dur.pick(Nat, Nat.is_ge(Nat.div(n, 1000000000n), 60n), Dur.round_to(n, 1n, 1000000000n), Dur.pick(Nat, Nat.is_ge(Nat.div(n, 1000000000n), 1n), Dur.round_to(n, 1n, 1000000n), Dur.pick(Nat, Nat.is_ge(n, 1000000n), Dur.round_to(n, 1n, 1000n), n))), L.round_to(n, 60n, 1000000000n), L.pick(Nat, Nat.is_ge(Nat.div(n, 1000000000n), 60n), L.round_to(n, 1n, 1000000000n), L.pick(Nat, Nat.is_ge(Nat.div(n, 1000000000n), 1n), L.round_to(n, 1n, 1000000n), L.pick(Nat, Nat.is_ge(n, 1000000n), L.round_to(n, 1n, 1000n), n))), round_to_same(n, 60n, 1000000000n), pickN(Nat.is_ge(Nat.div(n, 1000000000n), 60n), Dur.round_to(n, 1n, 1000000000n), Dur.pick(Nat, Nat.is_ge(Nat.div(n, 1000000000n), 1n), Dur.round_to(n, 1n, 1000000n), Dur.pick(Nat, Nat.is_ge(n, 1000000n), Dur.round_to(n, 1n, 1000n), n)), L.round_to(n, 1n, 1000000000n), L.pick(Nat, Nat.is_ge(Nat.div(n, 1000000000n), 1n), L.round_to(n, 1n, 1000000n), L.pick(Nat, Nat.is_ge(n, 1000000n), L.round_to(n, 1n, 1000n), n)), round_to_same(n, 1n, 1000000000n), pickN(Nat.is_ge(Nat.div(n, 1000000000n), 1n), Dur.round_to(n, 1n, 1000000n), Dur.pick(Nat, Nat.is_ge(n, 1000000n), Dur.round_to(n, 1n, 1000n), n), L.round_to(n, 1n, 1000000n), L.pick(Nat, Nat.is_ge(n, 1000000n), L.round_to(n, 1n, 1000n), n), round_to_same(n, 1n, 1000000n), pickN(Nat.is_ge(n, 1000000n), Dur.round_to(n, 1n, 1000n), n, L.round_to(n, 1n, 1000n), n, round_to_same(n, 1n, 1000n), {==}))))

# ---------------------------------------------------------------------
# dur_show
# ---------------------------------------------------------------------

def strip_same(s: String) -> {Dur.strip_zeros_l(s) == L.strip_zeros_l(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          pickS(U32.is_eq(k, 48), Dur.strip_zeros_l(rest), SCon{Chr{k}, rest}, L.strip_zeros_l(rest), SCon{Chr{k}, rest}, strip_same(rest), {==})

def trim_same(+s: String) -> {Dur.trim_zeros_r(s) == L.trim_zeros_r(s) : String}:
  %strip_same(String.reverse(s)) : {String.reverse(Dur.strip_zeros_l(String.reverse(s))) == String.reverse(_) : String}
  {==}

def frac_same(+r: Nat, +prec: Nat) -> {Dur.frac_text(r, prec) == L.frac_text(r, prec) : String}:
  pickS(Nat.is_eq(r, 0n), "", String.append(".", Dur.trim_zeros_r(Dec.pad(prec, r))), "", String.append(".", L.trim_zeros_r(Dec.pad(prec, r))),
    {==}, app_cong_r(".", Dur.trim_zeros_r(Dec.pad(prec, r)), L.trim_zeros_r(Dec.pad(prec, r)), trim_same(Dec.pad(prec, r))))

def L.dur_show(n):
  pickS(Nat.is_eq(n, 0n), "0s", Dur.pick(String, Nat.is_lt(n, 1000n), String.append(Dec.show(n), "ns"), Dur.pick(String, Nat.is_lt(n, 1000000n), String.append(Dec.show(Nat.div(n, 1000n)), String.append(Dur.frac_text(Nat.mod(n, 1000n), 3n), String.append(Dur.micro(), "s"))), Dur.pick(String, Nat.is_lt(n, 1000000000n), String.append(Dec.show(Nat.div(n, 1000000n)), String.append(Dur.frac_text(Nat.mod(n, 1000000n), 6n), "ms")), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(Dur.frac_text(Nat.mod(n, 1000000000n), 9n), "s"))))))), "0s", L.pick(String, Nat.is_lt(n, 1000n), String.append(Dec.show(n), "ns"), L.pick(String, Nat.is_lt(n, 1000000n), String.append(Dec.show(Nat.div(n, 1000n)), String.append(L.frac_text(Nat.mod(n, 1000n), 3n), String.append(L.micro(), "s"))), L.pick(String, Nat.is_lt(n, 1000000000n), String.append(Dec.show(Nat.div(n, 1000000n)), String.append(L.frac_text(Nat.mod(n, 1000000n), 6n), "ms")), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(L.frac_text(Nat.mod(n, 1000000000n), 9n), "s"))))))), {==}, pickS(Nat.is_lt(n, 1000n), String.append(Dec.show(n), "ns"), Dur.pick(String, Nat.is_lt(n, 1000000n), String.append(Dec.show(Nat.div(n, 1000n)), String.append(Dur.frac_text(Nat.mod(n, 1000n), 3n), String.append(Dur.micro(), "s"))), Dur.pick(String, Nat.is_lt(n, 1000000000n), String.append(Dec.show(Nat.div(n, 1000000n)), String.append(Dur.frac_text(Nat.mod(n, 1000000n), 6n), "ms")), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(Dur.frac_text(Nat.mod(n, 1000000000n), 9n), "s")))))), String.append(Dec.show(n), "ns"), L.pick(String, Nat.is_lt(n, 1000000n), String.append(Dec.show(Nat.div(n, 1000n)), String.append(L.frac_text(Nat.mod(n, 1000n), 3n), String.append(L.micro(), "s"))), L.pick(String, Nat.is_lt(n, 1000000000n), String.append(Dec.show(Nat.div(n, 1000000n)), String.append(L.frac_text(Nat.mod(n, 1000000n), 6n), "ms")), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(L.frac_text(Nat.mod(n, 1000000000n), 9n), "s")))))), {==}, pickS(Nat.is_lt(n, 1000000n), String.append(Dec.show(Nat.div(n, 1000n)), String.append(Dur.frac_text(Nat.mod(n, 1000n), 3n), String.append(Dur.micro(), "s"))), Dur.pick(String, Nat.is_lt(n, 1000000000n), String.append(Dec.show(Nat.div(n, 1000000n)), String.append(Dur.frac_text(Nat.mod(n, 1000000n), 6n), "ms")), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(Dur.frac_text(Nat.mod(n, 1000000000n), 9n), "s"))))), String.append(Dec.show(Nat.div(n, 1000n)), String.append(L.frac_text(Nat.mod(n, 1000n), 3n), String.append(L.micro(), "s"))), L.pick(String, Nat.is_lt(n, 1000000000n), String.append(Dec.show(Nat.div(n, 1000000n)), String.append(L.frac_text(Nat.mod(n, 1000000n), 6n), "ms")), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(L.frac_text(Nat.mod(n, 1000000000n), 9n), "s"))))), app_cong_r(Dec.show(Nat.div(n, 1000n)), String.append(Dur.frac_text(Nat.mod(n, 1000n), 3n), String.append(Dur.micro(), "s")), String.append(L.frac_text(Nat.mod(n, 1000n), 3n), String.append(L.micro(), "s")), app_cong_l(Dur.frac_text(Nat.mod(n, 1000n), 3n), L.frac_text(Nat.mod(n, 1000n), 3n), String.append(Dur.micro(), "s"), frac_same(Nat.mod(n, 1000n), 3n))), pickS(Nat.is_lt(n, 1000000000n), String.append(Dec.show(Nat.div(n, 1000000n)), String.append(Dur.frac_text(Nat.mod(n, 1000000n), 6n), "ms")), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(Dur.frac_text(Nat.mod(n, 1000000000n), 9n), "s")))), String.append(Dec.show(Nat.div(n, 1000000n)), String.append(L.frac_text(Nat.mod(n, 1000000n), 6n), "ms")), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(L.frac_text(Nat.mod(n, 1000000000n), 9n), "s")))), app_cong_r(Dec.show(Nat.div(n, 1000000n)), String.append(Dur.frac_text(Nat.mod(n, 1000000n), 6n), "ms"), String.append(L.frac_text(Nat.mod(n, 1000000n), 6n), "ms"), app_cong_l(Dur.frac_text(Nat.mod(n, 1000000n), 6n), L.frac_text(Nat.mod(n, 1000000n), 6n), "ms", frac_same(Nat.mod(n, 1000000n), 6n))), app_cong_both(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), ""), String.append(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(Dur.frac_text(Nat.mod(n, 1000000000n), 9n), "s"))), String.append(L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(L.frac_text(Nat.mod(n, 1000000000n), 9n), "s"))), pickS(Nat.is_ge(Nat.div(n, 1000000000n), 3600n), String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), "", String.append(Dec.show(Nat.div(Nat.div(n, 1000000000n), 3600n)), "h"), "", {==}, {==}), app_cong_both(Dur.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), L.pick(String, Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), ""), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(Dur.frac_text(Nat.mod(n, 1000000000n), 9n), "s")), String.append(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(L.frac_text(Nat.mod(n, 1000000000n), 9n), "s")), pickS(Nat.is_ge(Nat.div(n, 1000000000n), 60n), String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), "", String.append(Dec.show(Nat.mod(Nat.div(Nat.div(n, 1000000000n), 60n), 60n)), "m"), "", {==}, {==}), app_cong_r(Dec.show(Nat.mod(Nat.div(n, 1000000000n), 60n)), String.append(Dur.frac_text(Nat.mod(n, 1000000000n), 9n), "s"), String.append(L.frac_text(Nat.mod(n, 1000000000n), 9n), "s"), app_cong_l(Dur.frac_text(Nat.mod(n, 1000000000n), 9n), L.frac_text(Nat.mod(n, 1000000000n), 9n), "s", frac_same(Nat.mod(n, 1000000000n), 9n)))))))))

# ---------------------------------------------------------------------
# dur_parse_domain and dur_parse_sign: lib's validity is LAWS' dur_ok,
# helper by helper (the types SS and Frac are each file's own)
# ---------------------------------------------------------------------

def pickB(c: Bool, +a: Big.Big, +b: Big.Big, +a2: Big.Big, +b2: Big.Big, +ea: {a == a2 : Big.Big}, +eb: {b == b2 : Big.Big})
  -> {Dur.pick(Big.Big, c, a, b) == L.pick(Big.Big, c, a2, b2) : Big.Big}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def pickS2(c: Bool, -c2: Bool, +a: String, +b: String, +a2: String, +b2: String, ec: {c == c2 : Bool}, +ea: {a == a2 : String}, +eb: {b == b2 : String})
  -> {Dur.pick(String, c, a, b) == L.pick(String, c2, a2, b2) : String}:
  %ec : {Dur.pick(String, c, a, b) == L.pick(String, _, a2, b2) : String}
  pickS(c, a, b, a2, b2, ea, eb)

def pickB2(c: Bool, -c2: Bool, +a: Big.Big, +b: Big.Big, +a2: Big.Big, +b2: Big.Big, ec: {c == c2 : Bool}, +ea: {a == a2 : Big.Big}, +eb: {b == b2 : Big.Big})
  -> {Dur.pick(Big.Big, c, a, b) == L.pick(Big.Big, c2, a2, b2) : Big.Big}:
  %ec : {Dur.pick(Big.Big, c, a, b) == L.pick(Big.Big, _, a2, b2) : Big.Big}
  pickB(c, a, b, a2, b2, ea, eb)

def fi_same(s: String, +k: U32) -> {Dur.first_is(s, k) == L.first_is(s, k) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+kk}:
          {==}

def ssa_pd(c: Bool, +x: Dur.SS, +y: Dur.SS) -> {Dur.SS.a(Dur.pick(Dur.SS, c, x, y)) == Dur.pick(String, c, Dur.SS.a(x), Dur.SS.a(y)) : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ssb_pd(c: Bool, +x: Dur.SS, +y: Dur.SS) -> {Dur.SS.b(Dur.pick(Dur.SS, c, x, y)) == Dur.pick(String, c, Dur.SS.b(x), Dur.SS.b(y)) : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ssa_pl(c: Bool, +x: L.SS, +y: L.SS) -> {L.SS.a(L.pick(L.SS, c, x, y)) == L.pick(String, c, L.SS.a(x), L.SS.a(y)) : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ssb_pl(c: Bool, +x: L.SS, +y: L.SS) -> {L.SS.b(L.pick(L.SS, c, x, y)) == L.pick(String, c, L.SS.b(x), L.SS.b(y)) : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def con_cong(+c: Char, -x: String, -y: String, e: {x == y : String}) -> {SCon{c, x} == SCon{c, y} : String}:
  %e : {SCon{c, x} == SCon{c, _} : String}
  {==}

# the leading digits and what follows, from either file
def spd_a(s: String) -> {Dur.SS.a(Dur.span_digits(s)) == L.SS.a(L.span_digits(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +cd = Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57))
          +rd = Dur.span_digits(rest)
          +rl = L.span_digits(rest)
          Equal.trans(String, Dur.SS.a(Dur.pick(Dur.SS, cd, Dur.SS{SCon{Chr{k}, Dur.SS.a(rd)}, Dur.SS.b(rd)}, Dur.SS{"", SCon{Chr{k}, rest}})),
            Dur.pick(String, cd, SCon{Chr{k}, Dur.SS.a(rd)}, ""), L.SS.a(L.span_digits(SCon{Chr{k}, rest})),
            ssa_pd(cd, Dur.SS{SCon{Chr{k}, Dur.SS.a(rd)}, Dur.SS.b(rd)}, Dur.SS{"", SCon{Chr{k}, rest}}),
            Equal.trans(String, Dur.pick(String, cd, SCon{Chr{k}, Dur.SS.a(rd)}, ""), L.pick(String, cd, SCon{Chr{k}, L.SS.a(rl)}, ""), L.SS.a(L.span_digits(SCon{Chr{k}, rest})),
              pickS(cd, SCon{Chr{k}, Dur.SS.a(rd)}, "", SCon{Chr{k}, L.SS.a(rl)}, "", con_cong(Chr{k}, Dur.SS.a(rd), L.SS.a(rl), spd_a(rest)), {==}),
              Equal.sym(String, L.SS.a(L.pick(L.SS, cd, L.SS{SCon{Chr{k}, L.SS.a(rl)}, L.SS.b(rl)}, L.SS{"", SCon{Chr{k}, rest}})), L.pick(String, cd, SCon{Chr{k}, L.SS.a(rl)}, ""),
                ssa_pl(cd, L.SS{SCon{Chr{k}, L.SS.a(rl)}, L.SS.b(rl)}, L.SS{"", SCon{Chr{k}, rest}}))))

def spd_b(s: String) -> {Dur.SS.b(Dur.span_digits(s)) == L.SS.b(L.span_digits(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +cd = Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57))
          +rd = Dur.span_digits(rest)
          +rl = L.span_digits(rest)
          Equal.trans(String, Dur.SS.b(Dur.pick(Dur.SS, cd, Dur.SS{SCon{Chr{k}, Dur.SS.a(rd)}, Dur.SS.b(rd)}, Dur.SS{"", SCon{Chr{k}, rest}})),
            Dur.pick(String, cd, Dur.SS.b(rd), SCon{Chr{k}, rest}), L.SS.b(L.span_digits(SCon{Chr{k}, rest})),
            ssb_pd(cd, Dur.SS{SCon{Chr{k}, Dur.SS.a(rd)}, Dur.SS.b(rd)}, Dur.SS{"", SCon{Chr{k}, rest}}),
            Equal.trans(String, Dur.pick(String, cd, Dur.SS.b(rd), SCon{Chr{k}, rest}), L.pick(String, cd, L.SS.b(rl), SCon{Chr{k}, rest}), L.SS.b(L.span_digits(SCon{Chr{k}, rest})),
              pickS(cd, Dur.SS.b(rd), SCon{Chr{k}, rest}, L.SS.b(rl), SCon{Chr{k}, rest}, spd_b(rest), {==}),
              Equal.sym(String, L.SS.b(L.pick(L.SS, cd, L.SS{SCon{Chr{k}, L.SS.a(rl)}, L.SS.b(rl)}, L.SS{"", SCon{Chr{k}, rest}})), L.pick(String, cd, L.SS.b(rl), SCon{Chr{k}, rest}),
                ssb_pl(cd, L.SS{SCon{Chr{k}, L.SS.a(rl)}, L.SS.b(rl)}, L.SS{"", SCon{Chr{k}, rest}}))))

# the leading unit name and what follows, from either file
def spu_a(s: String) -> {Dur.SS.a(Dur.span_unit(s)) == L.SS.a(L.span_unit(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +cd = Bool.or(Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57)), U32.is_eq(k, 46))
          +rd = Dur.span_unit(rest)
          +rl = L.span_unit(rest)
          Equal.trans(String, Dur.SS.a(Dur.pick(Dur.SS, cd, Dur.SS{"", SCon{Chr{k}, rest}}, Dur.SS{SCon{Chr{k}, Dur.SS.a(rd)}, Dur.SS.b(rd)})),
            Dur.pick(String, cd, "", SCon{Chr{k}, Dur.SS.a(rd)}), L.SS.a(L.span_unit(SCon{Chr{k}, rest})),
            ssa_pd(cd, Dur.SS{"", SCon{Chr{k}, rest}}, Dur.SS{SCon{Chr{k}, Dur.SS.a(rd)}, Dur.SS.b(rd)}),
            Equal.trans(String, Dur.pick(String, cd, "", SCon{Chr{k}, Dur.SS.a(rd)}), L.pick(String, cd, "", SCon{Chr{k}, L.SS.a(rl)}), L.SS.a(L.span_unit(SCon{Chr{k}, rest})),
              pickS(cd, "", SCon{Chr{k}, Dur.SS.a(rd)}, "", SCon{Chr{k}, L.SS.a(rl)}, {==}, con_cong(Chr{k}, Dur.SS.a(rd), L.SS.a(rl), spu_a(rest))),
              Equal.sym(String, L.SS.a(L.pick(L.SS, cd, L.SS{"", SCon{Chr{k}, rest}}, L.SS{SCon{Chr{k}, L.SS.a(rl)}, L.SS.b(rl)})), L.pick(String, cd, "", SCon{Chr{k}, L.SS.a(rl)}),
                ssa_pl(cd, L.SS{"", SCon{Chr{k}, rest}}, L.SS{SCon{Chr{k}, L.SS.a(rl)}, L.SS.b(rl)}))))

def spu_b(s: String) -> {Dur.SS.b(Dur.span_unit(s)) == L.SS.b(L.span_unit(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          +cd = Bool.or(Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57)), U32.is_eq(k, 46))
          +rd = Dur.span_unit(rest)
          +rl = L.span_unit(rest)
          Equal.trans(String, Dur.SS.b(Dur.pick(Dur.SS, cd, Dur.SS{"", SCon{Chr{k}, rest}}, Dur.SS{SCon{Chr{k}, Dur.SS.a(rd)}, Dur.SS.b(rd)})),
            Dur.pick(String, cd, SCon{Chr{k}, rest}, Dur.SS.b(rd)), L.SS.b(L.span_unit(SCon{Chr{k}, rest})),
            ssb_pd(cd, Dur.SS{"", SCon{Chr{k}, rest}}, Dur.SS{SCon{Chr{k}, Dur.SS.a(rd)}, Dur.SS.b(rd)}),
            Equal.trans(String, Dur.pick(String, cd, SCon{Chr{k}, rest}, Dur.SS.b(rd)), L.pick(String, cd, SCon{Chr{k}, rest}, L.SS.b(rl)), L.SS.b(L.span_unit(SCon{Chr{k}, rest})),
              pickS(cd, SCon{Chr{k}, rest}, Dur.SS.b(rd), SCon{Chr{k}, rest}, L.SS.b(rl), {==}, spu_b(rest)),
              Equal.sym(String, L.SS.b(L.pick(L.SS, cd, L.SS{"", SCon{Chr{k}, rest}}, L.SS{SCon{Chr{k}, L.SS.a(rl)}, L.SS.b(rl)})), L.pick(String, cd, SCon{Chr{k}, rest}, L.SS.b(rl)),
                ssb_pl(cd, L.SS{"", SCon{Chr{k}, rest}}, L.SS{SCon{Chr{k}, L.SS.a(rl)}, L.SS.b(rl)}))))

def hnz_same(s: String) -> {Dur.has_nonzero_digit(s) == L.has_nonzero_digit(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %hnz_same(rest) : {Dur.has_nonzero_digit(SCon{Chr{k}, rest}) == Bool.or(Bool.and(U32.is_ge(k, 49), U32.is_le(k, 57)), _) : Bool}
          {==}

def fi_cong(-x: String, -y: String, e: {x == y : String}) -> {L.first_is(x, 46) == L.first_is(y, 46) : Bool}:
  %e : {L.first_is(x, 46) == L.first_is(_, 46) : Bool}
  {==}

def drop_cong(-x: String, -y: String, e: {x == y : String}) -> {String.drop(x, 1n) == String.drop(y, 1n) : String}:
  %e : {String.drop(x, 1n) == String.drop(_, 1n) : String}
  {==}

def la_cong(-x: String, -y: String, e: {x == y : String}) -> {L.SS.a(L.span_digits(x)) == L.SS.a(L.span_digits(y)) : String}:
  %e : {L.SS.a(L.span_digits(x)) == L.SS.a(L.span_digits(_)) : String}
  {==}

def lb_cong(-x: String, -y: String, e: {x == y : String}) -> {L.SS.b(L.span_digits(x)) == L.SS.b(L.span_digits(y)) : String}:
  %e : {L.SS.b(L.span_digits(x)) == L.SS.b(L.span_digits(_)) : String}
  {==}

def lua_cong(-x: String, -y: String, e: {x == y : String}) -> {L.SS.a(L.span_unit(x)) == L.SS.a(L.span_unit(y)) : String}:
  %e : {L.SS.a(L.span_unit(x)) == L.SS.a(L.span_unit(_)) : String}
  {==}

def lub_cong(-x: String, -y: String, e: {x == y : String}) -> {L.SS.b(L.span_unit(x)) == L.SS.b(L.span_unit(y)) : String}:
  %e : {L.SS.b(L.span_unit(x)) == L.SS.b(L.span_unit(_)) : String}
  {==}

def tok_rec_cong(-f: Nat, -x: String, -y: String, e: {x == y : String}) -> {L.terms_ok(f, x) == L.terms_ok(f, y) : Bool}:
  %e : {L.terms_ok(f, x) == L.terms_ok(f, _) : Bool}
  {==}

# the body of terms_ok, from its parts
def tok(+pa: String, +dot: Bool, +qa: String, +ua: String, +ub: String, +rec: Bool) -> Bool:
  Bool.and(Bool.and(Bool.or(Bool.not(String.is_empty(pa)), Bool.and(dot, Bool.not(String.is_empty(qa)))), L.is_unit_name(ua)), Bool.or(String.is_empty(ub), rec))

def tok_cong(-pa: String, -pa2: String, -dot: Bool, -dot2: Bool, -qa: String, -qa2: String, -ua: String, -ua2: String, -ub: String, -ub2: String, -rec: Bool, -rec2: Bool,
  e1: {pa == pa2 : String}, e2: {dot == dot2 : Bool}, e3: {qa == qa2 : String}, e4: {ua == ua2 : String}, e5: {ub == ub2 : String}, e6: {rec == rec2 : Bool})
  -> {tok(pa, dot, qa, ua, ub, rec) == tok(pa2, dot2, qa2, ua2, ub2, rec2) : Bool}:
  %e1 : {tok(pa, dot, qa, ua, ub, rec) == tok(_, dot2, qa2, ua2, ub2, rec2) : Bool}
  %e2 : {tok(pa, dot, qa, ua, ub, rec) == tok(pa, _, qa2, ua2, ub2, rec2) : Bool}
  %e3 : {tok(pa, dot, qa, ua, ub, rec) == tok(pa, dot, _, ua2, ub2, rec2) : Bool}
  %e4 : {tok(pa, dot, qa, ua, ub, rec) == tok(pa, dot, qa, _, ub2, rec2) : Bool}
  %e5 : {tok(pa, dot, qa, ua, ub, rec) == tok(pa, dot, qa, ua, _, rec2) : Bool}
  %e6 : {tok(pa, dot, qa, ua, ub, rec) == tok(pa, dot, qa, ua, ub, _) : Bool}
  {==}

def terms_ok_same(f: Nat, +s: String) -> {Dur.terms_ok(f, s) == L.terms_ok(f, s) : Bool}:
  match f:
    case 0n:
      {==}
    case 1n++fp:
      +e_pa = spd_a(s)
      +e_pb = spd_b(s)
      +e_dot = Equal.trans(Bool, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), L.first_is(Dur.SS.b(Dur.span_digits(s)), 46), L.first_is(L.SS.b(L.span_digits(s)), 46), fi_same(Dur.SS.b(Dur.span_digits(s)), 46), fi_cong(Dur.SS.b(Dur.span_digits(s)), L.SS.b(L.span_digits(s)), e_pb))
      +e_x = pickS2(Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s)), e_dot, drop_cong(Dur.SS.b(Dur.span_digits(s)), L.SS.b(L.span_digits(s)), e_pb), e_pb)
      +e_qa = Equal.trans(String, Dur.SS.a(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))), L.SS.a(L.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))), L.SS.a(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))), spd_a(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)))), la_cong(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))), L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))), e_x))
      +e_qb = Equal.trans(String, Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))), L.SS.b(L.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))), L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))), spd_b(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)))), lb_cong(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))), L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))), e_x))
      +e_ua = Equal.trans(String, Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))))), L.SS.a(L.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))))), L.SS.a(L.span_unit(L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))))), spu_a(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)))))), lua_cong(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))), L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))), e_qb))
      +e_ub = Equal.trans(String, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))))), L.SS.b(L.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))))), L.SS.b(L.span_unit(L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))))), spu_b(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)))))), lub_cong(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))), L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))), e_qb))
      +e_rec = Equal.trans(Bool, Dur.terms_ok(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)))))))), L.terms_ok(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)))))))), L.terms_ok(fp, L.SS.b(L.span_unit(L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s)))))))), terms_ok_same(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)))))))), tok_rec_cong(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))))), L.SS.b(L.span_unit(L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))))), e_ub))
      tok_cong(Dur.SS.a(Dur.span_digits(s)), L.SS.a(L.span_digits(s)), Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), L.first_is(L.SS.b(L.span_digits(s)), 46), Dur.SS.a(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))), L.SS.a(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))), Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))))), L.SS.a(L.span_unit(L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))))), Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s))))))), L.SS.b(L.span_unit(L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s))))))), Dur.terms_ok(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.span_digits(Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), Dur.SS.b(Dur.span_digits(s)))))))), L.terms_ok(fp, L.SS.b(L.span_unit(L.SS.b(L.span_digits(L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), String.drop(L.SS.b(L.span_digits(s)), 1n), L.SS.b(L.span_digits(s)))))))),
        e_pa, e_dot, e_qa, e_ua, e_ub, e_rec)

def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def P2.fst(-A: Data, -B: Data, +p: P2(A, B)) -> A:
  (a, b) = p
  a

def P2.snd(-A: Data, -B: Data, +p: P2(A, B)) -> B:
  (a, b) = p
  b

def dn(+x: Dur.Frac) -> Big.Big:
  Dur.Frac{n, d} = x
  n

def dd(+x: Dur.Frac) -> Big.Big:
  Dur.Frac{n, d} = x
  d

def ln(+x: L.Frac) -> Big.Big:
  L.Frac{n, d} = x
  n

def ld(+x: L.Frac) -> Big.Big:
  L.Frac{n, d} = x
  d

def dnp(c: Bool, +x: Dur.Frac, +y: Dur.Frac) -> {dn(Dur.pick(Dur.Frac, c, x, y)) == Dur.pick(Big.Big, c, dn(x), dn(y)) : Big.Big}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ddp(c: Bool, +x: Dur.Frac, +y: Dur.Frac) -> {dd(Dur.pick(Dur.Frac, c, x, y)) == Dur.pick(Big.Big, c, dd(x), dd(y)) : Big.Big}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def lnp(c: Bool, +x: L.Frac, +y: L.Frac) -> {ln(L.pick(L.Frac, c, x, y)) == L.pick(Big.Big, c, ln(x), ln(y)) : Big.Big}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ldp(c: Bool, +x: L.Frac, +y: L.Frac) -> {ld(L.pick(L.Frac, c, x, y)) == L.pick(Big.Big, c, ld(x), ld(y)) : Big.Big}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def dfa_n(a: Dur.Frac, b: Dur.Frac) -> {dn(Dur.frac_add(a, b)) == Big.add(Big.mul(dn(a), dd(b)), Big.mul(dn(b), dd(a))) : Big.Big}:
  match a:
    case Dur.Frac{+an, +ad}:
      match b:
        case Dur.Frac{+bn, +bd}:
          {==}

def dfa_d(a: Dur.Frac, b: Dur.Frac) -> {dd(Dur.frac_add(a, b)) == Big.mul(dd(a), dd(b)) : Big.Big}:
  match a:
    case Dur.Frac{+an, +ad}:
      match b:
        case Dur.Frac{+bn, +bd}:
          {==}

def lfa_n(a: L.Frac, b: L.Frac) -> {ln(L.frac_add(a, b)) == Big.add(Big.mul(ln(a), ld(b)), Big.mul(ln(b), ld(a))) : Big.Big}:
  match a:
    case L.Frac{+an, +ad}:
      match b:
        case L.Frac{+bn, +bd}:
          {==}

def lfa_d(a: L.Frac, b: L.Frac) -> {ld(L.frac_add(a, b)) == Big.mul(ld(a), ld(b)) : Big.Big}:
  match a:
    case L.Frac{+an, +ad}:
      match b:
        case L.Frac{+bn, +bd}:
          {==}

def dpick_cong(c: Bool, +a: Big.Big, -b: Big.Big, -b2: Big.Big, e: {b == b2 : Big.Big}) -> {Dur.pick(Big.Big, c, a, b) == Dur.pick(Big.Big, c, a, b2) : Big.Big}:
  %e : {Dur.pick(Big.Big, c, a, b) == Dur.pick(Big.Big, c, a, _) : Big.Big}
  {==}

def lpick_cong(c: Bool, +a: Big.Big, -b: Big.Big, -b2: Big.Big, e: {b == b2 : Big.Big}) -> {L.pick(Big.Big, c, a, b) == L.pick(Big.Big, c, a, b2) : Big.Big}:
  %e : {L.pick(Big.Big, c, a, b) == L.pick(Big.Big, c, a, _) : Big.Big}
  {==}

def bp_same(n: Nat) -> {Dur.bpow10(n) == L.bpow10(n) : Big.Big}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %bp_same(p) : {Big.mul(Dur.bpow10(p), Big.of(10n)) == Big.mul(_, Big.of(10n)) : Big.Big}
      {==}

def dig_same(s: String, +acc: Big.Big) -> {Dur.ldigits.go(s, acc) == L.bdigits.go(s, acc) : Big.Big}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          dig_same(rest, Big.add(Big.mul(acc, Big.of(10n)), Big.of(Dec.digit(Chr{k}))))

def ub_same(+u: String) -> {Dur.unit_big(u) == L.unit_big(u) : Big.Big}:
  pickB(String.eq(u, "ns"), Big.Big{[1n]}, Dur.pick(Big.Big, Bool.or(Bool.or(String.eq(u, "us"), String.eq(u, String.append(Dur.micro(), "s"))), String.eq(u, String.append(Dur.greek_mu(), "s"))), Big.Big{[1000n]}, Dur.pick(Big.Big, String.eq(u, "ms"), Big.Big{[0n, 100n]}, Dur.pick(Big.Big, String.eq(u, "s"), Big.Big{[0n, 0n, 10n]}, Dur.pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]})))), Big.Big{[1n]}, L.pick(Big.Big, Bool.or(Bool.or(String.eq(u, "us"), String.eq(u, String.append(Dur.micro(), "s"))), String.eq(u, String.append(Dur.greek_mu(), "s"))), Big.Big{[1000n]}, L.pick(Big.Big, String.eq(u, "ms"), Big.Big{[0n, 100n]}, L.pick(Big.Big, String.eq(u, "s"), Big.Big{[0n, 0n, 10n]}, L.pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]})))), {==}, pickB(Bool.or(Bool.or(String.eq(u, "us"), String.eq(u, String.append(Dur.micro(), "s"))), String.eq(u, String.append(Dur.greek_mu(), "s"))), Big.Big{[1000n]}, Dur.pick(Big.Big, String.eq(u, "ms"), Big.Big{[0n, 100n]}, Dur.pick(Big.Big, String.eq(u, "s"), Big.Big{[0n, 0n, 10n]}, Dur.pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]}))), Big.Big{[1000n]}, L.pick(Big.Big, String.eq(u, "ms"), Big.Big{[0n, 100n]}, L.pick(Big.Big, String.eq(u, "s"), Big.Big{[0n, 0n, 10n]}, L.pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]}))), {==}, pickB(String.eq(u, "ms"), Big.Big{[0n, 100n]}, Dur.pick(Big.Big, String.eq(u, "s"), Big.Big{[0n, 0n, 10n]}, Dur.pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]})), Big.Big{[0n, 100n]}, L.pick(Big.Big, String.eq(u, "s"), Big.Big{[0n, 0n, 10n]}, L.pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]})), {==}, pickB(String.eq(u, "s"), Big.Big{[0n, 0n, 10n]}, Dur.pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]}), Big.Big{[0n, 0n, 10n]}, L.pick(Big.Big, String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]}), {==}, pickB(String.eq(u, "m"), Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]}, Big.Big{[0n, 0n, 600n]}, Big.Big{[0n, 0n, 6000n, 3n]}, {==}, {==})))))

def bp_cong(-x: Nat, -y: Nat, e: {x == y : Nat}) -> {L.bpow10(x) == L.bpow10(y) : Big.Big}:
  %e : {L.bpow10(x) == L.bpow10(_) : Big.Big}
  {==}

def len_cong(-x: String, -y: String, e: {x == y : String}) -> {String.length(x) == String.length(y) : Nat}:
  %e : {String.length(x) == String.length(_) : Nat}
  {==}

def bd_cong(-x: String, -y: String, e: {x == y : String}) -> {L.bdigits(x) == L.bdigits(y) : Big.Big}:
  %e : {L.bdigits(x) == L.bdigits(_) : Big.Big}
  {==}

def ubl_cong(-x: String, -y: String, e: {x == y : String}) -> {L.unit_big(x) == L.unit_big(y) : Big.Big}:
  %e : {L.unit_big(x) == L.unit_big(_) : Big.Big}
  {==}

def empty_cong(-x: String, -y: String, e: {x == y : String}) -> {String.is_empty(x) == String.is_empty(y) : Bool}:
  %e : {String.is_empty(x) == String.is_empty(_) : Bool}
  {==}

def ln_cong(-f: Nat, -x: String, -y: String, e: {x == y : String}) -> {ln(L.terms_val(f, x)) == ln(L.terms_val(f, y)) : Big.Big}:
  %e : {ln(L.terms_val(f, x)) == ln(L.terms_val(f, _)) : Big.Big}
  {==}

def ld_cong(-f: Nat, -x: String, -y: String, e: {x == y : String}) -> {ld(L.terms_val(f, x)) == ld(L.terms_val(f, y)) : Big.Big}:
  %e : {ld(L.terms_val(f, x)) == ld(L.terms_val(f, _)) : Big.Big}
  {==}

def tn_cong(-a: Big.Big, -a2: Big.Big, -b: Big.Big, -b2: Big.Big, -c: Big.Big, -c2: Big.Big, -d: Big.Big, -d2: Big.Big,
  ea: {a == a2 : Big.Big}, eb: {b == b2 : Big.Big}, ec: {c == c2 : Big.Big}, ed: {d == d2 : Big.Big})
  -> {Big.mul(Big.add(Big.mul(a, b), c), d) == Big.mul(Big.add(Big.mul(a2, b2), c2), d2) : Big.Big}:
  %ea : {Big.mul(Big.add(Big.mul(a, b), c), d) == Big.mul(Big.add(Big.mul(_, b2), c2), d2) : Big.Big}
  %eb : {Big.mul(Big.add(Big.mul(a, b), c), d) == Big.mul(Big.add(Big.mul(a, _), c2), d2) : Big.Big}
  %ec : {Big.mul(Big.add(Big.mul(a, b), c), d) == Big.mul(Big.add(Big.mul(a, b), _), d2) : Big.Big}
  %ed : {Big.mul(Big.add(Big.mul(a, b), c), d) == Big.mul(Big.add(Big.mul(a, b), c), _) : Big.Big}
  {==}

def sum_cong(-a: Big.Big, -a2: Big.Big, -b: Big.Big, -b2: Big.Big, -c: Big.Big, -c2: Big.Big, -d: Big.Big, -d2: Big.Big,
  ea: {a == a2 : Big.Big}, eb: {b == b2 : Big.Big}, ec: {c == c2 : Big.Big}, ed: {d == d2 : Big.Big})
  -> {Big.add(Big.mul(a, b), Big.mul(c, d)) == Big.add(Big.mul(a2, b2), Big.mul(c2, d2)) : Big.Big}:
  %ea : {Big.add(Big.mul(a, b), Big.mul(c, d)) == Big.add(Big.mul(_, b2), Big.mul(c2, d2)) : Big.Big}
  %eb : {Big.add(Big.mul(a, b), Big.mul(c, d)) == Big.add(Big.mul(a, _), Big.mul(c2, d2)) : Big.Big}
  %ec : {Big.add(Big.mul(a, b), Big.mul(c, d)) == Big.add(Big.mul(a, b), Big.mul(_, d2)) : Big.Big}
  %ed : {Big.add(Big.mul(a, b), Big.mul(c, d)) == Big.add(Big.mul(a, b), Big.mul(c, _)) : Big.Big}
  {==}

def mul_cong2(-a: Big.Big, -a2: Big.Big, -b: Big.Big, -b2: Big.Big, ea: {a == a2 : Big.Big}, eb: {b == b2 : Big.Big})
  -> {Big.mul(a, b) == Big.mul(a2, b2) : Big.Big}:
  %ea : {Big.mul(a, b) == Big.mul(_, b2) : Big.Big}
  %eb : {Big.mul(a, b) == Big.mul(a, _) : Big.Big}
  {==}

def TV(+x: Dur.Frac, +y: L.Frac) -> Data:
  P2({dn(x) == ln(y) : Big.Big}, {dd(x) == ld(y) : Big.Big})

# the exact value, from either file
def tv_same(f: Nat, +s: String) -> TV(Dur.terms_val(f, s), L.terms_val(f, s)):
  match f:
    case 0n:
      ({==}, {==})
    case 1n++fp:
      +e_pa = spd_a(s)
      +e_pb = spd_b(s)
      +e_dot = Equal.trans(Bool, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), L.first_is(Dur.SS.b(Dur.span_digits(s)), 46), L.first_is(L.SS.b(L.span_digits(s)), 46), fi_same(Dur.SS.b(Dur.span_digits(s)), 46), fi_cong(Dur.SS.b(Dur.span_digits(s)), L.SS.b(L.span_digits(s)), e_pb))
      +e_dsa = Equal.trans(String, Dur.SS.a(Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), L.SS.a(L.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), L.SS.a(L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n))), spd_a(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)),
        la_cong(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), String.drop(L.SS.b(L.span_digits(s)), 1n), drop_cong(Dur.SS.b(Dur.span_digits(s)), L.SS.b(L.span_digits(s)), e_pb)))
      +e_dsb = Equal.trans(String, Dur.SS.b(Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), L.SS.b(L.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), L.SS.b(L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n))), spd_b(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)),
        lb_cong(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n), String.drop(L.SS.b(L.span_digits(s)), 1n), drop_cong(Dur.SS.b(Dur.span_digits(s)), L.SS.b(L.span_digits(s)), e_pb)))
      +e_qa = Equal.trans(String, Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})), Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.SS.a(Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), ""), L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})),
        ssa_pd(Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}),
        Equal.trans(String, Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.SS.a(Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), ""), L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), L.SS.a(L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n))), ""), L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})),
          pickS2(Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), L.first_is(L.SS.b(L.span_digits(s)), 46), Dur.SS.a(Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), "", L.SS.a(L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n))), "", e_dot, e_dsa, {==}),
          Equal.sym(String, L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})), L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), L.SS.a(L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n))), ""), ssa_pl(L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))
      +e_qb = Equal.trans(String, Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})), Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.SS.b(Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), Dur.SS.b(Dur.span_digits(s))), L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})),
        ssb_pd(Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}),
        Equal.trans(String, Dur.pick(String, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.SS.b(Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), Dur.SS.b(Dur.span_digits(s))), L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), L.SS.b(L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n))), L.SS.b(L.span_digits(s))), L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})),
          pickS2(Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), L.first_is(L.SS.b(L.span_digits(s)), 46), Dur.SS.b(Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n))), Dur.SS.b(Dur.span_digits(s)), L.SS.b(L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n))), L.SS.b(L.span_digits(s)), e_dot, e_dsb, e_pb),
          Equal.sym(String, L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})), L.pick(String, L.first_is(L.SS.b(L.span_digits(s)), 46), L.SS.b(L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n))), L.SS.b(L.span_digits(s))), ssb_pl(L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))
      +e_ua = Equal.trans(String, Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.SS.a(L.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), spu_a(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))), lua_cong(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})), L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})), e_qb))
      +e_ub = Equal.trans(String, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.SS.b(L.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), spu_b(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))), lub_cong(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})), L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})), e_qb))
      +e_sc = Equal.trans(Big.Big, Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), bp_same(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), bp_cong(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))), String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))), len_cong(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})), L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})), e_qa)))
      +e_da = Equal.trans(Big.Big, Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), L.bdigits(Dur.SS.a(Dur.span_digits(s))), L.bdigits(L.SS.a(L.span_digits(s))), dig_same(Dur.SS.a(Dur.span_digits(s)), Big.of(0n)), bd_cong(Dur.SS.a(Dur.span_digits(s)), L.SS.a(L.span_digits(s)), e_pa))
      +e_db = Equal.trans(Big.Big, Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))), L.bdigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))), dig_same(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})), Big.of(0n)), bd_cong(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})), L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})), e_qa))
      +e_u = Equal.trans(Big.Big, Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), L.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), ub_same(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), ubl_cong(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), e_ua))
      +e_tn = tn_cong(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), L.bdigits(L.SS.a(L.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), e_da, e_sc, e_db, e_u)
      +e_e = empty_cong(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), e_ub)
      +ih = tv_same(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))
      +ihn = Equal.trans(Big.Big, dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), ln(L.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), ln(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), P2.fst({dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))) == ln(L.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))) : Big.Big}, {dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))) == ld(L.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))) : Big.Big}, ih), ln_cong(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), e_ub))
      +ihd = Equal.trans(Big.Big, dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), ld(L.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), P2.snd({dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))) == ln(L.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))) : Big.Big}, {dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))) == ld(L.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))) : Big.Big}, ih), ld_cong(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), e_ub))
      +e_x = sum_cong(Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), ln(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), e_tn, ihd, ihn, e_sc)
      +e_y = mul_cong2(Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), e_sc, ihd)
      +en = Equal.trans(Big.Big, dn(Dur.terms_val(1n+fp, s)), Dur.pick(Big.Big, String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), Big.mul(dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), ln(L.terms_val(1n+fp, s)),
        Equal.trans(Big.Big, dn(Dur.terms_val(1n+fp, s)), Dur.pick(Big.Big, String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), dn(Dur.frac_add(Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))))), Dur.pick(Big.Big, String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), Big.mul(dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))),
          dnp(String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.frac_add(Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), dpick_cong(String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), dn(Dur.frac_add(Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), Big.mul(dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), dfa_n(Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))))),
        Equal.trans(Big.Big, Dur.pick(Big.Big, String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), Big.mul(dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), L.pick(Big.Big, String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), Big.mul(ln(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), ln(L.terms_val(1n+fp, s)),
          pickB2(String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), Big.mul(dn(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), Big.mul(ln(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), e_e, e_tn, e_x),
          Equal.sym(Big.Big, ln(L.terms_val(1n+fp, s)), L.pick(Big.Big, String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), Big.mul(ln(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))),
            Equal.trans(Big.Big, ln(L.terms_val(1n+fp, s)), L.pick(Big.Big, String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), ln(L.frac_add(L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))))), L.pick(Big.Big, String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), Big.mul(ln(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))),
              lnp(String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.frac_add(L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), lpick_cong(String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), ln(L.frac_add(L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), Big.add(Big.mul(Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), Big.mul(ln(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), lfa_n(L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))))))))
      +ed = Equal.trans(Big.Big, dd(Dur.terms_val(1n+fp, s)), Dur.pick(Big.Big, String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Big.mul(Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))))), ld(L.terms_val(1n+fp, s)),
        Equal.trans(Big.Big, dd(Dur.terms_val(1n+fp, s)), Dur.pick(Big.Big, String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), dd(Dur.frac_add(Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))))), Dur.pick(Big.Big, String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Big.mul(Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))))),
          ddp(String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.frac_add(Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), dpick_cong(String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), dd(Dur.frac_add(Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), Big.mul(Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), dfa_d(Dur.Frac{Big.mul(Big.add(Big.mul(Dur.ldigits(Dur.SS.a(Dur.span_digits(s))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.ldigits(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Dur.unit_big(Dur.SS.a(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))}, Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))))),
        Equal.trans(Big.Big, Dur.pick(Big.Big, String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Big.mul(Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))))))), L.pick(Big.Big, String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), Big.mul(L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))))), ld(L.terms_val(1n+fp, s)),
          pickB2(String.is_empty(Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))), String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), Big.mul(Dur.bpow10(String.length(Dur.SS.a(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))})))), dd(Dur.terms_val(fp, Dur.SS.b(Dur.span_unit(Dur.SS.b(Dur.pick(Dur.SS, Dur.first_is(Dur.SS.b(Dur.span_digits(s)), 46), Dur.span_digits(String.drop(Dur.SS.b(Dur.span_digits(s)), 1n)), Dur.SS{"", Dur.SS.b(Dur.span_digits(s))}))))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), Big.mul(L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), e_e, e_sc, e_y),
          Equal.sym(Big.Big, ld(L.terms_val(1n+fp, s)), L.pick(Big.Big, String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), Big.mul(L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))))),
            Equal.trans(Big.Big, ld(L.terms_val(1n+fp, s)), L.pick(Big.Big, String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), ld(L.frac_add(L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))))), L.pick(Big.Big, String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), Big.mul(L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))))),
              ldp(String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.frac_add(L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), lpick_cong(String.is_empty(L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), ld(L.frac_add(L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), Big.mul(L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), ld(L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))))), lfa_d(L.Frac{Big.mul(Big.add(Big.mul(L.bdigits(L.SS.a(L.span_digits(s))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))), L.bdigits(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))), L.unit_big(L.SS.a(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))), L.bpow10(String.length(L.SS.a(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))}))))}, L.terms_val(fp, L.SS.b(L.span_unit(L.SS.b(L.pick(L.SS, L.first_is(L.SS.b(L.span_digits(s)), 46), L.span_digits(String.drop(L.SS.b(L.span_digits(s)), 1n)), L.SS{"", L.SS.b(L.span_digits(s))})))))))))))
      (en, ed)

def fb(x: Dur.Frac, y: L.Frac, +b: Big.Big, en: {dn(x) == ln(y) : Big.Big}, ed: {dd(x) == ld(y) : Big.Big})
  -> {Dur.frac_below(x, b) == L.frac_below(y, b) : Bool}:
  match x:
    case Dur.Frac{+n, +d}:
      match y:
        case L.Frac{+n2, +d2}:
          %en : {Cmp.is_lt(Big.cmp(n, Big.mul(b, d))) == Cmp.is_lt(Big.cmp(_, Big.mul(b, d2))) : Bool}
          %ed : {Cmp.is_lt(Big.cmp(n, Big.mul(b, d))) == Cmp.is_lt(Big.cmp(n, Big.mul(b, _))) : Bool}
          {==}

def fits_same(+t: String) -> {Dur.dur_fits(t) == L.dur_fits(t) : Bool}:
  +tv = tv_same(String.length(t), t)
  +x = Dur.terms_val(String.length(t), t)
  +y = L.terms_val(String.length(t), t)
  fb(x, y, Dur.dur_bound(), P2.fst({dn(x) == ln(y) : Big.Big}, {dd(x) == ld(y) : Big.Big}, tv), P2.snd({dn(x) == ln(y) : Big.Big}, {dd(x) == ld(y) : Big.Big}, tv))

def is_some_of(v: Bool, +n: Nat) -> {Maybe.is_some(&2, Nat, Dur.parse.of(v, n)) == v : Bool}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def body_some(v: Bool, +t: String) -> {Maybe.is_some(&2, Nat, Dur.parse.body(v, t)) == v : Bool}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def zero_some(z: Bool, +t: String)
  -> {Maybe.is_some(&2, Nat, Dur.parse.zero(z, t)) == Bool.or(z, Bool.and(Dur.terms_ok(String.length(t), t), Dur.dur_fits(t))) : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      body_some(Bool.and(Dur.terms_ok(String.length(t), t), Dur.dur_fits(t)), t)

def again_some(a: Bool, +t: String)
  -> {Maybe.is_some(&2, Nat, Dur.parse.again(a, t)) == Bool.and(Bool.not(a), Bool.or(String.eq(t, "0"), Bool.and(Dur.terms_ok(String.length(t), t), Dur.dur_fits(t)))) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      zero_some(String.eq(t, "0"), t)

def bool4_cong(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool, -c: Bool, -c2: Bool, -d: Bool, -d2: Bool, -z: Bool,
  e1: {a == a2 : Bool}, e2: {b == b2 : Bool}, e3: {c == c2 : Bool}, e4: {d == d2 : Bool})
  -> {Bool.and(Bool.not(Bool.or(a, b)), Bool.or(z, Bool.and(c, d))) == Bool.and(Bool.not(Bool.or(a2, b2)), Bool.or(z, Bool.and(c2, d2))) : Bool}:
  %e1 : {Bool.and(Bool.not(Bool.or(a, b)), Bool.or(z, Bool.and(c, d))) == Bool.and(Bool.not(Bool.or(_, b2)), Bool.or(z, Bool.and(c2, d2))) : Bool}
  %e2 : {Bool.and(Bool.not(Bool.or(a, b)), Bool.or(z, Bool.and(c, d))) == Bool.and(Bool.not(Bool.or(a, _)), Bool.or(z, Bool.and(c2, d2))) : Bool}
  %e3 : {Bool.and(Bool.not(Bool.or(a, b)), Bool.or(z, Bool.and(c, d))) == Bool.and(Bool.not(Bool.or(a, b)), Bool.or(z, Bool.and(_, d2))) : Bool}
  %e4 : {Bool.and(Bool.not(Bool.or(a, b)), Bool.or(z, Bool.and(c, d))) == Bool.and(Bool.not(Bool.or(a, b)), Bool.or(z, Bool.and(c, _))) : Bool}
  {==}

def not_cong(-a: Bool, -b: Bool, e: {a == b : Bool}) -> {Bool.not(a) == Bool.not(b) : Bool}:
  %e : {Bool.not(a) == Bool.not(_) : Bool}
  {==}

# the unsigned language, from either file
def pos_same(+t: String)
  -> {Bool.and(Bool.not(Bool.or(Dur.first_is(t, 43), Dur.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(Dur.terms_ok(String.length(t), t), Dur.dur_fits(t))))
      == Bool.and(Bool.not(Bool.or(L.first_is(t, 43), L.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(L.terms_ok(String.length(t), t), L.dur_fits(t)))) : Bool}:
  bool4_cong(Dur.first_is(t, 43), L.first_is(t, 43), Dur.first_is(t, 45), L.first_is(t, 45), Dur.terms_ok(String.length(t), t), L.terms_ok(String.length(t), t),
    Dur.dur_fits(t), L.dur_fits(t), String.eq(t, "0"), fi_same(t, 43), fi_same(t, 45), terms_ok_same(String.length(t), t), fits_same(t))

# after "-", from either file
def neg_same(+t: String)
  -> {Bool.and(Bool.not(Bool.or(Dur.first_is(t, 43), Dur.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(Dur.terms_ok(String.length(t), t), Bool.not(Dur.has_nonzero_digit(t)))))
      == Bool.and(Bool.not(Bool.or(L.first_is(t, 43), L.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(L.terms_ok(String.length(t), t), Bool.not(L.has_nonzero_digit(t))))) : Bool}:
  bool4_cong(Dur.first_is(t, 43), L.first_is(t, 43), Dur.first_is(t, 45), L.first_is(t, 45), Dur.terms_ok(String.length(t), t), L.terms_ok(String.length(t), t),
    Bool.not(Dur.has_nonzero_digit(t)), Bool.not(L.has_nonzero_digit(t)), String.eq(t, "0"), fi_same(t, 43), fi_same(t, 45), terms_ok_same(String.length(t), t),
    not_cong(Dur.has_nonzero_digit(t), L.has_nonzero_digit(t), hnz_same(t)))

# LAWS' dur_ok with the sign tests as parameters
def durok_g(+n: Bool, +p: Bool, +s: String) -> Bool:
  +t = L.pick(String, Bool.or(n, p), String.drop(s, 1n), s)
  Bool.and(Bool.not(Bool.or(L.first_is(t, 43), L.first_is(t, 45))), Bool.or(String.eq(t, "0"),
    Bool.and(L.terms_ok(String.length(t), t), L.pick(Bool, n, Bool.not(L.has_nonzero_digit(t)), L.dur_fits(t)))))

def dom.of(n: Bool, p: Bool, +s: String) -> {Maybe.is_some(&2, Nat, Dur.parse.sgn(n, p, s)) == durok_g(n, p, s) : Bool}:
  match n:
    case True{}:
      +t = String.drop(s, 1n)
      Equal.trans(Bool, Maybe.is_some(&2, Nat, Dur.parse.neg(t)),
        Bool.and(Bool.not(Bool.or(Dur.first_is(t, 43), Dur.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(Dur.terms_ok(String.length(t), t), Bool.not(Dur.has_nonzero_digit(t))))),
        durok_g(True{}, p, s),
        is_some_of(Bool.and(Bool.not(Bool.or(Dur.first_is(t, 43), Dur.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(Dur.terms_ok(String.length(t), t), Bool.not(Dur.has_nonzero_digit(t))))), 0n),
        neg_same(t))
    case False{}:
      match p:
        case True{}:
          +t = String.drop(s, 1n)
          Equal.trans(Bool, Maybe.is_some(&2, Nat, Dur.parse.t(t)),
            Bool.and(Bool.not(Bool.or(Dur.first_is(t, 43), Dur.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(Dur.terms_ok(String.length(t), t), Dur.dur_fits(t)))),
            durok_g(False{}, True{}, s), again_some(Bool.or(Dur.first_is(t, 43), Dur.first_is(t, 45)), t), pos_same(t))
        case False{}:
          Equal.trans(Bool, Maybe.is_some(&2, Nat, Dur.parse.t(s)),
            Bool.and(Bool.not(Bool.or(Dur.first_is(s, 43), Dur.first_is(s, 45))), Bool.or(String.eq(s, "0"), Bool.and(Dur.terms_ok(String.length(s), s), Dur.dur_fits(s)))),
            durok_g(False{}, False{}, s), again_some(Bool.or(Dur.first_is(s, 43), Dur.first_is(s, 45)), s), pos_same(s))

def g_cong(-n: Bool, -n2: Bool, -p: Bool, -p2: Bool, -s: String, en: {n == n2 : Bool}, ep: {p == p2 : Bool}) -> {durok_g(n, p, s) == durok_g(n2, p2, s) : Bool}:
  %en : {durok_g(n, p, s) == durok_g(_, p2, s) : Bool}
  %ep : {durok_g(n, p, s) == durok_g(n, _, s) : Bool}
  {==}

def L.dur_parse_domain(s):
  Equal.trans(Bool, Maybe.is_some(&2, Nat, Dur.parse(s)), durok_g(Dur.first_is(s, 45), Dur.first_is(s, 43), s), durok_g(L.first_is(s, 45), L.first_is(s, 43), s),
    dom.of(Dur.first_is(s, 45), Dur.first_is(s, 43), s),
    g_cong(Dur.first_is(s, 45), L.first_is(s, 45), Dur.first_is(s, 43), L.first_is(s, 43), s, fi_same(s, 45), fi_same(s, 43)))

# ---------------------------------------------------------------------
# dur_parse_sign
# ---------------------------------------------------------------------

def plus.of(a: Bool, b: Bool, +s: String, +ha: {a == Dur.first_is(s, 43) : Bool}, +hb: {b == Dur.first_is(s, 45) : Bool})
  -> {Dur.parse.t(s) == L.pick(Maybe<&2, Nat>, Bool.or(a, b), None{}, Dur.parse.sgn(b, a, s)) : Maybe<&2, Nat>}:
  match a:
    case True{}:
      %ha : {Dur.parse.again(Bool.or(_, Dur.first_is(s, 45)), s) == None{} : Maybe<&2, Nat>}
      {==}
    case False{}:
      match b:
        case True{}:
          %ha : {Dur.parse.again(Bool.or(_, Dur.first_is(s, 45)), s) == None{} : Maybe<&2, Nat>}
          %hb : {Dur.parse.again(Bool.or(False{}, _), s) == None{} : Maybe<&2, Nat>}
          {==}
        case False{}:
          %ha : {Dur.parse.again(Bool.or(_, Dur.first_is(s, 45)), s) == Dur.parse.again(Bool.or(_, Dur.first_is(s, 45)), s) : Maybe<&2, Nat>}
          %hb : {Dur.parse.again(Bool.or(False{}, _), s) == Dur.parse.again(Bool.or(False{}, _), s) : Maybe<&2, Nat>}
          {==}

def plus_cong(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool, -r: Maybe<&2, Nat>, ea: {a == a2 : Bool}, eb: {b == b2 : Bool})
  -> {L.pick(Maybe<&2, Nat>, Bool.or(a, b), None{}, r) == L.pick(Maybe<&2, Nat>, Bool.or(a2, b2), None{}, r) : Maybe<&2, Nat>}:
  %ea : {L.pick(Maybe<&2, Nat>, Bool.or(a, b), None{}, r) == L.pick(Maybe<&2, Nat>, Bool.or(_, b2), None{}, r) : Maybe<&2, Nat>}
  %eb : {L.pick(Maybe<&2, Nat>, Bool.or(a, b), None{}, r) == L.pick(Maybe<&2, Nat>, Bool.or(a, _), None{}, r) : Maybe<&2, Nat>}
  {==}

def of_pick(v: Bool) -> {Dur.parse.of(v, 0n) == L.pick(Maybe<&2, Nat>, v, Some{0n}, None{}) : Maybe<&2, Nat>}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def of_cong(-v: Bool, -w: Bool, e: {v == w : Bool}) -> {Dur.parse.of(v, 0n) == Dur.parse.of(w, 0n) : Maybe<&2, Nat>}:
  %e : {Dur.parse.of(v, 0n) == Dur.parse.of(_, 0n) : Maybe<&2, Nat>}
  {==}

def drop0(s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      {==}

def pt_cong(-x: String, -y: String, e: {x == y : String}) -> {Dur.parse.t(x) == Dur.parse.t(y) : Maybe<&2, Nat>}:
  %e : {Dur.parse.t(x) == Dur.parse.t(_) : Maybe<&2, Nat>}
  {==}

def sign_plus(+s: String)
  -> {Dur.parse(String.append("+", s)) == L.pick(Maybe<&2, Nat>, Bool.or(L.first_is(s, 43), L.first_is(s, 45)), None{}, Dur.parse(s)) : Maybe<&2, Nat>}:
  Equal.trans(Maybe<&2, Nat>, Dur.parse.t(String.drop(s, 0n)), Dur.parse.t(s), L.pick(Maybe<&2, Nat>, Bool.or(L.first_is(s, 43), L.first_is(s, 45)), None{}, Dur.parse(s)),
    pt_cong(String.drop(s, 0n), s, drop0(s)),
    Equal.trans(Maybe<&2, Nat>, Dur.parse.t(s), L.pick(Maybe<&2, Nat>, Bool.or(Dur.first_is(s, 43), Dur.first_is(s, 45)), None{}, Dur.parse(s)),
      L.pick(Maybe<&2, Nat>, Bool.or(L.first_is(s, 43), L.first_is(s, 45)), None{}, Dur.parse(s)),
      plus.of(Dur.first_is(s, 43), Dur.first_is(s, 45), s, {==}, {==}),
      plus_cong(Dur.first_is(s, 43), L.first_is(s, 43), Dur.first_is(s, 45), L.first_is(s, 45), Dur.parse(s), fi_same(s, 43), fi_same(s, 45))))

def sign_minus(+s: String)
  -> {Dur.parse(String.append("-", s)) == L.pick(Maybe<&2, Nat>, L.dur_ok(String.append("-", s)), Some{0n}, None{}) : Maybe<&2, Nat>}:
  +t = String.drop(s, 0n)
  +vd = Bool.and(Bool.not(Bool.or(Dur.first_is(t, 43), Dur.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(Dur.terms_ok(String.length(t), t), Bool.not(Dur.has_nonzero_digit(t)))))
  +vl = Bool.and(Bool.not(Bool.or(L.first_is(t, 43), L.first_is(t, 45))), Bool.or(String.eq(t, "0"), Bool.and(L.terms_ok(String.length(t), t), Bool.not(L.has_nonzero_digit(t)))))
  Equal.trans(Maybe<&2, Nat>, Dur.parse.of(vd, 0n), Dur.parse.of(vl, 0n), L.pick(Maybe<&2, Nat>, vl, Some{0n}, None{}),
    of_cong(vd, vl, neg_same(t)), of_pick(vl))

def L.dur_parse_sign(s):
  (sign_plus(s), sign_minus(s), {==})

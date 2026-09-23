# Proofs of the calendar laws (civil_*).
#
# lib/civil.bend counts days as LAWS' days_of does and writes RFC3339 as
# rfc_text does; its picks and helpers are its own, so they are related to
# LAWS' by the lemmas below. Instants compare and add in nanoseconds with
# the second count first (Nat.mul(s, 1000000000n): a literal-first product
# would unfold into 10^9 terms).
import Base
import ../LAWS.bend as L
import ../lib/dec.bend as Dec
import ../lib/civil.bend as Civil
import ./nat.bend as PNat

def pickN(c: Bool, +a: Nat, +b: Nat, +a2: Nat, +b2: Nat, +ea: {a == a2 : Nat}, +eb: {b == b2 : Nat})
  -> {Civil.pick(Nat, c, a, b) == L.pick(Nat, c, a2, b2) : Nat}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def pickS(c: Bool, +a: String, +b: String, +a2: String, +b2: String, +ea: {a == a2 : String}, +eb: {b == b2 : String})
  -> {Civil.pick(String, c, a, b) == L.pick(String, c, a2, b2) : String}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def add_cong(-a: Nat, -a2: Nat, -b: Nat, -b2: Nat, ea: {a == a2 : Nat}, eb: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  %ea : {Nat.add(a, b) == Nat.add(_, b2) : Nat}
  %eb : {Nat.add(a, b) == Nat.add(a, _) : Nat}
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
# civil_days: the day count is the calendar's
# ---------------------------------------------------------------------

def year_len_same(+y: Nat) -> {Civil.year_len(y) == L.year_len(y) : Nat}:
  pickN(Civil.leap(y), 366n, 365n, 366n, 365n, {==}, {==})

def month_len_same(+y: Nat, +m: Nat) -> {Civil.month_len(y, m) == L.month_len(y, m) : Nat}:
  +short = Bool.or(Bool.or(Nat.is_eq(m, 4n), Nat.is_eq(m, 6n)), Bool.or(Nat.is_eq(m, 9n), Nat.is_eq(m, 11n)))
  pickN(Nat.is_eq(m, 2n), Civil.pick(Nat, Civil.leap(y), 29n, 28n), Civil.pick(Nat, short, 30n, 31n), L.pick(Nat, Civil.leap(y), 29n, 28n), L.pick(Nat, short, 30n, 31n),
    pickN(Civil.leap(y), 29n, 28n, 29n, 28n, {==}, {==}), pickN(short, 30n, 31n, 30n, 31n, {==}, {==}))

def years_same(c: Nat) -> {Civil.days_in_years(c) == L.days_in_years(c) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      add_cong(Civil.days_in_years(p), L.days_in_years(p), Civil.year_len(Nat.add(1970n, p)), L.year_len(Nat.add(1970n, p)),
        years_same(p), year_len_same(Nat.add(1970n, p)))

def months_same(k: Nat, +y: Nat) -> {Civil.days_in_months(k, y) == L.days_in_months(k, y) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      add_cong(Civil.days_in_months(p, y), L.days_in_months(p, y), Civil.month_len(y, 1n+p), L.month_len(y, 1n+p),
        months_same(p, y), month_len_same(y, 1n+p))

def days_same(+y: Nat, +m: Nat, +d: Nat) -> {Civil.ymd_to_days(y, m, d) == L.days_of(y, m, d) : Nat}:
  add_cong(Civil.days_in_years(Nat.sub(y, 1970n)), L.days_in_years(Nat.sub(y, 1970n)),
    Nat.add(Civil.days_in_months(Nat.sub(m, 1n), y), Nat.sub(d, 1n)), Nat.add(L.days_in_months(Nat.sub(m, 1n), y), Nat.sub(d, 1n)),
    years_same(Nat.sub(y, 1970n)),
    add_cong(Civil.days_in_months(Nat.sub(m, 1n), y), L.days_in_months(Nat.sub(m, 1n), y), Nat.sub(d, 1n), Nat.sub(d, 1n), months_same(Nat.sub(m, 1n), y), {==}))

def L.civil_days(y, m, d, h):
  days_same(y, m, d)

# ---------------------------------------------------------------------
# civil_rfc3339: the text is rfc_text
# ---------------------------------------------------------------------

def strip_same(s: String) -> {Civil.strip_zeros_l(s) == L.strip_zeros_l(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          pickS(U32.is_eq(k, 48), Civil.strip_zeros_l(rest), SCon{Chr{k}, rest}, L.strip_zeros_l(rest), SCon{Chr{k}, rest}, strip_same(rest), {==})

def trim_same(+s: String) -> {Civil.trim_zeros_r(s) == L.trim_zeros_r(s) : String}:
  %strip_same(String.reverse(s)) : {String.reverse(Civil.strip_zeros_l(String.reverse(s))) == String.reverse(_) : String}
  {==}

def frac_same(+r: Nat, +prec: Nat) -> {Civil.frac_text(r, prec) == L.frac_text(r, prec) : String}:
  pickS(Nat.is_eq(r, 0n), "", String.append(".", Civil.trim_zeros_r(Dec.pad(prec, r))), "", String.append(".", L.trim_zeros_r(Dec.pad(prec, r))),
    {==}, app_cong_r(".", Civil.trim_zeros_r(Dec.pad(prec, r)), L.trim_zeros_r(Dec.pad(prec, r)), trim_same(Dec.pad(prec, r))))

def rfc_date_same(+t: Civil.Ymd) -> {Civil.rfc_date(t) == L.rfc_date(t) : String}:
  match t:
    case Civil.Ymd{+y, +m, +d}:
      {==}

def rfc_same(+s: Nat, +ns: Nat, +off: Nat) -> {Civil.rfc3339(Civil.Time{s, ns, off}) == L.rfc_text(Civil.Time{s, ns, off}) : String}:
  app_cong_both(Civil.rfc_date(Civil.days_to_ymd(Nat.div(Nat.sub(Nat.add(s, off), 86400n), 86400n))), L.rfc_date(Civil.days_to_ymd(Nat.div(Nat.sub(Nat.add(s, off), 86400n), 86400n))), String.append("T", String.append(Civil.pad2(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 3600n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(Civil.frac_text(ns, 9n), Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))))))))))), String.append("T", String.append(Civil.pad2(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 3600n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(L.frac_text(ns, 9n), L.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))))))))))), rfc_date_same(Civil.days_to_ymd(Nat.div(Nat.sub(Nat.add(s, off), 86400n), 86400n))), app_cong_r("T", String.append(Civil.pad2(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 3600n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(Civil.frac_text(ns, 9n), Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))))))))))), String.append(Civil.pad2(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 3600n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(L.frac_text(ns, 9n), L.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))))))))))), app_cong_r(Civil.pad2(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 3600n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(Civil.frac_text(ns, 9n), Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))))))))), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(L.frac_text(ns, 9n), L.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))))))))), app_cong_r(":", String.append(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(Civil.frac_text(ns, 9n), Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))))))))), String.append(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(L.frac_text(ns, 9n), L.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))))))))), app_cong_r(Civil.pad2(Nat.mod(Nat.div(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n), 60n)), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(Civil.frac_text(ns, 9n), Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))))))), String.append(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(L.frac_text(ns, 9n), L.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))))))), app_cong_r(":", String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(Civil.frac_text(ns, 9n), Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))))))), String.append(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(L.frac_text(ns, 9n), L.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))))))), app_cong_r(Civil.pad2(Nat.mod(Nat.mod(Nat.sub(Nat.add(s, off), 86400n), 86400n), 60n)), String.append(Civil.frac_text(ns, 9n), Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))))), String.append(L.frac_text(ns, 9n), L.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))))), app_cong_both(Civil.frac_text(ns, 9n), L.frac_text(ns, 9n), Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))))), L.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))))), frac_same(ns, 9n), pickS(Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))), "Z", String.append(L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n))))), {==}, app_cong_l(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"), L.pick(String, Nat.is_gt(off, 86400n), "+", "-"), String.append(Civil.pad2(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(Nat.add(Nat.sub(off, 86400n), Nat.sub(86400n, off)), 60n), 60n)))), pickS(Nat.is_gt(off, 86400n), "+", "-", "+", "-", {==}, {==})))))))))))

def L.civil_rfc3339(t, h):
  match t:
    case Civil.Time{+s, +ns, +off}:
      rfc_same(s, ns, off)

# ---------------------------------------------------------------------
# civil_cmp and civil_add_sub: instants in nanoseconds
# ---------------------------------------------------------------------

def cmp_cancel(b: Nat, -x: Nat, -y: Nat) -> {Nat.cmp(Nat.add(b, x), Nat.add(b, y)) == Nat.cmp(x, y) : Cmp}:
  match b:
    case 0n:
      {==}
    case 1n++p:
      cmp_cancel(p, x, y)

def cmp_lt_base(x: Nat, b: Nat, -w: Nat, +h: {Nat.is_lt(x, b) == True{} : Bool}) -> {Nat.cmp(x, Nat.add(b, w)) == LT{} : Cmp}:
  match x:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(0n, w) == LT{} : Cmp}, PNat.false_ne_true(h))
        case 1n++p:
          {==}
    case 1n++xp:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(1n+xp, w) == LT{} : Cmp}, PNat.false_ne_true(h))
        case 1n++p:
          cmp_lt_base(xp, p, w, h)

def cmp_gt_base(y: Nat, b: Nat, -w: Nat, +h: {Nat.is_lt(y, b) == True{} : Bool}) -> {Nat.cmp(Nat.add(b, w), y) == GT{} : Cmp}:
  match y:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(w, 0n) == GT{} : Cmp}, PNat.false_ne_true(h))
        case 1n++p:
          {==}
    case 1n++yp:
      match b:
        case 0n:
          Empty.absurd({Nat.cmp(w, 1n+yp) == GT{} : Cmp}, PNat.false_ne_true(h))
        case 1n++p:
          cmp_gt_base(yp, p, w, h)

# comparing x + B a with y + B b (digits x, y below B): the high parts first

def add_zero_r(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  Equal.sym(Nat, a, Nat.add(a, 0n), PNat.add_zero(a))

def then(c: Cmp, x: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      x
    case GT{}:
      GT{}

def pick_then(c: Cmp, +x: Cmp) -> {Civil.pick(Cmp, Cmp.is_eq(c), x, c) == then(c, x) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# comparing x + a b with y + c b (x, y below b): the high parts first
def lex2(a: Nat, c: Nat, +x: Nat, +y: Nat, +b: Nat, +hx: {Nat.is_lt(x, b) == True{} : Bool}, +hy: {Nat.is_lt(y, b) == True{} : Bool})
  -> {Nat.cmp(Nat.add(x, Nat.mul(a, b)), Nat.add(y, Nat.mul(c, b))) == then(Nat.cmp(a, c), Nat.cmp(x, y)) : Cmp}:
  match a:
    case 0n:
      match c:
        case 0n:
          %PNat.add_zero(x) : {Nat.cmp(_, Nat.add(y, 0n)) == Nat.cmp(x, y) : Cmp}
          %PNat.add_zero(y) : {Nat.cmp(x, _) == Nat.cmp(x, y) : Cmp}
          {==}
        case 1n++cp:
          %PNat.add_zero(x) : {Nat.cmp(_, Nat.add(y, Nat.add(b, Nat.mul(cp, b)))) == LT{} : Cmp}
          %PNat.add_swap(b, y, Nat.mul(cp, b)) : {Nat.cmp(x, _) == LT{} : Cmp}
          cmp_lt_base(x, b, Nat.add(y, Nat.mul(cp, b)), hx)
    case 1n++ap:
      match c:
        case 0n:
          %PNat.add_zero(y) : {Nat.cmp(Nat.add(x, Nat.add(b, Nat.mul(ap, b))), _) == GT{} : Cmp}
          %PNat.add_swap(b, x, Nat.mul(ap, b)) : {Nat.cmp(_, y) == GT{} : Cmp}
          cmp_gt_base(y, b, Nat.add(x, Nat.mul(ap, b)), hy)
        case 1n++cp:
          %PNat.add_swap(b, x, Nat.mul(ap, b)) : {Nat.cmp(_, Nat.add(y, Nat.add(b, Nat.mul(cp, b)))) == then(Nat.cmp(ap, cp), Nat.cmp(x, y)) : Cmp}
          %PNat.add_swap(b, y, Nat.mul(cp, b)) : {Nat.cmp(Nat.add(b, Nat.add(x, Nat.mul(ap, b))), _) == then(Nat.cmp(ap, cp), Nat.cmp(x, y)) : Cmp}
          %Equal.sym(Cmp, Nat.cmp(Nat.add(b, Nat.add(x, Nat.mul(ap, b))), Nat.add(b, Nat.add(y, Nat.mul(cp, b)))), Nat.cmp(Nat.add(x, Nat.mul(ap, b)), Nat.add(y, Nat.mul(cp, b))),
              cmp_cancel(b, Nat.add(x, Nat.mul(ap, b)), Nat.add(y, Nat.mul(cp, b))))
            : {_ == then(Nat.cmp(ap, cp), Nat.cmp(x, y)) : Cmp}
          lex2(ap, cp, x, y, b, hx, hy)

# s B + n == (n mod B) + (s + n / B) B, for B = 1 + b
def norm_eq(+s: Nat, +n: Nat, +b: Nat)
  -> {Nat.add(Nat.mul(s, 1n+b), n) == Nat.add(Nat.mod(n, 1n+b), Nat.mul(Nat.add(s, Nat.div(n, 1n+b)), 1n+b)) : Nat}:
  +q = Nat.div(n, 1n+b)
  +r = Nat.mod(n, 1n+b)
  +sb = Nat.mul(s, 1n+b)
  +qb = Nat.mul(q, 1n+b)
  %PNat.mul_dist(s, q, 1n+b) : {Nat.add(sb, n) == Nat.add(r, _) : Nat}
  %Equal.sym(Nat, n, Nat.add(qb, r), PNat.div_mod_eq(n, b)) : {Nat.add(sb, _) == Nat.add(r, Nat.add(sb, qb)) : Nat}
  %PNat.add_comm(r, qb) : {Nat.add(sb, _) == Nat.add(r, Nat.add(sb, qb)) : Nat}
  PNat.add_swap(sb, r, qb)

def cmp_same(+s: Nat, +ns: Nat, +o1: Nat, +t: Nat, +nt: Nat, +o2: Nat)
  -> {Civil.cmp(Civil.Time{s, ns, o1}, Civil.Time{t, nt, o2}) == Nat.cmp(Nat.add(Nat.mul(s, 1000000000n), ns), Nat.add(Nat.mul(t, 1000000000n), nt)) : Cmp}:
  +sa = Nat.add(s, Nat.div(ns, 1000000000n))
  +sb = Nat.add(t, Nat.div(nt, 1000000000n))
  +na = Nat.mod(ns, 1000000000n)
  +nb = Nat.mod(nt, 1000000000n)
  +lhs = Civil.pick(Cmp, Cmp.is_eq(Nat.cmp(sa, sb)), Nat.cmp(na, nb), Nat.cmp(sa, sb))
  %Equal.sym(Nat, Nat.add(Nat.mul(s, 1000000000n), ns), Nat.add(na, Nat.mul(sa, 1000000000n)), norm_eq(s, ns, 999999999n))
    : {lhs == Nat.cmp(_, Nat.add(Nat.mul(t, 1000000000n), nt)) : Cmp}
  %Equal.sym(Nat, Nat.add(Nat.mul(t, 1000000000n), nt), Nat.add(nb, Nat.mul(sb, 1000000000n)), norm_eq(t, nt, 999999999n))
    : {lhs == Nat.cmp(Nat.add(na, Nat.mul(sa, 1000000000n)), _) : Cmp}
  %Equal.sym(Cmp, Nat.cmp(Nat.add(na, Nat.mul(sa, 1000000000n)), Nat.add(nb, Nat.mul(sb, 1000000000n))), then(Nat.cmp(sa, sb), Nat.cmp(na, nb)),
      lex2(sa, sb, na, nb, 1000000000n, PNat.mod_lt(ns, 999999999n), PNat.mod_lt(nt, 999999999n)))
    : {lhs == _ : Cmp}
  pick_then(Nat.cmp(sa, sb), Nat.cmp(na, nb))

def L.civil_cmp(a, b):
  match a:
    case Civil.Time{+s, +ns, +off}:
      match b:
        case Civil.Time{+t, +nt, +ot}:
          cmp_same(s, ns, off, t, nt, ot)

def add_sub(u: Nat, z: Nat, +h: {Nat.is_le(u, z) == True{} : Bool}) -> {Nat.add(u, Nat.sub(z, u)) == z : Nat}:
  match u:
    case 0n:
      match z:
        case 0n:
          {==}
        case 1n++zp:
          {==}
    case 1n++up:
      match z:
        case 0n:
          Empty.absurd({Nat.add(1n+up, 0n) == 0n : Nat}, PNat.false_ne_true(h))
        case 1n++zp:
          %add_sub(up, zp, h) : {1n+Nat.add(up, Nat.sub(zp, up)) == 1n+_ : Nat}
          {==}

# ---------------------------------------------------------------------
# Subtraction
# ---------------------------------------------------------------------

def nlt_le(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, h)))
    case 1n++ap:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          nlt_le(ap, bp, h)

def add_val(+s: Nat, +ns: Nat, +n: Nat)
  -> {Nat.add(Nat.mul(Nat.add(s, Nat.div(Nat.add(ns, n), 1000000000n)), 1000000000n), Nat.mod(Nat.add(ns, n), 1000000000n)) == Nat.add(Nat.add(Nat.mul(s, 1000000000n), ns), n) : Nat}:
  +x = Nat.add(ns, n)
  +rhs = Nat.add(Nat.add(Nat.mul(s, 1000000000n), ns), n)
  %PNat.add_comm(Nat.mod(x, 1000000000n), Nat.mul(Nat.add(s, Nat.div(x, 1000000000n)), 1000000000n)) : {_ == rhs : Nat}
  %norm_eq(s, x, 999999999n) : {_ == rhs : Nat}
  PNat.add_assoc(Nat.mul(s, 1000000000n), ns, n)

def cmp_lt(c: Cmp, h: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, PNat.false_ne_true(h))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, PNat.false_ne_true(h))

def then_lt(-c: Cmp, -x: Cmp, e: {c == LT{} : Cmp}) -> {then(c, x) == LT{} : Cmp}:
  %Equal.sym(Cmp, c, LT{}, e) : {then(_, x) == LT{} : Cmp}
  {==}

def not_lt_t(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

def eq_ne_lt(e: {EQ{} == LT{} : Cmp}) -> Empty:
  %e : not_lt_t(_)
  Unit{}

def gt_ne_lt(e: {GT{} == LT{} : Cmp}) -> Empty:
  %e : not_lt_t(_)
  Unit{}

def sub_of_lt(x: Nat, y: Nat, h: {Nat.cmp(x, y) == LT{} : Cmp}) -> {Nat.sub(x, y) == 0n : Nat}:
  match x:
    case 0n:
      match y:
        case 0n:
          Empty.absurd({Nat.sub(0n, 0n) == 0n : Nat}, eq_ne_lt(h))
        case 1n++yp:
          {==}
    case 1n++xp:
      match y:
        case 0n:
          Empty.absurd({Nat.sub(1n+xp, 0n) == 0n : Nat}, gt_ne_lt(h))
        case 1n++yp:
          sub_of_lt(xp, yp, h)

def sub_cancel_l(c: Nat, -x: Nat, -y: Nat) -> {Nat.sub(Nat.add(c, x), Nat.add(c, y)) == Nat.sub(x, y) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      sub_cancel_l(p, x, y)

def sub_fin(v: Bool, +sa: Nat, +sb: Nat, +na: Nat, +nb: Nat, +hv: {v == Nat.is_lt(sa, sb) : Bool},
  +hna: {Nat.is_lt(na, 1000000000n) == True{} : Bool}, +hnb: {Nat.is_lt(nb, 1000000000n) == True{} : Bool})
  -> {Civil.pick(Nat, v, 0n, Nat.sub(Nat.add(Nat.mul(Nat.sub(sa, sb), 1000000000n), na), nb)) == Nat.sub(Nat.add(na, Nat.mul(sa, 1000000000n)), Nat.add(nb, Nat.mul(sb, 1000000000n))) : Nat}:
  match v:
    case True{}:
      +x = Nat.add(na, Nat.mul(sa, 1000000000n))
      +y = Nat.add(nb, Nat.mul(sb, 1000000000n))
      +lt = Equal.trans(Cmp, Nat.cmp(x, y), then(Nat.cmp(sa, sb), Nat.cmp(na, nb)), LT{}, lex2(sa, sb, na, nb, 1000000000n, hna, hnb),
        then_lt(Nat.cmp(sa, sb), Nat.cmp(na, nb), cmp_lt(Nat.cmp(sa, sb), Equal.sym(Bool, True{}, Nat.is_lt(sa, sb), hv))))
      Equal.sym(Nat, Nat.sub(x, y), 0n, sub_of_lt(x, y, lt))
    case False{}:
      +k = Nat.sub(sa, sb)
      +sbb = Nat.mul(sb, 1000000000n)
      +kb = Nat.mul(k, 1000000000n)
      +lhs = Nat.sub(Nat.add(kb, na), nb)
      %add_sub(sb, sa, nlt_le(sa, sb, Equal.sym(Bool, False{}, Nat.is_lt(sa, sb), hv))) : {lhs == Nat.sub(Nat.add(na, Nat.mul(_, 1000000000n)), Nat.add(nb, sbb)) : Nat}
      %PNat.mul_dist(sb, k, 1000000000n) : {lhs == Nat.sub(Nat.add(na, _), Nat.add(nb, sbb)) : Nat}
      %PNat.add_swap(sbb, na, kb) : {lhs == Nat.sub(_, Nat.add(nb, sbb)) : Nat}
      %PNat.add_comm(sbb, nb) : {lhs == Nat.sub(Nat.add(sbb, Nat.add(na, kb)), _) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(sbb, Nat.add(na, kb)), Nat.add(sbb, nb)), Nat.sub(Nat.add(na, kb), nb), sub_cancel_l(sbb, Nat.add(na, kb), nb)) : {lhs == _ : Nat}
      %PNat.add_comm(kb, na) : {lhs == Nat.sub(_, nb) : Nat}
      {==}

def sub_same(+us: Nat, +un: Nat, +uo: Nat, +s: Nat, +ns: Nat, +off: Nat)
  -> {Civil.sub_ns(Civil.Time{us, un, uo}, Civil.Time{s, ns, off}) == Nat.sub(Nat.add(Nat.mul(us, 1000000000n), un), Nat.add(Nat.mul(s, 1000000000n), ns)) : Nat}:
  +sa = Nat.add(us, Nat.div(un, 1000000000n))
  +sb = Nat.add(s, Nat.div(ns, 1000000000n))
  +na = Nat.mod(un, 1000000000n)
  +nb = Nat.mod(ns, 1000000000n)
  +lhs = Civil.pick(Nat, Nat.is_lt(sa, sb), 0n, Nat.sub(Nat.add(Nat.mul(Nat.sub(sa, sb), 1000000000n), na), nb))
  %Equal.sym(Nat, Nat.add(Nat.mul(us, 1000000000n), un), Nat.add(na, Nat.mul(sa, 1000000000n)), norm_eq(us, un, 999999999n))
    : {lhs == Nat.sub(_, Nat.add(Nat.mul(s, 1000000000n), ns)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(s, 1000000000n), ns), Nat.add(nb, Nat.mul(sb, 1000000000n)), norm_eq(s, ns, 999999999n))
    : {lhs == Nat.sub(Nat.add(na, Nat.mul(sa, 1000000000n)), _) : Nat}
  sub_fin(Nat.is_lt(sa, sb), sa, sb, na, nb, {==}, PNat.mod_lt(un, 999999999n), PNat.mod_lt(ns, 999999999n))

def L.civil_add_sub(t, u, n, h):
  match t:
    case Civil.Time{+s, +ns, +off}:
      match u:
        case Civil.Time{+us, +un, +uo}:
          (add_val(s, ns, n), {==}, PNat.mod_lt(Nat.add(ns, n), 999999999n), sub_same(us, un, uo, s, ns, off))

# ---------------------------------------------------------------------
# civil_days_ymd and civil_ymd_days: counting years and months out
# ---------------------------------------------------------------------

def and_i(-a: Bool, -b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# and(a, b) is false with b true: a is false

def le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      {==}

def le0(z: Nat, +h: {Nat.is_le(z, 0n) == True{} : Bool}) -> {z == 0n : Nat}:
  match z:
    case 0n:
      {==}
    case 1n++p:
      Empty.absurd({1n+p == 0n : Nat}, PNat.false_ne_true(h))

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      le_refl(p)

def le_succ(a: Nat) -> {Nat.is_le(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      le_succ(p)

def le_trans(a: Nat, b: Nat, c: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      le_zero(c)
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, PNat.false_ne_true(h1))
        case 1n++bp:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, PNat.false_ne_true(h2))
            case 1n++cp:
              le_trans(ap, bp, cp, h1, h2)

def lt_to_le(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          le_zero(bp)
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(2n+ap, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          lt_to_le(ap, bp, h)

def le_to_lt(a: Nat, b: Nat, +h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          {==}
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, PNat.false_ne_true(h))
        case 1n++bp:
          le_to_lt(ap, bp, h)

def le_add(x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      le_zero(y)
    case 1n++p:
      le_add(p, y)

def lt_le_absurd(e: Nat, b: Nat, +h1: {Nat.is_lt(e, b) == True{} : Bool}, +h2: {Nat.is_le(b, e) == True{} : Bool}) -> Empty:
  match e:
    case 0n:
      match b:
        case 0n:
          PNat.false_ne_true(h1)
        case 1n++bp:
          PNat.false_ne_true(h2)
    case 1n++ep:
      match b:
        case 0n:
          PNat.false_ne_true(h1)
        case 1n++bp:
          lt_le_absurd(ep, bp, h1, h2)

# a B <= c B + e with e < B: a <= c

def cmp_refl(n: Nat) -> {Nat.cmp(n, n) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      cmp_refl(p)

def le_rw_r(-a: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, +h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(a, y) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

def le_rw_l(-x: Nat, -y: Nat, -b: Nat, e: {x == y : Nat}, +h: {Nat.is_le(x, b) == True{} : Bool}) -> {Nat.is_le(y, b) == True{} : Bool}:
  %e : {Nat.is_le(_, b) == True{} : Bool}
  h

def lt_rw_l(-x: Nat, -y: Nat, -b: Nat, e: {x == y : Nat}, +h: {Nat.is_lt(x, b) == True{} : Bool}) -> {Nat.is_lt(y, b) == True{} : Bool}:
  %e : {Nat.is_lt(_, b) == True{} : Bool}
  h

def P2(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

def P2.fst(-A: Data, -B: Data, +p: P2(A, B)) -> A:
  (a, b) = p
  a

def P2.snd(-A: Data, -B: Data, +p: P2(A, B)) -> B:
  (a, b) = p
  b

def sub0(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      {==}

def ge0(n: Nat) -> {Nat.is_ge(n, 0n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      {==}

def eq_is_eq(-a: Nat, +b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_eq(_, b) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(b, b), EQ{}, cmp_refl(b)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def sub_le(a: Nat, b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          {==}
    case 1n++ap:
      match b:
        case 0n:
          le_refl(1n+ap)
        case 1n++bp:
          le_trans(Nat.sub(ap, bp), ap, 1n+ap, sub_le(ap, bp), le_succ(ap))

# r <= 1 + f and y >= 1: r - y <= f
def sub_le_pred(r: Nat, y: Nat, +f: Nat, +h1: {Nat.is_le(1n, y) == True{} : Bool}, +h2: {Nat.is_le(r, 1n+f) == True{} : Bool})
  -> {Nat.is_le(Nat.sub(r, y), f) == True{} : Bool}:
  match r:
    case 0n:
      match y:
        case 0n:
          Empty.absurd({Nat.is_le(0n, f) == True{} : Bool}, PNat.false_ne_true(h1))
        case 1n++yp:
          le_zero(f)
    case 1n++rp:
      match y:
        case 0n:
          Empty.absurd({Nat.is_le(1n+rp, f) == True{} : Bool}, PNat.false_ne_true(h1))
        case 1n++yp:
          le_trans(Nat.sub(rp, yp), rp, f, sub_le(rp, yp), h2)

# (d + y) + (r - y) == d + r, for y <= r
def step_eq(+d: Nat, +y: Nat, +r: Nat, +ge: {Nat.is_le(y, r) == True{} : Bool}) -> {Nat.add(Nat.add(d, y), Nat.sub(r, y)) == Nat.add(d, r) : Nat}:
  %PNat.add_assoc(d, y, Nat.sub(r, y)) : {_ == Nat.add(d, r) : Nat}
  %add_sub(y, r, ge) : {Nat.add(d, Nat.add(y, Nat.sub(r, y))) == Nat.add(d, _) : Nat}
  {==}

def yl_pos.of(v: Bool) -> {Nat.is_le(1n, Civil.pick(Nat, v, 366n, 365n)) == True{} : Bool}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def yl_pos(+y: Nat) -> {Nat.is_le(1n, Civil.year_len(y)) == True{} : Bool}:
  yl_pos.of(Civil.leap(y))

def YSpec(+x: Civil.CR, +n: Nat) -> Data:
  P2({Nat.add(Civil.days_in_years(Civil.CR.c(x)), Civil.CR.r(x)) == n : Nat},
     {Nat.is_lt(Civil.CR.r(x), Civil.year_len(Nat.add(1970n, Civil.CR.c(x)))) == True{} : Bool})

# counting years out: diy(C) + R == n with R within year C
def years_spec(f: Nat, stop: Bool, +c: Nat, +r: Nat, +n: Nat,
  +hs: {stop == Nat.is_lt(r, Civil.year_len(Nat.add(1970n, c))) : Bool},
  +hf: {Nat.is_le(r, f) == True{} : Bool},
  +hn: {Nat.add(Civil.days_in_years(c), r) == n : Nat})
  -> YSpec(Civil.years.go(f, stop, c, r), n):
  match f:
    case 0n:
      +yl = Civil.year_len(Nat.add(1970n, c))
      (hn, lt_rw_l(0n, r, yl, Equal.sym(Nat, r, 0n, le0(r, hf)), le_to_lt(0n, yl, yl_pos(Nat.add(1970n, c)))))
    case 1n++fp:
      match stop:
        case True{}:
          (hn, Equal.sym(Bool, True{}, Nat.is_lt(r, Civil.year_len(Nat.add(1970n, c))), hs))
        case False{}:
          +y = Nat.add(1970n, c)
          +yl = Civil.year_len(y)
          +ge = nlt_le(r, yl, Equal.sym(Bool, False{}, Nat.is_lt(r, yl), hs))
          +r2 = Nat.sub(r, yl)
          years_spec(fp, Nat.is_lt(r2, Civil.year_len(Nat.add(1970n, 1n+c))), 1n+c, r2, n, {==},
            sub_le_pred(r, yl, fp, yl_pos(y), hf),
            Equal.trans(Nat, Nat.add(Nat.add(Civil.days_in_years(c), yl), r2), Nat.add(Civil.days_in_years(c), r), n, step_eq(Civil.days_in_years(c), yl, r, ge), hn))

def dimg(v: Bool) -> {Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(Nat.add(0n, 31n), Civil.pick(Nat, v, 29n, 28n)), 31n), 30n), 31n), 30n), 31n), 31n), 30n), 31n), 30n), 31n) == Civil.pick(Nat, v, 366n, 365n) : Nat}:
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

def dim12(+y: Nat) -> {Civil.days_in_months(12n, y) == Civil.year_len(y) : Nat}:
  dimg(Civil.leap(y))

def dim_cong(-k: Nat, -k2: Nat, -y: Nat, e: {k == k2 : Nat}) -> {Civil.days_in_months(k, y) == Civil.days_in_months(k2, y) : Nat}:
  %e : {Civil.days_in_months(k, y) == Civil.days_in_months(_, y) : Nat}
  {==}

def MSpec(+x: Civil.CR, +y: Nat, +n: Nat) -> Data:
  P2(P2({Nat.add(Civil.days_in_months(Civil.CR.c(x), y), Civil.CR.r(x)) == n : Nat},
        {Nat.is_lt(Civil.CR.r(x), Civil.month_len(y, 1n+Civil.CR.c(x))) == True{} : Bool}),
     {Nat.is_le(Civil.CR.c(x), 11n) == True{} : Bool})

# counting months out: dim(K) + R == n with R within month 1 + K, K <= 11
def months_spec(f: Nat, stop: Bool, +y: Nat, +k: Nat, +r: Nat, +n: Nat,
  +hs: {stop == Nat.is_lt(r, Civil.month_len(y, 1n+k)) : Bool},
  +hk: {Nat.add(k, f) == 12n : Nat},
  +hn: {Nat.add(Civil.days_in_months(k, y), r) == n : Nat},
  +hy: {Nat.is_lt(n, Civil.year_len(y)) == True{} : Bool})
  -> MSpec(Civil.months.go(f, stop, y, k, r), y, n):
  match f:
    case 0n:
      +ek = Equal.trans(Nat, k, Nat.add(k, 0n), 12n, PNat.add_zero(k), hk)
      +e = Equal.trans(Nat, Civil.days_in_months(k, y), Civil.days_in_months(12n, y), Civil.year_len(y), dim_cong(k, 12n, y, ek), dim12(y))
      +h1 = le_rw_r(Civil.days_in_months(k, y), Nat.add(Civil.days_in_months(k, y), r), n, hn, le_add(Civil.days_in_months(k, y), r))
      Empty.absurd(MSpec(Civil.months.go(0n, stop, y, k, r), y, n),
        lt_le_absurd(n, Civil.year_len(y), hy, le_rw_l(Civil.days_in_months(k, y), Civil.year_len(y), n, e, h1)))
    case 1n++fp:
      match stop:
        case True{}:
          +e11 = PNat.succ_inj(Nat.add(k, fp), 11n, Equal.trans(Nat, 1n+Nat.add(k, fp), Nat.add(k, 1n+fp), 12n, PNat.add_succ(k, fp), hk))
          ((hn, Equal.sym(Bool, True{}, Nat.is_lt(r, Civil.month_len(y, 1n+k)), hs)), le_rw_r(k, Nat.add(k, fp), 11n, e11, le_add(k, fp)))
        case False{}:
          +ml = Civil.month_len(y, 1n+k)
          +ge = nlt_le(r, ml, Equal.sym(Bool, False{}, Nat.is_lt(r, ml), hs))
          +r2 = Nat.sub(r, ml)
          months_spec(fp, Nat.is_lt(r2, Civil.month_len(y, 2n+k)), y, 1n+k, r2, n, {==},
            Equal.trans(Nat, 1n+Nat.add(k, fp), Nat.add(k, 1n+fp), 12n, PNat.add_succ(k, fp), hk),
            Equal.trans(Nat, Nat.add(Nat.add(Civil.days_in_months(k, y), ml), r2), Nat.add(Civil.days_in_months(k, y), r), n, step_eq(Civil.days_in_months(k, y), ml, r, ge), hn),
            hy)

# ymd_to_days of the date read back is n
def days_back(+n: Nat, +c: Nat, +r1: Nat, +kk: Nat, +rr: Nat,
  +ya: {Nat.add(Civil.days_in_years(c), r1) == n : Nat},
  +ma: {Nat.add(Civil.days_in_months(kk, Nat.add(1970n, c)), rr) == r1 : Nat})
  -> {Civil.ymd_to_days(Nat.add(1970n, c), 1n+kk, 1n+rr) == n : Nat}:
  +y = Nat.add(1970n, c)
  %Equal.sym(Nat, Nat.sub(c, 0n), c, sub0(c)) : {Nat.add(Civil.days_in_years(_), Nat.add(Civil.days_in_months(Nat.sub(kk, 0n), y), Nat.sub(rr, 0n))) == n : Nat}
  %Equal.sym(Nat, Nat.sub(kk, 0n), kk, sub0(kk)) : {Nat.add(Civil.days_in_years(c), Nat.add(Civil.days_in_months(_, y), Nat.sub(rr, 0n))) == n : Nat}
  %Equal.sym(Nat, Nat.sub(rr, 0n), rr, sub0(rr)) : {Nat.add(Civil.days_in_years(c), Nat.add(Civil.days_in_months(kk, y), _)) == n : Nat}
  %Equal.sym(Nat, Nat.add(Civil.days_in_months(kk, y), rr), r1, ma) : {Nat.add(Civil.days_in_years(c), _) == n : Nat}
  ya

# the day number n read back as a date
def back_of(+n: Nat, +c: Nat, +r1: Nat, +kk: Nat, +rr: Nat,
  +ya: {Nat.add(Civil.days_in_years(c), r1) == n : Nat},
  +ma: {Nat.add(Civil.days_in_months(kk, Nat.add(1970n, c)), rr) == r1 : Nat},
  +mb: {Nat.is_lt(rr, Civil.month_len(Nat.add(1970n, c), 1n+kk)) == True{} : Bool},
  +mc: {Nat.is_le(kk, 11n) == True{} : Bool})
  -> {L.civil_ymd_ok(n, Civil.Ymd{Nat.add(1970n, c), 1n+kk, 1n+rr}) == True{} : Bool}:
  +y = Nat.add(1970n, c)
  +valid = and_i(Nat.is_ge(y, 1970n), Bool.and(Bool.and(Nat.is_ge(1n+kk, 1n), Nat.is_le(1n+kk, 12n)), Bool.and(Nat.is_ge(1n+rr, 1n), Nat.is_le(1n+rr, L.month_len(y, 1n+kk)))),
    ge0(c),
    and_i(Bool.and(Nat.is_ge(1n+kk, 1n), Nat.is_le(1n+kk, 12n)), Bool.and(Nat.is_ge(1n+rr, 1n), Nat.is_le(1n+rr, L.month_len(y, 1n+kk))),
      and_i(Nat.is_ge(1n+kk, 1n), Nat.is_le(1n+kk, 12n), ge0(kk), mc),
      and_i(Nat.is_ge(1n+rr, 1n), Nat.is_le(1n+rr, L.month_len(y, 1n+kk)), ge0(rr),
        le_rw_r(1n+rr, Civil.month_len(y, 1n+kk), L.month_len(y, 1n+kk), month_len_same(y, 1n+kk), lt_to_le(rr, Civil.month_len(y, 1n+kk), mb)))))
  and_i(L.valid_date(y, 1n+kk, 1n+rr), Nat.is_eq(Civil.ymd_to_days(y, 1n+kk, 1n+rr), n), valid, eq_is_eq(Civil.ymd_to_days(y, 1n+kk, 1n+rr), n, days_back(n, c, r1, kk, rr, ya, ma)))

def L.civil_days_ymd(n):
  +yr = Civil.years.go(1n+n, Nat.is_lt(n, Civil.year_len(1970n)), 0n, n)
  +ys = years_spec(1n+n, Nat.is_lt(n, Civil.year_len(1970n)), 0n, n, n, {==}, le_succ(n), {==})
  +c = Civil.CR.c(yr)
  +r1 = Civil.CR.r(yr)
  +y = Nat.add(1970n, c)
  +ya = P2.fst({Nat.add(Civil.days_in_years(c), r1) == n : Nat}, {Nat.is_lt(r1, Civil.year_len(y)) == True{} : Bool}, ys)
  +yb = P2.snd({Nat.add(Civil.days_in_years(c), r1) == n : Nat}, {Nat.is_lt(r1, Civil.year_len(y)) == True{} : Bool}, ys)
  +mr = Civil.months.go(12n, Nat.is_lt(r1, Civil.month_len(y, 1n)), y, 0n, r1)
  +ms = months_spec(12n, Nat.is_lt(r1, Civil.month_len(y, 1n)), y, 0n, r1, r1, {==}, {==}, {==}, yb)
  +kk = Civil.CR.c(mr)
  +rr = Civil.CR.r(mr)
  +mab = P2.fst(P2({Nat.add(Civil.days_in_months(kk, y), rr) == r1 : Nat}, {Nat.is_lt(rr, Civil.month_len(y, 1n+kk)) == True{} : Bool}), {Nat.is_le(kk, 11n) == True{} : Bool}, ms)
  +mc = P2.snd(P2({Nat.add(Civil.days_in_months(kk, y), rr) == r1 : Nat}, {Nat.is_lt(rr, Civil.month_len(y, 1n+kk)) == True{} : Bool}), {Nat.is_le(kk, 11n) == True{} : Bool}, ms)
  +ma = P2.fst({Nat.add(Civil.days_in_months(kk, y), rr) == r1 : Nat}, {Nat.is_lt(rr, Civil.month_len(y, 1n+kk)) == True{} : Bool}, mab)
  +mb = P2.snd({Nat.add(Civil.days_in_months(kk, y), rr) == r1 : Nat}, {Nat.is_lt(rr, Civil.month_len(y, 1n+kk)) == True{} : Bool}, mab)
  back_of(n, c, r1, kk, rr, ya, ma, mb, mc)

def succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def le_antisym(a: Nat, b: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          Empty.absurd({0n == 1n+bp : Nat}, PNat.false_ne_true(h2))
    case 1n++ap:
      match b:
        case 0n:
          Empty.absurd({1n+ap == 0n : Nat}, PNat.false_ne_true(h1))
        case 1n++bp:
          succ_cong(ap, bp, le_antisym(ap, bp, h1, h2))

def le_cancel(c: Nat, -a: Nat, -b: Nat) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == Nat.is_le(a, b) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      le_cancel(p, a, b)

def le_add_mono(+c: Nat, +a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.add(c, a), Nat.add(c, b)), Nat.is_le(a, b), True{}, le_cancel(c, a, b), h)

def le_add_l(+x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(y, x)) == True{} : Bool}:
  %PNat.add_comm(x, y) : {Nat.is_le(x, _) == True{} : Bool}
  le_add(x, y)

def dy_cong(-k: Nat, -k2: Nat, e: {k == k2 : Nat}) -> {Civil.days_in_years(k) == Civil.days_in_years(k2) : Nat}:
  %e : {Civil.days_in_years(k) == Civil.days_in_years(_) : Nat}
  {==}

def dm_cong(-k: Nat, -k2: Nat, -yy: Nat, e: {k == k2 : Nat}) -> {Civil.days_in_months(k, yy) == Civil.days_in_months(k2, yy) : Nat}:
  %e : {Civil.days_in_months(k, yy) == Civil.days_in_months(_, yy) : Nat}
  {==}

def dy_mono(j: Nat, +c: Nat) -> {Nat.is_le(Civil.days_in_years(c), Civil.days_in_years(Nat.add(j, c))) == True{} : Bool}:
  match j:
    case 0n:
      le_refl(Civil.days_in_years(c))
    case 1n++jp:
      le_trans(Civil.days_in_years(c), Civil.days_in_years(Nat.add(jp, c)), Civil.days_in_years(1n+Nat.add(jp, c)), dy_mono(jp, c), le_add(Civil.days_in_years(Nat.add(jp, c)), Civil.year_len(Nat.add(1970n, Nat.add(jp, c)))))

# a < b: S(a) + L(a) <= S(b)
def dy_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Civil.days_in_years(a), Civil.year_len(Nat.add(1970n, a))), Civil.days_in_years(b)) == True{} : Bool}:
  +j = Nat.sub(b, 1n+a)
  +e = Equal.trans(Nat, Nat.add(j, 1n+a), Nat.add(1n+a, j), b, PNat.add_comm(j, 1n+a), add_sub(1n+a, b, lt_to_le(a, b, h)))
  le_rw_r(Civil.days_in_years(1n+a), Civil.days_in_years(Nat.add(j, 1n+a)), Civil.days_in_years(b), dy_cong(Nat.add(j, 1n+a), b, e), dy_mono(j, 1n+a))

# S(a) + x == S(b) + y with a < b and x < L(a) is impossible
def dy_no(+a: Nat, +b: Nat, +x: Nat, +y: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool},
  +e: {Nat.add(Civil.days_in_years(a), x) == Nat.add(Civil.days_in_years(b), y) : Nat}, +hx: {Nat.is_lt(x, Civil.year_len(Nat.add(1970n, a))) == True{} : Bool}) -> Empty:
  +h1 = le_trans(Nat.add(Civil.days_in_years(a), Civil.year_len(Nat.add(1970n, a))), Civil.days_in_years(b), Nat.add(Civil.days_in_years(b), y), dy_lt(a, b, h), le_add(Civil.days_in_years(b), y))
  +h2 = le_rw_r(Nat.add(Civil.days_in_years(a), Civil.year_len(Nat.add(1970n, a))), Nat.add(Civil.days_in_years(b), y), Nat.add(Civil.days_in_years(a), x), Equal.sym(Nat, Nat.add(Civil.days_in_years(a), x), Nat.add(Civil.days_in_years(b), y), e), h1)
  lt_le_absurd(x, Civil.year_len(Nat.add(1970n, a)), hx, Equal.trans(Bool, Nat.is_le(Civil.year_len(Nat.add(1970n, a)), x), Nat.is_le(Nat.add(Civil.days_in_years(a), Civil.year_len(Nat.add(1970n, a))), Nat.add(Civil.days_in_years(a), x)), True{},
    Equal.sym(Bool, Nat.is_le(Nat.add(Civil.days_in_years(a), Civil.year_len(Nat.add(1970n, a))), Nat.add(Civil.days_in_years(a), x)), Nat.is_le(Civil.year_len(Nat.add(1970n, a)), x), le_cancel(Civil.days_in_years(a), Civil.year_len(Nat.add(1970n, a)), x)), h2))

def dy_uniq.of(v1: Bool, v2: Bool, +a: Nat, +b: Nat, +x: Nat, +y: Nat,
  +h1: {v1 == Nat.is_lt(a, b) : Bool}, +h2: {v2 == Nat.is_lt(b, a) : Bool},
  +e: {Nat.add(Civil.days_in_years(a), x) == Nat.add(Civil.days_in_years(b), y) : Nat}, +hx: {Nat.is_lt(x, Civil.year_len(Nat.add(1970n, a))) == True{} : Bool}, +hy: {Nat.is_lt(y, Civil.year_len(Nat.add(1970n, b))) == True{} : Bool})
  -> {a == b : Nat}:
  match v1:
    case True{}:
      Empty.absurd({a == b : Nat}, dy_no(a, b, x, y, Equal.sym(Bool, True{}, Nat.is_lt(a, b), h1), e, hx))
    case False{}:
      match v2:
        case True{}:
          Empty.absurd({a == b : Nat}, dy_no(b, a, y, x, Equal.sym(Bool, True{}, Nat.is_lt(b, a), h2), Equal.sym(Nat, Nat.add(Civil.days_in_years(a), x), Nat.add(Civil.days_in_years(b), y), e), hy))
        case False{}:
          le_antisym(a, b, nlt_le(b, a, Equal.sym(Bool, False{}, Nat.is_lt(b, a), h2)), nlt_le(a, b, Equal.sym(Bool, False{}, Nat.is_lt(a, b), h1)))

def dy_uniq(+a: Nat, +b: Nat, +x: Nat, +y: Nat,
  +e: {Nat.add(Civil.days_in_years(a), x) == Nat.add(Civil.days_in_years(b), y) : Nat}, +hx: {Nat.is_lt(x, Civil.year_len(Nat.add(1970n, a))) == True{} : Bool}, +hy: {Nat.is_lt(y, Civil.year_len(Nat.add(1970n, b))) == True{} : Bool})
  -> {a == b : Nat}:
  dy_uniq.of(Nat.is_lt(a, b), Nat.is_lt(b, a), a, b, x, y, {==}, {==}, e, hx, hy)

def dm_mono(j: Nat, +c: Nat, +yy: Nat) -> {Nat.is_le(Civil.days_in_months(c, yy), Civil.days_in_months(Nat.add(j, c), yy)) == True{} : Bool}:
  match j:
    case 0n:
      le_refl(Civil.days_in_months(c, yy))
    case 1n++jp:
      le_trans(Civil.days_in_months(c, yy), Civil.days_in_months(Nat.add(jp, c), yy), Civil.days_in_months(1n+Nat.add(jp, c), yy), dm_mono(jp, c, yy), le_add(Civil.days_in_months(Nat.add(jp, c), yy), Civil.month_len(yy, 1n+Nat.add(jp, c))))

# a < b: S(a) + L(a) <= S(b)
def dm_lt(+a: Nat, +b: Nat, +yy: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool})
  -> {Nat.is_le(Nat.add(Civil.days_in_months(a, yy), Civil.month_len(yy, 1n+a)), Civil.days_in_months(b, yy)) == True{} : Bool}:
  +j = Nat.sub(b, 1n+a)
  +e = Equal.trans(Nat, Nat.add(j, 1n+a), Nat.add(1n+a, j), b, PNat.add_comm(j, 1n+a), add_sub(1n+a, b, lt_to_le(a, b, h)))
  le_rw_r(Civil.days_in_months(1n+a, yy), Civil.days_in_months(Nat.add(j, 1n+a), yy), Civil.days_in_months(b, yy), dm_cong(Nat.add(j, 1n+a), b, yy, e), dm_mono(j, 1n+a, yy))

# S(a) + x == S(b) + y with a < b and x < L(a) is impossible
def dm_no(+a: Nat, +b: Nat, +x: Nat, +y: Nat, +yy: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool},
  +e: {Nat.add(Civil.days_in_months(a, yy), x) == Nat.add(Civil.days_in_months(b, yy), y) : Nat}, +hx: {Nat.is_lt(x, Civil.month_len(yy, 1n+a)) == True{} : Bool}) -> Empty:
  +h1 = le_trans(Nat.add(Civil.days_in_months(a, yy), Civil.month_len(yy, 1n+a)), Civil.days_in_months(b, yy), Nat.add(Civil.days_in_months(b, yy), y), dm_lt(a, b, yy, h), le_add(Civil.days_in_months(b, yy), y))
  +h2 = le_rw_r(Nat.add(Civil.days_in_months(a, yy), Civil.month_len(yy, 1n+a)), Nat.add(Civil.days_in_months(b, yy), y), Nat.add(Civil.days_in_months(a, yy), x), Equal.sym(Nat, Nat.add(Civil.days_in_months(a, yy), x), Nat.add(Civil.days_in_months(b, yy), y), e), h1)
  lt_le_absurd(x, Civil.month_len(yy, 1n+a), hx, Equal.trans(Bool, Nat.is_le(Civil.month_len(yy, 1n+a), x), Nat.is_le(Nat.add(Civil.days_in_months(a, yy), Civil.month_len(yy, 1n+a)), Nat.add(Civil.days_in_months(a, yy), x)), True{},
    Equal.sym(Bool, Nat.is_le(Nat.add(Civil.days_in_months(a, yy), Civil.month_len(yy, 1n+a)), Nat.add(Civil.days_in_months(a, yy), x)), Nat.is_le(Civil.month_len(yy, 1n+a), x), le_cancel(Civil.days_in_months(a, yy), Civil.month_len(yy, 1n+a), x)), h2))

def dm_uniq.of(v1: Bool, v2: Bool, +a: Nat, +b: Nat, +x: Nat, +y: Nat, +yy: Nat,
  +h1: {v1 == Nat.is_lt(a, b) : Bool}, +h2: {v2 == Nat.is_lt(b, a) : Bool},
  +e: {Nat.add(Civil.days_in_months(a, yy), x) == Nat.add(Civil.days_in_months(b, yy), y) : Nat}, +hx: {Nat.is_lt(x, Civil.month_len(yy, 1n+a)) == True{} : Bool}, +hy: {Nat.is_lt(y, Civil.month_len(yy, 1n+b)) == True{} : Bool})
  -> {a == b : Nat}:
  match v1:
    case True{}:
      Empty.absurd({a == b : Nat}, dm_no(a, b, x, y, yy, Equal.sym(Bool, True{}, Nat.is_lt(a, b), h1), e, hx))
    case False{}:
      match v2:
        case True{}:
          Empty.absurd({a == b : Nat}, dm_no(b, a, y, x, yy, Equal.sym(Bool, True{}, Nat.is_lt(b, a), h2), Equal.sym(Nat, Nat.add(Civil.days_in_months(a, yy), x), Nat.add(Civil.days_in_months(b, yy), y), e), hy))
        case False{}:
          le_antisym(a, b, nlt_le(b, a, Equal.sym(Bool, False{}, Nat.is_lt(b, a), h2)), nlt_le(a, b, Equal.sym(Bool, False{}, Nat.is_lt(a, b), h1)))

def dm_uniq(+a: Nat, +b: Nat, +x: Nat, +y: Nat, +yy: Nat,
  +e: {Nat.add(Civil.days_in_months(a, yy), x) == Nat.add(Civil.days_in_months(b, yy), y) : Nat}, +hx: {Nat.is_lt(x, Civil.month_len(yy, 1n+a)) == True{} : Bool}, +hy: {Nat.is_lt(y, Civil.month_len(yy, 1n+b)) == True{} : Bool})
  -> {a == b : Nat}:
  dm_uniq.of(Nat.is_lt(a, b), Nat.is_lt(b, a), a, b, x, y, yy, {==}, {==}, e, hx, hy)


def and_l(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(h))

def and_r(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, PNat.false_ne_true(h))

def ge_le(a: Nat, b: Nat, +h: {Nat.is_ge(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, PNat.false_ne_true(h))
    case 1n++ap:
      match b:
        case 0n:
          {==}
        case 1n++bp:
          ge_le(ap, bp, h)

def lt_le_trans(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  le_to_lt(a, c, le_trans(1n+a, b, c, lt_to_le(a, b, h1), h2))

def lt_rw_r(-a: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, +h: {Nat.is_lt(a, x) == True{} : Bool}) -> {Nat.is_lt(a, y) == True{} : Bool}:
  %e : {Nat.is_lt(a, _) == True{} : Bool}
  h

def yl_cong(-y1: Nat, -y2: Nat, e: {y1 == y2 : Nat}) -> {Civil.year_len(y1) == Civil.year_len(y2) : Nat}:
  %e : {Civil.year_len(y1) == Civil.year_len(_) : Nat}
  {==}

def sp1(n: Nat, h: {Nat.is_ge(n, 1n) == True{} : Bool}) -> {1n+Nat.sub(n, 1n) == n : Nat}:
  match n:
    case 0n:
      Empty.absurd({1n+Nat.sub(0n, 1n) == 0n : Nat}, PNat.false_ne_true(h))
    case 1n++p:
      match p:
        case 0n:
          {==}
        case 1n++q:
          {==}

def add_cancel(a: Nat, -x: Nat, -y: Nat, e: {Nat.add(a, x) == Nat.add(a, y) : Nat}) -> {x == y : Nat}:
  match a:
    case 0n:
      e
    case 1n++p:
      add_cancel(p, x, y, PNat.succ_inj(Nat.add(p, x), Nat.add(p, y), e))

def dmy_cong(-k: Nat, -y1: Nat, -y2: Nat, e: {y1 == y2 : Nat}) -> {Civil.days_in_months(k, y1) == Civil.days_in_months(k, y2) : Nat}:
  %e : {Civil.days_in_months(k, y1) == Civil.days_in_months(k, _) : Nat}
  {==}

def ml_cong(-y1: Nat, -y2: Nat, -m1: Nat, -m2: Nat, ey: {y1 == y2 : Nat}, em: {m1 == m2 : Nat}) -> {Civil.month_len(y1, m1) == Civil.month_len(y2, m2) : Nat}:
  %ey : {Civil.month_len(y1, m1) == Civil.month_len(_, m2) : Nat}
  %em : {Civil.month_len(y1, m1) == Civil.month_len(y1, _) : Nat}
  {==}

def ymd_cong(-y1: Nat, -y2: Nat, -m1: Nat, -m2: Nat, -d1: Nat, -d2: Nat, ey: {y1 == y2 : Nat}, em: {m1 == m2 : Nat}, ed: {d1 == d2 : Nat})
  -> {Civil.Ymd{y1, m1, d1} == Civil.Ymd{y2, m2, d2} : Civil.Ymd}:
  %ey : {Civil.Ymd{y1, m1, d1} == Civil.Ymd{_, m2, d2} : Civil.Ymd}
  %em : {Civil.Ymd{y1, m1, d1} == Civil.Ymd{y1, _, d2} : Civil.Ymd}
  %ed : {Civil.Ymd{y1, m1, d1} == Civil.Ymd{y1, m1, _} : Civil.Ymd}
  {==}

# the date read back from the days of a valid date is that date
def ymd_back(+y: Nat, +m: Nat, +d: Nat, +c: Nat, +r1: Nat, +kk: Nat, +rr: Nat,
  +hy: {Nat.is_ge(y, 1970n) == True{} : Bool}, +hm1: {Nat.is_ge(m, 1n) == True{} : Bool}, +hm12: {Nat.is_le(m, 12n) == True{} : Bool},
  +hd1: {Nat.is_ge(d, 1n) == True{} : Bool}, +hdm: {Nat.is_le(d, Civil.month_len(y, m)) == True{} : Bool},
  +ya: {Nat.add(Civil.days_in_years(c), r1) == Civil.ymd_to_days(y, m, d) : Nat},
  +yb: {Nat.is_lt(r1, Civil.year_len(Nat.add(1970n, c))) == True{} : Bool},
  +ma: {Nat.add(Civil.days_in_months(kk, Nat.add(1970n, c)), rr) == r1 : Nat},
  +mb: {Nat.is_lt(rr, Civil.month_len(Nat.add(1970n, c), 1n+kk)) == True{} : Bool})
  -> {Civil.Ymd{Nat.add(1970n, c), 1n+kk, 1n+rr} == Civil.Ymd{y, m, d} : Civil.Ymd}:
  +c0 = Nat.sub(y, 1970n)
  +m0 = Nat.sub(m, 1n)
  +d0 = Nat.sub(d, 1n)
  +r0 = Nat.add(Civil.days_in_months(m0, y), d0)
  +ey = add_sub(1970n, y, ge_le(y, 1970n, hy))
  +em = sp1(m, hm1)
  +ed = sp1(d, hd1)
  +hd0 = le_to_lt(d0, Civil.month_len(y, 1n+m0),
    le_rw_l(d, 1n+d0, Civil.month_len(y, 1n+m0), Equal.sym(Nat, 1n+d0, d, ed),
      le_rw_r(d, Civil.month_len(y, m), Civil.month_len(y, 1n+m0), ml_cong(y, y, m, 1n+m0, {==}, Equal.sym(Nat, 1n+m0, m, em)), hdm)))
  +j = Nat.sub(12n, 1n+m0)
  +ej = Equal.trans(Nat, Nat.add(j, 1n+m0), Nat.add(1n+m0, j), 12n, PNat.add_comm(j, 1n+m0),
    add_sub(1n+m0, 12n, le_rw_l(m, 1n+m0, 12n, Equal.sym(Nat, 1n+m0, m, em), hm12)))
  +h12 = le_rw_r(Civil.days_in_months(1n+m0, y), Civil.days_in_months(Nat.add(j, 1n+m0), y), Civil.year_len(y),
    Equal.trans(Nat, Civil.days_in_months(Nat.add(j, 1n+m0), y), Civil.days_in_months(12n, y), Civil.year_len(y), dm_cong(Nat.add(j, 1n+m0), 12n, y, ej), dim12(y)),
    dm_mono(j, 1n+m0, y))
  +hr0y = lt_le_trans(r0, Civil.days_in_months(1n+m0, y), Civil.year_len(y),
    le_to_lt(r0, Nat.add(Civil.days_in_months(m0, y), Civil.month_len(y, 1n+m0)),
      le_rw_l(Nat.add(Civil.days_in_months(m0, y), 1n+d0), 1n+r0, Nat.add(Civil.days_in_months(m0, y), Civil.month_len(y, 1n+m0)),
        Equal.sym(Nat, 1n+r0, Nat.add(Civil.days_in_months(m0, y), 1n+d0), PNat.add_succ(Civil.days_in_months(m0, y), d0)),
        le_add_mono(Civil.days_in_months(m0, y), 1n+d0, Civil.month_len(y, 1n+m0), lt_to_le(d0, Civil.month_len(y, 1n+m0), hd0)))),
    h12)
  +hr0 = lt_rw_r(r0, Civil.year_len(y), Civil.year_len(Nat.add(1970n, c0)), yl_cong(y, Nat.add(1970n, c0), Equal.sym(Nat, Nat.add(1970n, c0), y, ey)), hr0y)
  +ec = dy_uniq(c, c0, r1, r0, ya, yb, hr0)
  +er = add_cancel(Civil.days_in_years(c0), r1, r0, Equal.trans(Nat, Nat.add(Civil.days_in_years(c0), r1), Nat.add(Civil.days_in_years(c), r1), Nat.add(Civil.days_in_years(c0), r0),
    add_cong(Civil.days_in_years(c0), Civil.days_in_years(c), r1, r1, dy_cong(c0, c, Equal.sym(Nat, c, c0, ec)), {==}), ya))
  +yY = Nat.add(1970n, c)
  +eY = Equal.trans(Nat, yY, Nat.add(1970n, c0), y, add_cong(1970n, 1970n, c, c0, {==}, ec), ey)
  +e1 = Equal.trans(Nat, Nat.add(Civil.days_in_months(kk, yY), rr), r1, Nat.add(Civil.days_in_months(m0, yY), d0), ma,
    Equal.trans(Nat, r1, r0, Nat.add(Civil.days_in_months(m0, yY), d0), er,
      add_cong(Civil.days_in_months(m0, y), Civil.days_in_months(m0, yY), d0, d0, dmy_cong(m0, y, yY, Equal.sym(Nat, yY, y, eY)), {==})))
  +hd0Y = lt_rw_r(d0, Civil.month_len(y, 1n+m0), Civil.month_len(yY, 1n+m0), ml_cong(y, yY, 1n+m0, 1n+m0, Equal.sym(Nat, yY, y, eY), {==}), hd0)
  +ek = dm_uniq(kk, m0, rr, d0, yY, e1, mb, hd0Y)
  +erd = add_cancel(Civil.days_in_months(m0, yY), rr, d0, Equal.trans(Nat, Nat.add(Civil.days_in_months(m0, yY), rr), Nat.add(Civil.days_in_months(kk, yY), rr), Nat.add(Civil.days_in_months(m0, yY), d0),
    add_cong(Civil.days_in_months(m0, yY), Civil.days_in_months(kk, yY), rr, rr, dm_cong(m0, kk, yY, Equal.sym(Nat, kk, m0, ek)), {==}), e1))
  ymd_cong(yY, y, 1n+kk, m, 1n+rr, d, eY,
    Equal.trans(Nat, 1n+kk, 1n+m0, m, succ_cong(kk, m0, ek), em),
    Equal.trans(Nat, 1n+rr, 1n+d0, d, succ_cong(rr, d0, erd), ed))

def ymd_days(+y: Nat, +m: Nat, +d: Nat, +hy: {Nat.is_ge(y, 1970n) == True{} : Bool}, +hm1: {Nat.is_ge(m, 1n) == True{} : Bool}, +hm12: {Nat.is_le(m, 12n) == True{} : Bool},
  +hd1: {Nat.is_ge(d, 1n) == True{} : Bool}, +hdm: {Nat.is_le(d, Civil.month_len(y, m)) == True{} : Bool})
  -> {Civil.days_to_ymd(Civil.ymd_to_days(y, m, d)) == Civil.Ymd{y, m, d} : Civil.Ymd}:
  +n = Civil.ymd_to_days(y, m, d)
  +yr = Civil.years.go(1n+n, Nat.is_lt(n, Civil.year_len(1970n)), 0n, n)
  +ys = years_spec(1n+n, Nat.is_lt(n, Civil.year_len(1970n)), 0n, n, n, {==}, le_succ(n), {==})
  +c = Civil.CR.c(yr)
  +r1 = Civil.CR.r(yr)
  +yY = Nat.add(1970n, c)
  +ya = P2.fst({Nat.add(Civil.days_in_years(c), r1) == n : Nat}, {Nat.is_lt(r1, Civil.year_len(yY)) == True{} : Bool}, ys)
  +yb = P2.snd({Nat.add(Civil.days_in_years(c), r1) == n : Nat}, {Nat.is_lt(r1, Civil.year_len(yY)) == True{} : Bool}, ys)
  +mr = Civil.months.go(12n, Nat.is_lt(r1, Civil.month_len(yY, 1n)), yY, 0n, r1)
  +ms = months_spec(12n, Nat.is_lt(r1, Civil.month_len(yY, 1n)), yY, 0n, r1, r1, {==}, {==}, {==}, yb)
  +kk = Civil.CR.c(mr)
  +rr = Civil.CR.r(mr)
  +mab = P2.fst(P2({Nat.add(Civil.days_in_months(kk, yY), rr) == r1 : Nat}, {Nat.is_lt(rr, Civil.month_len(yY, 1n+kk)) == True{} : Bool}), {Nat.is_le(kk, 11n) == True{} : Bool}, ms)
  +ma = P2.fst({Nat.add(Civil.days_in_months(kk, yY), rr) == r1 : Nat}, {Nat.is_lt(rr, Civil.month_len(yY, 1n+kk)) == True{} : Bool}, mab)
  +mb = P2.snd({Nat.add(Civil.days_in_months(kk, yY), rr) == r1 : Nat}, {Nat.is_lt(rr, Civil.month_len(yY, 1n+kk)) == True{} : Bool}, mab)
  ymd_back(y, m, d, c, r1, kk, rr, hy, hm1, hm12, hd1, hdm, ya, yb, ma, mb)

def ymd_days_h(+y: Nat, +m: Nat, +d: Nat, +h: {L.valid_date(y, m, d) == True{} : Bool})
  -> {Civil.days_to_ymd(Civil.ymd_to_days(y, m, d)) == Civil.Ymd{y, m, d} : Civil.Ymd}:
  +a = Nat.is_ge(y, 1970n)
  +b = Bool.and(Bool.and(Nat.is_ge(m, 1n), Nat.is_le(m, 12n)), Bool.and(Nat.is_ge(d, 1n), Nat.is_le(d, L.month_len(y, m))))
  +hb = and_r(a, b, h)
  +b1 = Bool.and(Nat.is_ge(m, 1n), Nat.is_le(m, 12n))
  +b2 = Bool.and(Nat.is_ge(d, 1n), Nat.is_le(d, L.month_len(y, m)))
  +hb1 = and_l(b1, b2, hb)
  +hb2 = and_r(b1, b2, hb)
  ymd_days(y, m, d, and_l(a, b, h), and_l(Nat.is_ge(m, 1n), Nat.is_le(m, 12n), hb1), and_r(Nat.is_ge(m, 1n), Nat.is_le(m, 12n), hb1),
    and_l(Nat.is_ge(d, 1n), Nat.is_le(d, L.month_len(y, m)), hb2),
    le_rw_r(d, L.month_len(y, m), Civil.month_len(y, m), Equal.sym(Nat, Civil.month_len(y, m), L.month_len(y, m), month_len_same(y, m)),
      and_r(Nat.is_ge(d, 1n), Nat.is_le(d, L.month_len(y, m)), hb2)))

def L.civil_ymd_days(y, m, d, h):
  ymd_days_h(y, m, d, h)

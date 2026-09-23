# Proofs of the calendar laws (civil_*).
#
# lib/civil.bend counts days as LAWS' days_of does and writes RFC3339 as
# rfc_text does; its picks and helpers are its own, so they are related to
# LAWS' by the lemmas below. Instants compare and add in nanoseconds with
# the second count first (Nat.mul(s, 1000000000n): a literal-first product
# would unfold into 10^9 terms).
#
# civil_rfc3339_parse writes the text's fields as explicit digits (pad2_d,
# pad4_d), so the parser's fixed positions compute; reads them back (rd2,
# rd4); reads the fraction back through trim_zeros_r (fE2: the nine
# digits are the fraction then zeros); and reads the zone back per sign.
# Closed constants stay small: 86400 only ever meets a variable, and a
# bound like hour < 24 comes from a closed quotient (86399 / 3600 = 23).
import Base
import ../LAWS.bend as L
import ../lib/dec.bend as Dec
import ../lib/civil.bend as Civil
import ./nat.bend as PNat
# for L.dec_show_value's lib form (value_go_same)
import ./dec.bend as PDec

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

# ---------------------------------------------------------------------
# civil_rfc3339_parse: arithmetic
# ---------------------------------------------------------------------

def symN(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {b == a : Nat}:
  Equal.sym(Nat, a, b, e)

def trN(-a: Nat, -b: Nat, -c: Nat, e1: {a == b : Nat}, e2: {b == c : Nat}) -> {a == c : Nat}:
  Equal.trans(Nat, a, b, c, e1, e2)

def absurdB(-P: Type, e: {False{} == True{} : Bool}) -> P:
  Empty.absurd(P, PNat.false_ne_true(e))

def absurdT(-P: Type, e: {True{} == False{} : Bool}) -> P:
  Empty.absurd(P, PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, e)))

def mul_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %PNat.mul_dist(b, Nat.mul(p, b), c) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      %symN(Nat.mul(Nat.mul(p, b), c), Nat.mul(p, Nat.mul(b, c)), mul_assoc(p, b, c)) : {Nat.add(Nat.mul(b, c), _) == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      {==}

def assoc3(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  symN(Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), PNat.add_assoc(a, b, c))

# B + y is not below B
def lt_add_self(bb: Nat, y: Nat) -> {Nat.is_lt(Nat.add(bb, y), bb) == False{} : Bool}:
  match bb:
    case 0n:
      match y:
        case 0n:
          {==}
        case 1n++p:
          {==}
    case 1n++p:
      lt_add_self(p, y)

# r == B + y is not below B
def lt_self_no(-r: Nat, +bb: Nat, +y: Nat, e: {r == Nat.add(bb, y) : Nat}, +h: {Nat.is_lt(r, bb) == True{} : Bool}) -> Empty:
  PNat.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(bb, y), bb), True{},
    Equal.sym(Bool, Nat.is_lt(Nat.add(bb, y), bb), False{}, lt_add_self(bb, y)),
    lt_rw_l(r, Nat.add(bb, y), bb, e, h)))

# Euclid's quotient is unique
def euq(q: Nat, d: Nat, +r: Nat, +m: Nat, +b: Nat, +e: {Nat.add(Nat.mul(q, 1n+b), r) == Nat.add(Nat.mul(d, 1n+b), m) : Nat},
  +hr: {Nat.is_lt(r, 1n+b) == True{} : Bool}, +hm: {Nat.is_lt(m, 1n+b) == True{} : Bool}) -> {q == d : Nat}:
  match q:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n++dp:
          Empty.absurd({0n == 1n+dp : Nat}, lt_self_no(r, 1n+b, Nat.add(Nat.mul(dp, 1n+b), m),
            trN(r, Nat.add(Nat.add(1n+b, Nat.mul(dp, 1n+b)), m), Nat.add(1n+b, Nat.add(Nat.mul(dp, 1n+b), m)), e, assoc3(1n+b, Nat.mul(dp, 1n+b), m)), hr))
    case 1n++qp:
      match d:
        case 0n:
          Empty.absurd({1n+qp == 0n : Nat}, lt_self_no(m, 1n+b, Nat.add(Nat.mul(qp, 1n+b), r),
            trN(m, Nat.add(Nat.add(1n+b, Nat.mul(qp, 1n+b)), r), Nat.add(1n+b, Nat.add(Nat.mul(qp, 1n+b), r)), symN(Nat.add(Nat.add(1n+b, Nat.mul(qp, 1n+b)), r), m, e), assoc3(1n+b, Nat.mul(qp, 1n+b), r)), hm))
        case 1n++dp:
          +e2 = trN(Nat.add(1n+b, Nat.add(Nat.mul(qp, 1n+b), r)), Nat.add(Nat.add(1n+b, Nat.mul(qp, 1n+b)), r), Nat.add(1n+b, Nat.add(Nat.mul(dp, 1n+b), m)),
            symN(Nat.add(Nat.add(1n+b, Nat.mul(qp, 1n+b)), r), Nat.add(1n+b, Nat.add(Nat.mul(qp, 1n+b), r)), assoc3(1n+b, Nat.mul(qp, 1n+b), r)),
            trN(Nat.add(Nat.add(1n+b, Nat.mul(qp, 1n+b)), r), Nat.add(Nat.add(1n+b, Nat.mul(dp, 1n+b)), m), Nat.add(1n+b, Nat.add(Nat.mul(dp, 1n+b), m)), e, assoc3(1n+b, Nat.mul(dp, 1n+b), m)))
          succ_cong(qp, dp, euq(qp, dp, r, m, b, add_cancel(1n+b, Nat.add(Nat.mul(qp, 1n+b), r), Nat.add(Nat.mul(dp, 1n+b), m), e2), hr, hm))

def div_unique(+q: Nat, +r: Nat, +b: Nat, +hr: {Nat.is_lt(r, 1n+b) == True{} : Bool})
  -> {Nat.div(Nat.add(Nat.mul(q, 1n+b), r), 1n+b) == q : Nat}:
  +n = Nat.add(Nat.mul(q, 1n+b), r)
  symN(q, Nat.div(n, 1n+b), euq(q, Nat.div(n, 1n+b), r, Nat.mod(n, 1n+b), b, PNat.div_mod_eq(n, b), hr, PNat.mod_lt(n, b)))

def mod_unique(+q: Nat, +r: Nat, +b: Nat, +hr: {Nat.is_lt(r, 1n+b) == True{} : Bool})
  -> {Nat.mod(Nat.add(Nat.mul(q, 1n+b), r), 1n+b) == r : Nat}:
  +n = Nat.add(Nat.mul(q, 1n+b), r)
  +eq = euq(q, Nat.div(n, 1n+b), r, Nat.mod(n, 1n+b), b, PNat.div_mod_eq(n, b), hr, PNat.mod_lt(n, b))
  +d = Nat.div(n, 1n+b)
  +md = Nat.mod(n, 1n+b)
  +e3 = Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(x, 1n+b), md), d, q, symN(q, d, eq))
  symN(r, md, add_cancel(Nat.mul(q, 1n+b), r, md, trN(n, Nat.add(Nat.mul(d, 1n+b), md), Nat.add(Nat.mul(q, 1n+b), md), PNat.div_mod_eq(n, b), e3)))

def le_mul(k: Nat, q: Nat, +bb: Nat, +h: {Nat.is_le(k, q) == True{} : Bool}) -> {Nat.is_le(Nat.mul(k, bb), Nat.mul(q, bb)) == True{} : Bool}:
  match k:
    case 0n:
      le_zero(Nat.mul(q, bb))
    case 1n++kp:
      match q:
        case 0n:
          absurdB({Nat.is_le(Nat.mul(1n+kp, bb), 0n) == True{} : Bool}, h)
        case 1n++qp:
          Equal.trans(Bool, Nat.is_le(Nat.add(bb, Nat.mul(kp, bb)), Nat.add(bb, Nat.mul(qp, bb))), Nat.is_le(Nat.mul(kp, bb), Nat.mul(qp, bb)), True{},
            le_cancel(bb, Nat.mul(kp, bb), Nat.mul(qp, bb)), le_mul(kp, qp, bb, h))

def lt_cancel(c: Nat, -a: Nat, -b: Nat) -> {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == Nat.is_lt(a, b) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++p:
      lt_cancel(p, a, b)

# q B <= n, for q = n / B
def le_qb(+n: Nat, +b: Nat) -> {Nat.is_le(Nat.mul(Nat.div(n, 1n+b), 1n+b), n) == True{} : Bool}:
  +q = Nat.div(n, 1n+b)
  le_rw_r(Nat.mul(q, 1n+b), Nat.add(Nat.mul(q, 1n+b), Nat.mod(n, 1n+b)), n, symN(n, Nat.add(Nat.mul(q, 1n+b), Nat.mod(n, 1n+b)), PNat.div_mod_eq(n, b)),
    le_add(Nat.mul(q, 1n+b), Nat.mod(n, 1n+b)))

# n < (q + 1) B, for q = n / B
def lt_q1b(+n: Nat, +b: Nat) -> {Nat.is_lt(n, Nat.add(1n+b, Nat.mul(Nat.div(n, 1n+b), 1n+b))) == True{} : Bool}:
  +q = Nat.div(n, 1n+b)
  +qb = Nat.mul(q, 1n+b)
  +r = Nat.mod(n, 1n+b)
  %PNat.add_comm(qb, 1n+b) : {Nat.is_lt(n, _) == True{} : Bool}
  %symN(n, Nat.add(qb, r), PNat.div_mod_eq(n, b)) : {Nat.is_lt(_, Nat.add(qb, 1n+b)) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(Nat.add(qb, r), Nat.add(qb, 1n+b)), Nat.is_lt(r, 1n+b), True{}, lt_cancel(qb, r, 1n+b), PNat.mod_lt(n, b))

def lt_div.fin(c: Bool, +n: Nat, +k: Nat, +b: Nat, +ec: {Nat.is_lt(Nat.div(n, 1n+b), k) == c : Bool},
  +h: {Nat.is_lt(n, Nat.mul(k, 1n+b)) == True{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      +q = Nat.div(n, 1n+b)
      +kq = le_mul(k, q, 1n+b, nlt_le(q, k, ec))
      Empty.absurd({False{} == True{} : Bool}, lt_le_absurd(n, Nat.mul(k, 1n+b), h, le_trans(Nat.mul(k, 1n+b), Nat.mul(q, 1n+b), n, kq, le_qb(n, b))))

# n < k B: n / B < k
def lt_div(+n: Nat, +k: Nat, +b: Nat, +h: {Nat.is_lt(n, Nat.mul(k, 1n+b)) == True{} : Bool}) -> {Nat.is_lt(Nat.div(n, 1n+b), k) == True{} : Bool}:
  lt_div.fin(Nat.is_lt(Nat.div(n, 1n+b), k), n, k, b, {==}, h)

def ge_div.fin(c: Bool, +n: Nat, +k: Nat, +b: Nat, +ec: {Nat.is_lt(Nat.div(n, 1n+b), k) == c : Bool},
  +h: {Nat.is_le(Nat.mul(k, 1n+b), n) == True{} : Bool}) -> {Nat.is_le(k, Nat.div(n, 1n+b)) == True{} : Bool}:
  match c:
    case False{}:
      nlt_le(Nat.div(n, 1n+b), k, ec)
    case True{}:
      +q = Nat.div(n, 1n+b)
      +le1 = le_mul(1n+q, k, 1n+b, lt_to_le(q, k, ec))
      Empty.absurd({Nat.is_le(k, q) == True{} : Bool}, lt_le_absurd(n, Nat.add(1n+b, Nat.mul(q, 1n+b)), lt_q1b(n, b),
        le_trans(Nat.add(1n+b, Nat.mul(q, 1n+b)), Nat.mul(k, 1n+b), n, le1, h)))

# k B <= n: k <= n / B
def ge_div(+n: Nat, +k: Nat, +b: Nat, +h: {Nat.is_le(Nat.mul(k, 1n+b), n) == True{} : Bool}) -> {Nat.is_le(k, Nat.div(n, 1n+b)) == True{} : Bool}:
  ge_div.fin(Nat.is_lt(Nat.div(n, 1n+b), k), n, k, b, {==}, h)

# m < k and s < B: m B + s < k B
def lt_lin(+m: Nat, +s: Nat, +k: Nat, +b: Nat, +hm: {Nat.is_lt(m, k) == True{} : Bool}, +hs: {Nat.is_lt(s, 1n+b) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Nat.mul(m, 1n+b), s), Nat.mul(k, 1n+b)) == True{} : Bool}:
  +mb = Nat.mul(m, 1n+b)
  +l1 = Equal.trans(Bool, Nat.is_lt(Nat.add(mb, s), Nat.add(mb, 1n+b)), Nat.is_lt(s, 1n+b), True{}, lt_cancel(mb, s, 1n+b), hs)
  +l2 = lt_rw_r(Nat.add(mb, s), Nat.add(mb, 1n+b), Nat.add(1n+b, mb), PNat.add_comm(mb, 1n+b), l1)
  lt_le_trans(Nat.add(mb, s), Nat.add(1n+b, mb), Nat.mul(k, 1n+b), l2, le_mul(1n+m, k, 1n+b, lt_to_le(m, k, hm)))

def congN(-f: Nat -> Nat, -a: Nat, -b: Nat, e: {a == b : Nat}) -> {f(a) == f(b) : Nat}:
  Equal.cong(Nat, Nat, f, a, b, e)

# hours, minutes and seconds of x add back up to x
def hms(+x: Nat) -> {Nat.add(Nat.add(Nat.mul(Nat.div(x, 3600n), 3600n), Nat.mul(Nat.mod(Nat.div(x, 60n), 60n), 60n)), Nat.mod(x, 60n)) == x : Nat}:
  +u = Nat.div(x, 60n)
  +s = Nat.mod(x, 60n)
  +v = Nat.div(u, 60n)
  +m = Nat.mod(u, 60n)
  +X1 = Nat.add(Nat.mul(u, 60n), s)
  +X2 = Nat.add(Nat.mul(Nat.add(Nat.mul(v, 60n), m), 60n), s)
  +X3 = Nat.add(Nat.add(Nat.mul(Nat.mul(v, 60n), 60n), Nat.mul(m, 60n)), s)
  +X4 = Nat.add(Nat.add(Nat.mul(v, 3600n), Nat.mul(m, 60n)), s)
  +R = Nat.add(Nat.mul(m, 60n), s)
  +X5 = Nat.add(Nat.mul(v, 3600n), R)
  +e12 = congN(y => Nat.add(Nat.mul(y, 60n), s), u, Nat.add(Nat.mul(v, 60n), m), PNat.div_mod_eq(u, 59n))
  +e23 = congN(y => Nat.add(y, s), Nat.mul(Nat.add(Nat.mul(v, 60n), m), 60n), Nat.add(Nat.mul(Nat.mul(v, 60n), 60n), Nat.mul(m, 60n)),
    symN(Nat.add(Nat.mul(Nat.mul(v, 60n), 60n), Nat.mul(m, 60n)), Nat.mul(Nat.add(Nat.mul(v, 60n), m), 60n), PNat.mul_dist(Nat.mul(v, 60n), m, 60n)))
  +e34 = congN(y => Nat.add(Nat.add(y, Nat.mul(m, 60n)), s), Nat.mul(Nat.mul(v, 60n), 60n), Nat.mul(v, 3600n), mul_assoc(v, 60n, 60n))
  +ex = trN(x, X1, X4, PNat.div_mod_eq(x, 59n), trN(X1, X2, X4, e12, trN(X2, X3, X4, e23, e34)))
  +ex5 = trN(x, X4, X5, ex, assoc3(Nat.mul(v, 3600n), Nat.mul(m, 60n), s))
  +hr = lt_lin(m, s, 60n, 59n, PNat.mod_lt(u, 59n), PNat.mod_lt(x, 59n))
  +dv = trN(Nat.div(x, 3600n), Nat.div(X5, 3600n), v, congN(y => Nat.div(y, 3600n), x, X5, ex5), div_unique(v, R, 3599n, hr))
  trN(Nat.add(Nat.add(Nat.mul(Nat.div(x, 3600n), 3600n), Nat.mul(m, 60n)), s), X4, x,
    congN(y => Nat.add(Nat.add(Nat.mul(y, 3600n), Nat.mul(m, 60n)), s), Nat.div(x, 3600n), v, dv), symN(x, X4, ex))

# ---------------------------------------------------------------------
# civil_rfc3339_parse: digits
# ---------------------------------------------------------------------

# a fact of each digit is a fact of every k < 10
def by_digit(-P: Nat -> Type, k: Nat, h: {Nat.is_lt(k, 10n) == True{} : Bool},
  p0: P(0n), p1: P(1n), p2: P(2n), p3: P(3n), p4: P(4n), p5: P(5n), p6: P(6n), p7: P(7n), p8: P(8n), p9: P(9n)) -> P(k):
  match k:
    case 0n:
      p0
    case 1n+a:
      match a:
        case 0n:
          p1
        case 1n+b:
          match b:
            case 0n:
              p2
            case 1n+c:
              match c:
                case 0n:
                  p3
                case 1n+d:
                  match d:
                    case 0n:
                      p4
                    case 1n+e:
                      match e:
                        case 0n:
                          p5
                        case 1n+f:
                          match f:
                            case 0n:
                              p6
                            case 1n+g:
                              match g:
                                case 0n:
                                  p7
                                case 1n+i:
                                  match i:
                                    case 0n:
                                      p8
                                    case 1n+j:
                                      match j:
                                        case 0n:
                                          p9
                                        case 1n++l:
                                          Empty.absurd(P(10n+l), lt_le_absurd(l, 0n, h, le_zero(l)))

def dc(+k: Nat) -> Char:
  Dec.digit_chr(k)

# reading a written digit
def sv_dig(+k: Nat, +rest: String, +acc: Nat, h: {Nat.is_lt(k, 10n) == True{} : Bool})
  -> {Civil.sval.go(SCon{dc(k), rest}, acc) == Civil.sval.go(rest, Nat.add(Nat.mul(acc, 10n), k)) : Nat}:
  by_digit(x => {Civil.sval.go(SCon{dc(x), rest}, acc) == Civil.sval.go(rest, Nat.add(Nat.mul(acc, 10n), x)) : Nat}, k, h,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def ad_dig(+k: Nat, +rest: String, h: {Nat.is_lt(k, 10n) == True{} : Bool})
  -> {Civil.all_digits.go(SCon{dc(k), rest}) == Civil.all_digits.go(rest) : Bool}:
  by_digit(x => {Civil.all_digits.go(SCon{dc(x), rest}) == Civil.all_digits.go(rest) : Bool}, k, h,
    {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})

def d2(+n: Nat) -> String:
  SCon{dc(Nat.mod(Nat.div(n, 10n), 10n)), SCon{dc(Nat.mod(n, 10n)), SNil{}}}

def div3(+y: Nat) -> Nat:
  Nat.div(Nat.div(Nat.div(y, 10n), 10n), 10n)

def d4(+y: Nat) -> String:
  SCon{dc(Nat.mod(div3(y), 10n)), SCon{dc(Nat.mod(Nat.div(Nat.div(y, 10n), 10n), 10n)), d2(y)}}

def stop_true(f: Nat, +q: Nat, +acc: String) -> {Dec.show.go(f, True{}, q, acc) == acc : String}:
  match f:
    case 0n:
      {==}
    case 1n++g:
      {==}

def symB(-a: Bool, -b: Bool, e: {a == b : Bool}) -> {b == a : Bool}:
  Equal.sym(Bool, a, b, e)

def symS(-a: String, -b: String, e: {a == b : String}) -> {b == a : String}:
  Equal.sym(String, a, b, e)

def le_nlt.fin(c: Bool, +a: Nat, +b: Nat, +ec: {Nat.is_lt(a, b) == c : Bool}, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, lt_le_absurd(a, b, ec, h))

def le_nlt(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  le_nlt.fin(Nat.is_lt(a, b), a, b, {==}, h)

# show of a one-digit number
def show1(+n: Nat, +ec: {Nat.is_lt(n, 10n) == True{} : Bool}) -> {Dec.show(n) == SCon{dc(Nat.mod(n, 10n)), SNil{}} : String}:
  %symB(Nat.is_lt(n, 10n), True{}, ec) : {Dec.show.go(n, _, Nat.div(n, 10n), SCon{dc(Nat.mod(n, 10n)), SNil{}}) == SCon{dc(Nat.mod(n, 10n)), SNil{}} : String}
  stop_true(n, Nat.div(n, 10n), SCon{dc(Nat.mod(n, 10n)), SNil{}})

# show of a two-digit number
def show2(+p: Nat, +e0: {Nat.is_lt(1n+p, 10n) == False{} : Bool}, +ec: {Nat.is_lt(Nat.div(1n+p, 10n), 10n) == True{} : Bool}) -> {Dec.show(1n+p) == d2(1n+p) : String}:
  %symB(Nat.is_lt(1n+p, 10n), False{}, e0) : {Dec.show.go(1n+p, _, Nat.div(1n+p, 10n), SCon{dc(Nat.mod(1n+p, 10n)), SNil{}}) == d2(1n+p) : String}
  %symB(Nat.is_lt(Nat.div(1n+p, 10n), 10n), True{}, ec) : {Dec.show.go(p, _, Nat.div(Nat.div(1n+p, 10n), 10n), d2(1n+p)) == d2(1n+p) : String}
  stop_true(p, Nat.div(Nat.div(1n+p, 10n), 10n), d2(1n+p))

def pad2.of(c: Bool, +n: Nat, +ec: {Nat.is_lt(n, 10n) == c : Bool}, +h: {Nat.is_lt(n, 100n) == True{} : Bool})
  -> {Dec.pad(2n, n) == d2(n) : String}:
  match c:
    case True{}:
      +e1 = {SCon{dc(Nat.mod(n, 10n)), SNil{}} : String}
      %symS(Dec.show(n), e1, show1(n, ec)) : {String.append(String.repeat("0", Nat.sub(2n, String.length(_))), _) == d2(n) : String}
      %Equal.sym(Nat, Nat.div(n, 10n), 0n, div_unique(0n, n, 9n, ec)) : {SCon{'0', e1} == SCon{dc(Nat.mod(_, 10n)), e1} : String}
      {==}
    case False{}:
      match n:
        case 0n:
          absurdT({Dec.pad(2n, 0n) == d2(0n) : String}, ec)
        case 1n++p:
          %symS(Dec.show(1n+p), d2(1n+p), show2(p, ec, lt_div(1n+p, 10n, 9n, h))) : {String.append(String.repeat("0", Nat.sub(2n, String.length(_))), _) == d2(1n+p) : String}
          {==}

# a number below 100 written in two digits
def pad2_d(+n: Nat, +h: {Nat.is_lt(n, 100n) == True{} : Bool}) -> {Dec.pad(2n, n) == d2(n) : String}:
  pad2.of(Nat.is_lt(n, 10n), n, {==}, h)

def show4(+p: Nat, +y: Nat, +c0: {Nat.is_lt(y, 10n) == False{} : Bool}, +c1: {Nat.is_lt(Nat.div(y, 10n), 10n) == False{} : Bool},
  +c2: {Nat.is_lt(Nat.div(Nat.div(y, 10n), 10n), 10n) == False{} : Bool}, +c3: {Nat.is_lt(div3(y), 10n) == True{} : Bool})
  -> {Dec.show.go(1n+(1n+(1n+(1n+p))), False{}, y, SNil{}) == d4(y) : String}:
  +q1 = Nat.div(y, 10n)
  +q2 = Nat.div(q1, 10n)
  +q3 = Nat.div(q2, 10n)
  +a1 = {SCon{dc(Nat.mod(y, 10n)), SNil{}} : String}
  +a2 = {SCon{dc(Nat.mod(q1, 10n)), a1} : String}
  +a3 = {SCon{dc(Nat.mod(q2, 10n)), a2} : String}
  %symB(Nat.is_lt(y, 10n), False{}, c0) : {Dec.show.go(1n+(1n+(1n+p)), _, q1, a1) == d4(y) : String}
  %symB(Nat.is_lt(q1, 10n), False{}, c1) : {Dec.show.go(1n+(1n+p), _, q2, a2) == d4(y) : String}
  %symB(Nat.is_lt(q2, 10n), False{}, c2) : {Dec.show.go(1n+p, _, q3, a3) == d4(y) : String}
  %symB(Nat.is_lt(q3, 10n), True{}, c3) : {Dec.show.go(p, _, Nat.div(q3, 10n), d4(y)) == d4(y) : String}
  stop_true(p, Nat.div(q3, 10n), d4(y))

def show_y4(+y: Nat, +p: Nat, e3: {1n+(1n+(1n+p)) == y : Nat}, s: {Dec.show.go(1n+(1n+(1n+(1n+p))), False{}, y, SNil{}) == d4(y) : String})
  -> {Dec.show(y) == d4(y) : String}:
  %e3 : {Dec.show.go(1n+_, False{}, y, SNil{}) == d4(y) : String}
  s

def tc1(+y: Nat, +hlo: {Nat.is_le(1000n, y) == True{} : Bool}) -> {Nat.is_lt(Nat.div(y, 10n), 10n) == False{} : Bool}:
  le_nlt(Nat.div(y, 10n), 10n, ge_div(y, 10n, 9n, le_trans(100n, 1000n, y, {==}, hlo)))

def tc2(+y: Nat, +hlo: {Nat.is_le(1000n, y) == True{} : Bool}) -> {Nat.is_lt(Nat.div(Nat.div(y, 10n), 10n), 10n) == False{} : Bool}:
  le_nlt(Nat.div(Nat.div(y, 10n), 10n), 10n, ge_div(Nat.div(y, 10n), 10n, 9n, ge_div(y, 100n, 9n, hlo)))

# a <= b: a / B <= b / B
def div_mono(+a: Nat, +b: Nat, +bb: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.div(a, 1n+bb), Nat.div(b, 1n+bb)) == True{} : Bool}:
  ge_div(b, Nat.div(a, 1n+bb), bb, le_trans(Nat.mul(Nat.div(a, 1n+bb), 1n+bb), a, b, le_qb(a, bb), h))

def d9999() -> {Nat.div(9999n, 10n) == 999n : Nat}:
  {==}

def d999() -> {Nat.div(999n, 10n) == 99n : Nat}:
  {==}

def d99() -> {Nat.div(99n, 10n) == 9n : Nat}:
  {==}

def le_rwr(-a: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, +h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(a, y) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

def tc3(+y: Nat, +hhi: {Nat.is_le(y, 9999n) == True{} : Bool}) -> {Nat.is_lt(div3(y), 10n) == True{} : Bool}:
  +q1 = Nat.div(y, 10n)
  +q2 = Nat.div(q1, 10n)
  +h1 = le_rwr(q1, Nat.div(9999n, 10n), 999n, d9999, div_mono(y, 9999n, 9n, hhi))
  +h2 = le_rwr(q2, Nat.div(999n, 10n), 99n, d999, div_mono(q1, 999n, 9n, h1))
  +h3 = le_rwr(Nat.div(q2, 10n), Nat.div(99n, 10n), 9n, d99, div_mono(q2, 99n, 9n, h2))
  le_to_lt(Nat.div(q2, 10n), 10n, h3)

# a year from 1000 to 9999 written in four digits
def pad4_d(+y: Nat, +hlo: {Nat.is_le(1000n, y) == True{} : Bool}, +hhi: {Nat.is_le(y, 9999n) == True{} : Bool}) -> {Dec.pad(4n, y) == d4(y) : String}:
  +p = Nat.sub(y, 3n)
  +e3 = {add_sub(3n, y, le_trans(3n, 1000n, y, {==}, hlo)) : {1n+(1n+(1n+p)) == y : Nat}}
  +c0 = le_nlt(y, 10n, le_trans(10n, 1000n, y, {==}, hlo))
  %symS(Dec.show(y), d4(y), show_y4(y, p, e3, show4(p, y, c0, tc1(y, hlo), tc2(y, hlo), tc3(y, hhi))))
    : {String.append(String.repeat("0", Nat.sub(4n, String.length(_))), _) == d4(y) : String}
  {==}

# the two digits read back
def rd2(+n: Nat, +h: {Nat.is_lt(n, 100n) == True{} : Bool}) -> {Civil.sval.go(d2(n), 0n) == n : Nat}:
  +q = Nat.div(n, 10n)
  +a = Nat.mod(q, 10n)
  +b = Nat.mod(n, 10n)
  +s1 = sv_dig(a, SCon{dc(b), SNil{}}, 0n, PNat.mod_lt(q, 9n))
  +s2 = sv_dig(b, SNil{}, a, PNat.mod_lt(n, 9n))
  +ea = {mod_unique(0n, q, 9n, lt_div(n, 10n, 9n, h)) : {a == q : Nat}}
  trN(Civil.sval.go(d2(n), 0n), Nat.add(Nat.mul(a, 10n), b), n, trN(Civil.sval.go(d2(n), 0n), Civil.sval.go(SCon{dc(b), SNil{}}, a), Nat.add(Nat.mul(a, 10n), b), s1, s2),
    trN(Nat.add(Nat.mul(a, 10n), b), Nat.add(Nat.mul(q, 10n), b), n, congN(x => Nat.add(Nat.mul(x, 10n), b), a, q, ea), symN(n, Nat.add(Nat.mul(q, 10n), b), PNat.div_mod_eq(n, 9n))))

def ad2(+n: Nat) -> {Civil.all_digits.go(d2(n)) == True{} : Bool}:
  +a = Nat.mod(Nat.div(n, 10n), 10n)
  +b = Nat.mod(n, 10n)
  Equal.trans(Bool, Civil.all_digits.go(d2(n)), Civil.all_digits.go(SCon{dc(b), SNil{}}), True{}, ad_dig(a, SCon{dc(b), SNil{}}, PNat.mod_lt(Nat.div(n, 10n), 9n)),
    ad_dig(b, SNil{}, PNat.mod_lt(n, 9n)))

def sval2(+n: Nat, +acc: Nat) -> {Civil.sval.go(d2(n), acc) == Nat.add(Nat.mul(Nat.add(Nat.mul(acc, 10n), Nat.mod(Nat.div(n, 10n), 10n)), 10n), Nat.mod(n, 10n)) : Nat}:
  +a = Nat.mod(Nat.div(n, 10n), 10n)
  +b = Nat.mod(n, 10n)
  trN(Civil.sval.go(d2(n), acc), Civil.sval.go(SCon{dc(b), SNil{}}, Nat.add(Nat.mul(acc, 10n), a)), Nat.add(Nat.mul(Nat.add(Nat.mul(acc, 10n), a), 10n), b),
    sv_dig(a, SCon{dc(b), SNil{}}, acc, PNat.mod_lt(Nat.div(n, 10n), 9n)), sv_dig(b, SNil{}, Nat.add(Nat.mul(acc, 10n), a), PNat.mod_lt(n, 9n)))

# the four digits read back
def rd4(+y: Nat, +hhi: {Nat.is_le(y, 9999n) == True{} : Bool}) -> {Civil.sval.go(d4(y), 0n) == y : Nat}:
  +q1 = Nat.div(y, 10n)
  +q2 = Nat.div(q1, 10n)
  +q3 = Nat.div(q2, 10n)
  +a3 = Nat.mod(q3, 10n)
  +a2 = Nat.mod(q2, 10n)
  +a1 = Nat.mod(q1, 10n)
  +a0 = Nat.mod(y, 10n)
  +s1 = sv_dig(a3, SCon{dc(a2), d2(y)}, 0n, PNat.mod_lt(q3, 9n))
  +s2 = sv_dig(a2, d2(y), a3, PNat.mod_lt(q2, 9n))
  +s3 = sval2(y, Nat.add(Nat.mul(a3, 10n), a2))
  +e3 = {mod_unique(0n, q3, 9n, tc3(y, hhi)) : {a3 == q3 : Nat}}
  +v1 = Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(a3, 10n), a2), 10n), a1), 10n), a0)
  +v2 = Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(q3, 10n), a2), 10n), a1), 10n), a0)
  +v3 = Nat.add(Nat.mul(Nat.add(Nat.mul(q2, 10n), a1), 10n), a0)
  +v4 = Nat.add(Nat.mul(q1, 10n), a0)
  +e12 = congN(x => Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(x, 10n), a2), 10n), a1), 10n), a0), a3, q3, e3)
  +e23 = congN(x => Nat.add(Nat.mul(Nat.add(Nat.mul(x, 10n), a1), 10n), a0), Nat.add(Nat.mul(q3, 10n), a2), q2, symN(q2, Nat.add(Nat.mul(q3, 10n), a2), PNat.div_mod_eq(q2, 9n)))
  +e34 = congN(x => Nat.add(Nat.mul(x, 10n), a0), Nat.add(Nat.mul(q2, 10n), a1), q1, symN(q1, Nat.add(Nat.mul(q2, 10n), a1), PNat.div_mod_eq(q1, 9n)))
  +e4y = symN(y, v4, PNat.div_mod_eq(y, 9n))
  +r1 = trN(Civil.sval.go(d4(y), 0n), Civil.sval.go(SCon{dc(a2), d2(y)}, a3), v1, s1, trN(Civil.sval.go(SCon{dc(a2), d2(y)}, a3), Civil.sval.go(d2(y), Nat.add(Nat.mul(a3, 10n), a2)), v1, s2, s3))
  trN(Civil.sval.go(d4(y), 0n), v1, y, r1, trN(v1, v2, y, e12, trN(v2, v3, y, e23, trN(v3, v4, y, e34, e4y))))

def ad4(+y: Nat) -> {Civil.all_digits.go(d4(y)) == True{} : Bool}:
  +a3 = Nat.mod(div3(y), 10n)
  +a2 = Nat.mod(Nat.div(Nat.div(y, 10n), 10n), 10n)
  Equal.trans(Bool, Civil.all_digits.go(d4(y)), Civil.all_digits.go(SCon{dc(a2), d2(y)}), True{}, ad_dig(a3, SCon{dc(a2), d2(y)}, PNat.mod_lt(div3(y), 9n)),
    Equal.trans(Bool, Civil.all_digits.go(SCon{dc(a2), d2(y)}), Civil.all_digits.go(d2(y)), True{}, ad_dig(a2, d2(y), PNat.mod_lt(Nat.div(Nat.div(y, 10n), 10n), 9n)), ad2(y)))

# ---------------------------------------------------------------------
# civil_rfc3339_parse: the parser on a text of digits
# ---------------------------------------------------------------------

# an RFC3339 text with its fields as digits, and r after the seconds
def txt(+y: Nat, +m: Nat, +d: Nat, +hh: Nat, +mi: Nat, +ss: Nat, +rc: Char, +rr: String) -> String:
  String.append(d4(y), SCon{'-', String.append(d2(m), SCon{'-', String.append(d2(d), SCon{'T',
    String.append(d2(hh), SCon{':', String.append(d2(mi), SCon{':', String.append(d2(ss), SCon{rc, rr})})})})})})

# date_ok on such a text, its digit checks and values as parameters
def date_body(+ay: Bool, +am: Bool, +ad: Bool, +vy: Nat, +vm: Nat, +vd: Nat) -> Bool:
  Bool.and(Bool.and(Bool.and(Nat.is_eq(4n, 4n), ay), Bool.and(True{}, Bool.and(Bool.and(Nat.is_eq(2n, 2n), am), Bool.and(True{}, Bool.and(Nat.is_eq(2n, 2n), ad))))),
    Bool.and(Nat.is_ge(vy, 1970n), Bool.and(Bool.and(Nat.is_ge(vm, 1n), Nat.is_le(vm, 12n)), Bool.and(Nat.is_ge(vd, 1n), Nat.is_le(vd, Civil.month_len(vy, vm))))))

def date_txt(+y: Nat, +m: Nat, +d: Nat, +hh: Nat, +mi: Nat, +ss: Nat, +rc: Char, +rr: String,
  +hv: {L.valid_date(y, m, d) == True{} : Bool}, +hy: {Nat.is_le(y, 9999n) == True{} : Bool},
  +hm: {Nat.is_lt(m, 100n) == True{} : Bool}, +hd: {Nat.is_lt(d, 100n) == True{} : Bool})
  -> {Civil.date_ok(txt(y, m, d, hh, mi, ss, rc, rr)) == True{} : Bool}:
  +AY = Civil.all_digits.go(d4(y))
  +AM = Civil.all_digits.go(d2(m))
  +AD = Civil.all_digits.go(d2(d))
  +VY = Civil.sval.go(d4(y), 0n)
  +VM = Civil.sval.go(d2(m), 0n)
  +VD = Civil.sval.go(d2(d), 0n)
  %symB(AY, True{}, ad4(y)) : {date_body(_, AM, AD, VY, VM, VD) == True{} : Bool}
  %symB(AM, True{}, ad2(m)) : {date_body(True{}, _, AD, VY, VM, VD) == True{} : Bool}
  %symB(AD, True{}, ad2(d)) : {date_body(True{}, True{}, _, VY, VM, VD) == True{} : Bool}
  %symN(VY, y, rd4(y, hy)) : {date_body(True{}, True{}, True{}, _, VM, VD) == True{} : Bool}
  %symN(VM, m, rd2(m, hm)) : {date_body(True{}, True{}, True{}, y, _, VD) == True{} : Bool}
  %symN(VD, d, rd2(d, hd)) : {date_body(True{}, True{}, True{}, y, m, _) == True{} : Bool}
  %symN(Civil.month_len(y, m), L.month_len(y, m), month_len_same(y, m)) : {Bool.and(Nat.is_ge(y, 1970n), Bool.and(Bool.and(Nat.is_ge(m, 1n), Nat.is_le(m, 12n)), Bool.and(Nat.is_ge(d, 1n), Nat.is_le(d, _)))) == True{} : Bool}
  hv

def clock_body(+ah: Bool, +am: Bool, +as: Bool, +vh: Nat, +vm: Nat, +vs: Nat) -> Bool:
  Bool.and(Bool.and(True{}, Bool.and(Bool.and(Nat.is_eq(2n, 2n), ah), Bool.and(True{}, Bool.and(Bool.and(Nat.is_eq(2n, 2n), am), Bool.and(True{}, Bool.and(Nat.is_eq(2n, 2n), as)))))),
    Bool.and(Nat.is_lt(vh, 24n), Bool.and(Nat.is_lt(vm, 60n), Nat.is_lt(vs, 60n))))

def lt24_100(+n: Nat, +h: {Nat.is_lt(n, 24n) == True{} : Bool}) -> {Nat.is_lt(n, 100n) == True{} : Bool}:
  lt_le_trans(n, 24n, 100n, h, {==})

def lt60_100(+n: Nat, +h: {Nat.is_lt(n, 60n) == True{} : Bool}) -> {Nat.is_lt(n, 100n) == True{} : Bool}:
  lt_le_trans(n, 60n, 100n, h, {==})

def clock_txt(+y: Nat, +m: Nat, +d: Nat, +hh: Nat, +mi: Nat, +ss: Nat, +rc: Char, +rr: String,
  +hh24: {Nat.is_lt(hh, 24n) == True{} : Bool}, +hm60: {Nat.is_lt(mi, 60n) == True{} : Bool}, +hs60: {Nat.is_lt(ss, 60n) == True{} : Bool})
  -> {Civil.clock_ok(txt(y, m, d, hh, mi, ss, rc, rr)) == True{} : Bool}:
  +AH = Civil.all_digits.go(d2(hh))
  +AM = Civil.all_digits.go(d2(mi))
  +AS = Civil.all_digits.go(d2(ss))
  +VH = Civil.sval.go(d2(hh), 0n)
  +VM = Civil.sval.go(d2(mi), 0n)
  +VS = Civil.sval.go(d2(ss), 0n)
  %symB(AH, True{}, ad2(hh)) : {clock_body(_, AM, AS, VH, VM, VS) == True{} : Bool}
  %symB(AM, True{}, ad2(mi)) : {clock_body(True{}, _, AS, VH, VM, VS) == True{} : Bool}
  %symB(AS, True{}, ad2(ss)) : {clock_body(True{}, True{}, _, VH, VM, VS) == True{} : Bool}
  %symN(VH, hh, rd2(hh, lt24_100(hh, hh24))) : {clock_body(True{}, True{}, True{}, _, VM, VS) == True{} : Bool}
  %symN(VM, mi, rd2(mi, lt60_100(mi, hm60))) : {clock_body(True{}, True{}, True{}, hh, _, VS) == True{} : Bool}
  %symN(VS, ss, rd2(ss, lt60_100(ss, hs60))) : {clock_body(True{}, True{}, True{}, hh, mi, _) == True{} : Bool}
  and_i(Nat.is_lt(hh, 24n), Bool.and(Nat.is_lt(mi, 60n), Nat.is_lt(ss, 60n)), hh24, and_i(Nat.is_lt(mi, 60n), Nat.is_lt(ss, 60n), hm60, hs60))

def loc_body(+vy: Nat, +vm: Nat, +vd: Nat, +vh: Nat, +vmi: Nat, +vs: Nat) -> Nat:
  Nat.add(Nat.add(Nat.mul(Civil.ymd_to_days(vy, vm, vd), 86400n), 86400n), Nat.add(Nat.add(Nat.mul(vh, 3600n), Nat.mul(vmi, 60n)), vs))

def loc_txt(+y: Nat, +m: Nat, +d: Nat, +hh: Nat, +mi: Nat, +ss: Nat, +rc: Char, +rr: String,
  +hy: {Nat.is_le(y, 9999n) == True{} : Bool}, +hm: {Nat.is_lt(m, 100n) == True{} : Bool}, +hd: {Nat.is_lt(d, 100n) == True{} : Bool},
  +hh24: {Nat.is_lt(hh, 24n) == True{} : Bool}, +hm60: {Nat.is_lt(mi, 60n) == True{} : Bool}, +hs60: {Nat.is_lt(ss, 60n) == True{} : Bool})
  -> {Civil.local86(txt(y, m, d, hh, mi, ss, rc, rr)) == loc_body(y, m, d, hh, mi, ss) : Nat}:
  +VY = Civil.sval.go(d4(y), 0n)
  +VM = Civil.sval.go(d2(m), 0n)
  +VD = Civil.sval.go(d2(d), 0n)
  +VH = Civil.sval.go(d2(hh), 0n)
  +VI = Civil.sval.go(d2(mi), 0n)
  +VS = Civil.sval.go(d2(ss), 0n)
  +R = loc_body(y, m, d, hh, mi, ss)
  %symN(VY, y, rd4(y, hy)) : {loc_body(_, VM, VD, VH, VI, VS) == R : Nat}
  %symN(VM, m, rd2(m, hm)) : {loc_body(y, _, VD, VH, VI, VS) == R : Nat}
  %symN(VD, d, rd2(d, hd)) : {loc_body(y, m, _, VH, VI, VS) == R : Nat}
  %symN(VH, hh, rd2(hh, lt24_100(hh, hh24))) : {loc_body(y, m, d, _, VI, VS) == R : Nat}
  %symN(VI, mi, rd2(mi, lt60_100(mi, hm60))) : {loc_body(y, m, d, hh, _, VS) == R : Nat}
  %symN(VS, ss, rd2(ss, lt60_100(ss, hs60))) : {loc_body(y, m, d, hh, mi, _) == R : Nat}
  {==}

def sub_add_l(b: Nat, +a: Nat) -> {Nat.sub(Nat.add(b, a), b) == a : Nat}:
  match b:
    case 0n:
      sub0(a)
    case 1n++p:
      sub_add_l(p, a)

def sub_add(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  %PNat.add_comm(b, a) : {Nat.sub(_, b) == a : Nat}
  sub_add_l(b, a)

def le_ge(a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_ge(b, a) == True{} : Bool}:
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
          absurdB({Nat.is_ge(0n, 1n+ap) == True{} : Bool}, h)
        case 1n++bp:
          le_ge(ap, bp, h)

def ge_add(+a: Nat, +b: Nat) -> {Nat.is_ge(Nat.add(a, b), b) == True{} : Bool}:
  le_ge(b, Nat.add(a, b), le_add_l(b, a))

def pbody(+dok: Bool, +cok: Bool, +fok: Bool, +zok: Bool, +zo: Nat, +fn: Nat, +l: Nat) -> Maybe<&2, Civil.Time>:
  Civil.parse.of(Bool.and(Bool.and(dok, cok), Bool.and(Bool.and(fok, zok), Nat.is_ge(l, zo))), Civil.Time{Nat.sub(l, zo), fn, zo})

def fz_of(-t: String, -r: String, -fz: Civil.FZ, e0: {String.drop(t, 19n) == r : String}, e: {Civil.split_frac(r) == fz : Civil.FZ})
  -> {Civil.split_frac(String.drop(t, 19n)) == fz : Civil.FZ}:
  %symS(String.drop(t, 19n), r, e0) : {Civil.split_frac(_) == fz : Civil.FZ}
  e

# the parser reads a text of digits back, given what the fraction and zone read as
def pmain(+y: Nat, +m: Nat, +d: Nat, +hh: Nat, +mi: Nat, +ss: Nat, +rc: Char, +rr: String, +fd: String, +z: String,
  +sec: Nat, +ns: Nat, +off: Nat,
  +hv: {L.valid_date(y, m, d) == True{} : Bool}, +hy: {Nat.is_le(y, 9999n) == True{} : Bool},
  +hm: {Nat.is_lt(m, 100n) == True{} : Bool}, +hd: {Nat.is_lt(d, 100n) == True{} : Bool},
  +hh24: {Nat.is_lt(hh, 24n) == True{} : Bool}, +hm60: {Nat.is_lt(mi, 60n) == True{} : Bool}, +hs60: {Nat.is_lt(ss, 60n) == True{} : Bool},
  +el: {loc_body(y, m, d, hh, mi, ss) == Nat.add(sec, off) : Nat},
  +esp: {Civil.split_frac(SCon{rc, rr}) == Civil.FZ{fd, z} : Civil.FZ},
  +efok: {Civil.frac_ok(SCon{rc, rr}, fd) == True{} : Bool}, +ens: {Civil.frac_ns(fd) == ns : Nat},
  +ezok: {Civil.zone_ok(z) == True{} : Bool}, +ezoff: {Civil.zone_off(z) == off : Nat})
  -> {Civil.parse_rfc3339(txt(y, m, d, hh, mi, ss, rc, rr)) == Some{Civil.Time{sec, ns, off}} : Maybe<&2, Civil.Time>}:
  +T = txt(y, m, d, hh, mi, ss, rc, rr)
  +R = String.drop(T, 19n)
  +FZ = Civil.split_frac(R)
  +G = {Some{Civil.Time{sec, ns, off}} : Maybe<&2, Civil.Time>}
  +esp2 = {fz_of(T, SCon{rc, rr}, Civil.FZ{fd, z}, {==}, esp) : {Civil.split_frac(R) == Civil.FZ{fd, z} : Civil.FZ}}
  +el2 = trN(Civil.local86(T), loc_body(y, m, d, hh, mi, ss), Nat.add(sec, off), loc_txt(y, m, d, hh, mi, ss, rc, rr, hy, hm, hd, hh24, hm60, hs60), el)
  %symB(Civil.date_ok(T), True{}, date_txt(y, m, d, hh, mi, ss, rc, rr, hv, hy, hm, hd))
    : {pbody(_, Civil.clock_ok(T), Civil.frac_ok(R, Civil.FZ.frac(FZ)), Civil.zone_ok(Civil.FZ.zone(FZ)), Civil.zone_off(Civil.FZ.zone(FZ)), Civil.frac_ns(Civil.FZ.frac(FZ)), Civil.local86(T)) == G : Maybe<&2, Civil.Time>}
  %symB(Civil.clock_ok(T), True{}, clock_txt(y, m, d, hh, mi, ss, rc, rr, hh24, hm60, hs60))
    : {pbody(True{}, _, Civil.frac_ok(R, Civil.FZ.frac(FZ)), Civil.zone_ok(Civil.FZ.zone(FZ)), Civil.zone_off(Civil.FZ.zone(FZ)), Civil.frac_ns(Civil.FZ.frac(FZ)), Civil.local86(T)) == G : Maybe<&2, Civil.Time>}
  %Equal.sym(Civil.FZ, FZ, Civil.FZ{fd, z}, esp2)
    : {pbody(True{}, True{}, Civil.frac_ok(R, Civil.FZ.frac(_)), Civil.zone_ok(Civil.FZ.zone(_)), Civil.zone_off(Civil.FZ.zone(_)), Civil.frac_ns(Civil.FZ.frac(_)), Civil.local86(T)) == G : Maybe<&2, Civil.Time>}
  %symN(Civil.local86(T), Nat.add(sec, off), el2)
    : {pbody(True{}, True{}, Civil.frac_ok(R, fd), Civil.zone_ok(z), Civil.zone_off(z), Civil.frac_ns(fd), _) == G : Maybe<&2, Civil.Time>}
  %symN(Civil.zone_off(z), off, ezoff)
    : {pbody(True{}, True{}, Civil.frac_ok(R, fd), Civil.zone_ok(z), _, Civil.frac_ns(fd), Nat.add(sec, off)) == G : Maybe<&2, Civil.Time>}
  %symB(Civil.frac_ok(SCon{rc, rr}, fd), True{}, efok)
    : {pbody(True{}, True{}, _, Civil.zone_ok(z), off, Civil.frac_ns(fd), Nat.add(sec, off)) == G : Maybe<&2, Civil.Time>}
  %symB(Civil.zone_ok(z), True{}, ezok)
    : {pbody(True{}, True{}, True{}, _, off, Civil.frac_ns(fd), Nat.add(sec, off)) == G : Maybe<&2, Civil.Time>}
  %symN(Civil.frac_ns(fd), ns, ens)
    : {pbody(True{}, True{}, True{}, True{}, off, _, Nat.add(sec, off)) == G : Maybe<&2, Civil.Time>}
  %symB(Nat.is_ge(Nat.add(sec, off), off), True{}, ge_add(sec, off))
    : {Civil.parse.of(_, Civil.Time{Nat.sub(Nat.add(sec, off), off), ns, off}) == G : Maybe<&2, Civil.Time>}
  %symN(Nat.sub(Nat.add(sec, off), off), sec, sub_add(sec, off))
    : {Civil.parse.of(True{}, Civil.Time{_, ns, off}) == G : Maybe<&2, Civil.Time>}
  {==}

# U32 equality (as in proofs/results.bend)

def fin_eq_t(t: Cmp, -ah: Bool, -bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, PNat.false_ne_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, PNat.false_ne_true(h))

def fin_eq_h(t: Cmp, ah: Bool, bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {ah == bh : Bool}:
  match t:
    case LT{}:
      Empty.absurd({ah == bh : Bool}, PNat.false_ne_true(h))
    case GT{}:
      Empty.absurd({ah == bh : Bool}, PNat.false_ne_true(h))
    case EQ{}:
      match ah bh:
        case False{} False{}:
          {==}
        case True{} True{}:
          {==}
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(h))
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, PNat.false_ne_true(h))

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
# civil_rfc3339_parse: the fraction read back
# ---------------------------------------------------------------------

def congS(-f: String -> String, -a: String, -b: String, e: {a == b : String}) -> {f(a) == f(b) : String}:
  Equal.cong(String, String, f, a, b, e)

def trS(-a: String, -b: String, -c: String, e1: {a == b : String}, e2: {b == c : String}) -> {a == c : String}:
  Equal.trans(String, a, b, c, e1, e2)

def zeros(+k: Nat) -> String:
  String.repeat("0", k)

def app_nil_s(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      %symS(String.append(r, SNil{}), r, app_nil_s(r)) : {SCon{c, _} == SCon{c, r} : String}
      {==}

def rev_acc2(r: String, +x: String, +acc: String) -> {String.reverse.go(r, String.append(x, acc)) == String.append(String.reverse.go(r, x), acc) : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      rev_acc2(rest, SCon{c, x}, acc)

def rev_app(a: String, +b: String, +acc: String) -> {String.reverse.go(String.append(a, b), acc) == String.reverse.go(b, String.reverse.go(a, acc)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      rev_app(rest, b, SCon{c, acc})

def rev_rev(l: String, +a: String, +b: String) -> {String.reverse.go(String.reverse.go(l, a), b) == String.reverse.go(a, String.append(l, b)) : String}:
  match l:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      rev_rev(rest, SCon{c, a}, b)

def zc(j: Nat, +acc: String) -> {String.append(zeros(j), SCon{'0', acc}) == SCon{'0', String.append(zeros(j), acc)} : String}:
  match j:
    case 0n:
      {==}
    case 1n++i:
      %symS(String.append(zeros(i), SCon{'0', acc}), SCon{'0', String.append(zeros(i), acc)}, zc(i, acc))
        : {SCon{'0', _} == SCon{'0', SCon{'0', String.append(zeros(i), acc)}} : String}
      {==}

def rev_zeros(k: Nat, +acc: String) -> {String.reverse.go(zeros(k), acc) == String.append(zeros(k), acc) : String}:
  match k:
    case 0n:
      {==}
    case 1n++i:
      trS(String.reverse.go(zeros(i), SCon{'0', acc}), String.append(zeros(i), SCon{'0', acc}), SCon{'0', String.append(zeros(i), acc)},
        rev_zeros(i, SCon{'0', acc}), zc(i, acc))

# the zeros a text starts with
def nz(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{+c, +rest}:
      Civil.pick(Nat, U32.is_eq(Civil.code(c), 48), 1n+nz(rest), 0n)

def ss.fin(b: Bool, +k: U32, +rest: String, +eb: {U32.is_eq(k, 48) == b : Bool},
  +ih: {rest == String.append(zeros(nz(rest)), Civil.strip_zeros_l(rest)) : String})
  -> {SCon{Chr{k}, rest} == String.append(zeros(Civil.pick(Nat, b, 1n+nz(rest), 0n)), Civil.pick(String, b, Civil.strip_zeros_l(rest), SCon{Chr{k}, rest})) : String}:
  match b:
    case True{}:
      +R = String.append(zeros(nz(rest)), Civil.strip_zeros_l(rest))
      %Equal.sym(U32, k, 48, u32_eq(k, 48, eb)) : {SCon{Chr{_}, rest} == SCon{'0', R} : String}
      %symS(rest, R, ih) : {SCon{'0', _} == SCon{'0', R} : String}
      {==}
    case False{}:
      {==}

# a text is its leading zeros, then the rest
def ss(s: String) -> {s == String.append(zeros(nz(s)), Civil.strip_zeros_l(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          ss.fin(U32.is_eq(k, 48), k, rest, {==}, ss(rest))

def vapp(a: String, +b: String, +acc: Nat) -> {Dec.value.go(String.append(a, b), acc) == Dec.value.go(b, Dec.value.go(a, acc)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      vapp(r, b, Nat.add(Nat.mul(acc, 10n), Dec.digit(c)))

def mul_one(v: Nat) -> {Nat.mul(v, 1n) == v : Nat}:
  match v:
    case 0n:
      {==}
    case 1n++p:
      succ_cong(Nat.mul(p, 1n), p, mul_one(p))

def vzeros(k: Nat, +v: Nat) -> {Dec.value.go(zeros(k), v) == Nat.mul(v, Nat.pow(10n, k)) : Nat}:
  match k:
    case 0n:
      symN(Nat.mul(v, 1n), v, mul_one(v))
    case 1n++j:
      +pw = Nat.pow(10n, j)
      trN(Dec.value.go(zeros(j), Nat.add(Nat.mul(v, 10n), 0n)), Nat.mul(Nat.add(Nat.mul(v, 10n), 0n), pw), Nat.mul(v, Nat.mul(10n, pw)),
        vzeros(j, Nat.add(Nat.mul(v, 10n), 0n)),
        trN(Nat.mul(Nat.add(Nat.mul(v, 10n), 0n), pw), Nat.mul(Nat.mul(v, 10n), pw), Nat.mul(v, Nat.mul(10n, pw)),
          congN(x => Nat.mul(x, pw), Nat.add(Nat.mul(v, 10n), 0n), Nat.mul(v, 10n), symN(Nat.mul(v, 10n), Nat.add(Nat.mul(v, 10n), 0n), PNat.add_zero(Nat.mul(v, 10n)))),
          mul_assoc(v, 10n, pw)))

def len_app(a: String, +b: String) -> {String.length(String.append(a, b)) == Nat.add(String.length(a), String.length(b)) : Nat}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      succ_cong(String.length(String.append(r, b)), Nat.add(String.length(r), String.length(b)), len_app(r, b))

def len_zeros(k: Nat) -> {String.length(zeros(k)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      succ_cong(String.length(zeros(j)), j, len_zeros(j))

def take_all(s: String, n: Nat, +h: {Nat.is_le(String.length(s), n) == True{} : Bool}) -> {String.take(s, n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      match n:
        case 0n:
          absurdB({String.take(SCon{c, r}, 0n) == SCon{c, r} : String}, h)
        case 1n++m:
          %symS(String.take(r, m), r, take_all(r, m, h)) : {SCon{c, _} == SCon{c, r} : String}
          {==}

def drop0(s: String) -> {String.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      {==}

def drop_app(a: String, +y: String) -> {String.drop(String.append(a, y), String.length(a)) == y : String}:
  match a:
    case SNil{}:
      drop0(y)
    case SCon{+c, +r}:
      drop_app(r, y)

# a + (b - a) with the literal-free order: (b - a) + a == b for a <= b
def sub_add_r(u: Nat, v: Nat, +h: {Nat.is_le(u, v) == True{} : Bool}) -> {Nat.add(Nat.sub(v, u), u) == v : Nat}:
  match u v:
    case 0n 0n:
      {==}
    case 0n 1n++bp:
      symN(1n+bp, Nat.add(1n+bp, 0n), PNat.add_zero(1n+bp))
    case 1n++ap 0n:
      absurdB({Nat.add(Nat.sub(0n, 1n+ap), 1n+ap) == 0n : Nat}, h)
    case 1n++ap 1n++bp:
      trN(Nat.add(Nat.sub(bp, ap), 1n+ap), 1n+Nat.add(Nat.sub(bp, ap), ap), 1n+bp,
        symN(1n+Nat.add(Nat.sub(bp, ap), ap), Nat.add(Nat.sub(bp, ap), 1n+ap), PNat.add_succ(Nat.sub(bp, ap), ap)),
        succ_cong(Nat.add(Nat.sub(bp, ap), ap), bp, sub_add_r(ap, bp, h)))

def adp(a: String, +b: String, +h: {Civil.all_digits.go(String.append(a, b)) == True{} : Bool}) -> {Civil.all_digits.go(a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      +hc = and_l(Civil.is_digit(c), Civil.all_digits.go(String.append(r, b)), h)
      +hr = and_r(Civil.is_digit(c), Civil.all_digits.go(String.append(r, b)), h)
      and_i(Civil.is_digit(c), Civil.all_digits.go(r), hc, adp(r, b, hr))

def adL(s: String) -> {L.all_digits.go(s) == Civil.all_digits.go(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          %symB(L.all_digits.go(rest), Civil.all_digits.go(rest), adL(rest))
            : {Bool.and(L.is_digit(Chr{k}), _) == Civil.all_digits.go(SCon{Chr{k}, rest}) : Bool}
          {==}

def la_ad(s: String, +h: {L.all_digits(s) == True{} : Bool}) -> {Civil.all_digits.go(s) == True{} : Bool}:
  match s:
    case SNil{}:
      absurdB({Civil.all_digits.go(SNil{}) == True{} : Bool}, h)
    case SCon{+c, +rest}:
      Equal.trans(Bool, Civil.all_digits.go(SCon{c, rest}), L.all_digits.go(SCon{c, rest}), True{},
        symB(L.all_digits.go(SCon{c, rest}), Civil.all_digits.go(SCon{c, rest}), adL(SCon{c, rest})), h)

def show_ad(+n: Nat) -> {Civil.all_digits.go(Dec.show(n)) == True{} : Bool}:
  +s = Dec.show(n)
  la_ad(s, and_l(L.all_digits(s), Bool.or(String.eq(s, "0"), Bool.not(String.starts_with(s, "0"))), L.dec_show_canonical(n)))

def ad_zeros(j: Nat, +s: String, +h: {Civil.all_digits.go(s) == True{} : Bool}) -> {Civil.all_digits.go(String.append(zeros(j), s)) == True{} : Bool}:
  match j:
    case 0n:
      h
    case 1n++i:
      ad_zeros(i, s, h)

# a run of digits, then a non-digit: span_digits takes the run
def span_T(t: String, +zc: Char, +zr: String, +ht: {Civil.all_digits.go(t) == True{} : Bool}, +hz: {Civil.is_digit(zc) == False{} : Bool})
  -> {Civil.span_digits.a(String.append(t, SCon{zc, zr})) == t : String}:
  match t:
    case SNil{}:
      %Equal.sym(Bool, Civil.is_digit(zc), False{}, hz) : {Civil.pick(String, _, SCon{zc, Civil.span_digits.a(zr)}, SNil{}) == SNil{} : String}
      {==}
    case SCon{+c, +r}:
      +hc = and_l(Civil.is_digit(c), Civil.all_digits.go(r), ht)
      %symB(Civil.is_digit(c), True{}, hc) : {Civil.pick(String, _, SCon{c, Civil.span_digits.a(String.append(r, SCon{zc, zr}))}, SNil{}) == SCon{c, r} : String}
      %symS(Civil.span_digits.a(String.append(r, SCon{zc, zr})), r, span_T(r, zc, zr, and_r(Civil.is_digit(c), Civil.all_digits.go(r), ht), hz))
        : {SCon{c, _} == SCon{c, r} : String}
      {==}

def fP(+ns: Nat) -> String:
  Dec.pad(9n, ns)

def fQ(+ns: Nat) -> String:
  String.reverse(fP(ns))

def fk(+ns: Nat) -> Nat:
  nz(fQ(ns))

def fS(+ns: Nat) -> String:
  Civil.strip_zeros_l(fQ(ns))

def fT(+ns: Nat) -> String:
  String.reverse(fS(ns))

# the 9 digits are the fraction's digits, then zeros
def fE2(+ns: Nat) -> {fP(ns) == String.append(fT(ns), zeros(fk(ns))) : String}:
  +P = fP(ns)
  +Q = fQ(ns)
  +k = fk(ns)
  +S = fS(ns)
  +e1 = trS(P, String.append(P, SNil{}), String.reverse.go(Q, SNil{}), symS(String.append(P, SNil{}), P, app_nil_s(P)),
    symS(String.reverse.go(Q, SNil{}), String.append(P, SNil{}), rev_rev(P, SNil{}, SNil{})))
  +e2 = congS(x => String.reverse.go(x, SNil{}), Q, String.append(zeros(k), S), ss(Q))
  +e3 = rev_app(zeros(k), S, SNil{})
  +e4 = congS(x => String.reverse.go(S, x), String.reverse.go(zeros(k), SNil{}), zeros(k), trS(String.reverse.go(zeros(k), SNil{}), String.append(zeros(k), SNil{}), zeros(k), rev_zeros(k, SNil{}), app_nil_s(zeros(k))))
  +e5 = rev_acc2(S, SNil{}, zeros(k))
  trS(P, String.reverse.go(Q, SNil{}), String.append(fT(ns), zeros(k)), e1,
    trS(String.reverse.go(Q, SNil{}), String.reverse.go(String.append(zeros(k), S), SNil{}), String.append(fT(ns), zeros(k)), e2,
      trS(String.reverse.go(String.append(zeros(k), S), SNil{}), String.reverse.go(S, String.reverse.go(zeros(k), SNil{})), String.append(fT(ns), zeros(k)), e3,
        trS(String.reverse.go(S, String.reverse.go(zeros(k), SNil{})), String.reverse.go(S, zeros(k)), String.append(fT(ns), zeros(k)), e4, e5))))

def fE3(+ns: Nat) -> {Dec.value(fP(ns)) == ns : Nat}:
  +s = Dec.show(ns)
  +z = zeros(Nat.sub(9n, String.length(s)))
  +j = Nat.sub(9n, String.length(s))
  trN(Dec.value(fP(ns)), Dec.value.go(s, Dec.value.go(z, 0n)), ns, vapp(z, s, 0n),
   trN(Dec.value.go(s, Dec.value.go(z, 0n)), Dec.value.go(s, 0n), ns, congN(x => Dec.value.go(s, x), Dec.value.go(z, 0n), 0n, vzeros(j, 0n)),
    trN(Dec.value.go(s, 0n), L.digits_value.go(s, 0n), ns, symN(L.digits_value.go(s, 0n), Dec.value.go(s, 0n), PDec.value_go_same(s, 0n)), L.dec_show_value(ns))))

def hL9(+ns: Nat, +h: {L.nsec_ok(ns) == True{} : Bool}) -> {Nat.is_le(String.length(Dec.show(ns)), 9n) == True{} : Bool}:
  lt_to_le(String.length(Dec.show(ns)), 10n, h)

def congSN(-f: String -> Nat, -a: String, -b: String, e: {a == b : String}) -> {f(a) == f(b) : Nat}:
  Equal.cong(String, Nat, f, a, b, e)

def fE5(+ns: Nat, +h: {L.nsec_ok(ns) == True{} : Bool}) -> {String.length(fP(ns)) == 9n : Nat}:
  +s = Dec.show(ns)
  +j = Nat.sub(9n, String.length(s))
  trN(String.length(fP(ns)), Nat.add(String.length(zeros(j)), String.length(s)), 9n, len_app(zeros(j), s),
    trN(Nat.add(String.length(zeros(j)), String.length(s)), Nat.add(j, String.length(s)), 9n,
      congN(x => Nat.add(x, String.length(s)), String.length(zeros(j)), j, len_zeros(j)), sub_add_r(String.length(s), 9n, hL9(ns, h))))

def fE6(+ns: Nat, +h: {L.nsec_ok(ns) == True{} : Bool}) -> {Nat.add(String.length(fT(ns)), fk(ns)) == 9n : Nat}:
  +T = fT(ns)
  +k = fk(ns)
  +a = String.append(T, zeros(k))
  +e1 = trN(Nat.add(String.length(T), k), Nat.add(String.length(T), String.length(zeros(k))), String.length(a),
    congN(x => Nat.add(String.length(T), x), k, String.length(zeros(k)), symN(String.length(zeros(k)), k, len_zeros(k))),
    symN(String.length(a), Nat.add(String.length(T), String.length(zeros(k))), len_app(T, zeros(k))))
  trN(Nat.add(String.length(T), k), String.length(a), 9n, e1,
    trN(String.length(a), String.length(fP(ns)), 9n, congSN(x => String.length(x), a, fP(ns), symS(fP(ns), a, fE2(ns))), fE5(ns, h)))

def rw_ne0(-a: Nat, -b: Nat, e: {a == b : Nat}, h: {Nat.is_eq(b, 0n) == False{} : Bool}) -> {Nat.is_eq(a, 0n) == False{} : Bool}:
  %symN(a, b, e) : {Nat.is_eq(_, 0n) == False{} : Bool}
  h

# a fraction that denotes a nonzero value has a digit
def tne(t: String, +k: Nat, +ns: Nat, +e: {Nat.mul(Dec.value(t), Nat.pow(10n, k)) == ns : Nat}, +h0: {Nat.is_eq(ns, 0n) == False{} : Bool})
  -> {Nat.is_ge(String.length(t), 1n) == True{} : Bool}:
  match t:
    case SNil{}:
      absurdT({Nat.is_ge(0n, 1n) == True{} : Bool}, rw_ne0(0n, ns, e, h0))
    case SCon{+c, +r}:
      ge0(String.length(r))

# the fraction's value times 10^k is ns
def fval(+ns: Nat) -> {Nat.mul(Dec.value(fT(ns)), Nat.pow(10n, fk(ns))) == ns : Nat}:
  +T = fT(ns)
  +k = fk(ns)
  +a = String.append(T, zeros(k))
  trN(Nat.mul(Dec.value(T), Nat.pow(10n, k)), Dec.value.go(zeros(k), Dec.value(T)), ns, symN(Dec.value.go(zeros(k), Dec.value(T)), Nat.mul(Dec.value(T), Nat.pow(10n, k)), vzeros(k, Dec.value(T))),
    trN(Dec.value.go(zeros(k), Dec.value(T)), Dec.value(a), ns, symN(Dec.value(a), Dec.value.go(zeros(k), Dec.value(T)), vapp(T, zeros(k), 0n)),
      trN(Dec.value(a), Dec.value(fP(ns)), ns, congSN(x => Dec.value(x), a, fP(ns), symS(fP(ns), a, fE2(ns))), fE3(ns))))

def fns(+ns: Nat, +h: {L.nsec_ok(ns) == True{} : Bool}) -> {Civil.frac_ns(fT(ns)) == ns : Nat}:
  +T = fT(ns)
  +k = fk(ns)
  +lt9 = le_rw_r(String.length(T), Nat.add(String.length(T), k), 9n, fE6(ns, h), le_add(String.length(T), k))
  +tk = take_all(T, 9n, lt9)
  +sk = trN(Nat.sub(9n, String.length(T)), Nat.sub(Nat.add(String.length(T), k), String.length(T)), k,
    congN(x => Nat.sub(x, String.length(T)), 9n, Nat.add(String.length(T), k), symN(Nat.add(String.length(T), k), 9n, fE6(ns, h))), sub_add_l(String.length(T), k))
  %symS(String.take(T, 9n), T, tk) : {Nat.mul(Dec.value(_), Nat.pow(10n, Nat.sub(9n, String.length(_)))) == ns : Nat}
  %symN(Nat.sub(9n, String.length(T)), k, sk) : {Nat.mul(Dec.value(T), Nat.pow(10n, _)) == ns : Nat}
  fval(ns)

def tdig_a(+ns: Nat) -> {Civil.all_digits.go(String.append(fT(ns), zeros(fk(ns)))) == True{} : Bool}:
  %fE2(ns) : {Civil.all_digits.go(_) == True{} : Bool}
  ad_zeros(Nat.sub(9n, String.length(Dec.show(ns))), Dec.show(ns), show_ad(ns))

def tdig(+ns: Nat) -> {Civil.all_digits.go(fT(ns)) == True{} : Bool}:
  adp(fT(ns), zeros(fk(ns)), tdig_a(ns))

# the parser's split of "." ++ fraction ++ zone
def fsplit(+ns: Nat, +zc: Char, +zr: String, +hz: {Civil.is_digit(zc) == False{} : Bool})
  -> {Civil.split_frac(SCon{'.', String.append(fT(ns), SCon{zc, zr})}) == Civil.FZ{fT(ns), SCon{zc, zr}} : Civil.FZ}:
  +T = fT(ns)
  +Z = {SCon{zc, zr} : String}
  +X = String.append(T, Z)
  +G = {Civil.FZ{T, Z} : Civil.FZ}
  %symS(String.drop(X, 0n), X, drop0(X)) : {Civil.FZ{Civil.span_digits.a(_), String.drop(X, String.length(Civil.span_digits.a(_)))} == G : Civil.FZ}
  %symS(Civil.span_digits.a(X), T, span_T(T, zc, zr, tdig(ns), hz)) : {Civil.FZ{_, String.drop(X, String.length(_))} == G : Civil.FZ}
  %symS(String.drop(X, String.length(T)), Z, drop_app(T, Z)) : {Civil.FZ{T, _} == G : Civil.FZ}
  {==}

def ffok(+ns: Nat, +zc: Char, +zr: String, +h0: {Nat.is_eq(ns, 0n) == False{} : Bool})
  -> {Civil.frac_ok(SCon{'.', String.append(fT(ns), SCon{zc, zr})}, fT(ns)) == True{} : Bool}:
  %symB(Nat.is_ge(String.length(fT(ns)), 1n), True{}, tne(fT(ns), fk(ns), ns, fval(ns), h0)) : {Bool.or(False{}, _) == True{} : Bool}
  {==}

# ---------------------------------------------------------------------
# civil_rfc3339_parse: the zone read back
# ---------------------------------------------------------------------

def sub_le0(u: Nat, v: Nat, +h: {Nat.is_le(u, v) == True{} : Bool}) -> {Nat.sub(u, v) == 0n : Nat}:
  match u v:
    case 0n 0n:
      {==}
    case 0n 1n++vp:
      {==}
    case 1n++up 0n:
      absurdB({Nat.sub(1n+up, 0n) == 0n : Nat}, h)
    case 1n++up 1n++vp:
      sub_le0(up, vp, h)

def gt_le(u: Nat, v: Nat, +h: {Nat.is_gt(u, v) == True{} : Bool}) -> {Nat.is_le(v, u) == True{} : Bool}:
  match u v:
    case 0n 0n:
      absurdB({Nat.is_le(0n, 0n) == True{} : Bool}, h)
    case 0n 1n++vp:
      absurdB({Nat.is_le(1n+vp, 0n) == True{} : Bool}, h)
    case 1n++up 0n:
      {==}
    case 1n++up 1n++vp:
      gt_le(up, vp, h)

def ngt_le(u: Nat, v: Nat, +h: {Nat.is_gt(u, v) == False{} : Bool}) -> {Nat.is_le(u, v) == True{} : Bool}:
  match u v:
    case 0n 0n:
      {==}
    case 0n 1n++vp:
      {==}
    case 1n++up 0n:
      absurdT({Nat.is_le(1n+up, 0n) == True{} : Bool}, h)
    case 1n++up 1n++vp:
      ngt_le(up, vp, h)

def sub_sub(+v: Nat, +u: Nat, +h: {Nat.is_le(u, v) == True{} : Bool}) -> {Nat.sub(v, Nat.sub(v, u)) == u : Nat}:
  +w = Nat.sub(v, u)
  trN(Nat.sub(v, w), Nat.sub(Nat.add(w, u), w), u, congN(x => Nat.sub(x, w), v, Nat.add(w, u), symN(Nat.add(w, u), v, sub_add_r(u, v, h))), sub_add_l(w, u))

def sub_mono(c: Nat, a: Nat, b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.sub(a, c), Nat.sub(b, c)) == True{} : Bool}:
  match c:
    case 0n:
      %symN(Nat.sub(a, 0n), a, sub0(a)) : {Nat.is_le(_, Nat.sub(b, 0n)) == True{} : Bool}
      %symN(Nat.sub(b, 0n), b, sub0(b)) : {Nat.is_le(a, _) == True{} : Bool}
      h
    case 1n++cp:
      match a b:
        case 0n 0n:
          {==}
        case 0n 1n++bp:
          le_zero(Nat.sub(bp, cp))
        case 1n++ap 0n:
          absurdB({Nat.is_le(Nat.sub(ap, cp), 0n) == True{} : Bool}, h)
        case 1n++ap 1n++bp:
          sub_mono(cp, ap, bp, h)

def sub_0l(x: Nat) -> {Nat.sub(0n, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      {==}

def mul_sub(q1: Nat, q2: Nat, +bb: Nat) -> {Nat.sub(Nat.mul(q1, bb), Nat.mul(q2, bb)) == Nat.mul(Nat.sub(q1, q2), bb) : Nat}:
  match q1 q2:
    case 0n 0n:
      {==}
    case 0n 1n++b:
      sub_0l(Nat.mul(1n+b, bb))
    case 1n++a 0n:
      sub0(Nat.mul(1n+a, bb))
    case 1n++a 1n++b:
      trN(Nat.sub(Nat.add(bb, Nat.mul(a, bb)), Nat.add(bb, Nat.mul(b, bb))), Nat.sub(Nat.mul(a, bb), Nat.mul(b, bb)), Nat.mul(Nat.sub(a, b), bb),
        sub_cancel_l(bb, Nat.mul(a, bb), Nat.mul(b, bb)), mul_sub(a, b, bb))

# x with no remainder by B is its quotient times B
def mul_of_mod0(+x: Nat, +b: Nat, +h: {Nat.mod(x, 1n+b) == 0n : Nat}) -> {x == Nat.mul(Nat.div(x, 1n+b), 1n+b) : Nat}:
  +q = Nat.div(x, 1n+b)
  trN(x, Nat.add(Nat.mul(q, 1n+b), Nat.mod(x, 1n+b)), Nat.mul(q, 1n+b), PNat.div_mod_eq(x, b),
    trN(Nat.add(Nat.mul(q, 1n+b), Nat.mod(x, 1n+b)), Nat.add(Nat.mul(q, 1n+b), 0n), Nat.mul(q, 1n+b),
      congN(z => Nat.add(Nat.mul(q, 1n+b), z), Nat.mod(x, 1n+b), 0n, h), symN(Nat.mul(q, 1n+b), Nat.add(Nat.mul(q, 1n+b), 0n), PNat.add_zero(Nat.mul(q, 1n+b)))))

def mod_mul0(+q: Nat, +b: Nat) -> {Nat.mod(Nat.mul(q, 1n+b), 1n+b) == 0n : Nat}:
  trN(Nat.mod(Nat.mul(q, 1n+b), 1n+b), Nat.mod(Nat.add(Nat.mul(q, 1n+b), 0n), 1n+b), 0n,
    congN(z => Nat.mod(z, 1n+b), Nat.mul(q, 1n+b), Nat.add(Nat.mul(q, 1n+b), 0n), PNat.add_zero(Nat.mul(q, 1n+b))), mod_unique(q, 0n, b, {==}))

def mod_sub0(+x: Nat, +y: Nat, +b: Nat, +hx: {Nat.mod(x, 1n+b) == 0n : Nat}, +hy: {Nat.mod(y, 1n+b) == 0n : Nat})
  -> {Nat.mod(Nat.sub(x, y), 1n+b) == 0n : Nat}:
  +qx = Nat.div(x, 1n+b)
  +qy = Nat.div(y, 1n+b)
  +e1 = trN(Nat.sub(x, y), Nat.sub(Nat.mul(qx, 1n+b), y), Nat.mul(Nat.sub(qx, qy), 1n+b),
    congN(z => Nat.sub(z, y), x, Nat.mul(qx, 1n+b), mul_of_mod0(x, b, hx)),
    trN(Nat.sub(Nat.mul(qx, 1n+b), y), Nat.sub(Nat.mul(qx, 1n+b), Nat.mul(qy, 1n+b)), Nat.mul(Nat.sub(qx, qy), 1n+b),
      congN(z => Nat.sub(Nat.mul(qx, 1n+b), z), y, Nat.mul(qy, 1n+b), mul_of_mod0(y, b, hy)), mul_sub(qx, qy, 1n+b)))
  trN(Nat.mod(Nat.sub(x, y), 1n+b), Nat.mod(Nat.mul(Nat.sub(qx, qy), 1n+b), 1n+b), 0n, congN(z => Nat.mod(z, 1n+b), Nat.sub(x, y), Nat.mul(Nat.sub(qx, qy), 1n+b), e1),
    mod_mul0(Nat.sub(qx, qy), b))

def m86400() -> {Nat.mod(86400n, 60n) == 0n : Nat}:
  {==}

def d86400() -> {Nat.div(86400n, 3600n) == 24n : Nat}:
  {==}

def d86399() -> {Nat.div(86399n, 3600n) == 23n : Nat}:
  {==}

def s172800() -> {Nat.sub(172800n, 86400n) == 86400n : Nat}:
  {==}

def eq_of_is_eq(u: Nat, v: Nat, +h: {Nat.is_eq(u, v) == True{} : Bool}) -> {u == v : Nat}:
  match u v:
    case 0n 0n:
      {==}
    case 0n 1n++vp:
      absurdB({0n == 1n+vp : Nat}, h)
    case 1n++up 0n:
      absurdB({1n+up == 0n : Nat}, h)
    case 1n++up 1n++vp:
      succ_cong(up, vp, eq_of_is_eq(up, vp, h))

def lt_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  le_trans(a, 1n+a, b, le_succ(a), lt_to_le(a, b, h))

def zstr(+sg: Char, +zh: Nat, +zm: Nat) -> String:
  SCon{sg, String.append(d2(zh), SCon{':', d2(zm)})}

def zbody(+sgok: Bool, +ah: Bool, +am: Bool, +vh: Nat, +vm: Nat) -> Bool:
  Bool.and(Nat.is_eq(6n, 6n), Bool.and(sgok, Bool.and(Bool.and(Nat.is_eq(2n, 2n), ah), Bool.and(True{}, Bool.and(Bool.and(Nat.is_eq(2n, 2n), am),
    Bool.and(Nat.is_le(vh, 24n), Nat.is_le(vm, 60n)))))))

def zok(+sg: Char, +zh: Nat, +zm: Nat, +hsg: {Bool.or(Civil.first_is(zstr(sg, zh, zm), 43), Civil.first_is(zstr(sg, zh, zm), 45)) == True{} : Bool},
  +hz: {String.eq(zstr(sg, zh, zm), "Z") == False{} : Bool},
  +hzh: {Nat.is_le(zh, 24n) == True{} : Bool}, +hzm: {Nat.is_lt(zm, 60n) == True{} : Bool}) -> {Civil.zone_ok(zstr(sg, zh, zm)) == True{} : Bool}:
  +z = zstr(sg, zh, zm)
  +SG = Bool.or(Civil.first_is(z, 43), Civil.first_is(z, 45))
  +AH = Civil.all_digits.go(d2(zh))
  +AM = Civil.all_digits.go(d2(zm))
  +VH = Civil.sval.go(d2(zh), 0n)
  +VM = Civil.sval.go(d2(zm), 0n)
  +h100 = le_to_lt(zh, 100n, le_trans(1n+zh, 25n, 100n, hzh, {==}))
  %symB(String.eq(z, "Z"), False{}, hz) : {Bool.or(_, zbody(SG, AH, AM, VH, VM)) == True{} : Bool}
  %symB(SG, True{}, hsg) : {zbody(_, AH, AM, VH, VM) == True{} : Bool}
  %symB(AH, True{}, ad2(zh)) : {zbody(True{}, _, AM, VH, VM) == True{} : Bool}
  %symB(AM, True{}, ad2(zm)) : {zbody(True{}, True{}, _, VH, VM) == True{} : Bool}
  %symN(VH, zh, rd2(zh, h100)) : {zbody(True{}, True{}, True{}, _, VM) == True{} : Bool}
  %symN(VM, zm, rd2(zm, lt60_100(zm, hzm))) : {zbody(True{}, True{}, True{}, zh, _) == True{} : Bool}
  and_i(Nat.is_le(zh, 24n), Nat.is_le(zm, 60n), hzh, lt_le(zm, 60n, hzm))

def zoff_p(+zh: Nat, +zm: Nat, +hzh: {Nat.is_lt(zh, 100n) == True{} : Bool}, +hzm: {Nat.is_lt(zm, 100n) == True{} : Bool})
  -> {Civil.zone_off(zstr('+', zh, zm)) == Nat.add(Nat.add(Nat.mul(zh, 3600n), Nat.mul(zm, 60n)), 86400n) : Nat}:
  +VH = Civil.sval.go(d2(zh), 0n)
  +VM = Civil.sval.go(d2(zm), 0n)
  +R = Nat.add(Nat.add(Nat.mul(zh, 3600n), Nat.mul(zm, 60n)), 86400n)
  %symN(VH, zh, rd2(zh, hzh)) : {Nat.add(Nat.add(Nat.mul(_, 3600n), Nat.mul(VM, 60n)), 86400n) == R : Nat}
  %symN(VM, zm, rd2(zm, hzm)) : {Nat.add(Nat.add(Nat.mul(zh, 3600n), Nat.mul(_, 60n)), 86400n) == R : Nat}
  {==}

def zoff_m(+zh: Nat, +zm: Nat, +hzh: {Nat.is_lt(zh, 100n) == True{} : Bool}, +hzm: {Nat.is_lt(zm, 100n) == True{} : Bool})
  -> {Civil.zone_off(zstr('-', zh, zm)) == Nat.sub(86400n, Nat.add(Nat.mul(zh, 3600n), Nat.mul(zm, 60n))) : Nat}:
  +VH = Civil.sval.go(d2(zh), 0n)
  +VM = Civil.sval.go(d2(zm), 0n)
  +R = Nat.sub(86400n, Nat.add(Nat.mul(zh, 3600n), Nat.mul(zm, 60n)))
  %symN(VH, zh, rd2(zh, hzh)) : {Nat.sub(86400n, Nat.add(Nat.mul(_, 3600n), Nat.mul(VM, 60n))) == R : Nat}
  %symN(VM, zm, rd2(zm, hzm)) : {Nat.sub(86400n, Nat.add(Nat.mul(zh, 3600n), Nat.mul(_, 60n))) == R : Nat}
  {==}

# hours and minutes of an offset in whole minutes add back up to it
def zsec(+zo: Nat, +h0: {Nat.mod(zo, 60n) == 0n : Nat})
  -> {Nat.add(Nat.mul(Nat.div(zo, 3600n), 3600n), Nat.mul(Nat.mod(Nat.div(zo, 60n), 60n), 60n)) == zo : Nat}:
  +X = Nat.add(Nat.mul(Nat.div(zo, 3600n), 3600n), Nat.mul(Nat.mod(Nat.div(zo, 60n), 60n), 60n))
  trN(X, Nat.add(X, 0n), zo, PNat.add_zero(X), trN(Nat.add(X, 0n), Nat.add(X, Nat.mod(zo, 60n)), zo, congN(z => Nat.add(X, z), 0n, Nat.mod(zo, 60n), symN(Nat.mod(zo, 60n), 0n, h0)), hms(zo)))

# ---------------------------------------------------------------------
# civil_rfc3339_parse: the text written
# ---------------------------------------------------------------------

def zone_str(+off: Nat) -> String:
  +zo = Civil.absdiff(off, 86400n)
  Civil.pick(String, Nat.is_eq(off, 86400n), "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"),
    String.append(Civil.pad2(Nat.div(zo, 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(zo, 60n), 60n))))))

def rrest(+ph: String, +pi: String, +ps: String, +w: String) -> String:
  String.append("T", String.append(ph, String.append(":", String.append(pi, String.append(":", String.append(ps, w))))))

def rtext(+p4: String, +pm: String, +pd: String, +ph: String, +pi: String, +ps: String, +w: String) -> String:
  String.append(String.append(p4, String.append("-", String.append(pm, String.append("-", pd)))), rrest(ph, pi, ps, w))

def loc(+s: Nat, +off: Nat) -> Nat:
  Nat.sub(Nat.add(s, off), 86400n)

def sodf(+s: Nat, +off: Nat) -> Nat:
  Nat.mod(loc(s, off), 86400n)

def daysf(+s: Nat, +off: Nat) -> Nat:
  Nat.div(loc(s, off), 86400n)

# the text of an instant, its fields written as digits
def text_txt(+s: Nat, +ns: Nat, +off: Nat, +y: Nat, +m: Nat, +d: Nat, +rc: Char, +rr: String,
  +e: {Civil.days_to_ymd(daysf(s, off)) == Civil.Ymd{y, m, d} : Civil.Ymd},
  +hy0: {Nat.is_le(1000n, y) == True{} : Bool}, +hy: {Nat.is_le(y, 9999n) == True{} : Bool},
  +hm: {Nat.is_lt(m, 100n) == True{} : Bool}, +hd: {Nat.is_lt(d, 100n) == True{} : Bool},
  +hh: {Nat.is_lt(Nat.div(sodf(s, off), 3600n), 100n) == True{} : Bool},
  +ew: {String.append(Civil.frac_text(ns, 9n), zone_str(off)) == SCon{rc, rr} : String})
  -> {Civil.rfc3339(Civil.Time{s, ns, off}) == txt(y, m, d, Nat.div(sodf(s, off), 3600n), Nat.mod(Nat.div(sodf(s, off), 60n), 60n), Nat.mod(sodf(s, off), 60n), rc, rr) : String}:
  +sod = sodf(s, off)
  +H = Nat.div(sod, 3600n)
  +I = Nat.mod(Nat.div(sod, 60n), 60n)
  +S = Nat.mod(sod, 60n)
  +W = String.append(Civil.frac_text(ns, 9n), zone_str(off))
  +G = txt(y, m, d, H, I, S, rc, rr)
  %Equal.sym(Civil.Ymd, Civil.days_to_ymd(daysf(s, off)), Civil.Ymd{y, m, d}, e)
    : {String.append(Civil.rfc_date(_), rrest(Civil.pad2(H), Civil.pad2(I), Civil.pad2(S), W)) == G : String}
  %symS(Dec.pad(4n, y), d4(y), pad4_d(y, hy0, hy)) : {rtext(_, Civil.pad2(m), Civil.pad2(d), Civil.pad2(H), Civil.pad2(I), Civil.pad2(S), W) == G : String}
  %symS(Civil.pad2(m), d2(m), pad2_d(m, hm)) : {rtext(d4(y), _, Civil.pad2(d), Civil.pad2(H), Civil.pad2(I), Civil.pad2(S), W) == G : String}
  %symS(Civil.pad2(d), d2(d), pad2_d(d, hd)) : {rtext(d4(y), d2(m), _, Civil.pad2(H), Civil.pad2(I), Civil.pad2(S), W) == G : String}
  %symS(Civil.pad2(H), d2(H), pad2_d(H, hh)) : {rtext(d4(y), d2(m), d2(d), _, Civil.pad2(I), Civil.pad2(S), W) == G : String}
  %symS(Civil.pad2(I), d2(I), pad2_d(I, lt60_100(I, PNat.mod_lt(Nat.div(sod, 60n), 59n)))) : {rtext(d4(y), d2(m), d2(d), d2(H), _, Civil.pad2(S), W) == G : String}
  %symS(Civil.pad2(S), d2(S), pad2_d(S, lt60_100(S, PNat.mod_lt(sod, 59n)))) : {rtext(d4(y), d2(m), d2(d), d2(H), d2(I), _, W) == G : String}
  %symS(W, SCon{rc, rr}, ew) : {rtext(d4(y), d2(m), d2(d), d2(H), d2(I), d2(S), _) == G : String}
  {==}

def swap_r(m: Nat, +k: Nat, +h: Nat) -> {Nat.add(Nat.add(m, k), h) == Nat.add(Nat.add(m, h), k) : Nat}:
  match m:
    case 0n:
      PNat.add_comm(k, h)
    case 1n++p:
      succ_cong(Nat.add(Nat.add(p, k), h), Nat.add(Nat.add(p, h), k), swap_r(p, k, h))

# the local seconds the parser adds up are the instant's, shifted by a day
def el_of(+s: Nat, +off: Nat, +y: Nat, +m: Nat, +d: Nat, +hyd: {Civil.ymd_to_days(y, m, d) == daysf(s, off) : Nat},
  +hge: {Nat.is_le(86400n, Nat.add(s, off)) == True{} : Bool})
  -> {loc_body(y, m, d, Nat.div(sodf(s, off), 3600n), Nat.mod(Nat.div(sodf(s, off), 60n), 60n), Nat.mod(sodf(s, off), 60n)) == Nat.add(s, off) : Nat}:
  +sod = sodf(s, off)
  +D = daysf(s, off)
  +l = loc(s, off)
  +hm = Nat.add(Nat.add(Nat.mul(Nat.div(sod, 3600n), 3600n), Nat.mul(Nat.mod(Nat.div(sod, 60n), 60n), 60n)), Nat.mod(sod, 60n))
  +A = Nat.mul(D, 86400n)
  +e1 = congN(x => Nat.add(Nat.add(Nat.mul(x, 86400n), 86400n), hm), Civil.ymd_to_days(y, m, d), D, hyd)
  +e2 = congN(x => Nat.add(Nat.add(A, 86400n), x), hm, sod, hms(sod))
  +e3 = swap_r(A, 86400n, sod)
  +e4 = congN(x => Nat.add(x, 86400n), Nat.add(A, sod), l, symN(l, Nat.add(A, sod), PNat.div_mod_eq(l, 86399n)))
  +e5 = sub_add_r(86400n, Nat.add(s, off), hge)
  trN(loc_body(y, m, d, Nat.div(sod, 3600n), Nat.mod(Nat.div(sod, 60n), 60n), Nat.mod(sod, 60n)), Nat.add(Nat.add(A, 86400n), hm), Nat.add(s, off), e1,
    trN(Nat.add(Nat.add(A, 86400n), hm), Nat.add(Nat.add(A, 86400n), sod), Nat.add(s, off), e2,
      trN(Nat.add(Nat.add(A, 86400n), sod), Nat.add(Nat.add(A, sod), 86400n), Nat.add(s, off), e3,
        trN(Nat.add(Nat.add(A, sod), 86400n), Nat.add(l, 86400n), Nat.add(s, off), e4, e5))))

def ew0(+ns: Nat, +off: Nat, +zc: Char, +zr: String, +ec: {Nat.is_eq(ns, 0n) == True{} : Bool}, +ezs: {zone_str(off) == SCon{zc, zr} : String})
  -> {String.append(Civil.frac_text(ns, 9n), zone_str(off)) == SCon{zc, zr} : String}:
  %symB(Nat.is_eq(ns, 0n), True{}, ec) : {String.append(Civil.pick(String, _, "", String.append(".", Civil.trim_zeros_r(Dec.pad(9n, ns)))), zone_str(off)) == SCon{zc, zr} : String}
  ezs

def ew1(+ns: Nat, +off: Nat, +zc: Char, +zr: String, +ec: {Nat.is_eq(ns, 0n) == False{} : Bool}, +ezs: {zone_str(off) == SCon{zc, zr} : String})
  -> {String.append(Civil.frac_text(ns, 9n), zone_str(off)) == SCon{'.', String.append(fT(ns), SCon{zc, zr})} : String}:
  +R = {SCon{'.', String.append(fT(ns), SCon{zc, zr})} : String}
  %symB(Nat.is_eq(ns, 0n), False{}, ec) : {String.append(Civil.pick(String, _, "", String.append(".", Civil.trim_zeros_r(Dec.pad(9n, ns)))), zone_str(off)) == R : String}
  %symS(zone_str(off), SCon{zc, zr}, ezs) : {SCon{'.', String.append(fT(ns), _)} == R : String}
  {==}

def fin.of(c: Bool, +s: Nat, +ns: Nat, +off: Nat, +y: Nat, +m: Nat, +d: Nat, +zc: Char, +zr: String,
  +ec: {Nat.is_eq(ns, 0n) == c : Bool}, +hns: {L.nsec_ok(ns) == True{} : Bool},
  +e: {Civil.days_to_ymd(daysf(s, off)) == Civil.Ymd{y, m, d} : Civil.Ymd}, +hvd: {L.valid_date(y, m, d) == True{} : Bool},
  +hyd: {Civil.ymd_to_days(y, m, d) == daysf(s, off) : Nat},
  +hy0: {Nat.is_le(1000n, y) == True{} : Bool}, +hy: {Nat.is_le(y, 9999n) == True{} : Bool},
  +hm: {Nat.is_lt(m, 100n) == True{} : Bool}, +hd: {Nat.is_lt(d, 100n) == True{} : Bool},
  +hH: {Nat.is_lt(Nat.div(sodf(s, off), 3600n), 24n) == True{} : Bool}, +hge: {Nat.is_le(86400n, Nat.add(s, off)) == True{} : Bool},
  +ezs: {zone_str(off) == SCon{zc, zr} : String}, +ezok: {Civil.zone_ok(SCon{zc, zr}) == True{} : Bool}, +ezoff: {Civil.zone_off(SCon{zc, zr}) == off : Nat},
  +hzd: {Civil.is_digit(zc) == False{} : Bool}, +hsp0: {Civil.split_frac(SCon{zc, zr}) == Civil.FZ{"", SCon{zc, zr}} : Civil.FZ},
  +hfo0: {Civil.frac_ok(SCon{zc, zr}, "") == True{} : Bool})
  -> {Civil.parse_rfc3339(Civil.rfc3339(Civil.Time{s, ns, off})) == Some{Civil.Time{s, ns, off}} : Maybe<&2, Civil.Time>}:
  match c:
    case True{}:
      +sod = sodf(s, off)
      +H = Nat.div(sod, 3600n)
      +I = Nat.mod(Nat.div(sod, 60n), 60n)
      +S = Nat.mod(sod, 60n)
      +hI = PNat.mod_lt(Nat.div(sod, 60n), 59n)
      +hS = PNat.mod_lt(sod, 59n)
      +el = el_of(s, off, y, m, d, hyd, hge)
      +G = {Some{Civil.Time{s, ns, off}} : Maybe<&2, Civil.Time>}
      +tx = text_txt(s, ns, off, y, m, d, zc, zr, e, hy0, hy, hm, hd, lt24_100(H, hH), ew0(ns, off, zc, zr, ec, ezs))
      %symS(Civil.rfc3339(Civil.Time{s, ns, off}), txt(y, m, d, H, I, S, zc, zr), tx) : {Civil.parse_rfc3339(_) == G : Maybe<&2, Civil.Time>}
      pmain(y, m, d, H, I, S, zc, zr, "", SCon{zc, zr}, s, ns, off, hvd, hy, hm, hd, hH, hI, hS, el, hsp0, hfo0,
        symN(ns, 0n, eq_of_is_eq(ns, 0n, ec)), ezok, ezoff)
    case False{}:
      +sod = sodf(s, off)
      +H = Nat.div(sod, 3600n)
      +I = Nat.mod(Nat.div(sod, 60n), 60n)
      +S = Nat.mod(sod, 60n)
      +hI = PNat.mod_lt(Nat.div(sod, 60n), 59n)
      +hS = PNat.mod_lt(sod, 59n)
      +el = el_of(s, off, y, m, d, hyd, hge)
      +G = {Some{Civil.Time{s, ns, off}} : Maybe<&2, Civil.Time>}
      +rr = String.append(fT(ns), SCon{zc, zr})
      +tx = text_txt(s, ns, off, y, m, d, '.', rr, e, hy0, hy, hm, hd, lt24_100(H, hH), ew1(ns, off, zc, zr, ec, ezs))
      %symS(Civil.rfc3339(Civil.Time{s, ns, off}), txt(y, m, d, H, I, S, '.', rr), tx) : {Civil.parse_rfc3339(_) == G : Maybe<&2, Civil.Time>}
      pmain(y, m, d, H, I, S, '.', rr, fT(ns), SCon{zc, zr}, s, ns, off, hvd, hy, hm, hd, hH, hI, hS, el,
        fsplit(ns, zc, zr, hzd), ffok(ns, zc, zr, ec), fns(ns, hns), ezok, ezoff)

# ---------------------------------------------------------------------
# civil_rfc3339_parse: the three zones, then the law
# ---------------------------------------------------------------------

def zs_Z(+off: Nat, +e1: {Nat.is_eq(off, 86400n) == True{} : Bool}) -> {zone_str(off) == SCon{'Z', SNil{}} : String}:
  +zo = Civil.absdiff(off, 86400n)
  %symB(Nat.is_eq(off, 86400n), True{}, e1) : {Civil.pick(String, _, "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"),
    String.append(Civil.pad2(Nat.div(zo, 3600n)), String.append(":", Civil.pad2(Nat.mod(Nat.div(zo, 60n), 60n)))))) == SCon{'Z', SNil{}} : String}
  {==}

def zs_s(+off: Nat, +sg: Char, c2: Bool, +e1: {Nat.is_eq(off, 86400n) == False{} : Bool}, +e2: {Nat.is_gt(off, 86400n) == c2 : Bool},
  +esg: {Civil.pick(String, c2, "+", "-") == SCon{sg, SNil{}} : String},
  +h1: {Nat.is_lt(Nat.div(Civil.absdiff(off, 86400n), 3600n), 100n) == True{} : Bool},
  +h2: {Nat.is_lt(Nat.mod(Nat.div(Civil.absdiff(off, 86400n), 60n), 60n), 100n) == True{} : Bool})
  -> {zone_str(off) == zstr(sg, Nat.div(Civil.absdiff(off, 86400n), 3600n), Nat.mod(Nat.div(Civil.absdiff(off, 86400n), 60n), 60n)) : String}:
  +zo = Civil.absdiff(off, 86400n)
  +zh = Nat.div(zo, 3600n)
  +zm = Nat.mod(Nat.div(zo, 60n), 60n)
  +G = zstr(sg, zh, zm)
  %symB(Nat.is_eq(off, 86400n), False{}, e1) : {Civil.pick(String, _, "Z", String.append(Civil.pick(String, Nat.is_gt(off, 86400n), "+", "-"),
    String.append(Civil.pad2(zh), String.append(":", Civil.pad2(zm))))) == G : String}
  %symB(Nat.is_gt(off, 86400n), c2, e2) : {String.append(Civil.pick(String, _, "+", "-"), String.append(Civil.pad2(zh), String.append(":", Civil.pad2(zm)))) == G : String}
  %symS(Civil.pick(String, c2, "+", "-"), SCon{sg, SNil{}}, esg) : {String.append(_, String.append(Civil.pad2(zh), String.append(":", Civil.pad2(zm)))) == G : String}
  %symS(Civil.pad2(zh), d2(zh), pad2_d(zh, h1)) : {SCon{sg, String.append(_, String.append(":", Civil.pad2(zm)))} == G : String}
  %symS(Civil.pad2(zm), d2(zm), pad2_d(zm, h2)) : {SCon{sg, String.append(d2(zh), SCon{':', _})} == G : String}
  {==}

# the zone's hour at most 24 and its minute below 60, from an offset within a day
def zh24(+zo: Nat, +zle: {Nat.is_le(zo, 86400n) == True{} : Bool}) -> {Nat.is_le(Nat.div(zo, 3600n), 24n) == True{} : Bool}:
  le_rw_r(Nat.div(zo, 3600n), Nat.div(86400n, 3600n), 24n, d86400, div_mono(zo, 86400n, 3599n, zle))

def lt100_24(+n: Nat, +h: {Nat.is_le(n, 24n) == True{} : Bool}) -> {Nat.is_lt(n, 100n) == True{} : Bool}:
  le_to_lt(n, 100n, le_trans(1n+n, 25n, 100n, h, {==}))

def fin_z.p(+s: Nat, +ns: Nat, +off: Nat, +y: Nat, +m: Nat, +d: Nat,
  +hns: {L.nsec_ok(ns) == True{} : Bool},
  +e: {Civil.days_to_ymd(daysf(s, off)) == Civil.Ymd{y, m, d} : Civil.Ymd}, +hvd: {L.valid_date(y, m, d) == True{} : Bool},
  +hyd: {Civil.ymd_to_days(y, m, d) == daysf(s, off) : Nat},
  +hy0: {Nat.is_le(1000n, y) == True{} : Bool}, +hy: {Nat.is_le(y, 9999n) == True{} : Bool},
  +hm: {Nat.is_lt(m, 100n) == True{} : Bool}, +hd: {Nat.is_lt(d, 100n) == True{} : Bool},
  +hH: {Nat.is_lt(Nat.div(sodf(s, off), 3600n), 24n) == True{} : Bool}, +hge: {Nat.is_le(86400n, Nat.add(s, off)) == True{} : Bool},
  +e1: {Nat.is_eq(off, 86400n) == False{} : Bool}, +e2: {Nat.is_gt(off, 86400n) == True{} : Bool},
  +hle: {Nat.is_le(off, 172800n) == True{} : Bool}, +hmod: {Nat.is_eq(Nat.mod(off, 60n), 0n) == True{} : Bool})
  -> {Civil.parse_rfc3339(Civil.rfc3339(Civil.Time{s, ns, off})) == Some{Civil.Time{s, ns, off}} : Maybe<&2, Civil.Time>}:
  +zo = Civil.absdiff(off, 86400n)
  +zh = Nat.div(zo, 3600n)
  +zm = Nat.mod(Nat.div(zo, 60n), 60n)
  +so = Nat.sub(off, 86400n)
  +h86 = gt_le(off, 86400n, e2)
  +zoe = trN(zo, Nat.add(so, 0n), so, congN(x => Nat.add(so, x), Nat.sub(86400n, off), 0n, sub_le0(86400n, off, h86)), symN(so, Nat.add(so, 0n), PNat.add_zero(so)))
  +zmod = trN(Nat.mod(zo, 60n), Nat.mod(so, 60n), 0n, congN(x => Nat.mod(x, 60n), zo, so, zoe), mod_sub0(off, 86400n, 59n, eq_of_is_eq(Nat.mod(off, 60n), 0n, hmod), m86400))
  +zle = le_rw_l(so, zo, 86400n, symN(zo, so, zoe), le_rw_r(so, Nat.sub(172800n, 86400n), 86400n, s172800, sub_mono(86400n, off, 172800n, hle)))
  +hzh = zh24(zo, zle)
  +hzm = PNat.mod_lt(Nat.div(zo, 60n), 59n)
  +X = Nat.add(Nat.mul(zh, 3600n), Nat.mul(zm, 60n))
  +ezoff = trN(Civil.zone_off(zstr('+', zh, zm)), Nat.add(X, 86400n), off, zoff_p(zh, zm, lt100_24(zh, hzh), lt60_100(zm, hzm)),
    trN(Nat.add(X, 86400n), Nat.add(zo, 86400n), off, congN(x => Nat.add(x, 86400n), X, zo, zsec(zo, zmod)),
      trN(Nat.add(zo, 86400n), Nat.add(so, 86400n), off, congN(x => Nat.add(x, 86400n), zo, so, zoe), sub_add_r(86400n, off, h86))))
  fin.of(Nat.is_eq(ns, 0n), s, ns, off, y, m, d, '+', String.append(d2(zh), SCon{':', d2(zm)}), {==}, hns, e, hvd, hyd, hy0, hy, hm, hd, hH, hge,
    zs_s(off, '+', True{}, e1, e2, {==}, lt100_24(zh, hzh), lt60_100(zm, hzm)), zok('+', zh, zm, {==}, {==}, hzh, hzm), ezoff, {==}, {==}, {==})

def fin_z.m(+s: Nat, +ns: Nat, +off: Nat, +y: Nat, +m: Nat, +d: Nat,
  +hns: {L.nsec_ok(ns) == True{} : Bool},
  +e: {Civil.days_to_ymd(daysf(s, off)) == Civil.Ymd{y, m, d} : Civil.Ymd}, +hvd: {L.valid_date(y, m, d) == True{} : Bool},
  +hyd: {Civil.ymd_to_days(y, m, d) == daysf(s, off) : Nat},
  +hy0: {Nat.is_le(1000n, y) == True{} : Bool}, +hy: {Nat.is_le(y, 9999n) == True{} : Bool},
  +hm: {Nat.is_lt(m, 100n) == True{} : Bool}, +hd: {Nat.is_lt(d, 100n) == True{} : Bool},
  +hH: {Nat.is_lt(Nat.div(sodf(s, off), 3600n), 24n) == True{} : Bool}, +hge: {Nat.is_le(86400n, Nat.add(s, off)) == True{} : Bool},
  +e1: {Nat.is_eq(off, 86400n) == False{} : Bool}, +e2: {Nat.is_gt(off, 86400n) == False{} : Bool},
  +hmod: {Nat.is_eq(Nat.mod(off, 60n), 0n) == True{} : Bool})
  -> {Civil.parse_rfc3339(Civil.rfc3339(Civil.Time{s, ns, off})) == Some{Civil.Time{s, ns, off}} : Maybe<&2, Civil.Time>}:
  +zo = Civil.absdiff(off, 86400n)
  +zh = Nat.div(zo, 3600n)
  +zm = Nat.mod(Nat.div(zo, 60n), 60n)
  +so = Nat.sub(86400n, off)
  +h86 = ngt_le(off, 86400n, e2)
  +zoe = congN(x => Nat.add(x, so), Nat.sub(off, 86400n), 0n, sub_le0(off, 86400n, h86))
  +zmod = trN(Nat.mod(zo, 60n), Nat.mod(so, 60n), 0n, congN(x => Nat.mod(x, 60n), zo, so, zoe), mod_sub0(86400n, off, 59n, m86400, eq_of_is_eq(Nat.mod(off, 60n), 0n, hmod)))
  +zle = le_rw_l(so, zo, 86400n, symN(zo, so, zoe), sub_le(86400n, off))
  +hzh = zh24(zo, zle)
  +hzm = PNat.mod_lt(Nat.div(zo, 60n), 59n)
  +X = Nat.add(Nat.mul(zh, 3600n), Nat.mul(zm, 60n))
  +ezoff = trN(Civil.zone_off(zstr('-', zh, zm)), Nat.sub(86400n, X), off, zoff_m(zh, zm, lt100_24(zh, hzh), lt60_100(zm, hzm)),
    trN(Nat.sub(86400n, X), Nat.sub(86400n, zo), off, congN(x => Nat.sub(86400n, x), X, zo, zsec(zo, zmod)),
      trN(Nat.sub(86400n, zo), Nat.sub(86400n, so), off, congN(x => Nat.sub(86400n, x), zo, so, zoe), sub_sub(86400n, off, h86))))
  fin.of(Nat.is_eq(ns, 0n), s, ns, off, y, m, d, '-', String.append(d2(zh), SCon{':', d2(zm)}), {==}, hns, e, hvd, hyd, hy0, hy, hm, hd, hH, hge,
    zs_s(off, '-', False{}, e1, e2, {==}, lt100_24(zh, hzh), lt60_100(zm, hzm)), zok('-', zh, zm, {==}, {==}, hzh, hzm), ezoff, {==}, {==}, {==})

def fin_z(c1: Bool, c2: Bool, +s: Nat, +ns: Nat, +off: Nat, +y: Nat, +m: Nat, +d: Nat,
  +hns: {L.nsec_ok(ns) == True{} : Bool},
  +e: {Civil.days_to_ymd(daysf(s, off)) == Civil.Ymd{y, m, d} : Civil.Ymd}, +hvd: {L.valid_date(y, m, d) == True{} : Bool},
  +hyd: {Civil.ymd_to_days(y, m, d) == daysf(s, off) : Nat},
  +hy0: {Nat.is_le(1000n, y) == True{} : Bool}, +hy: {Nat.is_le(y, 9999n) == True{} : Bool},
  +hm: {Nat.is_lt(m, 100n) == True{} : Bool}, +hd: {Nat.is_lt(d, 100n) == True{} : Bool},
  +hH: {Nat.is_lt(Nat.div(sodf(s, off), 3600n), 24n) == True{} : Bool}, +hge: {Nat.is_le(86400n, Nat.add(s, off)) == True{} : Bool},
  +e1: {Nat.is_eq(off, 86400n) == c1 : Bool}, +e2: {Nat.is_gt(off, 86400n) == c2 : Bool},
  +hle: {Nat.is_le(off, 172800n) == True{} : Bool}, +hmod: {Nat.is_eq(Nat.mod(off, 60n), 0n) == True{} : Bool})
  -> {Civil.parse_rfc3339(Civil.rfc3339(Civil.Time{s, ns, off})) == Some{Civil.Time{s, ns, off}} : Maybe<&2, Civil.Time>}:
  match c1:
    case True{}:
      fin.of(Nat.is_eq(ns, 0n), s, ns, off, y, m, d, 'Z', SNil{}, {==}, hns, e, hvd, hyd, hy0, hy, hm, hd, hH, hge,
        zs_Z(off, e1), {==}, symN(off, 86400n, eq_of_is_eq(off, 86400n, e1)), {==}, {==}, {==})
    case False{}:
      match c2:
        case True{}:
          fin_z.p(s, ns, off, y, m, d, hns, e, hvd, hyd, hy0, hy, hm, hd, hH, hge, e1, e2, hle, hmod)
        case False{}:
          fin_z.m(s, ns, off, y, m, d, hns, e, hvd, hyd, hy0, hy, hm, hd, hH, hge, e1, e2, hmod)

def pickle(c: Bool, +a: Nat, +b: Nat, +k: Nat, +ha: {Nat.is_le(a, k) == True{} : Bool}, +hb: {Nat.is_le(b, k) == True{} : Bool})
  -> {Nat.is_le(L.pick(Nat, c, a, b), k) == True{} : Bool}:
  match c:
    case True{}:
      ha
    case False{}:
      hb

def ml31(+y: Nat, +m: Nat) -> {Nat.is_le(L.month_len(y, m), 31n) == True{} : Bool}:
  pickle(Nat.is_eq(m, 2n), L.pick(Nat, L.leap(y), 29n, 28n),
    L.pick(Nat, Bool.or(Bool.or(Nat.is_eq(m, 4n), Nat.is_eq(m, 6n)), Bool.or(Nat.is_eq(m, 9n), Nat.is_eq(m, 11n))), 30n, 31n), 31n,
    pickle(L.leap(y), 29n, 28n, 31n, {==}, {==}),
    pickle(Bool.or(Bool.or(Nat.is_eq(m, 4n), Nat.is_eq(m, 6n)), Bool.or(Nat.is_eq(m, 9n), Nat.is_eq(m, 11n))), 30n, 31n, 31n, {==}, {==}))

def cb_of(+n: Nat, +y: Nat, +m: Nat, +d: Nat, +e: {Civil.days_to_ymd(n) == Civil.Ymd{y, m, d} : Civil.Ymd})
  -> {L.civil_ymd_ok(n, Civil.Ymd{y, m, d}) == True{} : Bool}:
  %e : {L.civil_ymd_ok(n, _) == True{} : Bool}
  L.civil_days_ymd(n)

def yr_of(+n: Nat, +y: Nat, +m: Nat, +d: Nat, +e: {Civil.days_to_ymd(n) == Civil.Ymd{y, m, d} : Civil.Ymd},
  +h: {Nat.is_le(L.ymd_year(Civil.days_to_ymd(n)), 9999n) == True{} : Bool}) -> {Nat.is_le(y, 9999n) == True{} : Bool}:
  %e : {Nat.is_le(L.ymd_year(_), 9999n) == True{} : Bool}
  h

def sod_le(+s: Nat, +off: Nat) -> {Nat.is_le(sodf(s, off), 86399n) == True{} : Bool}:
  lt_to_le(sodf(s, off), 86400n, PNat.mod_lt(loc(s, off), 86399n))

def hH_of(+s: Nat, +off: Nat) -> {Nat.is_lt(Nat.div(sodf(s, off), 3600n), 24n) == True{} : Bool}:
  le_to_lt(Nat.div(sodf(s, off), 3600n), 24n,
    le_rw_r(Nat.div(sodf(s, off), 3600n), Nat.div(86399n, 3600n), 23n, d86399, div_mono(sodf(s, off), 86399n, 3599n, sod_le(s, off))))

def top.ymd(yd: Civil.Ymd, +s: Nat, +ns: Nat, +off: Nat, +e: {Civil.days_to_ymd(daysf(s, off)) == yd : Civil.Ymd},
  +hns: {L.nsec_ok(ns) == True{} : Bool}, +hle: {Nat.is_le(off, 172800n) == True{} : Bool},
  +hmod: {Nat.is_eq(Nat.mod(off, 60n), 0n) == True{} : Bool}, +hge: {Nat.is_le(86400n, Nat.add(s, off)) == True{} : Bool},
  +hyr: {Nat.is_le(L.ymd_year(Civil.days_to_ymd(daysf(s, off))), 9999n) == True{} : Bool})
  -> {Civil.parse_rfc3339(Civil.rfc3339(Civil.Time{s, ns, off})) == Some{Civil.Time{s, ns, off}} : Maybe<&2, Civil.Time>}:
  match yd:
    case Civil.Ymd{+y, +m, +d}:
      +D = daysf(s, off)
      +cb = cb_of(D, y, m, d, e)
      +vd = L.valid_date(y, m, d)
      +hvd = and_l(vd, Nat.is_eq(Civil.ymd_to_days(y, m, d), D), cb)
      +hyd = eq_of_is_eq(Civil.ymd_to_days(y, m, d), D, and_r(vd, Nat.is_eq(Civil.ymd_to_days(y, m, d), D), cb))
      +mm = Bool.and(Nat.is_ge(m, 1n), Nat.is_le(m, 12n))
      +dd = Bool.and(Nat.is_ge(d, 1n), Nat.is_le(d, L.month_len(y, m)))
      +h1 = and_r(Nat.is_ge(y, 1970n), Bool.and(mm, dd), hvd)
      +hy0 = le_trans(1000n, 1970n, y, {==}, ge_le(y, 1970n, and_l(Nat.is_ge(y, 1970n), Bool.and(mm, dd), hvd)))
      +hm12 = and_r(Nat.is_ge(m, 1n), Nat.is_le(m, 12n), and_l(mm, dd, h1))
      +hdm = and_r(Nat.is_ge(d, 1n), Nat.is_le(d, L.month_len(y, m)), and_r(mm, dd, h1))
      +hm = le_to_lt(m, 100n, le_trans(1n+m, 13n, 100n, hm12, {==}))
      +hd = le_to_lt(d, 100n, le_trans(1n+d, 32n, 100n, le_trans(d, L.month_len(y, m), 31n, hdm, ml31(y, m)), {==}))
      fin_z(Nat.is_eq(off, 86400n), Nat.is_gt(off, 86400n), s, ns, off, y, m, d, hns, e, hvd, hyd, hy0, yr_of(D, y, m, d, e, hyr), hm, hd,
        hH_of(s, off), hge, {==}, {==}, hle, hmod)

def top(+s: Nat, +ns: Nat, +off: Nat, +h: {Bool.and(L.valid_time(Civil.Time{s, ns, off}), L.year_ok(Civil.Time{s, ns, off})) == True{} : Bool})
  -> {Civil.parse_rfc3339(Civil.rfc3339(Civil.Time{s, ns, off})) == Some{Civil.Time{s, ns, off}} : Maybe<&2, Civil.Time>}:
  +t = {Civil.Time{s, ns, off} : Civil.Time}
  +hv = and_l(L.valid_time(t), L.year_ok(t), h)
  +hyr = and_r(L.valid_time(t), L.year_ok(t), h)
  +a3 = Bool.and(Nat.is_eq(Nat.mod(off, 60n), 0n), Nat.is_ge(Nat.add(s, off), 86400n))
  +a2 = Bool.and(Nat.is_le(off, 172800n), a3)
  +r1 = and_r(L.nsec_ok(ns), a2, hv)
  +r2 = and_r(Nat.is_le(off, 172800n), a3, r1)
  top.ymd(Civil.days_to_ymd(daysf(s, off)), s, ns, off, {==}, and_l(L.nsec_ok(ns), a2, hv), and_l(Nat.is_le(off, 172800n), a3, r1),
    and_l(Nat.is_eq(Nat.mod(off, 60n), 0n), Nat.is_ge(Nat.add(s, off), 86400n), r2),
    ge_le(Nat.add(s, off), 86400n, and_r(Nat.is_eq(Nat.mod(off, 60n), 0n), Nat.is_ge(Nat.add(s, off), 86400n), r2)), hyr)

def L.civil_rfc3339_parse(t, h):
  match t:
    case Civil.Time{+s, +ns, +off}:
      top(s, ns, off, h)

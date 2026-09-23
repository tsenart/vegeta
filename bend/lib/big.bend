# Big naturals: little-endian base-10000 limbs.
#
# Canonical form: every limb below 10000 and no high zero limb (zero is
# Big{[]}). add, mul, div and mod keep it; cmp accepts any limbs (it
# normalizes first). Every runtime Nat stays far below 2^48.
import Base
import ./dec.bend as Dec

type Big is Data:
  Big{limbs: List<&2, Nat>}

def base() -> Nat:
  10000n

def limbs(+b: Big) -> List<&2, Nat>:
  Big{ls} = b
  ls

# c ? a : b
def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

# ---------------------------------------------------------------------
# Canonical form
# ---------------------------------------------------------------------

# h in front of r, unless both are zero (the verdict is a parameter: a
# proof never has to open r under limbs_val)
def cons_nz.of(drop: Bool, +h: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match drop:
    case True{}:
      Nil{}
    case False{}:
      Con{h, r}

# h in front of a list with no high zero limb, keeping it so
def cons_nz(+h: Nat, +r: List<&2, Nat>) -> List<&2, Nat>:
  cons_nz.of(Bool.and(Nat.is_eq(h, 0n), List.is_empty(&2, Nat, r)), h, r)

# no high zero limb
def trim(ls: List<&2, Nat>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      cons_nz(h, trim(t))

# the limbs of a leftover carry
def carry.rest(fuel: Nat, stop: Bool, +c: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match stop:
        case True{}:
          Nil{}
        case False{}:
          Con{Nat.mod(c, base()), carry.rest(f, Nat.is_eq(Nat.div(c, base()), 0n), Nat.div(c, base()))}

# carry every limb into range (limbs may be any Nat)
def carry.go(ls: List<&2, Nat>, +c: Nat) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      carry.rest(1n+c, Nat.is_eq(c, 0n), c)
    case Con{+h, +t}:
      +s = Nat.add(h, c)
      Con{Nat.mod(s, base()), carry.go(t, Nat.div(s, base()))}

def norm(+ls: List<&2, Nat>) -> List<&2, Nat>:
  trim(carry.go(ls, 0n))

# ---------------------------------------------------------------------
# Conversions
# ---------------------------------------------------------------------

def of.go(+n: Nat) -> Big:
  Big{trim(carry.rest(1n+n, Nat.is_eq(n, 0n), n))}

def of(n: Nat) -> Big:
  of.go(n)

# the Nat a Big denotes (only meaningful below 2^48 at runtime)
def to_nat.go(ls: List<&2, Nat>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{+h, +t}:
      Nat.add(h, Nat.mul(10000n, to_nat.go(t)))

def to_nat(+b: Big) -> Nat:
  to_nat.go(limbs(b))

def is_zero(+b: Big) -> Bool:
  List.is_empty(&2, Nat, limbs(b))

# ---------------------------------------------------------------------
# Addition and subtraction
# ---------------------------------------------------------------------

def add.go(xs: List<&2, Nat>, ys: List<&2, Nat>, +c: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      carry.go(ys, c)
    case Con{+x, +xt}:
      match ys:
        case Nil{}:
          carry.go(Con{x, xt}, c)
        case Con{+y, +yt}:
          +s = Nat.add(Nat.add(x, y), c)
          Con{Nat.mod(s, base()), add.go(xt, yt, Nat.div(s, base()))}

def add(+a: Big, +b: Big) -> Big:
  Big{trim(add.go(limbs(a), limbs(b), 0n))}

# the low limb of ys (0 for none), and the rest
def hd0(ys: List<&2, Nat>) -> Nat:
  match ys:
    case Nil{}:
      0n
    case Con{+y, +t}:
      y

def tl0(ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, +t}:
      t

# xs - ys - borrow w, for xs >= ys + w (canonical limbs, w <= 1)
def sub.go(xs: List<&2, Nat>, +ys: List<&2, Nat>, +w: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +xt}:
      +u = Nat.add(hd0(ys), w)
      +low = Nat.is_lt(x, u)
      Con{Nat.sub(Nat.add(x, pick(Nat, low, base(), 0n)), u), sub.go(xt, tl0(ys), pick(Nat, low, 1n, 0n))}

# a - b, for a >= b
def sub(+a: Big, +b: Big) -> Big:
  Big{trim(sub.go(limbs(a), limbs(b), 0n))}

# ---------------------------------------------------------------------
# Multiplication
# ---------------------------------------------------------------------

# ys * k + c, for k < 2^30 (limb products stay below 2^44)
def mul_small.go(ys: List<&2, Nat>, +k: Nat, +c: Nat) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      carry.rest(1n+c, Nat.is_eq(c, 0n), c)
    case Con{+y, +yt}:
      +s = Nat.add(Nat.mul(y, k), c)
      Con{Nat.mod(s, base()), mul_small.go(yt, k, Nat.div(s, base()))}

# b * k, for k < 2^30
def mul_small(+b: Big, +k: Nat) -> Big:
  Big{trim(mul_small.go(limbs(b), k, 0n))}

def shift1.of(empty: Bool, ls: List<&2, Nat>) -> List<&2, Nat>:
  match empty:
    case True{}:
      Nil{}
    case False{}:
      Con{0n, ls}

# ls * 10000 (the verdict a parameter, as in cons_nz)
def shift1(+ls: List<&2, Nat>) -> List<&2, Nat>:
  shift1.of(List.is_empty(&2, Nat, ls), ls)

def mul.go(xs: List<&2, Nat>, +b: Big) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +xt}:
      add.go(limbs(mul_small(b, x)), shift1(mul.go(xt, b)), 0n)

def mul(+a: Big, +b: Big) -> Big:
  Big{trim(mul.go(limbs(a), b))}

# ---------------------------------------------------------------------
# Comparison
# ---------------------------------------------------------------------

def cmp_then(+hi: Cmp, +lo: Cmp) -> Cmp:
  match hi:
    case LT{}:
      LT{}
    case EQ{}:
      lo
    case GT{}:
      GT{}

# canonical limbs, little-endian
def cmp.go(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Cmp:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          EQ{}
        case Con{+y, +yt}:
          LT{}
    case Con{+x, +xt}:
      match ys:
        case Nil{}:
          GT{}
        case Con{+y, +yt}:
          cmp_then(cmp.go(xt, yt), Nat.cmp(x, y))

def cmp(+a: Big, +b: Big) -> Cmp:
  cmp.go(norm(limbs(a)), norm(limbs(b)))

def le(+a: Big, +b: Big) -> Bool:
  Bool.not(Cmp.is_gt(cmp.go(limbs(a), limbs(b))))

# ---------------------------------------------------------------------
# Division
# ---------------------------------------------------------------------

type QR is Data:
  QR{q: List<&2, Nat>, r: Big}

def QR.q(+x: QR) -> List<&2, Nat>:
  QR{q, r} = x
  q

def QR.r(+x: QR) -> Big:
  QR{q, r} = x
  r

# the largest d in lo .. hi with b * d <= r, by bisection, given
# b * lo <= r < b * (1 + hi); stop says lo >= hi. It first opens bl, b's
# limbs, so a proof sees it stuck on them, not unfolded
def qsearch(bl: List<&2, Nat>, fuel: Nat, stop: Bool, +lo: Nat, +hi: Nat, +b: Big, +r: Big) -> Nat:
  match bl:
    case Nil{}:
      lo
    case Con{+g, +more}:
      match fuel:
        case 0n:
          lo
        case 1n+f:
          match stop:
            case True{}:
              lo
            case False{}:
              +mid = Nat.div(Nat.add(Nat.add(lo, hi), 1n), 2n)
              +ok = le(mul_small(b, mid), r)
              +lo2 = pick(Nat, ok, mid, lo)
              +hi2 = pick(Nat, ok, hi, Nat.sub(mid, 1n))
              qsearch(Con{g, more}, f, Nat.is_ge(lo2, hi2), lo2, hi2, b, r)

# bring down limb h onto the remainder, find the quotient digit
def div.step(+h: Nat, +b: Big, +acc: QR) -> QR:
  +r2 = {Big{trim(Con{h, limbs(QR.r(acc))})} : Big}
  +d = qsearch(limbs(b), 10000n, False{}, 0n, 9999n, b, r2)
  QR{Con{d, QR.q(acc)}, sub(r2, mul_small(b, d))}

# long division, the high limbs first (they are the recursion)
def div.go(ls: List<&2, Nat>, +b: Big) -> QR:
  match ls:
    case Nil{}:
      QR{Nil{}, Big{Nil{}}}
    case Con{+h, +t}:
      div.step(h, b, div.go(t, b))

def divmod(+a: Big, +b: Big) -> QR:
  +x = div.go(limbs(a), b)
  QR{trim(QR.q(x)), QR.r(x)}

def div(+a: Big, +b: Big) -> Big:
  Big{QR.q(divmod(a, b))}

def mod(+a: Big, +b: Big) -> Big:
  QR.r(divmod(a, b))

# b / k and b mod k for 0 < k < 2^30 (r * 10000 + limb stays below 2^44)
def div_small.go(hs: List<&2, Nat>, +k: Nat, +r: Nat, +q: List<&2, Nat>) -> QR:
  match hs:
    case Nil{}:
      QR{trim(q), of(r)}
    case Con{+h, +t}:
      +x = Nat.add(Nat.mul(r, 10000n), h)
      div_small.go(t, k, Nat.mod(x, k), Con{Nat.div(x, k), q})

def div_small(+b: Big, +k: Nat) -> QR:
  div_small.go(List.reverse(&2, Nat, limbs(b)), k, 0n, Nil{})

# ---------------------------------------------------------------------
# Decimal text
# ---------------------------------------------------------------------

# the four decimal digits of a limb h < 10000, leading zeros kept
def pad4(+h: Nat) -> String:
  +h1 = Nat.div(h, 10n)
  +h2 = Nat.div(h1, 10n)
  SCon{Dec.digit_chr(Nat.div(h2, 10n)), SCon{Dec.digit_chr(Nat.mod(h2, 10n)),
    SCon{Dec.digit_chr(Nat.mod(h1, 10n)), SCon{Dec.digit_chr(Nat.mod(h, 10n)), SNil{}}}}}

# the text of the limbs so far: the top limb unpadded (top says h is it)
def show.cons(top: Bool, +h: Nat, rest: String) -> String:
  match top:
    case True{}:
      Dec.show(h)
    case False{}:
      rest ++ pad4(h)

# a list with no high zero limb
def show.go(ls: List<&2, Nat>) -> String:
  match ls:
    case Nil{}:
      "0"
    case Con{+h, +t}:
      show.cons(List.is_empty(&2, Nat, t), h, show.go(t))

def show(+b: Big) -> String:
  show.go(limbs(b))

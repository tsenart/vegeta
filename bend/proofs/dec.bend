# Proofs of the decimal laws (dec_*).
import Base
import ../LAWS.bend as L
import ../lib/dec.bend as Dec
import ./nat.bend as PNat

def L.dec_pad(w, n):
  {==}

def is_digit_same(c: Char) -> {Dec.is_digit(c) == L.is_digit(c) : Bool}:
  match c:
    case Chr{k}:
      {==}

def all_go_same(s: String) -> {Dec.all_digits.go(s) == L.all_digits.go(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %all_go_same(rest) : {Bool.and(Dec.is_digit(c), Dec.all_digits.go(rest)) == Bool.and(L.is_digit(c), _) : Bool}
      %is_digit_same(c) : {Bool.and(Dec.is_digit(c), Dec.all_digits.go(rest)) == Bool.and(_, Dec.all_digits.go(rest)) : Bool}
      {==}

# LAWS' digit reading and lib's agree
def all_same(s: String) -> {L.all_digits(s) == Dec.all_digits(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %all_go_same(rest) : {Bool.and(L.is_digit(c), _) == Bool.and(Dec.is_digit(c), Dec.all_digits.go(rest)) : Bool}
      %is_digit_same(c) : {Bool.and(_, Dec.all_digits.go(rest)) == Bool.and(Dec.is_digit(c), Dec.all_digits.go(rest)) : Bool}
      {==}

def digit_same(c: Char) -> {L.digit(c) == Dec.digit(c) : Nat}:
  match c:
    case Chr{k}:
      {==}

def value_go_same(s: String, +acc: Nat) -> {L.digits_value.go(s, acc) == Dec.value.go(s, acc) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %digit_same(c) : {L.digits_value.go(rest, Nat.add(Nat.mul(acc, 10n), L.digit(c))) == Dec.value.go(rest, Nat.add(Nat.mul(acc, 10n), _)) : Nat}
      value_go_same(rest, Nat.add(Nat.mul(acc, 10n), L.digit(c)))

def L.dec_read_accepts(s, h):
  %all_same(s) : {Dec.read.of(_, s) == Some{L.digits_value(s)} : Maybe<&2, Nat>}
  %Equal.sym(Bool, L.all_digits(s), True{}, h) : {Dec.read.of(_, s) == Some{L.digits_value(s)} : Maybe<&2, Nat>}
  %value_go_same(s, 0n) : {Some{_} == Some{L.digits_value(s)} : Maybe<&2, Nat>}
  {==}

def L.dec_read_rejects(s, h):
  %all_same(s) : {Dec.read.of(_, s) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Bool, L.all_digits(s), False{}, h) : {Dec.read.of(_, s) == None{} : Maybe<&2, Nat>}
  {==}

# ---------------------------------------------------------------------
# show: digits_value(show(n)) == n and show(n) is canonical
# ---------------------------------------------------------------------

# canonical text other than "0": digits, the first one not 0
def canon_ok(+s: String) -> Bool:
  Bool.and(L.all_digits(s), Bool.not(String.starts_with(s, "0")))

def digit_of_chr(+d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {L.digit(Dec.digit_chr(d)) == d : Nat}:
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
                                          Empty.absurd({L.digit(Dec.digit_chr(10n+j)) == 10n+j : Nat}, PNat.lt_zero(j, h))

def digit_chr_is_digit(+d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {L.is_digit(Dec.digit_chr(d)) == True{} : Bool}:
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
                                          Empty.absurd({L.is_digit(Dec.digit_chr(10n+j)) == True{} : Bool}, PNat.lt_zero(j, h))

# a lone digit other than 0 is canon_ok
def single_ok(+d: Nat, -m: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}, en: {d == 1n+m : Nat}) -> {canon_ok(SCon{Dec.digit_chr(d), SNil{}}) == True{} : Bool}:
  match d:
    case 0n:
      Empty.absurd({canon_ok(SCon{Dec.digit_chr(0n), SNil{}}) == True{} : Bool}, PNat.no_zero(m, Equal.sym(Nat, 0n, 1n+m, en)))
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
                                          Empty.absurd({canon_ok(SCon{Dec.digit_chr(10n+j), SNil{}}) == True{} : Bool}, PNat.lt_zero(j, h))


def and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(h))

def and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, PNat.false_ne_true(h))

def or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# show.go only prepends to its accumulator
def go_app(f: Nat, b: Bool, +n: Nat, acc: String, +t: String)
  -> {String.append(Dec.show.go(f, b, n, acc), t) == Dec.show.go(f, b, n, String.append(acc, t)) : String}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match b:
        case True{}:
          {==}
        case False{}:
          go_app(g, Nat.is_lt(n, 10n), Nat.div(n, 10n), SCon{Dec.digit_chr(Nat.mod(n, 10n)), acc}, t)

def val_app(s: String, +t: String, +x: Nat)
  -> {L.digits_value.go(t, L.digits_value.go(s, x)) == L.digits_value.go(String.append(s, t), x) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      val_app(rest, t, Nat.add(Nat.mul(x, 10n), L.digit(c)))

# (10p + r) + k == p + (9p + r + k)
def fuel_arith(+p: Nat, +r: Nat, +k: Nat)
  -> {Nat.add(Nat.add(Nat.mul(p, 10n), r), k) == Nat.add(p, Nat.add(Nat.add(Nat.mul(9n, p), r), k)) : Nat}:
  %Equal.sym(Nat, Nat.mul(p, 10n), Nat.mul(10n, p), PNat.mul_comm(p, 10n))
    : {Nat.add(Nat.add(_, r), k) == Nat.add(p, Nat.add(Nat.add(Nat.mul(9n, p), r), k)) : Nat}
  %PNat.add_assoc(p, Nat.mul(9n, p), r)
    : {Nat.add(_, k) == Nat.add(p, Nat.add(Nat.add(Nat.mul(9n, p), r), k)) : Nat}
  %PNat.add_assoc(p, Nat.add(Nat.mul(9n, p), r), k)
    : {_ == Nat.add(p, Nat.add(Nat.add(Nat.mul(9n, p), r), k)) : Nat}
  {==}

# the fuel left after a digit of 10(1+p) + r still covers 1+p
def fuel_next(+p: Nat, +r: Nat, +k: Nat, -g: Nat,
  e: {9n+Nat.add(Nat.add(Nat.mul(p, 10n), r), k) == g : Nat})
  -> {Nat.add(1n+p, 8n+Nat.add(Nat.add(Nat.mul(9n, p), r), k)) == g : Nat}:
  %Equal.sym(Nat, Nat.add(p, 8n+Nat.add(Nat.add(Nat.mul(9n, p), r), k)), 8n+Nat.add(p, Nat.add(Nat.add(Nat.mul(9n, p), r), k)),
      PNat.add_swap(p, 8n, Nat.add(Nat.add(Nat.mul(9n, p), r), k)))
    : {1n+_ == g : Nat}
  %fuel_arith(p, r, k) : {9n+_ == g : Nat}
  e

def tr_add(-n: Nat, -m: Nat, -k: Nat, -f: Nat, en: {n == m : Nat}, e: {Nat.add(n, k) == f : Nat})
  -> {Nat.add(m, k) == f : Nat}:
  %en : {Nat.add(_, k) == f : Nat}
  e

def tr_lt(-n: Nat, -m: Nat, en: {n == m : Nat}) -> {Nat.is_lt(n, 10n) == Nat.is_lt(m, 10n) : Bool}:
  %en : {Nat.is_lt(n, 10n) == Nat.is_lt(_, 10n) : Bool}
  {==}

# one step of show.go on 10q + r with fuel 1 + g, the verdict c split;
# ih is the induction hypothesis on the fuel g
def val_step(c: Bool, q: Nat, +g: Nat, +r: Nat, +k: Nat,
  ef: {Nat.add(Nat.add(Nat.mul(q, 10n), r), k) == 1n+g : Nat},
  ec: {c == Nat.is_lt(Nat.add(Nat.mul(q, 10n), r), 10n) : Bool},
  hr: {Nat.is_lt(r, 10n) == True{} : Bool},
  ih: @k2:Nat -> {Nat.add(q, k2) == g : Nat} -> {L.digits_value.go(Dec.show.go(1n+g, False{}, q, SNil{}), 0n) == q : Nat})
  -> {L.digits_value.go(Dec.show.go(1n+g, c, q, SCon{Dec.digit_chr(r), SNil{}}), 0n) == Nat.add(Nat.mul(q, 10n), r) : Nat}:
  match c:
    case True{}:
      match q:
        case 0n:
          digit_of_chr(r, hr)
        case 1n+p:
          Empty.absurd({L.digits_value.go(Dec.show.go(1n+g, True{}, 1n+p, SCon{Dec.digit_chr(r), SNil{}}), 0n) == Nat.add(Nat.mul(1n+p, 10n), r) : Nat},
            PNat.lt_zero(Nat.add(Nat.mul(p, 10n), r), Equal.sym(Bool, True{}, Nat.is_lt(Nat.add(Nat.mul(1n+p, 10n), r), 10n), ec)))
    case False{}:
      match q:
        case 0n:
          Empty.absurd({L.digits_value.go(Dec.show.go(1n+g, False{}, 0n, SCon{Dec.digit_chr(r), SNil{}}), 0n) == r : Nat},
            PNat.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(r, 10n), True{}, ec, hr)))
        case 1n++p:
          %go_app(1n+g, False{}, 1n+p, SNil{}, SCon{Dec.digit_chr(r), SNil{}})
            : {L.digits_value.go(_, 0n) == Nat.add(Nat.mul(1n+p, 10n), r) : Nat}
          %val_app(Dec.show.go(1n+g, False{}, 1n+p, SNil{}), SCon{Dec.digit_chr(r), SNil{}}, 0n)
            : {_ == Nat.add(Nat.mul(1n+p, 10n), r) : Nat}
          %Equal.sym(Nat, L.digits_value.go(Dec.show.go(1n+g, False{}, 1n+p, SNil{}), 0n), 1n+p,
              ih(8n+Nat.add(Nat.add(Nat.mul(9n, p), r), k),
                fuel_next(p, r, k, g, PNat.succ_inj(9n+Nat.add(Nat.add(Nat.mul(p, 10n), r), k), g, ef))))
            : {Nat.add(Nat.mul(_, 10n), L.digit(Dec.digit_chr(r))) == Nat.add(Nat.mul(1n+p, 10n), r) : Nat}
          %Equal.sym(Nat, L.digit(Dec.digit_chr(r)), r, digit_of_chr(r, hr))
            : {Nat.add(Nat.mul(1n+p, 10n), _) == Nat.add(Nat.mul(1n+p, 10n), r) : Nat}
          {==}

# with fuel 1 + f and f >= n, show.go's digits of n denote n
def val_main(f: Nat, +n: Nat, +k: Nat, e: {Nat.add(n, k) == f : Nat})
  -> {L.digits_value.go(Dec.show.go(1n+f, False{}, n, SNil{}), 0n) == n : Nat}:
  match f:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+m:
          Empty.absurd({L.digits_value.go(Dec.show.go(1n, False{}, 1n+m, SNil{}), 0n) == 1n+m : Nat}, PNat.no_zero(Nat.add(m, k), e))
    case 1n++g:
      %Equal.sym(Nat, n, Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), PNat.div_mod_eq(n, 9n))
        : {L.digits_value.go(Dec.show.go(2n+g, False{}, n, SNil{}), 0n) == _ : Nat}
      val_step(Nat.is_lt(n, 10n), Nat.div(n, 10n), g, Nat.mod(n, 10n), k,
        tr_add(n, Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), k, 1n+g, PNat.div_mod_eq(n, 9n), e),
        tr_lt(n, Nat.add(Nat.mul(Nat.div(n, 10n), 10n), Nat.mod(n, 10n)), PNat.div_mod_eq(n, 9n)),
        PNat.mod_lt(n, 9n),
        k2 => e2 => val_main(g, Nat.div(n, 10n), k2, e2))

def L.dec_show_value(n):
  val_main(n, n, 0n, Equal.sym(Nat, n, Nat.add(n, 0n), PNat.add_zero(n)))

def ad_go_app(s: String, +c: Char, +h1: {L.all_digits.go(s) == True{} : Bool}, h2: {L.is_digit(c) == True{} : Bool})
  -> {L.all_digits.go(String.append(s, SCon{c, SNil{}})) == True{} : Bool}:
  match s:
    case SNil{}:
      %Equal.sym(Bool, L.is_digit(c), True{}, h2) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case SCon{+x, +rest}:
      %Equal.sym(Bool, L.is_digit(x), True{}, and_l(L.is_digit(x), L.all_digits.go(rest), h1))
        : {Bool.and(_, L.all_digits.go(String.append(rest, SCon{c, SNil{}}))) == True{} : Bool}
      ad_go_app(rest, c, and_r(L.is_digit(x), L.all_digits.go(rest), h1), h2)

# a text not starting with 0 still does not once extended
def sw_if(b: Bool, s: String, -t: String, h: {Bool.not(String.starts_with.if(s, SNil{}, b)) == True{} : Bool})
  -> {Bool.not(String.starts_with.if(String.append(s, t), SNil{}, b)) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      match s:
        case SNil{}:
          Empty.absurd({Bool.not(String.starts_with.if(t, SNil{}, True{})) == True{} : Bool}, PNat.false_ne_true(h))
        case SCon{x, rest}:
          Empty.absurd({Bool.not(String.starts_with.if(SCon{x, String.append(rest, t)}, SNil{}, True{})) == True{} : Bool}, PNat.false_ne_true(h))

def ok_app(s: String, +c: Char, +h: {canon_ok(s) == True{} : Bool}, hc: {L.is_digit(c) == True{} : Bool})
  -> {canon_ok(String.append(s, SCon{c, SNil{}})) == True{} : Bool}:
  match s:
    case SNil{}:
      Empty.absurd({canon_ok(SCon{c, SNil{}}) == True{} : Bool}, PNat.false_ne_true(h))
    case SCon{+x, +rest}:
      +a = L.all_digits(SCon{x, rest})
      +b = Bool.not(String.starts_with(SCon{x, rest}, "0"))
      %Equal.sym(Bool, L.all_digits.go(SCon{x, String.append(rest, SCon{c, SNil{}})}), True{},
          ad_go_app(SCon{x, rest}, c, and_l(a, b, h), hc))
        : {Bool.and(_, Bool.not(String.starts_with(SCon{x, String.append(rest, SCon{c, SNil{}})}, "0"))) == True{} : Bool}
      sw_if(Char.is_eq(x, '0'), rest, SCon{c, SNil{}}, and_r(a, b, h))

# one step of show.go on 10q + r = 1 + m with fuel 1 + g
def canon_step(c: Bool, q: Nat, +g: Nat, +r: Nat, -m: Nat, +k: Nat,
  ef: {Nat.add(Nat.add(Nat.mul(q, 10n), r), k) == 1n+g : Nat},
  en: {Nat.add(Nat.mul(q, 10n), r) == 1n+m : Nat},
  ec: {c == Nat.is_lt(Nat.add(Nat.mul(q, 10n), r), 10n) : Bool},
  hr: {Nat.is_lt(r, 10n) == True{} : Bool},
  ih: @m2:Nat -> @k2:Nat -> {Nat.add(1n+m2, k2) == g : Nat} -> {canon_ok(Dec.show.go(1n+g, False{}, 1n+m2, SNil{})) == True{} : Bool})
  -> {canon_ok(Dec.show.go(1n+g, c, q, SCon{Dec.digit_chr(r), SNil{}})) == True{} : Bool}:
  match c:
    case True{}:
      match q:
        case 0n:
          single_ok(r, m, hr, en)
        case 1n+p:
          Empty.absurd({canon_ok(Dec.show.go(1n+g, True{}, 1n+p, SCon{Dec.digit_chr(r), SNil{}})) == True{} : Bool},
            PNat.lt_zero(Nat.add(Nat.mul(p, 10n), r), Equal.sym(Bool, True{}, Nat.is_lt(Nat.add(Nat.mul(1n+p, 10n), r), 10n), ec)))
    case False{}:
      match q:
        case 0n:
          Empty.absurd({canon_ok(Dec.show.go(1n+g, False{}, 0n, SCon{Dec.digit_chr(r), SNil{}})) == True{} : Bool},
            PNat.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(r, 10n), True{}, ec, hr)))
        case 1n++p:
          %go_app(1n+g, False{}, 1n+p, SNil{}, SCon{Dec.digit_chr(r), SNil{}}) : {canon_ok(_) == True{} : Bool}
          ok_app(Dec.show.go(1n+g, False{}, 1n+p, SNil{}), Dec.digit_chr(r),
            ih(p, 8n+Nat.add(Nat.add(Nat.mul(9n, p), r), k),
              fuel_next(p, r, k, g, PNat.succ_inj(9n+Nat.add(Nat.add(Nat.mul(p, 10n), r), k), g, ef))),
            digit_chr_is_digit(r, hr))

# with fuel 1 + f and f >= 1 + m, show.go writes 1 + m canonically
def canon_main(f: Nat, +m: Nat, +k: Nat, e: {Nat.add(1n+m, k) == f : Nat})
  -> {canon_ok(Dec.show.go(1n+f, False{}, 1n+m, SNil{})) == True{} : Bool}:
  match f:
    case 0n:
      Empty.absurd({canon_ok(Dec.show.go(1n, False{}, 1n+m, SNil{})) == True{} : Bool}, PNat.no_zero(Nat.add(m, k), e))
    case 1n++g:
      canon_step(Nat.is_lt(1n+m, 10n), Nat.div(1n+m, 10n), g, Nat.mod(1n+m, 10n), m, k,
        tr_add(1n+m, Nat.add(Nat.mul(Nat.div(1n+m, 10n), 10n), Nat.mod(1n+m, 10n)), k, 1n+g, PNat.div_mod_eq(1n+m, 9n), e),
        Equal.sym(Nat, 1n+m, Nat.add(Nat.mul(Nat.div(1n+m, 10n), 10n), Nat.mod(1n+m, 10n)), PNat.div_mod_eq(1n+m, 9n)),
        tr_lt(1n+m, Nat.add(Nat.mul(Nat.div(1n+m, 10n), 10n), Nat.mod(1n+m, 10n)), PNat.div_mod_eq(1n+m, 9n)),
        PNat.mod_lt(1n+m, 9n),
        m2 => k2 => e2 => canon_main(g, m2, k2, e2))

def L.dec_show_canonical(n):
  match n:
    case 0n:
      {==}
    case 1n++m:
      +a = L.all_digits(Dec.show(1n+m))
      +b = Bool.not(String.starts_with(Dec.show(1n+m), "0"))
      +h = canon_main(1n+m, m, 0n, Equal.sym(Nat, 1n+m, Nat.add(1n+m, 0n), PNat.add_zero(1n+m)))
      %Equal.sym(Bool, a, True{}, and_l(a, b, h))
        : {Bool.and(_, Bool.or(String.eq(Dec.show(1n+m), "0"), b)) == True{} : Bool}
      %Equal.sym(Bool, b, True{}, and_r(a, b, h))
        : {Bool.and(True{}, Bool.or(String.eq(Dec.show(1n+m), "0"), _)) == True{} : Bool}
      or_true(String.eq(Dec.show(1n+m), "0"))

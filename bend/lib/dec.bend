# Decimal codec for Nat.
#
# Written for proof and for the strict compiled lane: recursion runs on a
# fuel argument, and a loop that is done stops through a Bool parameter
# it matches itself (a `pick` would evaluate both branches).
import Base

# the digit character for d < 10 (a table: its proofs are case analysis)
def digit_chr(d: Nat) -> Char:
  match d:
    case 0n:
      '0'
    case 1n+a:
      match a:
        case 0n:
          '1'
        case 1n+b:
          match b:
            case 0n:
              '2'
            case 1n+c:
              match c:
                case 0n:
                  '3'
                case 1n+e:
                  match e:
                    case 0n:
                      '4'
                    case 1n+f:
                      match f:
                        case 0n:
                          '5'
                        case 1n+g:
                          match g:
                            case 0n:
                              '6'
                            case 1n+h:
                              match h:
                                case 0n:
                                  '7'
                                case 1n+i:
                                  match i:
                                    case 0n:
                                      '8'
                                    case 1n+j:
                                      '9'

# the digits of n (least significant first), pushed onto acc; stop ends
# the loop, fuel bounds it (n's digits never outnumber n + 1)
def show.go(fuel: Nat, stop: Bool, +n: Nat, acc: String) -> String:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match stop:
        case True{}:
          acc
        case False{}:
          show.go(f, Nat.is_lt(n, 10n), Nat.div(n, 10n), SCon{digit_chr(Nat.mod(n, 10n)), acc})

def show(+n: Nat) -> String:
  show.go(1n+n, False{}, n, "")

def code(c: Char) -> U32:
  Chr{k} = c
  k

def is_digit(c: Char) -> Bool:
  +k = code(c)
  Bool.and(U32.is_ge(k, 48), U32.is_le(k, 57))

def digit(c: Char) -> Nat:
  U32.to_nat((code(c) - 48 : U32))

def all_digits.go(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, rest}:
      Bool.and(is_digit(c), all_digits.go(rest))

# a non-empty run of ASCII digits
def all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, rest}:
      Bool.and(is_digit(c), all_digits.go(rest))

def value.go(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{c, rest}:
      value.go(rest, Nat.add(Nat.mul(acc, 10n), digit(c)))

def value(s: String) -> Nat:
  value.go(s, 0n)

def read.of(ok: Bool, +s: String) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{value(s)}
    case False{}:
      None{}

def read(+s: String) -> Maybe<&2, Nat>:
  read.of(all_digits(s), s)

def pad(w: Nat, +n: Nat) -> String:
  String.repeat("0", Nat.sub(w, String.length(show(n)))) ++ show(n)

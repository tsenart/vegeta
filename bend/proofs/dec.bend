# Proofs of the decimal laws (dec_*).
import Base
import ../LAWS.bend as L
import ../lib/dec.bend as Dec

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

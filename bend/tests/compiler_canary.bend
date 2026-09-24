# Compiler canary (github.com/bendlang/bend/issues/1026; still wrong in
# 2.0.27). Bend 2.0.25's native compiler gets
# Bool.or(x, pick(Bool, <computed condition>, a, b)) wrong: f and g below
# must print True (the checker and bend's default lane do), but compiled
# they print False. The expected lines pin today's wrong output: when this
# test fails, the compiler changed; check it and update this file and the
# plan's note. Until then, lib/ code avoids this shape (bind the pick to
# a def of its own) and compiled end-to-end tests stay the last word.
import Base

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def lim(+m: Maybe<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, m, 0n)

# n bound once, used in the condition and in a branch
def f(+x: Bool, +m: Maybe<&2, Nat>) -> Bool:
  +n = lim(m)
  Bool.or(x, pick(Bool, Nat.is_lt(0n, n), False{}, Nat.is_eq(n, 0n)))

# same, n not reused
def g(+x: Bool, +m: Maybe<&2, Nat>) -> Bool:
  Bool.or(x, pick(Bool, Nat.is_lt(0n, lim(m)), False{}, Nat.is_eq(lim(m), 0n)))

# same, without Bool.or
def h(+m: Maybe<&2, Nat>) -> Bool:
  +n = lim(m)
  pick(Bool, Nat.is_lt(0n, n), False{}, Nat.is_eq(n, 0n))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("f " ++ Bool.show(f(False{}, Some{0n})) ++ " g " ++ Bool.show(g(False{}, Some{0n})) ++ " h " ++ Bool.show(h(Some{0n})))

#|f False g False h True

import Base
import ../.build/laws_helpers.bend as L
import ../lib/engine.bend as Eng

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(L.days_of(1970n, 1n, 1n)) ++ " " ++ Nat.show(L.days_of(2000n, 3n, 1n)) ++ " " ++ Nat.show(L.days_of(2026n, 9n, 23n)))
    IO.print(Bool.show(L.leap(1900n)) ++ " " ++ Bool.show(L.leap(2000n)) ++ " " ++ Bool.show(L.leap(2024n)))
    IO.print(Nat.show(L.rank(50n, 1n)) ++ " " ++ Nat.show(L.rank(50n, 10n)) ++ " " ++ Nat.show(L.rank(99n, 10n)) ++ " " ++ Nat.show(L.rank(90n, 100n)))
    IO.print(Nat.show(L.bucket_of([0n, 1000000n, 10000000n], 5n)) ++ " " ++ Nat.show(L.bucket_of([0n, 1000000n, 10000000n], 1000000n)) ++ " " ++ Nat.show(L.bucket_of([0n, 1000000n, 10000000n], 99999999n)) ++ " " ++ Nat.show(L.bucket_of([5n, 10n], 1n)))
    IO.print(Nat.show(L.round_unit(999n)) ++ " " ++ Nat.show(L.round_unit(1500000n)) ++ " " ++ Nat.show(L.round_unit(Nat.mul(61n, 1000000000n))))
    IO.print(Bool.show(L.needs_quotes("")) ++ " " ++ Bool.show(L.needs_quotes(" x")) ++ " " ++ Bool.show(L.needs_quotes("a,b")) ++ " " ++ Bool.show(L.needs_quotes("ab")))
    IO.print(L.canon("content-type") ++ " " ++ L.canon("X-VEGETA-seq") ++ " " ++ L.canon("bad key"))
    IO.print(L.trim_ows("  a b\t") ++ "|" ++ L.hex(255n) ++ "|" ++ L.hex(0n) ++ "|" ++ L.hex(4096n))
    IO.print(Bool.show(L.starts_method("GET http://x")) ++ " " ++ Bool.show(L.starts_method("Get http://x")) ++ " " ++ Bool.show(L.starts_method("GET")))
    IO.print(L.redirect_method(302n, "POST") ++ " " ++ L.redirect_method(302n, "PUT") ++ " " ++ L.redirect_method(303n, "HEAD") ++ " " ++ L.redirect_method(303n, "PUT") ++ " " ++ L.redirect_method(307n, "POST"))
    IO.print(L.op("GET") ++ " " ++ L.op("POST"))
    IO.print(Nat.show(L.utf8_len("abc")) ++ " " ++ Nat.show(L.utf8_len(L.micro())) ++ " " ++ Nat.show(L.runes(L.micro() ++ "s")))
    IO.print(Nat.show(L.scheduled(Eng.ECfg{50n, 1000000000n, 2000000000n, 10n, 100n, 1n})))

#|0 11017 20719
#|False True True
#|0 4 9 89
#|0 1 2 1
#|1 1000 1000000000
#|False True True False
#|Content-Type X-Vegeta-Seq bad key
#|a b|ff|0|1000
#|True False False
#|GET PUT HEAD GET POST
#|Get Post
#|1 2 2
#|100

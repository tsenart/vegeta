# Vegeta in Bend -- the proofs. Each law L.x of LAWS.bend is proven by a
# def named L.x in one of proofs/*.bend, one file per module. Proofs stay
# symbolic: a step never computes with a closed Nat above ~10^5 (theory
# Nats are unary in the checker).
import Base
import ./LAWS.bend as L
import ./proofs/nat.bend as PNat
import ./proofs/dec.bend as PDec

# Vegeta in Bend -- the proofs. Each law L.x of LAWS.bend is proven by a
# def named L.x in one of proofs/*.bend, one file per module. Proofs stay
# symbolic: a step never computes with a closed Nat above ~10^5 (theory
# Nats are unary in the checker).
import Base
import ./LAWS.bend as L
import ./proofs/nat.bend as PNat
import ./proofs/dec.bend as PDec
import ./proofs/codec.bend as PCodec
import ./proofs/engine.bend as PEng
import ./proofs/http.bend as PHttp
import ./proofs/big.bend as PBig
import ./proofs/flags.bend as PFlags
import ./proofs/results.bend as PRes
import ./proofs/dur.bend as PDur
import ./proofs/civil.bend as PCivil
import ./proofs/metrics.bend as PMet
import ./proofs/f64.bend as PF64
import ./proofs/conn.bend as PConn
import ./proofs/nums.bend as PNums

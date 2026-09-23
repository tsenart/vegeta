# Wall-clock time: UTC seconds, nanoseconds, and the local offset in
# seconds plus 86400 (so it is never negative). STUB.
import Base

type Time is Data:
  Time{sec: Nat, nsec: Nat, off: Nat}

type Ymd is Data:
  Ymd{y: Nat, m: Nat, d: Nat}

def ymd_to_days(y: Nat, m: Nat, d: Nat) -> Nat:
  0n

def days_to_ymd(d: Nat) -> Ymd:
  Ymd{1970n, 1n, 1n}

def rfc3339(+t: Time) -> String:
  ""

def parse_rfc3339(s: String) -> Maybe<&2, Time>:
  None{}

def unix_nanos(+t: Time) -> String:
  "0"

def cmp(+a: Time, +b: Time) -> Cmp:
  EQ{}

def add_ns(+t: Time, n: Nat) -> Time:
  t

def sub_ns(+a: Time, +b: Time) -> Nat:
  0n

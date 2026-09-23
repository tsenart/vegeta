# The constant rate: freq hits per `per` ns; freq = 0 or per = 0 is unbounded. STUB.
import Base

type Rate is Data:
  Rate{freq: Nat, per: Nat}

def parse_rate(s: String) -> Result<&2, &2, String, Rate>:
  Fail{"stub"}

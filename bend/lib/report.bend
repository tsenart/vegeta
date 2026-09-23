# The text, JSON and histogram reports. STUB.
import Base
import ./metrics.bend as Met

def text(+s: Met.Summary) -> String:
  ""

# the local UTC offsets (plus 86400) of the earliest, latest and end times
type Zones is Data:
  Zones{earliest: Nat, latest: Nat, end: Nat}

def json(+s: Met.Summary, +z: Zones) -> String:
  ""

def hist(+s: Met.Summary) -> String:
  ""

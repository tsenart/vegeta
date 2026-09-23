# HTTP headers, in the order they were written.
import Base

type Header is Data:
  Header{key: String, vals: List<&2, String>}

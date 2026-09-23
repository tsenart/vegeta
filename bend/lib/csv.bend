# CSV as Go's encoding/csv writes and reads it (TrimLeadingSpace on).
#
# The writer follows the csv_* laws' helpers. The reader works one field
# at a time (read_field), each a loop over bytes whose fuel is the input
# itself (one byte of fuel per step, so no length is ever computed), and
# which stops through the cut it matches.
import Base

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def in_range32(+k: U32, +lo: U32, +hi: U32) -> Bool:
  Bool.and(U32.is_ge(k, lo), U32.is_le(k, hi))

def has_char(s: String, +k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      Bool.or(U32.is_eq(code(c), k), has_char(rest, k))

# the byte at index i, or 0 past the end
def byte_at(s: String, i: Nat) -> U32:
  match s:
    case SNil{}:
      0
    case SCon{+c, +rest}:
      match i:
        case 0n:
          code(c)
        case 1n+j:
          byte_at(rest, j)

def is_space(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), Bool.and(U32.is_ge(k, 9), U32.is_le(k, 13)))

def first_is(+s: String, k: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +rest}:
      U32.is_eq(code(c), k)

# ---------------------------------------------------------------------
# Writing
# ---------------------------------------------------------------------

# s starts with a rune Go's unicode.IsSpace accepts (as UTF-8 bytes)
def first_space(+s: String) -> Bool:
  +b0 = byte_at(s, 0n)
  +b1 = byte_at(s, 1n)
  +b2 = byte_at(s, 2n)
  Bool.and(Bool.not(String.is_empty(s)),
  Bool.or(Bool.or(is_space(b0), Bool.and(U32.is_eq(b0, 194), Bool.or(U32.is_eq(b1, 133), U32.is_eq(b1, 160)))),
  Bool.or(Bool.and(U32.is_eq(b0, 225), Bool.and(U32.is_eq(b1, 154), U32.is_eq(b2, 128))),
  Bool.or(Bool.and(U32.is_eq(b0, 226), Bool.or(Bool.and(U32.is_eq(b1, 128), Bool.or(in_range32(b2, 128, 138), Bool.or(in_range32(b2, 168, 169), U32.is_eq(b2, 175)))),
                                               Bool.and(U32.is_eq(b1, 129), U32.is_eq(b2, 159)))),
    Bool.and(U32.is_eq(b0, 227), Bool.and(U32.is_eq(b1, 128), U32.is_eq(b2, 128)))))))

# Go's fieldNeedsQuotes (the delimiter is a comma)
def needs_quotes(+s: String) -> Bool:
  pick(Bool, String.is_empty(s), False{},
    Bool.or(String.eq(s, "\\."), Bool.or(first_space(s),
      Bool.or(Bool.or(has_char(s, 44), has_char(s, 34)), Bool.or(has_char(s, 13), has_char(s, 10))))))

def double_quotes(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +rest}:
      pick(String, U32.is_eq(code(c), 34), "\"\"", SCon{c, SNil{}}) ++ double_quotes(rest)

def field.of(+s: String) -> String:
  pick(String, needs_quotes(s), "\"" ++ double_quotes(s) ++ "\"", s)

def field(s: String) -> String:
  field.of(s)

def join_fields(fs: List<&2, String>) -> String:
  match fs:
    case Nil{}:
      ""
    case Con{+f, +rest}:
      match rest:
        case Nil{}:
          field(f)
        case Con{+g, +more}:
          field(f) ++ "," ++ join_fields(Con{g, more})

def row(fs: List<&2, String>) -> String:
  join_fields(fs) ++ "\n"

# ---------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------

# how a field read ends: not yet, at a comma, at the end of the record,
# or at a syntax error (Go's ErrBareQuote, ErrQuote)
type Cut is Data:
  CsvMore{}
  CsvSep{}
  CsvEnd{}
  CsvBad{}

# a field being read: its bytes so far (reversed), what is left, the cut
type Fld is Data:
  Fld{acc: String, rest: String, cut: Cut}

# the bytes of s after its first n (by n first: n = 0 needs nothing of s)
def dropn(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+p:
      match s:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          dropn(p, t)

# the length of the space rune s starts with, or 0 (a newline is not
# trimmed: it ends the record)
def space_len(+s: String) -> Nat:
  +b0 = byte_at(s, 0n)
  pick(Nat, Bool.or(U32.is_eq(b0, 10), Bool.not(first_space(s))), 0n,
  pick(Nat, U32.is_lt(b0, 128), 1n,
  pick(Nat, U32.is_eq(b0, 194), 2n, 3n)))

def trim.go(fuel: String, stop: Bool, +s: String) -> String:
  match fuel:
    case SNil{}:
      s
    case SCon{c, f}:
      match stop:
        case True{}:
          s
        case False{}:
          +n = space_len(s)
          trim.go(f, Nat.is_eq(n, 0n), dropn(n, s))

# TrimLeadingSpace: drop the space runes a field starts with
def trim(+s: String) -> String:
  trim.go(SCon{Chr{0}, s}, False{}, s)

# one byte k of a bare field, followed by t (each link of the pick chain
# has a def of its own, so a proof can name the branches)
def bare.byte.4(+k: U32, +acc: String, +t: String) -> Fld:
  pick(Fld, U32.is_eq(k, 34), Fld{acc, t, CsvBad{}}, Fld{SCon{Chr{k}, acc}, t, CsvMore{}})

def bare.byte.3(+k: U32, +acc: String, +t: String) -> Fld:
  pick(Fld, Bool.and(U32.is_eq(k, 13), Bool.or(String.is_empty(t), first_is(t, 10))), Fld{acc, dropn(1n, t), CsvEnd{}},
    bare.byte.4(k, acc, t))

def bare.byte.2(+k: U32, +acc: String, +t: String) -> Fld:
  pick(Fld, U32.is_eq(k, 10), Fld{acc, t, CsvEnd{}}, bare.byte.3(k, acc, t))

def bare.byte(+k: U32, +acc: String, +t: String) -> Fld:
  pick(Fld, U32.is_eq(k, 44), Fld{acc, t, CsvSep{}}, bare.byte.2(k, acc, t))

# after a closing quote, followed by t
def quoted.close(+acc: String, +t: String) -> Fld:
  +b1 = byte_at(t, 0n)
  pick(Fld, String.is_empty(t), Fld{acc, "", CsvEnd{}},
  pick(Fld, U32.is_eq(b1, 34), Fld{SCon{'"', acc}, dropn(1n, t), CsvMore{}},
  pick(Fld, U32.is_eq(b1, 44), Fld{acc, dropn(1n, t), CsvSep{}},
  pick(Fld, U32.is_eq(b1, 10), Fld{acc, dropn(1n, t), CsvEnd{}},
  pick(Fld, Bool.and(U32.is_eq(b1, 13), Bool.or(Nat.is_eq(String.length(String.take(t, 2n)), 1n), U32.is_eq(byte_at(t, 1n), 10))),
    Fld{acc, dropn(2n, t), CsvEnd{}},
    Fld{acc, t, CsvBad{}})))))

# one byte k inside a quoted field, followed by t
def quoted.byte.2(+k: U32, +acc: String, +t: String) -> Fld:
  pick(Fld, Bool.and(U32.is_eq(k, 13), first_is(t, 10)), Fld{SCon{'\n', acc}, dropn(1n, t), CsvMore{}},
    Fld{SCon{Chr{k}, acc}, t, CsvMore{}})

def quoted.byte.of(q: Bool, +k: U32, +acc: String, +t: String) -> Fld:
  match q:
    case True{}:
      quoted.close(acc, t)
    case False{}:
      quoted.byte.2(k, acc, t)

def quoted.byte(+k: U32, +acc: String, +t: String) -> Fld:
  quoted.byte.of(U32.is_eq(k, 34), k, acc, t)

# one step of a field; an unterminated quote is an error, as in Go
def step(quoted: Bool, acc: String, s: String) -> Fld:
  match quoted:
    case True{}:
      match s:
        case SNil{}:
          Fld{acc, "", CsvBad{}}
        case SCon{c, t}:
          quoted.byte(code(c), acc, t)
    case False{}:
      match s:
        case SNil{}:
          Fld{acc, "", CsvEnd{}}
        case SCon{c, t}:
          bare.byte(code(c), acc, t)

def field.go(fuel: String, +quoted: Bool, st: Fld) -> Fld:
  match fuel:
    case SNil{}:
      st
    case SCon{c, f}:
      match st:
        case Fld{acc, rest, cut}:
          match cut:
            case CsvMore{}:
              field.go(f, quoted, step(quoted, acc, rest))
            case CsvSep{}:
              Fld{acc, rest, CsvSep{}}
            case CsvEnd{}:
              Fld{acc, rest, CsvEnd{}}
            case CsvBad{}:
              Fld{acc, rest, CsvBad{}}

def read_field.of(quoted: Bool, +s: String) -> Fld:
  match quoted:
    case True{}:
      field.go(SCon{Chr{0}, s}, True{}, Fld{"", dropn(1n, s), CsvMore{}})
    case False{}:
      field.go(SCon{Chr{0}, s}, False{}, Fld{"", s, CsvMore{}})

# one field of a record, after trimming its leading space
def read_field(+s: String) -> Fld:
  +t = trim(s)
  read_field.of(first_is(t, 34), t)

# the fields read so far (reversed, each in order), what is left, the cut
type Rec is Data:
  Rec{fs: List<&2, String>, rest: String, cut: Cut}

def rec.step(fs: List<&2, String>, st: Fld) -> Rec:
  match st:
    case Fld{acc, rest, cut}:
      Rec{Con{String.reverse(acc), fs}, rest, cut}

def rec.done(fs: List<&2, String>, rest: String) -> Maybe<&1, List<&2, String> & String>:
  Some{(List.reverse(&2, String, fs), rest)}

def rec.go(fuel: String, st: Rec) -> Maybe<&1, List<&2, String> & String>:
  match fuel:
    case SNil{}:
      None{}
    case SCon{c, f}:
      match st:
        case Rec{fs, rest, cut}:
          match cut:
            case CsvMore{}:
              None{}
            case CsvSep{}:
              rec.go(f, rec.step(fs, read_field(rest)))
            case CsvEnd{}:
              rec.done(fs, rest)
            case CsvBad{}:
              None{}

# the length of the blank line s starts with ("\n", "\r\n", or a lone
# "\r" at the end), or 0
def blank_len(+s: String) -> Nat:
  +b0 = byte_at(s, 0n)
  pick(Nat, Bool.and(U32.is_eq(b0, 10), Bool.not(String.is_empty(s))), 1n,
  pick(Nat, Bool.and(U32.is_eq(b0, 13), Bool.or(U32.is_eq(byte_at(s, 1n), 10), Nat.is_eq(String.length(String.take(s, 2n)), 1n))),
    Nat.min(2n, String.length(String.take(s, 2n))), 0n))

def skip_blank.go(fuel: String, stop: Bool, +s: String) -> String:
  match fuel:
    case SNil{}:
      s
    case SCon{c, f}:
      match stop:
        case True{}:
          s
        case False{}:
          +n = blank_len(s)
          skip_blank.go(f, Nat.is_eq(n, 0n), dropn(n, s))

def parse_row.of(empty: Bool, +s: String) -> Maybe<&1, List<&2, String> & String>:
  match empty:
    case True{}:
      None{}
    case False{}:
      rec.go(SCon{Chr{0}, SCon{Chr{0}, s}}, Rec{[], s, CsvSep{}})

# one record (Go's Reader.Read, skipping blank lines first) and the input
# after it; None at the end of the input or on a syntax error
def parse_row.go(+s: String) -> Maybe<&1, List<&2, String> & String>:
  +t = skip_blank.go(SCon{Chr{0}, s}, False{}, s)
  parse_row.of(String.is_empty(t), t)

def parse_row(s: String) -> Maybe<&1, List<&2, String> & String>:
  parse_row.go(s)

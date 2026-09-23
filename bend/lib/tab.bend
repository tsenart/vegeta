# text/tabwriter as Vegeta configures it: minwidth 0, tabwidth 8,
# padding 2, padchar ' ', StripEscape.
#
# A line is cells ended by tabs, then trailing text. A column is the j-th
# cell of a run of consecutive lines that all have one; its cells are
# padded with spaces to the widest in the run plus 2 (widths in runes).
# The widest is found in two linear passes: going down, the widest of cell
# j in this line and the ones above in its run; going up, the same below;
# a cell's column width is the larger of the two.
import Base
import ./json.bend as Json

def pick(-A: Data, c: Bool, a: A, b: A) -> A:
  match c:
    case True{}:
      a
    case False{}:
      b

def code(c: Char) -> U32:
  Chr{k} = c
  k

def nmax(+a: Nat, +b: Nat) -> Nat:
  pick(Nat, Nat.is_le(a, b), b, a)

def split_cons(+c: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{c, SNil{}}]
    case Con{+p, +rest}:
      Con{SCon{c, p}, rest}

# s cut at every byte k (k itself dropped): one more part than there are k
def split_on(+k: U32, s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [""]
    case SCon{+c, +rest}:
      +r = split_on(k, rest)
      pick(List<&2, String>, U32.is_eq(code(c), k), Con{"", r}, split_cons(c, r))

def join_lines(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, +rest}:
      match rest:
        case Nil{}:
          x
        case Con{+y, +more}:
          x ++ "\n" ++ join_lines(Con{y, more})

# Go's utf8.RuneCount: a valid sequence is one rune, a stray byte too
def runes.go(fuel: Nat, stop: Bool, +s: String, +acc: Nat) -> Nat:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      match stop:
        case True{}:
          acc
        case False{}:
          +t = String.drop(s, Json.esc_len(s))
          runes.go(f, String.is_empty(t), t, 1n+acc)

def runes(+s: String) -> Nat:
  runes.go(String.length(s), String.is_empty(s), s, 0n)

# the cells of a line ended by tabs (all its tab-split parts but the last)
def cells(+l: String) -> List<&2, String>:
  +ps = split_on(9, l)
  List.take(&2, String, ps, Nat.sub(List.length(&2, String, ps), 1n))

def trailing(+l: String) -> String:
  Maybe.default(&2, String, List.last(&2, String, split_on(9, l)), "")

def widths(cs: List<&2, String>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      []
    case Con{+c, +rest}:
      Con{runes(c), widths(rest)}

def all_widths(ls: List<&2, String>) -> List<&2, List<&2, Nat>>:
  match ls:
    case Nil{}:
      []
    case Con{+l, +rest}:
      Con{widths(cells(l)), all_widths(rest)}

def head0(+xs: List<&2, Nat>) -> Nat:
  Maybe.default(&2, Nat, List.head(&2, Nat, xs), 0n)

# this line's widths, each raised to the run's widest so far (a column
# the line before lacks starts a new run)
def zmax(ws: List<&2, Nat>, +prev: List<&2, Nat>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      []
    case Con{+w, +rest}:
      Con{nmax(w, head0(prev)), zmax(rest, List.tail(&2, Nat, prev))}

def runs(wss: List<&2, List<&2, Nat>>, +prev: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match wss:
    case Nil{}:
      []
    case Con{+ws, +rest}:
      +u = zmax(ws, prev)
      Con{u, runs(rest, u)}

def pad_cells(cs: List<&2, String>, +up: List<&2, Nat>, +down: List<&2, Nat>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{+c, +rest}:
      +w = Nat.add(nmax(head0(up), head0(down)), 2n)
      c ++ String.repeat(" ", Nat.sub(w, runes(c))) ++ pad_cells(rest, List.tail(&2, Nat, up), List.tail(&2, Nat, down))

def lay(ls: List<&2, String>, +ups: List<&2, List<&2, Nat>>, +downs: List<&2, List<&2, Nat>>) -> List<&2, String>:
  match ls:
    case Nil{}:
      []
    case Con{+l, +rest}:
      +up = Maybe.default(&2, List<&2, Nat>, List.head(&2, List<&2, Nat>, ups), [])
      +down = Maybe.default(&2, List<&2, Nat>, List.head(&2, List<&2, Nat>, downs), [])
      Con{pad_cells(cells(l), up, down) ++ trailing(l),
        lay(rest, List.tail(&2, List<&2, Nat>, ups), List.tail(&2, List<&2, Nat>, downs))}

def render(s: String) -> String:
  +ls = split_on(10, s)
  +wss = all_widths(ls)
  +ups = runs(wss, [])
  +downs = List.reverse(&2, List<&2, Nat>, runs(List.reverse(&2, List<&2, Nat>, wss), []))
  join_lines(lay(ls, ups, downs))

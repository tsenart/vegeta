# Proofs of the codec laws (b64_*, csv_*, json_*, text_utf8).
#
# Each lib module has its own pick, which the checker does not identify
# with LAWS' pick on an opaque condition; pick_<m> relates them branch by
# branch. The lib gives every link of a pick chain a def of its own, and
# the l_* defs here are the same chain with LAWS' pick.
#
# The round trips (b64_decode, json_read_str, csv_parse_row) go by case
# analysis on computed verdicts: a helper takes the verdict b and an
# equation {cond == b}, matches b, and rewrites cond in the goal. A helper
# never calls the loop it serves (no mutual recursion): it proves one step
# as an equation, and the loop chains the steps. Opaque bytes are split
# into bits only where arithmetic must compute (byte_eq, k5_eq); the long
# nested matches there (and vc, u00) are mechanical.
import Base
import ../LAWS.bend as L
import ../lib/b64.bend as B64
import ../lib/csv.bend as Csv
import ../lib/json.bend as Json
import ../lib/text.bend as Text
import ./nat.bend as N

# ---------------------------------------------------------------------
# Text
# ---------------------------------------------------------------------

def pick_t(-A: Data, c: Bool, -a: A, -b: A, -x: A, -y: A, ea: {a == x : A}, eb: {b == y : A})
  -> {Text.pick(A, c, a, b) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def l_char3(+k: U32) -> String:
  L.pick(String, U32.is_lt(k, 65536), Text.char.three(k), Text.char.four(k))

def l_char2(+k: U32) -> String:
  L.pick(String, U32.is_lt(k, 2048), Text.char.two(k), l_char3(k))

def char_same(+c: Char) -> {Text.char(Text.code(c)) == L.utf8_char(L.code(c)) : String}:
  match c:
    case Chr{+k}:
      pick_t(String, U32.is_lt(k, 128), Text.str1(k), Text.char.2(k), Text.str1(k), l_char2(k), {==},
        pick_t(String, U32.is_lt(k, 2048), Text.char.two(k), Text.char.3(k), Text.char.two(k), l_char3(k), {==},
          pick_t(String, U32.is_lt(k, 65536), Text.char.three(k), Text.char.four(k), Text.char.three(k), Text.char.four(k), {==}, {==})))

def L.text_utf8(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      %L.text_utf8(rest) : {Text.char(Text.code(c)) ++ Text.utf8(rest) == L.utf8_char(L.code(c)) ++ _ : String}
      %char_same(c) : {Text.char(Text.code(c)) ++ Text.utf8(rest) == _ ++ Text.utf8(rest) : String}
      {==}

# ---------------------------------------------------------------------
# CSV
# ---------------------------------------------------------------------

def join_same(rest: List<&2, String>, +f: String)
  -> {Csv.join_fields(Con{f, rest}) == L.join_fields(Con{f, rest}) : String}:
  match rest:
    case Nil{}:
      {==}
    case Con{+g, +more}:
      %join_same(more, g) : {Csv.field(f) ++ "," ++ Csv.join_fields(Con{g, more}) == Csv.field(f) ++ "," ++ _ : String}
      {==}

def L.csv_row(fs):
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      %join_same(rest, f) : {Csv.join_fields(Con{f, rest}) ++ "\n" == _ ++ "\n" : String}
      {==}

def pick_c(-A: Data, c: Bool, -a: A, -b: A, -x: A, -y: A, ea: {a == x : A}, eb: {b == y : A})
  -> {Csv.pick(A, c, a, b) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def byte_at_c(s: String, +i: Nat) -> {Csv.byte_at(s, i) == L.byte_at(s, i) : U32}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              byte_at_c(rest, j)

def has_char_c(s: String, +k: U32) -> {Csv.has_char(s, k) == L.has_char(s, k) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+kc}:
          %has_char_c(rest, k) : {Csv.has_char(SCon{Chr{kc}, rest}, k) == Bool.or(U32.is_eq(kc, k), _) : Bool}
          {==}

# first_space with its three bytes as parameters
def l_first_space(+b0: U32, +b1: U32, +b2: U32, +s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)),
  Bool.or(Bool.or(L.is_space(b0), Bool.and(U32.is_eq(b0, 194), Bool.or(U32.is_eq(b1, 133), U32.is_eq(b1, 160)))),
  Bool.or(Bool.and(U32.is_eq(b0, 225), Bool.and(U32.is_eq(b1, 154), U32.is_eq(b2, 128))),
  Bool.or(Bool.and(U32.is_eq(b0, 226), Bool.or(Bool.and(U32.is_eq(b1, 128), Bool.or(L.in_range32(b2, 128, 138), Bool.or(L.in_range32(b2, 168, 169), U32.is_eq(b2, 175)))),
                                               Bool.and(U32.is_eq(b1, 129), U32.is_eq(b2, 159)))),
    Bool.and(U32.is_eq(b0, 227), Bool.and(U32.is_eq(b1, 128), U32.is_eq(b2, 128)))))))

def first_space_c(+s: String) -> {Csv.first_space(s) == L.first_space(s) : Bool}:
  %byte_at_c(s, 0n) : {Csv.first_space(s) == l_first_space(_, L.byte_at(s, 1n), L.byte_at(s, 2n), s) : Bool}
  %byte_at_c(s, 1n) : {Csv.first_space(s) == l_first_space(Csv.byte_at(s, 0n), _, L.byte_at(s, 2n), s) : Bool}
  %byte_at_c(s, 2n) : {Csv.first_space(s) == l_first_space(Csv.byte_at(s, 0n), Csv.byte_at(s, 1n), _, s) : Bool}
  {==}

def l_needs_quotes(fs: Bool, h44: Bool, h34: Bool, h13: Bool, h10: Bool, +s: String) -> Bool:
  L.pick(Bool, String.is_empty(s), False{},
    Bool.or(String.eq(s, "\\."), Bool.or(fs, Bool.or(Bool.or(h44, h34), Bool.or(h13, h10)))))

def c_needs_quotes(fs: Bool, h44: Bool, h34: Bool, h13: Bool, h10: Bool, +s: String) -> Bool:
  Csv.pick(Bool, String.is_empty(s), False{},
    Bool.or(String.eq(s, "\\."), Bool.or(fs, Bool.or(Bool.or(h44, h34), Bool.or(h13, h10)))))

def needs_quotes_c(+s: String) -> {Csv.needs_quotes(s) == L.needs_quotes(s) : Bool}:
  %first_space_c(s) : {Csv.needs_quotes(s) == l_needs_quotes(_, L.has_char(s, 44), L.has_char(s, 34), L.has_char(s, 13), L.has_char(s, 10), s) : Bool}
  %has_char_c(s, 44) : {Csv.needs_quotes(s) == l_needs_quotes(Csv.first_space(s), _, L.has_char(s, 34), L.has_char(s, 13), L.has_char(s, 10), s) : Bool}
  %has_char_c(s, 34) : {Csv.needs_quotes(s) == l_needs_quotes(Csv.first_space(s), Csv.has_char(s, 44), _, L.has_char(s, 13), L.has_char(s, 10), s) : Bool}
  %has_char_c(s, 13) : {Csv.needs_quotes(s) == l_needs_quotes(Csv.first_space(s), Csv.has_char(s, 44), Csv.has_char(s, 34), _, L.has_char(s, 10), s) : Bool}
  %has_char_c(s, 10) : {Csv.needs_quotes(s) == l_needs_quotes(Csv.first_space(s), Csv.has_char(s, 44), Csv.has_char(s, 34), Csv.has_char(s, 13), _, s) : Bool}
  +x = Bool.or(String.eq(s, "\\."), Bool.or(Csv.first_space(s), Bool.or(Bool.or(Csv.has_char(s, 44), Csv.has_char(s, 34)), Bool.or(Csv.has_char(s, 13), Csv.has_char(s, 10)))))
  pick_c(Bool, String.is_empty(s), False{}, x, False{}, x, {==}, {==})

def double_quotes_c(s: String) -> {Csv.double_quotes(s) == L.double_quotes(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %double_quotes_c(rest) : {Csv.double_quotes(SCon{Chr{k}, rest}) == L.pick(String, U32.is_eq(k, 34), "\"\"", SCon{Chr{k}, SNil{}}) ++ _ : String}
          %pick_c(String, U32.is_eq(k, 34), "\"\"", SCon{Chr{k}, SNil{}}, "\"\"", SCon{Chr{k}, SNil{}}, {==}, {==})
            : {Csv.double_quotes(SCon{Chr{k}, rest}) == _ ++ Csv.double_quotes(rest) : String}
          {==}

def L.csv_field(s):
  %needs_quotes_c(s) : {Csv.field(s) == L.pick(String, _, "\"" ++ L.double_quotes(s) ++ "\"", s) : String}
  %double_quotes_c(s) : {Csv.field(s) == L.pick(String, Csv.needs_quotes(s), "\"" ++ _ ++ "\"", s) : String}
  pick_c(String, Csv.needs_quotes(s), "\"" ++ Csv.double_quotes(s) ++ "\"", s, "\"" ++ Csv.double_quotes(s) ++ "\"", s, {==}, {==})

# ---------------------------------------------------------------------
# JSON strings
# ---------------------------------------------------------------------

def pick_j(-A: Data, c: Bool, -a: A, -b: A, -x: A, -y: A, ea: {a == x : A}, eb: {b == y : A})
  -> {Json.pick(A, c, a, b) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def byte_at_j(s: String, +i: Nat) -> {Json.byte_at(s, i) == L.byte_at(s, i) : U32}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              byte_at_j(rest, j)

# lib's cont needs no length: byte_at is 0 past the end
def cont_j(s: String, +i: Nat) -> {Json.cont(s, i) == L.cont(s, i) : Bool}:
  match s:
    case SNil{}:
      match i:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case SCon{c, +rest}:
      match c:
        case Chr{+k}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              cont_j(rest, j)

# LAWS' utf8_len chain, link by link
def l_u8(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  L.pick(Nat, Bool.and(U32.is_eq(b0, 244), Bool.and(L.in_range32(b1, 128, 143), Bool.and(c2, c3))), 4n, 0n)

def l_u7(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  L.pick(Nat, Bool.and(L.in_range32(b0, 241, 243), Bool.and(c1, Bool.and(c2, c3))), 4n, l_u8(b0, b1, c1, c2, c3))

def l_u6(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  L.pick(Nat, Bool.and(U32.is_eq(b0, 240), Bool.and(L.in_range32(b1, 144, 191), Bool.and(c2, c3))), 4n, l_u7(b0, b1, c1, c2, c3))

def l_u5(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  L.pick(Nat, Bool.and(U32.is_eq(b0, 237), Bool.and(L.in_range32(b1, 128, 159), c2)), 3n, l_u6(b0, b1, c1, c2, c3))

def l_u4(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  L.pick(Nat, Bool.and(Bool.or(L.in_range32(b0, 225, 236), L.in_range32(b0, 238, 239)), Bool.and(c1, c2)), 3n, l_u5(b0, b1, c1, c2, c3))

def l_u3(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  L.pick(Nat, Bool.and(U32.is_eq(b0, 224), Bool.and(L.in_range32(b1, 160, 191), c2)), 3n, l_u4(b0, b1, c1, c2, c3))

def l_u2(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  L.pick(Nat, Bool.and(L.in_range32(b0, 194, 223), c1), 2n, l_u3(b0, b1, c1, c2, c3))

def l_u1(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool) -> Nat:
  L.pick(Nat, U32.is_lt(b0, 128), 1n, l_u2(b0, b1, c1, c2, c3))

def utf8_len_of_j(+b0: U32, +b1: U32, +c1: Bool, +c2: Bool, +c3: Bool)
  -> {Json.utf8_len.of(b0, b1, c1, c2, c3) == l_u1(b0, b1, c1, c2, c3) : Nat}:
  pick_j(Nat, U32.is_lt(b0, 128), 1n, Json.utf8_len.2(b0, b1, c1, c2, c3), 1n, l_u2(b0, b1, c1, c2, c3), {==},
  pick_j(Nat, Bool.and(L.in_range32(b0, 194, 223), c1), 2n, Json.utf8_len.3(b0, b1, c1, c2, c3), 2n, l_u3(b0, b1, c1, c2, c3), {==},
  pick_j(Nat, Bool.and(U32.is_eq(b0, 224), Bool.and(L.in_range32(b1, 160, 191), c2)), 3n, Json.utf8_len.4(b0, b1, c1, c2, c3), 3n, l_u4(b0, b1, c1, c2, c3), {==},
  pick_j(Nat, Bool.and(Bool.or(L.in_range32(b0, 225, 236), L.in_range32(b0, 238, 239)), Bool.and(c1, c2)), 3n, Json.utf8_len.5(b0, b1, c1, c2, c3), 3n, l_u5(b0, b1, c1, c2, c3), {==},
  pick_j(Nat, Bool.and(U32.is_eq(b0, 237), Bool.and(L.in_range32(b1, 128, 159), c2)), 3n, Json.utf8_len.6(b0, b1, c1, c2, c3), 3n, l_u6(b0, b1, c1, c2, c3), {==},
  pick_j(Nat, Bool.and(U32.is_eq(b0, 240), Bool.and(L.in_range32(b1, 144, 191), Bool.and(c2, c3))), 4n, Json.utf8_len.7(b0, b1, c1, c2, c3), 4n, l_u7(b0, b1, c1, c2, c3), {==},
  pick_j(Nat, Bool.and(L.in_range32(b0, 241, 243), Bool.and(c1, Bool.and(c2, c3))), 4n, Json.utf8_len.8(b0, b1, c1, c2, c3), 4n, l_u8(b0, b1, c1, c2, c3), {==},
  pick_j(Nat, Bool.and(U32.is_eq(b0, 244), Bool.and(L.in_range32(b1, 128, 143), Bool.and(c2, c3))), 4n, 0n, 4n, 0n, {==}, {==}))))))))

def utf8_len_j(+s: String) -> {Json.utf8_len(s) == L.utf8_len(s) : Nat}:
  %byte_at_j(s, 0n) : {Json.utf8_len(s) == l_u1(_, L.byte_at(s, 1n), L.cont(s, 1n), L.cont(s, 2n), L.cont(s, 3n)) : Nat}
  %byte_at_j(s, 1n) : {Json.utf8_len(s) == l_u1(Json.byte_at(s, 0n), _, L.cont(s, 1n), L.cont(s, 2n), L.cont(s, 3n)) : Nat}
  %cont_j(s, 1n) : {Json.utf8_len(s) == l_u1(Json.byte_at(s, 0n), Json.byte_at(s, 1n), _, L.cont(s, 2n), L.cont(s, 3n)) : Nat}
  %cont_j(s, 2n) : {Json.utf8_len(s) == l_u1(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), _, L.cont(s, 3n)) : Nat}
  %cont_j(s, 3n) : {Json.utf8_len(s) == l_u1(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), _) : Nat}
  utf8_len_of_j(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))

def hexd_j(+n: U32) -> {Json.hexd(n) == L.hexd(n) : String}:
  %pick_j(U32, U32.is_lt(n, 10), (48 + n : U32), (87 + n : U32), (48 + n : U32), (87 + n : U32), {==}, {==})
    : {Json.hexd(n) == L.str1(_) : String}
  {==}

def l_a6(+k: U32) -> String:
  L.pick(String, Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))),
    "\\u00" ++ L.hexd((k >> 4n : U32)) ++ L.hexd((k .&. 15 : U32)),
    L.str1(k))

def l_a5(+k: U32) -> String:
  L.pick(String, U32.is_eq(k, 9), "\\t", l_a6(k))

def l_a4(+k: U32) -> String:
  L.pick(String, U32.is_eq(k, 13), "\\r", l_a5(k))

def l_a3(+k: U32) -> String:
  L.pick(String, U32.is_eq(k, 10), "\\n", l_a4(k))

def l_a2(+k: U32) -> String:
  L.pick(String, U32.is_eq(k, 92), "\\\\", l_a3(k))

def u00_j(+k: U32) -> {"\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))
                       == "\\u00" ++ L.hexd((k >> 4n : U32)) ++ L.hexd((k .&. 15 : U32)) : String}:
  %hexd_j((k >> 4n : U32)) : {"\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))
                              == "\\u00" ++ _ ++ L.hexd((k .&. 15 : U32)) : String}
  %hexd_j((k .&. 15 : U32)) : {"\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))
                               == "\\u00" ++ Json.hexd((k >> 4n : U32)) ++ _ : String}
  {==}

def esc_ascii_j(+k: U32) -> {Json.esc_ascii(k) == L.jesc_ascii(k) : String}:
  pick_j(String, U32.is_eq(k, 34), "\\\"", Json.esc_ascii.2(k), "\\\"", l_a2(k), {==},
  pick_j(String, U32.is_eq(k, 92), "\\\\", Json.esc_ascii.3(k), "\\\\", l_a3(k), {==},
  pick_j(String, U32.is_eq(k, 10), "\\n", Json.esc_ascii.4(k), "\\n", l_a4(k), {==},
  pick_j(String, U32.is_eq(k, 13), "\\r", Json.esc_ascii.5(k), "\\r", l_a5(k), {==},
  pick_j(String, U32.is_eq(k, 9), "\\t", Json.esc_ascii.6(k), "\\t", l_a6(k), {==},
  pick_j(String, Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))),
    "\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32)), Json.str1(k),
    "\\u00" ++ L.hexd((k >> 4n : U32)) ++ L.hexd((k .&. 15 : U32)), L.str1(k),
    u00_j(k), {==}))))))

# LAWS' jesc_head chain, with its length and bytes as parameters
def l_h4(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String) -> String:
  L.pick(String, Bool.and(Nat.is_eq(n, 3n), Bool.and(U32.is_eq(b0, 226), Bool.and(U32.is_eq(b1, 128),
      Bool.or(U32.is_eq(b2, 168), U32.is_eq(b2, 169))))),
    "\\u202" ++ L.pick(String, U32.is_eq(b2, 168), "8", "9"),
    String.take(s, n))

def l_h3(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String) -> String:
  L.pick(String, Nat.is_eq(n, 1n), L.jesc_ascii(b0), l_h4(n, b0, b1, b2, s))

def l_h2(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String) -> String:
  L.pick(String, Nat.is_eq(n, 0n), "\\ufffd", l_h3(n, b0, b1, b2, s))

def l_h1(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String) -> String:
  L.pick(String, String.is_empty(s), "", l_h2(n, b0, b1, b2, s))

def sep_j(+b2: U32) -> {"\\u202" ++ Json.esc_sep(b2) == "\\u202" ++ L.pick(String, U32.is_eq(b2, 168), "8", "9") : String}:
  %pick_j(String, U32.is_eq(b2, 168), "8", "9", "8", "9", {==}, {==})
    : {"\\u202" ++ Json.esc_sep(b2) == "\\u202" ++ _ : String}
  {==}

def esc_head_of_j(+n: Nat, +b0: U32, +b1: U32, +b2: U32, +s: String)
  -> {Json.esc_head.of(n, b0, b1, b2, s) == l_h1(n, b0, b1, b2, s) : String}:
  pick_j(String, String.is_empty(s), "", Json.esc_head.2(n, b0, b1, b2, s), "", l_h2(n, b0, b1, b2, s), {==},
  pick_j(String, Nat.is_eq(n, 0n), "\\ufffd", Json.esc_head.3(n, b0, b1, b2, s), "\\ufffd", l_h3(n, b0, b1, b2, s), {==},
  pick_j(String, Nat.is_eq(n, 1n), Json.esc_ascii(b0), Json.esc_head.4(n, b0, b1, b2, s), L.jesc_ascii(b0), l_h4(n, b0, b1, b2, s), esc_ascii_j(b0),
  pick_j(String, Bool.and(Nat.is_eq(n, 3n), Bool.and(U32.is_eq(b0, 226), Bool.and(U32.is_eq(b1, 128),
      Bool.or(U32.is_eq(b2, 168), U32.is_eq(b2, 169))))),
    "\\u202" ++ Json.esc_sep(b2), String.take(s, n),
    "\\u202" ++ L.pick(String, U32.is_eq(b2, 168), "8", "9"), String.take(s, n),
    sep_j(b2), {==}))))

def esc_head_j(+s: String) -> {Json.esc_head(s) == L.jesc_head(s) : String}:
  %utf8_len_j(s) : {Json.esc_head(s) == l_h1(_, L.byte_at(s, 0n), L.byte_at(s, 1n), L.byte_at(s, 2n), s) : String}
  %byte_at_j(s, 0n) : {Json.esc_head(s) == l_h1(Json.utf8_len(s), _, L.byte_at(s, 1n), L.byte_at(s, 2n), s) : String}
  %byte_at_j(s, 1n) : {Json.esc_head(s) == l_h1(Json.utf8_len(s), Json.byte_at(s, 0n), _, L.byte_at(s, 2n), s) : String}
  %byte_at_j(s, 2n) : {Json.esc_head(s) == l_h1(Json.utf8_len(s), Json.byte_at(s, 0n), Json.byte_at(s, 1n), _, s) : String}
  esc_head_of_j(Json.utf8_len(s), Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.byte_at(s, 2n), s)

def esc_len_j(+s: String) -> {Json.esc_len(s) == L.jesc_len(s) : Nat}:
  %utf8_len_j(s) : {Json.esc_len(s) == Nat.max(1n, _) : Nat}
  {==}

def esc_go_j(fuel: Nat, +s: String) -> {Json.esc.go(fuel, s) == L.jesc.go(fuel, s) : String}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      %esc_go_j(f, String.drop(s, L.jesc_len(s)))
        : {Json.esc.go(1n+f, s) == L.jesc_head(s) ++ _ : String}
      %esc_len_j(s)
        : {Json.esc.go(1n+f, s) == L.jesc_head(s) ++ Json.esc.go(f, String.drop(s, _)) : String}
      %esc_head_j(s)
        : {Json.esc.go(1n+f, s) == _ ++ Json.esc.go(f, String.drop(s, Json.esc_len(s))) : String}
      {==}

def L.json_str(s):
  %esc_go_j(String.length(s), s) : {Json.str(s) == "\"" ++ _ ++ "\"" : String}
  {==}

# ---------------------------------------------------------------------
# Base64
# ---------------------------------------------------------------------

def pick_b(-A: Data, c: Bool, -a: A, -b: A, -x: A, -y: A, ea: {a == x : A}, eb: {b == y : A})
  -> {B64.pick(A, c, a, b) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

def l_code4(+i: U32) -> U32:
  L.pick(U32, U32.is_eq(i, 62), 43, 47)

def l_code3(+i: U32) -> U32:
  L.pick(U32, U32.is_lt(i, 62), (i - 4 : U32), l_code4(i))

def l_code2(+i: U32) -> U32:
  L.pick(U32, U32.is_lt(i, 52), (71 + i : U32), l_code3(i))

def l_code(+i: U32) -> U32:
  L.pick(U32, U32.is_lt(i, 26), (65 + i : U32), l_code2(i))

def code_b(+i: U32) -> {B64.char.code(i) == l_code(i) : U32}:
  pick_b(U32, U32.is_lt(i, 26), (65 + i : U32), B64.char.code2(i), (65 + i : U32), l_code2(i), {==},
  pick_b(U32, U32.is_lt(i, 52), (71 + i : U32), B64.char.code3(i), (71 + i : U32), l_code3(i), {==},
  pick_b(U32, U32.is_lt(i, 62), (i - 4 : U32), B64.char.code4(i), (i - 4 : U32), l_code4(i), {==},
  pick_b(U32, U32.is_eq(i, 62), 43, 47, 43, 47, {==}, {==}))))

def char_b(+i: U32) -> {B64.char(i) == L.b64_char(i) : String}:
  %code_b(i) : {B64.char(i) == L.str1(_) : String}
  {==}

def L.b64_three(a, b, c, h):
  %char_b((a >> 2n : U32))
    : {B64.encode(L.str1(a) ++ L.str1(b) ++ L.str1(c))
       == _ ++ L.b64_char((((a .&. 3) << 4n) .|. (b >> 4n) : U32))
          ++ L.b64_char((((b .&. 15) << 2n) .|. (c >> 6n) : U32)) ++ L.b64_char((c .&. 63 : U32)) : String}
  %char_b((((a .&. 3) << 4n) .|. (b >> 4n) : U32))
    : {B64.encode(L.str1(a) ++ L.str1(b) ++ L.str1(c))
       == B64.char((a >> 2n : U32)) ++ _
          ++ L.b64_char((((b .&. 15) << 2n) .|. (c >> 6n) : U32)) ++ L.b64_char((c .&. 63 : U32)) : String}
  %char_b((((b .&. 15) << 2n) .|. (c >> 6n) : U32))
    : {B64.encode(L.str1(a) ++ L.str1(b) ++ L.str1(c))
       == B64.char((a >> 2n : U32)) ++ B64.char((((a .&. 3) << 4n) .|. (b >> 4n) : U32))
          ++ _ ++ L.b64_char((c .&. 63 : U32)) : String}
  %char_b((c .&. 63 : U32))
    : {B64.encode(L.str1(a) ++ L.str1(b) ++ L.str1(c))
       == B64.char((a >> 2n : U32)) ++ B64.char((((a .&. 3) << 4n) .|. (b >> 4n) : U32))
          ++ B64.char((((b .&. 15) << 2n) .|. (c >> 6n) : U32)) ++ _ : String}
  {==}

def tail2_b(+a: U32, +b: U32)
  -> {B64.encode(L.str1(a) ++ L.str1(b))
      == L.b64_char((a >> 2n : U32)) ++ L.b64_char((((a .&. 3) << 4n) .|. (b >> 4n) : U32)) ++ L.b64_char(((b .&. 15) << 2n : U32)) ++ "=" : String}:
  %char_b((a >> 2n : U32))
    : {B64.encode(L.str1(a) ++ L.str1(b))
       == _ ++ L.b64_char((((a .&. 3) << 4n) .|. (b >> 4n) : U32)) ++ L.b64_char(((b .&. 15) << 2n : U32)) ++ "=" : String}
  %char_b((((a .&. 3) << 4n) .|. (b >> 4n) : U32))
    : {B64.encode(L.str1(a) ++ L.str1(b))
       == B64.char((a >> 2n : U32)) ++ _ ++ L.b64_char(((b .&. 15) << 2n : U32)) ++ "=" : String}
  %char_b(((b .&. 15) << 2n : U32))
    : {B64.encode(L.str1(a) ++ L.str1(b))
       == B64.char((a >> 2n : U32)) ++ B64.char((((a .&. 3) << 4n) .|. (b >> 4n) : U32)) ++ _ ++ "=" : String}
  {==}

def tail1_b(+a: U32)
  -> {B64.encode(L.str1(a)) == L.b64_char((a >> 2n : U32)) ++ L.b64_char(((a .&. 3) << 4n : U32)) ++ "==" : String}:
  %char_b((a >> 2n : U32))
    : {B64.encode(L.str1(a))
       == _ ++ L.b64_char(((a .&. 3) << 4n : U32)) ++ "==" : String}
  %char_b(((a .&. 3) << 4n : U32))
    : {B64.encode(L.str1(a)) == B64.char((a >> 2n : U32)) ++ _ ++ "==" : String}
  {==}

def L.b64_tail(a, b, h):
  (tail2_b(a, b), (tail1_b(a), {==}))

# the remainder of Base's divmod loop does not depend on the quotient so far
def rem_free(n: Nat, +m: Nat, +d: Nat, +e: Nat, +r: Nat)
  -> {Nat.mod.fin(Nat.divmod.go(n, m, d, r)) == Nat.mod.fin(Nat.divmod.go(n, m, e, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          rem_free(np, r, 1n+d, 1n+e, 0n)
        case 1n+mp:
          rem_free(np, mp, d, e, 1n+r)

# a length divisible by 3 stays so without its first three
def mod3_drop(+n: Nat, h: {Nat.mod(3n+n, 3n) == 0n : Nat}) -> {Nat.mod(n, 3n) == 0n : Nat}:
  Equal.trans(Nat, Nat.mod(n, 3n), Nat.mod(3n+n, 3n), 0n, rem_free(n, 2n, 0n, 1n, 0n), h)

def concat_b(x: String, +y: String, h: {Nat.mod(String.length(x), 3n) == 0n : Nat})
  -> {B64.encode(x ++ y) == B64.encode(x) ++ B64.encode(y) : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+a, +r1}:
      match r1:
        case SNil{}:
          Empty.absurd({B64.encode(SCon{a, SNil{}} ++ y) == B64.encode(SCon{a, SNil{}}) ++ B64.encode(y) : String},
            N.no_zero(0n, h))
        case SCon{+b, +r2}:
          match r2:
            case SNil{}:
              Empty.absurd({B64.encode(SCon{a, SCon{b, SNil{}}} ++ y) == B64.encode(SCon{a, SCon{b, SNil{}}}) ++ B64.encode(y) : String},
                N.no_zero(1n, h))
            case SCon{+c, +r3}:
              %Equal.sym(String, B64.encode(r3 ++ y), B64.encode(r3) ++ B64.encode(y),
                  concat_b(r3, y, mod3_drop(String.length(r3), h)))
                : {B64.three(B64.code(a), B64.code(b), B64.code(c)) ++ _
                   == B64.encode(SCon{a, SCon{b, SCon{c, r3}}}) ++ B64.encode(y) : String}
              {==}

def L.b64_concat(x, y, h0, h1):
  concat_b(x, y, h0)

# ---------------------------------------------------------------------
# Base64 decoding: bit by bit
#
# A byte is ub(a), its eight bits over zeros (byte_eq, from a < 256).
# Each six-bit index encode computes is w6 of six bit expressions (the
# idx_* lemmas clear the stuck Bool.and(x, True) and Bool.and(x, False)
# that U32 arithmetic leaves on an opaque bit), value inverts the
# alphabet on every w6 (vc, 64 cases), and decode reassembles the bytes
# from those bits.
# ---------------------------------------------------------------------

def bool_t(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def no_ft(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_t(_)
  Unit{}

def no_tf(e: {True{} == False{} : Bool}) -> Empty:
  no_ft(Equal.sym(Bool, True{}, False{}, e))

def and_l(p: Bool, -q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {p == True{} : Bool}:
  match p:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, no_ft(h))
    case True{}:
      {==}

def and_r(p: Bool, -q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case False{}:
      Empty.absurd({q == True{} : Bool}, no_ft(h))
    case True{}:
      h

def and_t(x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def and_f(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def or_and_t(x: Bool) -> {Bool.or(Bool.and(x, True{}), False{}) == x : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def or_and_f(x: Bool) -> {Bool.or(Bool.and(x, False{}), False{}) == False{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def z26() -> Word(26n):
  WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}

# a six-bit value
def w6(+t0: Bool, +t1: Bool, +t2: Bool, +t3: Bool, +t4: Bool, +t5: Bool) -> U32:
  U32{WCon{t0, WCon{t1, WCon{t2, WCon{t3, WCon{t4, WCon{t5, z26()}}}}}}}

def pb0(a: U32) -> Bool:
  match a:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          b0

def pb1(a: U32) -> Bool:
  match a:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              b1

def pb2(a: U32) -> Bool:
  match a:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  b2

def pb3(a: U32) -> Bool:
  match a:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      b3

def pb4(a: U32) -> Bool:
  match a:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      match w4:
                        case WCon{b4, w5}:
                          b4

def pb5(a: U32) -> Bool:
  match a:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      match w4:
                        case WCon{b4, w5}:
                          match w5:
                            case WCon{b5, w6}:
                              b5

def pb6(a: U32) -> Bool:
  match a:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      match w4:
                        case WCon{b4, w5}:
                          match w5:
                            case WCon{b5, w6}:
                              match w6:
                                case WCon{b6, w7}:
                                  b6

def pb7(a: U32) -> Bool:
  match a:
    case U32{w0}:
      match w0:
        case WCon{b0, w1}:
          match w1:
            case WCon{b1, w2}:
              match w2:
                case WCon{b2, w3}:
                  match w3:
                    case WCon{b3, w4}:
                      match w4:
                        case WCon{b4, w5}:
                          match w5:
                            case WCon{b5, w6}:
                              match w6:
                                case WCon{b6, w7}:
                                  match w7:
                                    case WCon{b7, w8}:
                                      b7

# a byte as its bits
def ub(+a: U32) -> U32:
  B64.mk8(pb0(a), pb1(a), pb2(a), pb3(a), pb4(a), pb5(a), pb6(a), pb7(a))

def fin_nlt(x: Bool, +t: Cmp, h: {Cmp.is_lt(t) == False{} : Bool}) -> {Cmp.is_lt(Word.cmp.fin(x, False{}, t)) == False{} : Bool}:
  match x:
    case False{}:
      match t:
        case LT{}:
          Empty.absurd({Cmp.is_lt(Word.cmp.fin(False{}, False{}, LT{})) == False{} : Bool}, no_tf(h))
        case EQ{}:
          {==}
        case GT{}:
          {==}
    case True{}:
      match t:
        case LT{}:
          Empty.absurd({Cmp.is_lt(Word.cmp.fin(True{}, False{}, LT{})) == False{} : Bool}, no_tf(h))
        case EQ{}:
          {==}
        case GT{}:
          {==}

def nlt(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool) -> {U32.is_lt(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 256) == False{} : Bool}:
  fin_nlt(x0, Word.cmp.fin(x1, False{}, Word.cmp.fin(x2, False{}, Word.cmp.fin(x3, False{}, Word.cmp.fin(x4, False{}, Word.cmp.fin(x5, False{}, Word.cmp.fin(x6, False{}, Word.cmp.fin(x7, False{}, EQ{}))))))), fin_nlt(x1, Word.cmp.fin(x2, False{}, Word.cmp.fin(x3, False{}, Word.cmp.fin(x4, False{}, Word.cmp.fin(x5, False{}, Word.cmp.fin(x6, False{}, Word.cmp.fin(x7, False{}, EQ{})))))), fin_nlt(x2, Word.cmp.fin(x3, False{}, Word.cmp.fin(x4, False{}, Word.cmp.fin(x5, False{}, Word.cmp.fin(x6, False{}, Word.cmp.fin(x7, False{}, EQ{}))))), fin_nlt(x3, Word.cmp.fin(x4, False{}, Word.cmp.fin(x5, False{}, Word.cmp.fin(x6, False{}, Word.cmp.fin(x7, False{}, EQ{})))), fin_nlt(x4, Word.cmp.fin(x5, False{}, Word.cmp.fin(x6, False{}, Word.cmp.fin(x7, False{}, EQ{}))), fin_nlt(x5, Word.cmp.fin(x6, False{}, Word.cmp.fin(x7, False{}, EQ{})), fin_nlt(x6, Word.cmp.fin(x7, False{}, EQ{}), fin_nlt(x7, EQ{}, {==}))))))))

def byte_eq.go(w32: Word(0n), +x31: Bool, +x30: Bool, +x29: Bool, +x28: Bool, +x27: Bool, +x26: Bool, +x25: Bool, +x24: Bool, +x23: Bool, +x22: Bool, +x21: Bool, +x20: Bool, +x19: Bool, +x18: Bool, +x17: Bool, +x16: Bool, +x15: Bool, +x14: Bool, +x13: Bool, +x12: Bool, +x11: Bool, +x10: Bool, +x9: Bool, +x8: Bool, +x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool, h: {U32.is_lt(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, w32}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 256) == True{} : Bool}) -> {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, w32}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, w32}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  match w32:
    case WNil{}:
      match x31:
        case True{}:
          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
        case False{}:
          match x30:
            case True{}:
              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
            case False{}:
              match x29:
                case True{}:
                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                case False{}:
                  match x28:
                    case True{}:
                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                    case False{}:
                      match x27:
                        case True{}:
                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                        case False{}:
                          match x26:
                            case True{}:
                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                            case False{}:
                              match x25:
                                case True{}:
                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                case False{}:
                                  match x24:
                                    case True{}:
                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                    case False{}:
                                      match x23:
                                        case True{}:
                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                        case False{}:
                                          match x22:
                                            case True{}:
                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                            case False{}:
                                              match x21:
                                                case True{}:
                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                case False{}:
                                                  match x20:
                                                    case True{}:
                                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                    case False{}:
                                                      match x19:
                                                        case True{}:
                                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                        case False{}:
                                                          match x18:
                                                            case True{}:
                                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                            case False{}:
                                                              match x17:
                                                                case True{}:
                                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                case False{}:
                                                                  match x16:
                                                                    case True{}:
                                                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                    case False{}:
                                                                      match x15:
                                                                        case True{}:
                                                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                        case False{}:
                                                                          match x14:
                                                                            case True{}:
                                                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                            case False{}:
                                                                              match x13:
                                                                                case True{}:
                                                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                case False{}:
                                                                                  match x12:
                                                                                    case True{}:
                                                                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                    case False{}:
                                                                                      match x11:
                                                                                        case True{}:
                                                                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                        case False{}:
                                                                                          match x10:
                                                                                            case True{}:
                                                                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                            case False{}:
                                                                                              match x9:
                                                                                                case True{}:
                                                                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                                case False{}:
                                                                                                  match x8:
                                                                                                    case True{}:
                                                                                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == ub(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(Equal.trans(Bool, False{}, U32.is_lt(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 256), True{}, Equal.sym(Bool, U32.is_lt(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 256), False{}, nlt(x0, x1, x2, x3, x4, x5, x6, x7)), h)))
                                                                                                    case False{}:
                                                                                                      {==}

def byte_eq(a: U32, h: {U32.is_lt(a, 256) == True{} : Bool}) -> {a == ub(a) : U32}:
  match a:
    case U32{w0}:
      match w0:
        case WCon{x0, w1}:
          match w1:
            case WCon{x1, w2}:
              match w2:
                case WCon{x2, w3}:
                  match w3:
                    case WCon{x3, w4}:
                      match w4:
                        case WCon{x4, w5}:
                          match w5:
                            case WCon{x5, w6}:
                              match w6:
                                case WCon{x6, w7}:
                                  match w7:
                                    case WCon{x7, w8}:
                                      match w8:
                                        case WCon{x8, w9}:
                                          match w9:
                                            case WCon{x9, w10}:
                                              match w10:
                                                case WCon{x10, w11}:
                                                  match w11:
                                                    case WCon{x11, w12}:
                                                      match w12:
                                                        case WCon{x12, w13}:
                                                          match w13:
                                                            case WCon{x13, w14}:
                                                              match w14:
                                                                case WCon{x14, w15}:
                                                                  match w15:
                                                                    case WCon{x15, w16}:
                                                                      match w16:
                                                                        case WCon{x16, w17}:
                                                                          match w17:
                                                                            case WCon{x17, w18}:
                                                                              match w18:
                                                                                case WCon{x18, w19}:
                                                                                  match w19:
                                                                                    case WCon{x19, w20}:
                                                                                      match w20:
                                                                                        case WCon{x20, w21}:
                                                                                          match w21:
                                                                                            case WCon{x21, w22}:
                                                                                              match w22:
                                                                                                case WCon{x22, w23}:
                                                                                                  match w23:
                                                                                                    case WCon{x23, w24}:
                                                                                                      match w24:
                                                                                                        case WCon{x24, w25}:
                                                                                                          match w25:
                                                                                                            case WCon{x25, w26}:
                                                                                                              match w26:
                                                                                                                case WCon{x26, w27}:
                                                                                                                  match w27:
                                                                                                                    case WCon{x27, w28}:
                                                                                                                      match w28:
                                                                                                                        case WCon{x28, w29}:
                                                                                                                          match w29:
                                                                                                                            case WCon{x29, w30}:
                                                                                                                              match w30:
                                                                                                                                case WCon{x30, w31}:
                                                                                                                                  match w31:
                                                                                                                                    case WCon{x31, w32}:
                                                                                                                                      byte_eq.go(w32, x31, x30, x29, x28, x27, x26, x25, x24, x23, x22, x21, x20, x19, x18, x17, x16, x15, x14, x13, x12, x11, x10, x9, x8, x0, x1, x2, x3, x4, x5, x6, x7, h)

def vc(+t0: Bool, +t1: Bool, +t2: Bool, +t3: Bool, +t4: Bool, +t5: Bool) -> {B64.value(B64.char.code(w6(t0, t1, t2, t3, t4, t5))) == w6(t0, t1, t2, t3, t4, t5) : U32}:
  match t0:
    case False{}:
      match t1:
        case False{}:
          match t2:
            case False{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                case True{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
            case True{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                case True{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
        case True{}:
          match t2:
            case False{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                case True{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
            case True{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                case True{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
    case True{}:
      match t1:
        case False{}:
          match t2:
            case False{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                case True{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
            case True{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                case True{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
        case True{}:
          match t2:
            case False{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                case True{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
            case True{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                case True{}:
                  match t4:
                    case False{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}
                    case True{}:
                      match t5:
                        case False{}:
                          {==}
                        case True{}:
                          {==}

def idx2(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool, +y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +y6: Bool, +y7: Bool) -> {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{x0, WCon{x1, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}:
  %or_and_t(x0) : {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{_, WCon{x1, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_t(x1) : {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{Bool.or(Bool.and(x0, True{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(x2) : {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{Bool.or(Bool.and(x0, True{}), False{}), WCon{Bool.or(Bool.and(x1, True{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(x3) : {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{Bool.or(Bool.and(x0, True{}), False{}), WCon{Bool.or(Bool.and(x1, True{}), False{}), WCon{Bool.or(Bool.and(x2, False{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(x4) : {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{Bool.or(Bool.and(x0, True{}), False{}), WCon{Bool.or(Bool.and(x1, True{}), False{}), WCon{Bool.or(Bool.and(x2, False{}), False{}), WCon{Bool.or(Bool.and(x3, False{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(x5) : {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{Bool.or(Bool.and(x0, True{}), False{}), WCon{Bool.or(Bool.and(x1, True{}), False{}), WCon{Bool.or(Bool.and(x2, False{}), False{}), WCon{Bool.or(Bool.and(x3, False{}), False{}), WCon{Bool.or(Bool.and(x4, False{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(x6) : {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{Bool.or(Bool.and(x0, True{}), False{}), WCon{Bool.or(Bool.and(x1, True{}), False{}), WCon{Bool.or(Bool.and(x2, False{}), False{}), WCon{Bool.or(Bool.and(x3, False{}), False{}), WCon{Bool.or(Bool.and(x4, False{}), False{}), WCon{Bool.or(Bool.and(x5, False{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(x7) : {((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32) == U32{WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{Bool.or(Bool.and(x0, True{}), False{}), WCon{Bool.or(Bool.and(x1, True{}), False{}), WCon{Bool.or(Bool.and(x2, False{}), False{}), WCon{Bool.or(Bool.and(x3, False{}), False{}), WCon{Bool.or(Bool.and(x4, False{}), False{}), WCon{Bool.or(Bool.and(x5, False{}), False{}), WCon{Bool.or(Bool.and(x6, False{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  {==}

def idx3(+y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +y6: Bool, +y7: Bool, +z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool) -> {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}:
  %or_and_t(y0) : {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{_, WCon{y1, WCon{y2, WCon{y3, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_t(y1) : {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{Bool.or(Bool.and(y0, True{}), False{}), WCon{_, WCon{y2, WCon{y3, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_t(y2) : {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{Bool.or(Bool.and(y0, True{}), False{}), WCon{Bool.or(Bool.and(y1, True{}), False{}), WCon{_, WCon{y3, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_t(y3) : {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{Bool.or(Bool.and(y0, True{}), False{}), WCon{Bool.or(Bool.and(y1, True{}), False{}), WCon{Bool.or(Bool.and(y2, True{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(y4) : {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{Bool.or(Bool.and(y0, True{}), False{}), WCon{Bool.or(Bool.and(y1, True{}), False{}), WCon{Bool.or(Bool.and(y2, True{}), False{}), WCon{Bool.or(Bool.and(y3, True{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(y5) : {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{Bool.or(Bool.and(y0, True{}), False{}), WCon{Bool.or(Bool.and(y1, True{}), False{}), WCon{Bool.or(Bool.and(y2, True{}), False{}), WCon{Bool.or(Bool.and(y3, True{}), False{}), WCon{Bool.or(Bool.and(y4, False{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(y6) : {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{Bool.or(Bool.and(y0, True{}), False{}), WCon{Bool.or(Bool.and(y1, True{}), False{}), WCon{Bool.or(Bool.and(y2, True{}), False{}), WCon{Bool.or(Bool.and(y3, True{}), False{}), WCon{Bool.or(Bool.and(y4, False{}), False{}), WCon{Bool.or(Bool.and(y5, False{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %or_and_f(y7) : {((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32) == U32{WCon{z6, WCon{z7, WCon{Bool.or(Bool.and(y0, True{}), False{}), WCon{Bool.or(Bool.and(y1, True{}), False{}), WCon{Bool.or(Bool.and(y2, True{}), False{}), WCon{Bool.or(Bool.and(y3, True{}), False{}), WCon{Bool.or(Bool.and(y4, False{}), False{}), WCon{Bool.or(Bool.and(y5, False{}), False{}), WCon{Bool.or(Bool.and(y6, False{}), False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  {==}

def idx4(+z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool) -> {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}:
  %and_t(z0) : {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{_, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(z1) : {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{Bool.and(z0, True{}), WCon{_, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(z2) : {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{Bool.and(z0, True{}), WCon{Bool.and(z1, True{}), WCon{_, WCon{z3, WCon{z4, WCon{z5, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(z3) : {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{Bool.and(z0, True{}), WCon{Bool.and(z1, True{}), WCon{Bool.and(z2, True{}), WCon{_, WCon{z4, WCon{z5, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(z4) : {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{Bool.and(z0, True{}), WCon{Bool.and(z1, True{}), WCon{Bool.and(z2, True{}), WCon{Bool.and(z3, True{}), WCon{_, WCon{z5, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(z5) : {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{Bool.and(z0, True{}), WCon{Bool.and(z1, True{}), WCon{Bool.and(z2, True{}), WCon{Bool.and(z3, True{}), WCon{Bool.and(z4, True{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(z6) : {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{Bool.and(z0, True{}), WCon{Bool.and(z1, True{}), WCon{Bool.and(z2, True{}), WCon{Bool.and(z3, True{}), WCon{Bool.and(z4, True{}), WCon{Bool.and(z5, True{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(z7) : {(B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32) == U32{WCon{Bool.and(z0, True{}), WCon{Bool.and(z1, True{}), WCon{Bool.and(z2, True{}), WCon{Bool.and(z3, True{}), WCon{Bool.and(z4, True{}), WCon{Bool.and(z5, True{}), WCon{Bool.and(z6, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  {==}

def idx2p(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool) -> {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{x0, WCon{x1, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}:
  %and_t(x0) : {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{_, WCon{x1, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(x1) : {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{Bool.and(x0, True{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(x2) : {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{Bool.and(x0, True{}), WCon{Bool.and(x1, True{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(x3) : {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{Bool.and(x0, True{}), WCon{Bool.and(x1, True{}), WCon{Bool.and(x2, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(x4) : {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{Bool.and(x0, True{}), WCon{Bool.and(x1, True{}), WCon{Bool.and(x2, False{}), WCon{Bool.and(x3, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(x5) : {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{Bool.and(x0, True{}), WCon{Bool.and(x1, True{}), WCon{Bool.and(x2, False{}), WCon{Bool.and(x3, False{}), WCon{Bool.and(x4, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(x6) : {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{Bool.and(x0, True{}), WCon{Bool.and(x1, True{}), WCon{Bool.and(x2, False{}), WCon{Bool.and(x3, False{}), WCon{Bool.and(x4, False{}), WCon{Bool.and(x5, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(x7) : {((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{Bool.and(x0, True{}), WCon{Bool.and(x1, True{}), WCon{Bool.and(x2, False{}), WCon{Bool.and(x3, False{}), WCon{Bool.and(x4, False{}), WCon{Bool.and(x5, False{}), WCon{Bool.and(x6, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  {==}

def idx3p(+y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +y6: Bool, +y7: Bool) -> {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}:
  %and_t(y0) : {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{_, WCon{y1, WCon{y2, WCon{y3, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(y1) : {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{Bool.and(y0, True{}), WCon{_, WCon{y2, WCon{y3, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(y2) : {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{Bool.and(y0, True{}), WCon{Bool.and(y1, True{}), WCon{_, WCon{y3, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_t(y3) : {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{Bool.and(y0, True{}), WCon{Bool.and(y1, True{}), WCon{Bool.and(y2, True{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(y4) : {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{Bool.and(y0, True{}), WCon{Bool.and(y1, True{}), WCon{Bool.and(y2, True{}), WCon{Bool.and(y3, True{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(y5) : {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{Bool.and(y0, True{}), WCon{Bool.and(y1, True{}), WCon{Bool.and(y2, True{}), WCon{Bool.and(y3, True{}), WCon{Bool.and(y4, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(y6) : {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{Bool.and(y0, True{}), WCon{Bool.and(y1, True{}), WCon{Bool.and(y2, True{}), WCon{Bool.and(y3, True{}), WCon{Bool.and(y4, False{}), WCon{Bool.and(y5, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %and_f(y7) : {((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32) == U32{WCon{False{}, WCon{False{}, WCon{Bool.and(y0, True{}), WCon{Bool.and(y1, True{}), WCon{Bool.and(y2, True{}), WCon{Bool.and(y3, True{}), WCon{Bool.and(y4, False{}), WCon{Bool.and(y5, False{}), WCon{Bool.and(y6, False{}), WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  {==}

def vi2(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool, +y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +y6: Bool, +y7: Bool) -> {B64.value(B64.char.code(((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32))) == w6(y4, y5, y6, y7, x0, x1) : U32}:
  Equal.trans(U32, B64.value(B64.char.code(((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32))), B64.value(B64.char.code(w6(y4, y5, y6, y7, x0, x1))), w6(y4, y5, y6, y7, x0, x1),
    Equal.cong(U32, U32, i => B64.value(B64.char.code(i)), ((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32), w6(y4, y5, y6, y7, x0, x1), idx2(x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7)),
    vc(y4, y5, y6, y7, x0, x1))

def vi3(+y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +y6: Bool, +y7: Bool, +z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool) -> {B64.value(B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32))) == w6(z6, z7, y0, y1, y2, y3) : U32}:
  Equal.trans(U32, B64.value(B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32))), B64.value(B64.char.code(w6(z6, z7, y0, y1, y2, y3))), w6(z6, z7, y0, y1, y2, y3),
    Equal.cong(U32, U32, i => B64.value(B64.char.code(i)), ((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32), w6(z6, z7, y0, y1, y2, y3), idx3(y0, y1, y2, y3, y4, y5, y6, y7, z0, z1, z2, z3, z4, z5, z6, z7)),
    vc(z6, z7, y0, y1, y2, y3))

def vi4(+z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool) -> {B64.value(B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32))) == w6(z0, z1, z2, z3, z4, z5) : U32}:
  Equal.trans(U32, B64.value(B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32))), B64.value(B64.char.code(w6(z0, z1, z2, z3, z4, z5))), w6(z0, z1, z2, z3, z4, z5),
    Equal.cong(U32, U32, i => B64.value(B64.char.code(i)), (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32), w6(z0, z1, z2, z3, z4, z5), idx4(z0, z1, z2, z3, z4, z5, z6, z7)),
    vc(z0, z1, z2, z3, z4, z5))

def vi2p(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool) -> {B64.value(B64.char.code(((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32))) == w6(False{}, False{}, False{}, False{}, x0, x1) : U32}:
  Equal.trans(U32, B64.value(B64.char.code(((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32))), B64.value(B64.char.code(w6(False{}, False{}, False{}, False{}, x0, x1))), w6(False{}, False{}, False{}, False{}, x0, x1),
    Equal.cong(U32, U32, i => B64.value(B64.char.code(i)), ((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32), w6(False{}, False{}, False{}, False{}, x0, x1), idx2p(x0, x1, x2, x3, x4, x5, x6, x7)),
    vc(False{}, False{}, False{}, False{}, x0, x1))

def vi3p(+y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +y6: Bool, +y7: Bool) -> {B64.value(B64.char.code(((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32))) == w6(False{}, False{}, y0, y1, y2, y3) : U32}:
  Equal.trans(U32, B64.value(B64.char.code(((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32))), B64.value(B64.char.code(w6(False{}, False{}, y0, y1, y2, y3))), w6(False{}, False{}, y0, y1, y2, y3),
    Equal.cong(U32, U32, i => B64.value(B64.char.code(i)), ((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32), w6(False{}, False{}, y0, y1, y2, y3), idx3p(y0, y1, y2, y3, y4, y5, y6, y7)),
    vc(False{}, False{}, y0, y1, y2, y3))

def vi1(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool) -> {B64.value(B64.char.code((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) >> 2n : U32))) == w6(x2, x3, x4, x5, x6, x7) : U32}:
  vc(x2, x3, x4, x5, x6, x7)

def block3(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool, +y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +y6: Bool, +y7: Bool, +z0: Bool, +z1: Bool, +z2: Bool, +z3: Bool, +z4: Bool, +z5: Bool, +z6: Bool, +z7: Bool, r: String, ih: {B64.decode(B64.encode(r)) == Some{r} : Maybe<&2, String>})
  -> {B64.decode(B64.encode(SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SCon{Chr{B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7)}, r}}})) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SCon{Chr{B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7)}, r}}}} : Maybe<&2, String>}:
  %Equal.sym(Maybe<&2, String>, B64.decode(B64.encode(r)), Some{r}, ih) : {B64.quad(B64.value(B64.char.code((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) >> 2n : U32))), B64.value(B64.char.code(((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32))), B64.value(B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32))), B64.value(B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32))), B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32)), B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32)), String.is_empty(B64.encode(r)), _) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SCon{Chr{B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7)}, r}}}} : Maybe<&2, String>}
  %Equal.sym(U32, B64.value(B64.char.code((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) >> 2n : U32))), w6(x2, x3, x4, x5, x6, x7), vi1(x0, x1, x2, x3, x4, x5, x6, x7)) : {B64.quad(_, B64.value(B64.char.code(((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32))), B64.value(B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32))), B64.value(B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32))), B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32)), B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32)), String.is_empty(B64.encode(r)), Some{r}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SCon{Chr{B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7)}, r}}}} : Maybe<&2, String>}
  %Equal.sym(U32, B64.value(B64.char.code(((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32))), w6(y4, y5, y6, y7, x0, x1), vi2(x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7)) : {B64.quad(w6(x2, x3, x4, x5, x6, x7), _, B64.value(B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32))), B64.value(B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32))), B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32)), B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32)), String.is_empty(B64.encode(r)), Some{r}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SCon{Chr{B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7)}, r}}}} : Maybe<&2, String>}
  %Equal.sym(U32, B64.value(B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32))), w6(z6, z7, y0, y1, y2, y3), vi3(y0, y1, y2, y3, y4, y5, y6, y7, z0, z1, z2, z3, z4, z5, z6, z7)) : {B64.quad(w6(x2, x3, x4, x5, x6, x7), w6(y4, y5, y6, y7, x0, x1), _, B64.value(B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32))), B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32)), B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32)), String.is_empty(B64.encode(r)), Some{r}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SCon{Chr{B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7)}, r}}}} : Maybe<&2, String>}
  %Equal.sym(U32, B64.value(B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32))), w6(z0, z1, z2, z3, z4, z5), vi4(z0, z1, z2, z3, z4, z5, z6, z7)) : {B64.quad(w6(x2, x3, x4, x5, x6, x7), w6(y4, y5, y6, y7, x0, x1), w6(z6, z7, y0, y1, y2, y3), _, B64.char.code(((((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)) .&. 15) << 2n) .|. (B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) >> 6n) : U32)), B64.char.code((B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7) .&. 63 : U32)), String.is_empty(B64.encode(r)), Some{r}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SCon{Chr{B64.mk8(z0, z1, z2, z3, z4, z5, z6, z7)}, r}}}} : Maybe<&2, String>}
  {==}

def block2(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool, +y0: Bool, +y1: Bool, +y2: Bool, +y3: Bool, +y4: Bool, +y5: Bool, +y6: Bool, +y7: Bool)
  -> {B64.decode(B64.encode(SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SNil{}}})) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SNil{}}}} : Maybe<&2, String>}:
  %Equal.sym(U32, B64.value(B64.char.code((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) >> 2n : U32))), w6(x2, x3, x4, x5, x6, x7), vi1(x0, x1, x2, x3, x4, x5, x6, x7)) : {B64.quad(_, B64.value(B64.char.code(((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32))), B64.value(B64.char.code(((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32))), B64.value(61), B64.char.code(((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32)), 61, True{}, Some{""}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SNil{}}}} : Maybe<&2, String>}
  %Equal.sym(U32, B64.value(B64.char.code(((((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)) .&. 3) << 4n) .|. (B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) >> 4n) : U32))), w6(y4, y5, y6, y7, x0, x1), vi2(x0, x1, x2, x3, x4, x5, x6, x7, y0, y1, y2, y3, y4, y5, y6, y7)) : {B64.quad(w6(x2, x3, x4, x5, x6, x7), _, B64.value(B64.char.code(((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32))), B64.value(61), B64.char.code(((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32)), 61, True{}, Some{""}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SNil{}}}} : Maybe<&2, String>}
  %Equal.sym(U32, B64.value(B64.char.code(((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32))), w6(False{}, False{}, y0, y1, y2, y3), vi3p(y0, y1, y2, y3, y4, y5, y6, y7)) : {B64.quad(w6(x2, x3, x4, x5, x6, x7), w6(y4, y5, y6, y7, x0, x1), _, B64.value(61), B64.char.code(((B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7) .&. 15) << 2n : U32)), 61, True{}, Some{""}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SCon{Chr{B64.mk8(y0, y1, y2, y3, y4, y5, y6, y7)}, SNil{}}}} : Maybe<&2, String>}
  {==}

def block1(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, +x5: Bool, +x6: Bool, +x7: Bool)
  -> {B64.decode(B64.encode(SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SNil{}})) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SNil{}}} : Maybe<&2, String>}:
  %Equal.sym(U32, B64.value(B64.char.code((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) >> 2n : U32))), w6(x2, x3, x4, x5, x6, x7), vi1(x0, x1, x2, x3, x4, x5, x6, x7)) : {B64.quad(_, B64.value(B64.char.code(((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32))), B64.value(61), B64.value(61), 61, 61, True{}, Some{""}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SNil{}}} : Maybe<&2, String>}
  %Equal.sym(U32, B64.value(B64.char.code(((B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7) .&. 3) << 4n : U32))), w6(False{}, False{}, False{}, False{}, x0, x1), vi2p(x0, x1, x2, x3, x4, x5, x6, x7)) : {B64.quad(w6(x2, x3, x4, x5, x6, x7), _, B64.value(61), B64.value(61), 61, 61, True{}, Some{""}) == Some{SCon{Chr{B64.mk8(x0, x1, x2, x3, x4, x5, x6, x7)}, SNil{}}} : Maybe<&2, String>}
  {==}

def sub_byte(+a: U32, h: {U32.is_lt(a, 256) == True{} : Bool}) -> {ub(a) == a : U32}:
  Equal.sym(U32, a, ub(a), byte_eq(a, h))

def decode_enc(s: String, +h: {L.bytes(s) == True{} : Bool}) -> {B64.decode(B64.encode(s)) == Some{s} : Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c0, r1}:
      match c0:
        case Chr{+a}:
          match r1:
            case SNil{}:
              +ha = and_l(U32.is_lt(a, 256), L.bytes(SNil{}), h)
              %sub_byte(a, ha) : {B64.decode(B64.encode(SCon{Chr{_}, SNil{}})) == Some{SCon{Chr{_}, SNil{}}} : Maybe<&2, String>}
              block1(pb0(a), pb1(a), pb2(a), pb3(a), pb4(a), pb5(a), pb6(a), pb7(a))
            case SCon{c1, r2}:
              match c1:
                case Chr{+b}:
                  match r2:
                    case SNil{}:
                      +ha = and_l(U32.is_lt(a, 256), L.bytes(SCon{Chr{b}, SNil{}}), h)
                      +h1 = and_r(U32.is_lt(a, 256), L.bytes(SCon{Chr{b}, SNil{}}), h)
                      +hb = and_l(U32.is_lt(b, 256), L.bytes(SNil{}), h1)
                      %sub_byte(a, ha) : {B64.decode(B64.encode(SCon{Chr{_}, SCon{Chr{b}, SNil{}}})) == Some{SCon{Chr{_}, SCon{Chr{b}, SNil{}}}} : Maybe<&2, String>}
                      %sub_byte(b, hb) : {B64.decode(B64.encode(SCon{Chr{ub(a)}, SCon{Chr{_}, SNil{}}})) == Some{SCon{Chr{ub(a)}, SCon{Chr{_}, SNil{}}}} : Maybe<&2, String>}
                      block2(pb0(a), pb1(a), pb2(a), pb3(a), pb4(a), pb5(a), pb6(a), pb7(a), pb0(b), pb1(b), pb2(b), pb3(b), pb4(b), pb5(b), pb6(b), pb7(b))
                    case SCon{c2, +r3}:
                      match c2:
                        case Chr{+c}:
                          +ha = and_l(U32.is_lt(a, 256), L.bytes(SCon{Chr{b}, SCon{Chr{c}, r3}}), h)
                          +h1 = and_r(U32.is_lt(a, 256), L.bytes(SCon{Chr{b}, SCon{Chr{c}, r3}}), h)
                          +hb = and_l(U32.is_lt(b, 256), L.bytes(SCon{Chr{c}, r3}), h1)
                          +h2 = and_r(U32.is_lt(b, 256), L.bytes(SCon{Chr{c}, r3}), h1)
                          +hc = and_l(U32.is_lt(c, 256), L.bytes(r3), h2)
                          +h3 = and_r(U32.is_lt(c, 256), L.bytes(r3), h2)
                          %sub_byte(a, ha) : {B64.decode(B64.encode(SCon{Chr{_}, SCon{Chr{b}, SCon{Chr{c}, r3}}})) == Some{SCon{Chr{_}, SCon{Chr{b}, SCon{Chr{c}, r3}}}} : Maybe<&2, String>}
                          %sub_byte(b, hb) : {B64.decode(B64.encode(SCon{Chr{ub(a)}, SCon{Chr{_}, SCon{Chr{c}, r3}}})) == Some{SCon{Chr{ub(a)}, SCon{Chr{_}, SCon{Chr{c}, r3}}}} : Maybe<&2, String>}
                          %sub_byte(c, hc) : {B64.decode(B64.encode(SCon{Chr{ub(a)}, SCon{Chr{ub(b)}, SCon{Chr{_}, r3}}})) == Some{SCon{Chr{ub(a)}, SCon{Chr{ub(b)}, SCon{Chr{_}, r3}}}} : Maybe<&2, String>}
                          block3(pb0(a), pb1(a), pb2(a), pb3(a), pb4(a), pb5(a), pb6(a), pb7(a), pb0(b), pb1(b), pb2(b), pb3(b), pb4(b), pb5(b), pb6(b), pb7(b), pb0(c), pb1(c), pb2(c), pb3(c), pb4(c), pb5(c), pb6(c), pb7(c), r3, decode_enc(r3, h3))

def L.b64_decode(s, h):
  decode_enc(s, h)


# ---------------------------------------------------------------------
# JSON reading: generic lemmas
# ---------------------------------------------------------------------

def not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, no_ft(h))

def or_l(p: Bool, -q: Bool, h: {Bool.or(p, q) == False{} : Bool}) -> {p == False{} : Bool}:
  match p:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, no_tf(h))

def or_r(p: Bool, -q: Bool, h: {Bool.or(p, q) == False{} : Bool}) -> {q == False{} : Bool}:
  match p:
    case False{}:
      h
    case True{}:
      Empty.absurd({q == False{} : Bool}, no_tf(h))

# Word.cmp decides equality
def fin_eq_t(t: Cmp, -ah: Bool, -bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, no_ft(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, no_ft(h))

def fin_eq_h(t: Cmp, ah: Bool, bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {ah == bh : Bool}:
  match t:
    case LT{}:
      Empty.absurd({ah == bh : Bool}, no_ft(h))
    case GT{}:
      Empty.absurd({ah == bh : Bool}, no_ft(h))
    case EQ{}:
      match ah bh:
        case False{} False{}:
          {==}
        case True{} True{}:
          {==}
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, no_ft(h))
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, no_ft(h))

def weq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          %weq(p, at, bt, Equal.cong(Cmp, Bool, Cmp.is_eq, Word.cmp(p, at, bt), EQ{}, fin_eq_t(Word.cmp(p, at, bt), ah, bh, h)))
            : {WCon{ah, at} == WCon{bh, _} : Word(1n+p)}
          %fin_eq_h(Word.cmp(p, at, bt), ah, bh, h) : {WCon{ah, at} == WCon{_, at} : Word(1n+p)}
          {==}

def u32_eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      %weq(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

# ---------------------------------------------------------------------
# JSON reading: which branch of utf8_len a string takes
# ---------------------------------------------------------------------

def cd1(+s: String) -> Bool:
  U32.is_lt(Json.byte_at(s, 0n), 128)

def cd2(+s: String) -> Bool:
  Bool.and(Json.in_range32(Json.byte_at(s, 0n), 194, 223), Json.cont(s, 1n))

def cd3(+s: String) -> Bool:
  Bool.and(U32.is_eq(Json.byte_at(s, 0n), 224), Bool.and(Json.in_range32(Json.byte_at(s, 1n), 160, 191), Json.cont(s, 2n)))

def cd4(+s: String) -> Bool:
  Bool.and(Bool.or(Json.in_range32(Json.byte_at(s, 0n), 225, 236), Json.in_range32(Json.byte_at(s, 0n), 238, 239)), Bool.and(Json.cont(s, 1n), Json.cont(s, 2n)))

def cd5(+s: String) -> Bool:
  Bool.and(U32.is_eq(Json.byte_at(s, 0n), 237), Bool.and(Json.in_range32(Json.byte_at(s, 1n), 128, 159), Json.cont(s, 2n)))

def cd6(+s: String) -> Bool:
  Bool.and(U32.is_eq(Json.byte_at(s, 0n), 240), Bool.and(Json.in_range32(Json.byte_at(s, 1n), 144, 191), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n))))

def cd7(+s: String) -> Bool:
  Bool.and(Json.in_range32(Json.byte_at(s, 0n), 241, 243), Bool.and(Json.cont(s, 1n), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n))))

def cd8(+s: String) -> Bool:
  Bool.and(U32.is_eq(Json.byte_at(s, 0n), 244), Bool.and(Json.in_range32(Json.byte_at(s, 1n), 128, 143), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n))))

def len1(+s: String, e1: {cd1(s) == True{} : Bool}) -> {Json.utf8_len(s) == 1n : Nat}:
  %Equal.sym(Bool, cd1(s), True{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 1n : Nat}
  {==}

def len2(+s: String, e1: {cd1(s) == False{} : Bool}, e2: {cd2(s) == True{} : Bool}) -> {Json.utf8_len(s) == 2n : Nat}:
  %Equal.sym(Bool, cd1(s), False{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 2n : Nat}
  %Equal.sym(Bool, cd2(s), True{}, e2) : {Json.pick(Nat, _, 2n, Json.utf8_len.3(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 2n : Nat}
  {==}

def len3a(+s: String, e1: {cd1(s) == False{} : Bool}, e2: {cd2(s) == False{} : Bool}, e3: {cd3(s) == True{} : Bool}) -> {Json.utf8_len(s) == 3n : Nat}:
  %Equal.sym(Bool, cd1(s), False{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd2(s), False{}, e2) : {Json.pick(Nat, _, 2n, Json.utf8_len.3(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd3(s), True{}, e3) : {Json.pick(Nat, _, 3n, Json.utf8_len.4(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  {==}

def len3b(+s: String, e1: {cd1(s) == False{} : Bool}, e2: {cd2(s) == False{} : Bool}, e3: {cd3(s) == False{} : Bool}, e4: {cd4(s) == True{} : Bool}) -> {Json.utf8_len(s) == 3n : Nat}:
  %Equal.sym(Bool, cd1(s), False{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd2(s), False{}, e2) : {Json.pick(Nat, _, 2n, Json.utf8_len.3(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd3(s), False{}, e3) : {Json.pick(Nat, _, 3n, Json.utf8_len.4(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd4(s), True{}, e4) : {Json.pick(Nat, _, 3n, Json.utf8_len.5(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  {==}

def len3c(+s: String, e1: {cd1(s) == False{} : Bool}, e2: {cd2(s) == False{} : Bool}, e3: {cd3(s) == False{} : Bool}, e4: {cd4(s) == False{} : Bool}, e5: {cd5(s) == True{} : Bool}) -> {Json.utf8_len(s) == 3n : Nat}:
  %Equal.sym(Bool, cd1(s), False{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd2(s), False{}, e2) : {Json.pick(Nat, _, 2n, Json.utf8_len.3(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd3(s), False{}, e3) : {Json.pick(Nat, _, 3n, Json.utf8_len.4(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd4(s), False{}, e4) : {Json.pick(Nat, _, 3n, Json.utf8_len.5(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  %Equal.sym(Bool, cd5(s), True{}, e5) : {Json.pick(Nat, _, 3n, Json.utf8_len.6(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 3n : Nat}
  {==}

def len4a(+s: String, e1: {cd1(s) == False{} : Bool}, e2: {cd2(s) == False{} : Bool}, e3: {cd3(s) == False{} : Bool}, e4: {cd4(s) == False{} : Bool}, e5: {cd5(s) == False{} : Bool}, e6: {cd6(s) == True{} : Bool}) -> {Json.utf8_len(s) == 4n : Nat}:
  %Equal.sym(Bool, cd1(s), False{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd2(s), False{}, e2) : {Json.pick(Nat, _, 2n, Json.utf8_len.3(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd3(s), False{}, e3) : {Json.pick(Nat, _, 3n, Json.utf8_len.4(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd4(s), False{}, e4) : {Json.pick(Nat, _, 3n, Json.utf8_len.5(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd5(s), False{}, e5) : {Json.pick(Nat, _, 3n, Json.utf8_len.6(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd6(s), True{}, e6) : {Json.pick(Nat, _, 4n, Json.utf8_len.7(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  {==}

def len4b(+s: String, e1: {cd1(s) == False{} : Bool}, e2: {cd2(s) == False{} : Bool}, e3: {cd3(s) == False{} : Bool}, e4: {cd4(s) == False{} : Bool}, e5: {cd5(s) == False{} : Bool}, e6: {cd6(s) == False{} : Bool}, e7: {cd7(s) == True{} : Bool}) -> {Json.utf8_len(s) == 4n : Nat}:
  %Equal.sym(Bool, cd1(s), False{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd2(s), False{}, e2) : {Json.pick(Nat, _, 2n, Json.utf8_len.3(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd3(s), False{}, e3) : {Json.pick(Nat, _, 3n, Json.utf8_len.4(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd4(s), False{}, e4) : {Json.pick(Nat, _, 3n, Json.utf8_len.5(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd5(s), False{}, e5) : {Json.pick(Nat, _, 3n, Json.utf8_len.6(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd6(s), False{}, e6) : {Json.pick(Nat, _, 4n, Json.utf8_len.7(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd7(s), True{}, e7) : {Json.pick(Nat, _, 4n, Json.utf8_len.8(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  {==}

def len4c(+s: String, e1: {cd1(s) == False{} : Bool}, e2: {cd2(s) == False{} : Bool}, e3: {cd3(s) == False{} : Bool}, e4: {cd4(s) == False{} : Bool}, e5: {cd5(s) == False{} : Bool}, e6: {cd6(s) == False{} : Bool}, e7: {cd7(s) == False{} : Bool}, e8: {cd8(s) == True{} : Bool}) -> {Json.utf8_len(s) == 4n : Nat}:
  %Equal.sym(Bool, cd1(s), False{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd2(s), False{}, e2) : {Json.pick(Nat, _, 2n, Json.utf8_len.3(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd3(s), False{}, e3) : {Json.pick(Nat, _, 3n, Json.utf8_len.4(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd4(s), False{}, e4) : {Json.pick(Nat, _, 3n, Json.utf8_len.5(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd5(s), False{}, e5) : {Json.pick(Nat, _, 3n, Json.utf8_len.6(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd6(s), False{}, e6) : {Json.pick(Nat, _, 4n, Json.utf8_len.7(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd7(s), False{}, e7) : {Json.pick(Nat, _, 4n, Json.utf8_len.8(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 4n : Nat}
  %Equal.sym(Bool, cd8(s), True{}, e8) : {Json.pick(Nat, _, 4n, 0n) == 4n : Nat}
  {==}

def len0(+s: String, e1: {cd1(s) == False{} : Bool}, e2: {cd2(s) == False{} : Bool}, e3: {cd3(s) == False{} : Bool}, e4: {cd4(s) == False{} : Bool}, e5: {cd5(s) == False{} : Bool}, e6: {cd6(s) == False{} : Bool}, e7: {cd7(s) == False{} : Bool}, e8: {cd8(s) == False{} : Bool}) -> {Json.utf8_len(s) == 0n : Nat}:
  %Equal.sym(Bool, cd1(s), False{}, e1) : {Json.pick(Nat, _, 1n, Json.utf8_len.2(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 0n : Nat}
  %Equal.sym(Bool, cd2(s), False{}, e2) : {Json.pick(Nat, _, 2n, Json.utf8_len.3(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 0n : Nat}
  %Equal.sym(Bool, cd3(s), False{}, e3) : {Json.pick(Nat, _, 3n, Json.utf8_len.4(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 0n : Nat}
  %Equal.sym(Bool, cd4(s), False{}, e4) : {Json.pick(Nat, _, 3n, Json.utf8_len.5(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 0n : Nat}
  %Equal.sym(Bool, cd5(s), False{}, e5) : {Json.pick(Nat, _, 3n, Json.utf8_len.6(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 0n : Nat}
  %Equal.sym(Bool, cd6(s), False{}, e6) : {Json.pick(Nat, _, 4n, Json.utf8_len.7(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 0n : Nat}
  %Equal.sym(Bool, cd7(s), False{}, e7) : {Json.pick(Nat, _, 4n, Json.utf8_len.8(Json.byte_at(s, 0n), Json.byte_at(s, 1n), Json.cont(s, 1n), Json.cont(s, 2n), Json.cont(s, 3n))) == 0n : Nat}
  %Equal.sym(Bool, cd8(s), False{}, e8) : {Json.pick(Nat, _, 4n, 0n) == 0n : Nat}
  {==}


# ---------------------------------------------------------------------
# JSON reading: one ASCII byte, escaped and read back
# ---------------------------------------------------------------------

def jgoal_a(+k: U32, +X: String) -> Type:
  {Json.unit(Json.esc_ascii(k) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}

def z27() -> Word(27n):
  WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def w5(+t0: Bool, +t1: Bool, +t2: Bool, +t3: Bool, +t4: Bool) -> U32:
  U32{WCon{t0, WCon{t1, WCon{t2, WCon{t3, WCon{t4, z27()}}}}}}

def u5(+a: U32) -> U32:
  w5(pb0(a), pb1(a), pb2(a), pb3(a), pb4(a))

def nlt5(+x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool) -> {U32.is_lt(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 32) == False{} : Bool}:
  fin_nlt(x0, Word.cmp.fin(x1, False{}, Word.cmp.fin(x2, False{}, Word.cmp.fin(x3, False{}, Word.cmp.fin(x4, False{}, EQ{})))), fin_nlt(x1, Word.cmp.fin(x2, False{}, Word.cmp.fin(x3, False{}, Word.cmp.fin(x4, False{}, EQ{}))), fin_nlt(x2, Word.cmp.fin(x3, False{}, Word.cmp.fin(x4, False{}, EQ{})), fin_nlt(x3, Word.cmp.fin(x4, False{}, EQ{}), fin_nlt(x4, EQ{}, {==})))))

def k5_eq.go(w32: Word(0n), +x31: Bool, +x30: Bool, +x29: Bool, +x28: Bool, +x27: Bool, +x26: Bool, +x25: Bool, +x24: Bool, +x23: Bool, +x22: Bool, +x21: Bool, +x20: Bool, +x19: Bool, +x18: Bool, +x17: Bool, +x16: Bool, +x15: Bool, +x14: Bool, +x13: Bool, +x12: Bool, +x11: Bool, +x10: Bool, +x9: Bool, +x8: Bool, +x7: Bool, +x6: Bool, +x5: Bool, +x0: Bool, +x1: Bool, +x2: Bool, +x3: Bool, +x4: Bool, h: {U32.is_lt(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, w32}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 32) == True{} : Bool}) -> {U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, w32}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, w32}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}:
  match w32:
    case WNil{}:
      match x31:
        case True{}:
          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{True{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
        case False{}:
          match x30:
            case True{}:
              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{True{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
            case False{}:
              match x29:
                case True{}:
                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                case False{}:
                  match x28:
                    case True{}:
                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                    case False{}:
                      match x27:
                        case True{}:
                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                        case False{}:
                          match x26:
                            case True{}:
                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                            case False{}:
                              match x25:
                                case True{}:
                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                case False{}:
                                  match x24:
                                    case True{}:
                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                    case False{}:
                                      match x23:
                                        case True{}:
                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                        case False{}:
                                          match x22:
                                            case True{}:
                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                            case False{}:
                                              match x21:
                                                case True{}:
                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                case False{}:
                                                  match x20:
                                                    case True{}:
                                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                    case False{}:
                                                      match x19:
                                                        case True{}:
                                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                        case False{}:
                                                          match x18:
                                                            case True{}:
                                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                            case False{}:
                                                              match x17:
                                                                case True{}:
                                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                case False{}:
                                                                  match x16:
                                                                    case True{}:
                                                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                    case False{}:
                                                                      match x15:
                                                                        case True{}:
                                                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                        case False{}:
                                                                          match x14:
                                                                            case True{}:
                                                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                            case False{}:
                                                                              match x13:
                                                                                case True{}:
                                                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                case False{}:
                                                                                  match x12:
                                                                                    case True{}:
                                                                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                    case False{}:
                                                                                      match x11:
                                                                                        case True{}:
                                                                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                        case False{}:
                                                                                          match x10:
                                                                                            case True{}:
                                                                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                            case False{}:
                                                                                              match x9:
                                                                                                case True{}:
                                                                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                                case False{}:
                                                                                                  match x8:
                                                                                                    case True{}:
                                                                                                      Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                                    case False{}:
                                                                                                      match x7:
                                                                                                        case True{}:
                                                                                                          Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                                        case False{}:
                                                                                                          match x6:
                                                                                                            case True{}:
                                                                                                              Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(h))
                                                                                                            case False{}:
                                                                                                              match x5:
                                                                                                                case True{}:
                                                                                                                  Empty.absurd({U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == u5(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}, no_ft(Equal.trans(Bool, False{}, U32.is_lt(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 32), True{}, Equal.sym(Bool, U32.is_lt(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, 32), False{}, nlt5(x0, x1, x2, x3, x4)), h)))
                                                                                                                case False{}:
                                                                                                                  {==}

def k5_eq(a: U32, h: {U32.is_lt(a, 32) == True{} : Bool}) -> {a == u5(a) : U32}:
  match a:
    case U32{w0}:
      match w0:
        case WCon{x0, w1}:
          match w1:
            case WCon{x1, w2}:
              match w2:
                case WCon{x2, w3}:
                  match w3:
                    case WCon{x3, w4}:
                      match w4:
                        case WCon{x4, w5}:
                          match w5:
                            case WCon{x5, w6}:
                              match w6:
                                case WCon{x6, w7}:
                                  match w7:
                                    case WCon{x7, w8}:
                                      match w8:
                                        case WCon{x8, w9}:
                                          match w9:
                                            case WCon{x9, w10}:
                                              match w10:
                                                case WCon{x10, w11}:
                                                  match w11:
                                                    case WCon{x11, w12}:
                                                      match w12:
                                                        case WCon{x12, w13}:
                                                          match w13:
                                                            case WCon{x13, w14}:
                                                              match w14:
                                                                case WCon{x14, w15}:
                                                                  match w15:
                                                                    case WCon{x15, w16}:
                                                                      match w16:
                                                                        case WCon{x16, w17}:
                                                                          match w17:
                                                                            case WCon{x17, w18}:
                                                                              match w18:
                                                                                case WCon{x18, w19}:
                                                                                  match w19:
                                                                                    case WCon{x19, w20}:
                                                                                      match w20:
                                                                                        case WCon{x20, w21}:
                                                                                          match w21:
                                                                                            case WCon{x21, w22}:
                                                                                              match w22:
                                                                                                case WCon{x22, w23}:
                                                                                                  match w23:
                                                                                                    case WCon{x23, w24}:
                                                                                                      match w24:
                                                                                                        case WCon{x24, w25}:
                                                                                                          match w25:
                                                                                                            case WCon{x25, w26}:
                                                                                                              match w26:
                                                                                                                case WCon{x26, w27}:
                                                                                                                  match w27:
                                                                                                                    case WCon{x27, w28}:
                                                                                                                      match w28:
                                                                                                                        case WCon{x28, w29}:
                                                                                                                          match w29:
                                                                                                                            case WCon{x29, w30}:
                                                                                                                              match w30:
                                                                                                                                case WCon{x30, w31}:
                                                                                                                                  match w31:
                                                                                                                                    case WCon{x31, w32}:
                                                                                                                                      k5_eq.go(w32, x31, x30, x29, x28, x27, x26, x25, x24, x23, x22, x21, x20, x19, x18, x17, x16, x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x0, x1, x2, x3, x4, h)

def u00(+t0: Bool, +t1: Bool, +t2: Bool, +t3: Bool, +t4: Bool, +X: String)
  -> {Json.unit(("\\u00" ++ Json.hexd((w5(t0, t1, t2, t3, t4) >> 4n : U32)) ++ Json.hexd((w5(t0, t1, t2, t3, t4) .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{w5(t0, t1, t2, t3, t4)}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match t0:
    case False{}:
      match t1:
        case False{}:
          match t2:
            case False{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
                case True{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
            case True{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
                case True{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
        case True{}:
          match t2:
            case False{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
                case True{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
            case True{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
                case True{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
    case True{}:
      match t1:
        case False{}:
          match t2:
            case False{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
                case True{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
            case True{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
                case True{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
        case True{}:
          match t2:
            case False{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
                case True{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
            case True{}:
              match t3:
                case False{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}
                case True{}:
                  match t4:
                    case False{}:
                      {==}
                    case True{}:
                      {==}

# the control-byte branch: below 32 (five bits, 32 cases), or one of < > &
def asc_u_60(b: Bool, +k: U32, +X: String, +e: {U32.is_eq(k, 60) == b : Bool}, +h: {b == True{} : Bool})
  -> {Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(U32, k, 60, u32_eq(k, 60, e)) : {Json.unit(("\\u00" ++ Json.hexd((_ >> 4n : U32)) ++ Json.hexd((_ .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      Empty.absurd({Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}, no_ft(h))

# the control-byte branch: below 32 (five bits, 32 cases), or one of < > &
def asc_u_62(b: Bool, +k: U32, +X: String, +e: {U32.is_eq(k, 62) == b : Bool}, +h: {b == True{} : Bool})
  -> {Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(U32, k, 62, u32_eq(k, 62, e)) : {Json.unit(("\\u00" ++ Json.hexd((_ >> 4n : U32)) ++ Json.hexd((_ .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      Empty.absurd({Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}, no_ft(h))

# the control-byte branch: below 32 (five bits, 32 cases), or one of < > &
def asc_u_38(b: Bool, +k: U32, +X: String, +e: {U32.is_eq(k, 38) == b : Bool}, +h: {b == True{} : Bool})
  -> {Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(U32, k, 38, u32_eq(k, 38, e)) : {Json.unit(("\\u00" ++ Json.hexd((_ >> 4n : U32)) ++ Json.hexd((_ .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      Empty.absurd({Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}, no_ft(h))

def asc_u62(b: Bool, +k: U32, +X: String, +e: {U32.is_eq(k, 62) == b : Bool}, +h: {Bool.or(b, U32.is_eq(k, 38)) == True{} : Bool})
  -> {Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      asc_u_62(True{}, k, X, e, {==})
    case False{}:
      asc_u_38(U32.is_eq(k, 38), k, X, {==}, h)

def asc_u60(b: Bool, +k: U32, +X: String, +e: {U32.is_eq(k, 60) == b : Bool}, +h: {Bool.or(b, Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38))) == True{} : Bool})
  -> {Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      asc_u_60(True{}, k, X, e, {==})
    case False{}:
      asc_u62(U32.is_eq(k, 62), k, X, {==}, h)

def asc_u(b: Bool, +k: U32, +X: String, +e: {U32.is_lt(k, 32) == b : Bool}, +h: {Bool.or(b, Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))) == True{} : Bool})
  -> {Json.unit(("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(U32, k, u5(k), k5_eq(k, e)) : {Json.unit(("\\u00" ++ Json.hexd((_ >> 4n : U32)) ++ Json.hexd((_ .&. 15 : U32))) ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      u00(pb0(k), pb1(k), pb2(k), pb3(k), pb4(k), X)
    case False{}:
      asc_u60(U32.is_eq(k, 60), k, X, {==}, h)

def asc_raw(+k: U32, +X: String, +h128: {U32.is_lt(k, 128) == True{} : Bool}, +e34: {U32.is_eq(k, 34) == False{} : Bool},
            +e92: {U32.is_eq(k, 92) == False{} : Bool}, +e32: {U32.is_lt(k, 32) == False{} : Bool})
  -> {Json.unit(Json.str1(k) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k}, X}), 1n, len1(SCon{Chr{k}, X}, h128)) : {Json.unit.n(_, SCon{Chr{k}, X}) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
  %Equal.sym(Bool, U32.is_eq(k, 34), False{}, e34) : {Json.pick(Json.JU, _, Json.JU{"", X, Json.JsDone{}}, Json.unit.ascii.2(U32.is_eq(k, 92), k, X)) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
  %Equal.sym(Bool, U32.is_eq(k, 92), False{}, e92) : {Json.unit.ascii.2(_, k, X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
  %Equal.sym(Bool, U32.is_lt(k, 32), False{}, e32) : {Json.pick(Json.JU, _, Json.JU{"", X, Json.JsBad{}}, Json.JU{Json.str1(k), X, Json.JsMore{}}) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
  {==}

def asc_ctl(b: Bool, +k: U32, +X: String, +h128: {U32.is_lt(k, 128) == True{} : Bool}, +e34: {U32.is_eq(k, 34) == False{} : Bool},
            +e92: {U32.is_eq(k, 92) == False{} : Bool}, +e: {Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))) == b : Bool})
  -> {Json.unit(Json.esc_ascii.6(k) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(Bool, Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))), True{}, e) : {Json.unit(Json.pick(String, _, ("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))), Json.str1(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      asc_u(U32.is_lt(k, 32), k, X, {==}, e)
    case False{}:
      %Equal.sym(Bool, Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))), False{}, e) : {Json.unit(Json.pick(String, _, ("\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32))), Json.str1(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      asc_raw(k, X, h128, e34, e92, or_l(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38))), e))

def asc_9(b: Bool, +k: U32, +X: String, +h128: {U32.is_lt(k, 128) == True{} : Bool}, +e34: {U32.is_eq(k, 34) == False{} : Bool}, +e92: {U32.is_eq(k, 92) == False{} : Bool}, +e: {U32.is_eq(k, 9) == b : Bool})
  -> {Json.unit(Json.esc_ascii.5(k) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(k, 9), True{}, e) : {Json.unit(Json.pick(String, _, "\\t", Json.esc_ascii.6(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      %Equal.sym(U32, k, 9, u32_eq(k, 9, e)) : {Json.unit("\\t" ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(k, 9), False{}, e) : {Json.unit(Json.pick(String, _, "\\t", Json.esc_ascii.6(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      asc_ctl(Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))), k, X, h128, e34, e92, {==})

def asc_13(b: Bool, +k: U32, +X: String, +h128: {U32.is_lt(k, 128) == True{} : Bool}, +e34: {U32.is_eq(k, 34) == False{} : Bool}, +e92: {U32.is_eq(k, 92) == False{} : Bool}, +e: {U32.is_eq(k, 13) == b : Bool})
  -> {Json.unit(Json.esc_ascii.4(k) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(k, 13), True{}, e) : {Json.unit(Json.pick(String, _, "\\r", Json.esc_ascii.5(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      %Equal.sym(U32, k, 13, u32_eq(k, 13, e)) : {Json.unit("\\r" ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(k, 13), False{}, e) : {Json.unit(Json.pick(String, _, "\\r", Json.esc_ascii.5(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      asc_9(U32.is_eq(k, 9), k, X, h128, e34, e92, {==})

def asc_10(b: Bool, +k: U32, +X: String, +h128: {U32.is_lt(k, 128) == True{} : Bool}, +e34: {U32.is_eq(k, 34) == False{} : Bool}, +e92: {U32.is_eq(k, 92) == False{} : Bool}, +e: {U32.is_eq(k, 10) == b : Bool})
  -> {Json.unit(Json.esc_ascii.3(k) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(k, 10), True{}, e) : {Json.unit(Json.pick(String, _, "\\n", Json.esc_ascii.4(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      %Equal.sym(U32, k, 10, u32_eq(k, 10, e)) : {Json.unit("\\n" ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(k, 10), False{}, e) : {Json.unit(Json.pick(String, _, "\\n", Json.esc_ascii.4(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      asc_13(U32.is_eq(k, 13), k, X, h128, e34, e92, {==})

def asc_92(b: Bool, +k: U32, +X: String, +h128: {U32.is_lt(k, 128) == True{} : Bool}, +e34: {U32.is_eq(k, 34) == False{} : Bool}, +e: {U32.is_eq(k, 92) == b : Bool})
  -> {Json.unit(Json.esc_ascii.2(k) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(k, 92), True{}, e) : {Json.unit(Json.pick(String, _, "\\\\", Json.esc_ascii.3(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      %Equal.sym(U32, k, 92, u32_eq(k, 92, e)) : {Json.unit("\\\\" ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(k, 92), False{}, e) : {Json.unit(Json.pick(String, _, "\\\\", Json.esc_ascii.3(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      asc_10(U32.is_eq(k, 10), k, X, h128, e34, e, {==})

def asc_34(b: Bool, +k: U32, +X: String, +h128: {U32.is_lt(k, 128) == True{} : Bool}, +e: {U32.is_eq(k, 34) == b : Bool})
  -> {Json.unit(Json.esc_ascii(k) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(k, 34), True{}, e) : {Json.unit(Json.pick(String, _, "\\\"", Json.esc_ascii.2(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      %Equal.sym(U32, k, 34, u32_eq(k, 34, e)) : {Json.unit("\\\"" ++ X) == Json.JU{SCon{Chr{_}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(k, 34), False{}, e) : {Json.unit(Json.pick(String, _, "\\\"", Json.esc_ascii.2(k)) ++ X) == Json.JU{SCon{Chr{k}, SNil{}}, X, Json.JsMore{}} : Json.JU}
      asc_92(U32.is_eq(k, 92), k, X, h128, e, {==})

def asc(+k: U32, +X: String, +h128: {U32.is_lt(k, 128) == True{} : Bool}) -> jgoal_a(k, X):
  asc_34(U32.is_eq(k, 34), k, X, h128, {==})


# ---------------------------------------------------------------------
# JSON reading: one unit of the escaped text reads back as the bytes it
# came from
# ---------------------------------------------------------------------

def take0(t: String) -> {String.take(t, 0n) == "" : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, r}:
      {==}

def ugoal(+s: String, +X: String) -> Type:
  {Json.unit(Json.esc_head(s) ++ X) == Json.JU{Json.taken(Json.utf8_len(s), s), X, Json.JsMore{}} : Json.JU}

# the continuation bytes a branch of utf8_len asks for
def c2_of_3(+s: String, +e: {cd3(s) == True{} : Bool}) -> {Json.cont(s, 2n) == True{} : Bool}:
  and_r(Json.in_range32(Json.byte_at(s, 1n), 160, 191), Json.cont(s, 2n), and_r(U32.is_eq(Json.byte_at(s, 0n), 224), Bool.and(Json.in_range32(Json.byte_at(s, 1n), 160, 191), Json.cont(s, 2n)), e))

def c2_of_4(+s: String, +e: {cd4(s) == True{} : Bool}) -> {Json.cont(s, 2n) == True{} : Bool}:
  and_r(Json.cont(s, 1n), Json.cont(s, 2n), and_r(Bool.or(Json.in_range32(Json.byte_at(s, 0n), 225, 236), Json.in_range32(Json.byte_at(s, 0n), 238, 239)), Bool.and(Json.cont(s, 1n), Json.cont(s, 2n)), e))

def c2_of_5(+s: String, +e: {cd5(s) == True{} : Bool}) -> {Json.cont(s, 2n) == True{} : Bool}:
  and_r(Json.in_range32(Json.byte_at(s, 1n), 128, 159), Json.cont(s, 2n), and_r(U32.is_eq(Json.byte_at(s, 0n), 237), Bool.and(Json.in_range32(Json.byte_at(s, 1n), 128, 159), Json.cont(s, 2n)), e))

def c3_of_6(+s: String, +e: {cd6(s) == True{} : Bool}) -> {Json.cont(s, 3n) == True{} : Bool}:
  and_r(Json.cont(s, 2n), Json.cont(s, 3n), and_r(Json.in_range32(Json.byte_at(s, 1n), 144, 191), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n)), and_r(U32.is_eq(Json.byte_at(s, 0n), 240), Bool.and(Json.in_range32(Json.byte_at(s, 1n), 144, 191), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n))), e)))

def c3_of_7(+s: String, +e: {cd7(s) == True{} : Bool}) -> {Json.cont(s, 3n) == True{} : Bool}:
  and_r(Json.cont(s, 2n), Json.cont(s, 3n), and_r(Json.cont(s, 1n), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n)), and_r(Json.in_range32(Json.byte_at(s, 0n), 241, 243), Bool.and(Json.cont(s, 1n), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n))), e)))

def c3_of_8(+s: String, +e: {cd8(s) == True{} : Bool}) -> {Json.cont(s, 3n) == True{} : Bool}:
  and_r(Json.cont(s, 2n), Json.cont(s, 3n), and_r(Json.in_range32(Json.byte_at(s, 1n), 128, 143), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n)), and_r(U32.is_eq(Json.byte_at(s, 0n), 244), Bool.and(Json.in_range32(Json.byte_at(s, 1n), 128, 143), Bool.and(Json.cont(s, 2n), Json.cont(s, 3n))), e)))

def lsep(b: Bool, +k2: U32, +X: String, +e: {U32.is_eq(k2, 168) == b : Bool}, +h: {Bool.or(b, U32.is_eq(k2, 169)) == True{} : Bool})
  -> {Json.unit(("\\u202" ++ Json.esc_sep(k2)) ++ X) == Json.JU{SCon{Chr{226}, SCon{Chr{128}, SCon{Chr{k2}, SNil{}}}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      %Equal.sym(U32, k2, 168, u32_eq(k2, 168, e))
        : {Json.unit(("\\u202" ++ Json.esc_sep(_)) ++ X) == Json.JU{SCon{Chr{226}, SCon{Chr{128}, SCon{Chr{_}, SNil{}}}}, X, Json.JsMore{}} : Json.JU}
      {==}
    case False{}:
      %Equal.sym(U32, k2, 169, u32_eq(k2, 169, h))
        : {Json.unit(("\\u202" ++ Json.esc_sep(_)) ++ X) == Json.JU{SCon{Chr{226}, SCon{Chr{128}, SCon{Chr{_}, SNil{}}}}, X, Json.JsMore{}} : Json.JU}
      {==}

# a three-byte sequence: U+2028 and U+2029 come back from their escapes,
# the rest is copied
def u3tail(b: Bool, +k0: U32, +k1: U32, +k2: U32, +t2: String, +X: String, +e: {Bool.and(U32.is_eq(k0, 226), Bool.and(U32.is_eq(k1, 128), Bool.or(U32.is_eq(k2, 168), U32.is_eq(k2, 169)))) == b : Bool},
           +l3: {Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, X}}}) == 3n : Nat})
  -> {Json.unit(Json.pick(String, b, "\\u202" ++ Json.esc_sep(k2), String.take(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, 3n)) ++ X) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, X, Json.JsMore{}} : Json.JU}:
  match b:
    case True{}:
      +h0 = and_l(U32.is_eq(k0, 226), Bool.and(U32.is_eq(k1, 128), Bool.or(U32.is_eq(k2, 168), U32.is_eq(k2, 169))), e)
      +h12 = and_r(U32.is_eq(k0, 226), Bool.and(U32.is_eq(k1, 128), Bool.or(U32.is_eq(k2, 168), U32.is_eq(k2, 169))), e)
      +h1 = and_l(U32.is_eq(k1, 128), Bool.or(U32.is_eq(k2, 168), U32.is_eq(k2, 169)), h12)
      +h2 = and_r(U32.is_eq(k1, 128), Bool.or(U32.is_eq(k2, 168), U32.is_eq(k2, 169)), h12)
      %Equal.sym(U32, k0, 226, u32_eq(k0, 226, h0))
        : {Json.unit(("\\u202" ++ Json.esc_sep(k2)) ++ X) == Json.JU{SCon{Chr{_}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, X, Json.JsMore{}} : Json.JU}
      %Equal.sym(U32, k1, 128, u32_eq(k1, 128, h1))
        : {Json.unit(("\\u202" ++ Json.esc_sep(k2)) ++ X) == Json.JU{SCon{Chr{226}, SCon{Chr{_}, SCon{Chr{k2}, SNil{}}}}, X, Json.JsMore{}} : Json.JU}
      lsep(U32.is_eq(k2, 168), k2, X, {==}, h2)
    case False{}:
      %Equal.sym(String, String.take(t2, 0n), "", take0(t2))
        : {Json.unit(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, _ ++ X}}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, X, Json.JsMore{}} : Json.JU}
      %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, X}}}), 3n, l3) : {Json.unit.n(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, X}}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, X, Json.JsMore{}} : Json.JU}
      {==}

def uc8(b: Bool, +k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool}, +e1: {cd1(SCon{Chr{k0}, t0}) == False{} : Bool}, +e2: {cd2(SCon{Chr{k0}, t0}) == False{} : Bool}, +e3: {cd3(SCon{Chr{k0}, t0}) == False{} : Bool}, +e4: {cd4(SCon{Chr{k0}, t0}) == False{} : Bool}, +e5: {cd5(SCon{Chr{k0}, t0}) == False{} : Bool}, +e6: {cd6(SCon{Chr{k0}, t0}) == False{} : Bool}, +e7: {cd7(SCon{Chr{k0}, t0}) == False{} : Bool}, +e8: {cd8(SCon{Chr{k0}, t0}) == b : Bool}) -> ugoal(SCon{Chr{k0}, t0}, X):
  match b:
    case True{}:
      match t0:
        case SNil{}:
          Empty.absurd(ugoal(SCon{Chr{k0}, SNil{}}, X), no_ft(c3_of_8(SCon{Chr{k0}, SNil{}}, e8)))
        case SCon{c1, t1}:
          match c1:
            case Chr{+k1}:
              match t1:
                case SNil{}:
                  Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, X), no_ft(c3_of_8(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, e8)))
                case SCon{c2, t2}:
                  match c2:
                    case Chr{+k2}:
                      match t2:
                        case SNil{}:
                          Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, X), no_ft(c3_of_8(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, e8)))
                        case SCon{c3, t3}:
                          match c3:
                            case Chr{+k3}:
                              %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}), 4n, len4c(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, e1, e2, e3, e4, e5, e6, e7, e8)) : {Json.unit(Json.esc_head.of(_, k0, Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, 1n), Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, 2n), SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}) ++ X) == Json.JU{Json.taken(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}), X, Json.JsMore{}} : Json.JU}
                              %Equal.sym(String, String.take(t3, 0n), "", take0(t3)) : {Json.unit(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, _ ++ X}}}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, SNil{}}}}}, X, Json.JsMore{}} : Json.JU}
                              %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}), 4n, len4c(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}, e1, e2, e3, e4, e5, e6, e7, e8)) : {Json.unit.n(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, SNil{}}}}}, X, Json.JsMore{}} : Json.JU}
                              {==}
    case False{}:
      Empty.absurd(ugoal(SCon{Chr{k0}, t0}, X), no_tf(Equal.trans(Bool, True{}, Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n), False{},
        Equal.cong(Nat, Bool, n => Nat.is_eq(n, 0n), 0n, Json.utf8_len(SCon{Chr{k0}, t0}), Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, t0}), 0n, len0(SCon{Chr{k0}, t0}, e1, e2, e3, e4, e5, e6, e7, e8))), hn)))

def uc7(b: Bool, +k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool}, +e1: {cd1(SCon{Chr{k0}, t0}) == False{} : Bool}, +e2: {cd2(SCon{Chr{k0}, t0}) == False{} : Bool}, +e3: {cd3(SCon{Chr{k0}, t0}) == False{} : Bool}, +e4: {cd4(SCon{Chr{k0}, t0}) == False{} : Bool}, +e5: {cd5(SCon{Chr{k0}, t0}) == False{} : Bool}, +e6: {cd6(SCon{Chr{k0}, t0}) == False{} : Bool}, +e7: {cd7(SCon{Chr{k0}, t0}) == b : Bool}) -> ugoal(SCon{Chr{k0}, t0}, X):
  match b:
    case True{}:
      match t0:
        case SNil{}:
          Empty.absurd(ugoal(SCon{Chr{k0}, SNil{}}, X), no_ft(c3_of_7(SCon{Chr{k0}, SNil{}}, e7)))
        case SCon{c1, t1}:
          match c1:
            case Chr{+k1}:
              match t1:
                case SNil{}:
                  Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, X), no_ft(c3_of_7(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, e7)))
                case SCon{c2, t2}:
                  match c2:
                    case Chr{+k2}:
                      match t2:
                        case SNil{}:
                          Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, X), no_ft(c3_of_7(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, e7)))
                        case SCon{c3, t3}:
                          match c3:
                            case Chr{+k3}:
                              %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}), 4n, len4b(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, e1, e2, e3, e4, e5, e6, e7)) : {Json.unit(Json.esc_head.of(_, k0, Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, 1n), Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, 2n), SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}) ++ X) == Json.JU{Json.taken(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}), X, Json.JsMore{}} : Json.JU}
                              %Equal.sym(String, String.take(t3, 0n), "", take0(t3)) : {Json.unit(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, _ ++ X}}}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, SNil{}}}}}, X, Json.JsMore{}} : Json.JU}
                              %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}), 4n, len4b(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}, e1, e2, e3, e4, e5, e6, e7)) : {Json.unit.n(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, SNil{}}}}}, X, Json.JsMore{}} : Json.JU}
                              {==}
    case False{}:
      uc8(cd8(SCon{Chr{k0}, t0}), k0, t0, X, hn, e1, e2, e3, e4, e5, e6, e7, {==})

def uc6(b: Bool, +k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool}, +e1: {cd1(SCon{Chr{k0}, t0}) == False{} : Bool}, +e2: {cd2(SCon{Chr{k0}, t0}) == False{} : Bool}, +e3: {cd3(SCon{Chr{k0}, t0}) == False{} : Bool}, +e4: {cd4(SCon{Chr{k0}, t0}) == False{} : Bool}, +e5: {cd5(SCon{Chr{k0}, t0}) == False{} : Bool}, +e6: {cd6(SCon{Chr{k0}, t0}) == b : Bool}) -> ugoal(SCon{Chr{k0}, t0}, X):
  match b:
    case True{}:
      match t0:
        case SNil{}:
          Empty.absurd(ugoal(SCon{Chr{k0}, SNil{}}, X), no_ft(c3_of_6(SCon{Chr{k0}, SNil{}}, e6)))
        case SCon{c1, t1}:
          match c1:
            case Chr{+k1}:
              match t1:
                case SNil{}:
                  Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, X), no_ft(c3_of_6(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, e6)))
                case SCon{c2, t2}:
                  match c2:
                    case Chr{+k2}:
                      match t2:
                        case SNil{}:
                          Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, X), no_ft(c3_of_6(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SNil{}}}}, e6)))
                        case SCon{c3, t3}:
                          match c3:
                            case Chr{+k3}:
                              %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}), 4n, len4a(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, e1, e2, e3, e4, e5, e6)) : {Json.unit(Json.esc_head.of(_, k0, Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, 1n), Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}, 2n), SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}) ++ X) == Json.JU{Json.taken(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, t3}}}}), X, Json.JsMore{}} : Json.JU}
                              %Equal.sym(String, String.take(t3, 0n), "", take0(t3)) : {Json.unit(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, _ ++ X}}}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, SNil{}}}}}, X, Json.JsMore{}} : Json.JU}
                              %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}), 4n, len4a(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}, e1, e2, e3, e4, e5, e6)) : {Json.unit.n(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, X}}}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, SCon{Chr{k3}, SNil{}}}}}, X, Json.JsMore{}} : Json.JU}
                              {==}
    case False{}:
      uc7(cd7(SCon{Chr{k0}, t0}), k0, t0, X, hn, e1, e2, e3, e4, e5, e6, {==})

def uc5(b: Bool, +k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool}, +e1: {cd1(SCon{Chr{k0}, t0}) == False{} : Bool}, +e2: {cd2(SCon{Chr{k0}, t0}) == False{} : Bool}, +e3: {cd3(SCon{Chr{k0}, t0}) == False{} : Bool}, +e4: {cd4(SCon{Chr{k0}, t0}) == False{} : Bool}, +e5: {cd5(SCon{Chr{k0}, t0}) == b : Bool}) -> ugoal(SCon{Chr{k0}, t0}, X):
  match b:
    case True{}:
      match t0:
        case SNil{}:
          Empty.absurd(ugoal(SCon{Chr{k0}, SNil{}}, X), no_ft(c2_of_5(SCon{Chr{k0}, SNil{}}, e5)))
        case SCon{c1, t1}:
          match c1:
            case Chr{+k1}:
              match t1:
                case SNil{}:
                  Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, X), no_ft(c2_of_5(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, e5)))
                case SCon{c2, t2}:
                  match c2:
                    case Chr{+k2}:
                      %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}), 3n, len3c(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, e1, e2, e3, e4, e5)) : {Json.unit(Json.esc_head.of(_, k0, Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, 1n), Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, 2n), SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}) ++ X) == Json.JU{Json.taken(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}), X, Json.JsMore{}} : Json.JU}
                      u3tail(Bool.and(U32.is_eq(k0, 226), Bool.and(U32.is_eq(k1, 128), Bool.or(U32.is_eq(k2, 168), U32.is_eq(k2, 169)))), k0, k1, k2, t2, X, {==}, len3c(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, X}}}, e1, e2, e3, e4, e5))
    case False{}:
      uc6(cd6(SCon{Chr{k0}, t0}), k0, t0, X, hn, e1, e2, e3, e4, e5, {==})

def uc4(b: Bool, +k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool}, +e1: {cd1(SCon{Chr{k0}, t0}) == False{} : Bool}, +e2: {cd2(SCon{Chr{k0}, t0}) == False{} : Bool}, +e3: {cd3(SCon{Chr{k0}, t0}) == False{} : Bool}, +e4: {cd4(SCon{Chr{k0}, t0}) == b : Bool}) -> ugoal(SCon{Chr{k0}, t0}, X):
  match b:
    case True{}:
      match t0:
        case SNil{}:
          Empty.absurd(ugoal(SCon{Chr{k0}, SNil{}}, X), no_ft(c2_of_4(SCon{Chr{k0}, SNil{}}, e4)))
        case SCon{c1, t1}:
          match c1:
            case Chr{+k1}:
              match t1:
                case SNil{}:
                  Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, X), no_ft(c2_of_4(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, e4)))
                case SCon{c2, t2}:
                  match c2:
                    case Chr{+k2}:
                      %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}), 3n, len3b(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, e1, e2, e3, e4)) : {Json.unit(Json.esc_head.of(_, k0, Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, 1n), Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, 2n), SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}) ++ X) == Json.JU{Json.taken(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}), X, Json.JsMore{}} : Json.JU}
                      u3tail(Bool.and(U32.is_eq(k0, 226), Bool.and(U32.is_eq(k1, 128), Bool.or(U32.is_eq(k2, 168), U32.is_eq(k2, 169)))), k0, k1, k2, t2, X, {==}, len3b(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, X}}}, e1, e2, e3, e4))
    case False{}:
      uc5(cd5(SCon{Chr{k0}, t0}), k0, t0, X, hn, e1, e2, e3, e4, {==})

def uc3(b: Bool, +k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool}, +e1: {cd1(SCon{Chr{k0}, t0}) == False{} : Bool}, +e2: {cd2(SCon{Chr{k0}, t0}) == False{} : Bool}, +e3: {cd3(SCon{Chr{k0}, t0}) == b : Bool}) -> ugoal(SCon{Chr{k0}, t0}, X):
  match b:
    case True{}:
      match t0:
        case SNil{}:
          Empty.absurd(ugoal(SCon{Chr{k0}, SNil{}}, X), no_ft(c2_of_3(SCon{Chr{k0}, SNil{}}, e3)))
        case SCon{c1, t1}:
          match c1:
            case Chr{+k1}:
              match t1:
                case SNil{}:
                  Empty.absurd(ugoal(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, X), no_ft(c2_of_3(SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, e3)))
                case SCon{c2, t2}:
                  match c2:
                    case Chr{+k2}:
                      %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}), 3n, len3a(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, e1, e2, e3)) : {Json.unit(Json.esc_head.of(_, k0, Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, 1n), Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}, 2n), SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}) ++ X) == Json.JU{Json.taken(_, SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, t2}}}), X, Json.JsMore{}} : Json.JU}
                      u3tail(Bool.and(U32.is_eq(k0, 226), Bool.and(U32.is_eq(k1, 128), Bool.or(U32.is_eq(k2, 168), U32.is_eq(k2, 169)))), k0, k1, k2, t2, X, {==}, len3a(SCon{Chr{k0}, SCon{Chr{k1}, SCon{Chr{k2}, X}}}, e1, e2, e3))
    case False{}:
      uc4(cd4(SCon{Chr{k0}, t0}), k0, t0, X, hn, e1, e2, e3, {==})

def uc2(b: Bool, +k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool}, +e1: {cd1(SCon{Chr{k0}, t0}) == False{} : Bool}, +e2: {cd2(SCon{Chr{k0}, t0}) == b : Bool}) -> ugoal(SCon{Chr{k0}, t0}, X):
  match b:
    case True{}:
      match t0:
        case SNil{}:
          Empty.absurd(ugoal(SCon{Chr{k0}, SNil{}}, X), no_ft(and_r(Json.in_range32(k0, 194, 223), Json.cont(SCon{Chr{k0}, SNil{}}, 1n), e2)))
        case SCon{c1, t1}:
          match c1:
            case Chr{+k1}:
              %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, t1}}), 2n, len2(SCon{Chr{k0}, SCon{Chr{k1}, t1}}, e1, e2)) : {Json.unit(Json.esc_head.of(_, k0, Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, t1}}, 1n), Json.byte_at(SCon{Chr{k0}, SCon{Chr{k1}, t1}}, 2n), SCon{Chr{k0}, SCon{Chr{k1}, t1}}) ++ X) == Json.JU{Json.taken(_, SCon{Chr{k0}, SCon{Chr{k1}, t1}}), X, Json.JsMore{}} : Json.JU}
              %Equal.sym(String, String.take(t1, 0n), "", take0(t1)) : {Json.unit(SCon{Chr{k0}, SCon{Chr{k1}, _ ++ X}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, X, Json.JsMore{}} : Json.JU}
              %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, SCon{Chr{k1}, X}}), 2n, len2(SCon{Chr{k0}, SCon{Chr{k1}, X}}, e1, e2)) : {Json.unit.n(_, SCon{Chr{k0}, SCon{Chr{k1}, X}}) == Json.JU{SCon{Chr{k0}, SCon{Chr{k1}, SNil{}}}, X, Json.JsMore{}} : Json.JU}
              {==}
    case False{}:
      uc3(cd3(SCon{Chr{k0}, t0}), k0, t0, X, hn, e1, e2, {==})

def uc1(b: Bool, +k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool}, +e1: {cd1(SCon{Chr{k0}, t0}) == b : Bool}) -> ugoal(SCon{Chr{k0}, t0}, X):
  match b:
    case True{}:
      %Equal.sym(Nat, Json.utf8_len(SCon{Chr{k0}, t0}), 1n, len1(SCon{Chr{k0}, t0}, e1)) : {Json.unit(Json.esc_head.of(_, k0, Json.byte_at(SCon{Chr{k0}, t0}, 1n), Json.byte_at(SCon{Chr{k0}, t0}, 2n), SCon{Chr{k0}, t0}) ++ X) == Json.JU{Json.taken(_, SCon{Chr{k0}, t0}), X, Json.JsMore{}} : Json.JU}
      asc(k0, X, e1)
    case False{}:
      uc2(cd2(SCon{Chr{k0}, t0}), k0, t0, X, hn, e1, {==})

def unit_esc(+k0: U32, +t0: String, +X: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool})
  -> ugoal(SCon{Chr{k0}, t0}, X):
  uc1(cd1(SCon{Chr{k0}, t0}), k0, t0, X, hn, {==})


# ---------------------------------------------------------------------
# JSON reading: the loop
# ---------------------------------------------------------------------

def app_assoc(a: String, +b: String, +c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %app_assoc(t, b, c) : {SCon{h, (t ++ b) ++ c} == SCon{h, _} : String}
      {==}

def esc_nil(m: Nat) -> {Json.esc.go(m, "") == "" : String}:
  match m:
    case 0n:
      {==}
    case 1n+(+p):
      esc_nil(p)

# the bytes a unit reads, then the rest of s, onto acc
def rtd(n: Nat, s: String, +acc: String)
  -> {String.reverse.go(String.drop(s, n), String.reverse.go(Json.taken(n, s), acc)) == String.reverse.go(s, acc) : String}:
  match n:
    case 0n:
      match s:
        case SNil{}:
          {==}
        case SCon{+h, +t}:
          {==}
    case 1n+(+p):
      match s:
        case SNil{}:
          {==}
        case SCon{+h, t}:
          rtd(p, t, SCon{h, acc})

def rr(s: String, +a: String) -> {String.reverse.go(String.reverse.go(s, a), "") == String.reverse.go(a, s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      rr(t, SCon{h, a})

def le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      le_refl(p)

def lt_succ_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      lt_succ_self(p)

def le_succ(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+(+ap):
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, no_ft(h))
        case 1n+(+bp):
          le_succ(ap, bp, h)

def le_trans(a: Nat, b: Nat, c: Nat, hab: {Nat.is_le(a, b) == True{} : Bool}, hbc: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      match c:
        case 0n:
          {==}
        case 1n+(+cp):
          {==}
    case 1n+(+ap):
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, no_ft(hab))
        case 1n+(+bp):
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, no_ft(hbc))
            case 1n+(+cp):
              le_trans(ap, bp, cp, hab, hbc)

def le_lt_trans(a: Nat, b: Nat, c: Nat, hab: {Nat.is_le(a, b) == True{} : Bool}, hbc: {Nat.is_lt(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          match c:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, no_ft(hbc))
            case 1n+(+cp):
              {==}
        case 1n+(+bp):
          match c:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, no_ft(hbc))
            case 1n+(+cp):
              {==}
    case 1n+(+ap):
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool}, no_ft(hab))
        case 1n+(+bp):
          match c:
            case 0n:
              Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, no_ft(hbc))
            case 1n+(+cp):
              le_lt_trans(ap, bp, cp, hab, hbc)

def lt_zero(a: Nat, h: {Nat.is_lt(a, 0n) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      no_ft(h)
    case 1n+(+p):
      no_ft(h)

def le_app(e: String, +x: String) -> {Nat.is_le(String.length(x), String.length(e ++ x)) == True{} : Bool}:
  match e:
    case SNil{}:
      le_refl(String.length(x))
    case SCon{+h, +t}:
      le_succ(String.length(x), String.length(t ++ x), le_app(t, x))

def lt_app(e: String, +x: String, +n: Nat, he: {String.is_empty(e) == False{} : Bool},
           h: {Nat.is_lt(String.length(e ++ x), 1n+n) == True{} : Bool}) -> {Nat.is_lt(String.length(x), n) == True{} : Bool}:
  match e:
    case SNil{}:
      Empty.absurd({Nat.is_lt(String.length(x), n) == True{} : Bool}, no_tf(he))
    case SCon{+c, +t}:
      le_lt_trans(String.length(x), String.length(t ++ x), n, le_app(t, x), h)

def drop_le(t: String, p: Nat) -> {Nat.is_le(String.length(String.drop(t, p)), String.length(t)) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+h, +r}:
      match p:
        case 0n:
          le_refl(String.length(r))
        case 1n+(+q):
          le_succ(String.length(String.drop(r, q)), String.length(r), drop_le(r, q))

def max1(n: Nat, hn: {Nat.is_eq(n, 0n) == False{} : Bool}) -> {Nat.max(1n, n) == n : Nat}:
  match n:
    case 0n:
      Empty.absurd({Nat.max(1n, 0n) == 0n : Nat}, no_tf(hn))
    case 1n+(+p):
      {==}

def drop_le1(+k0: U32, +t0: String, n: Nat, hn: {Nat.is_eq(n, 0n) == False{} : Bool})
  -> {Nat.is_le(String.length(String.drop(SCon{Chr{k0}, t0}, n)), String.length(t0)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(String.length(String.drop(SCon{Chr{k0}, t0}, 0n)), String.length(t0)) == True{} : Bool}, no_tf(hn))
    case 1n+(+p):
      drop_le(t0, p)

def take_ne(+k0: U32, +t0: String, n: Nat, hn: {Nat.is_eq(n, 0n) == False{} : Bool})
  -> {String.is_empty(String.take(SCon{Chr{k0}, t0}, n)) == False{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({String.is_empty(String.take(SCon{Chr{k0}, t0}, 0n)) == False{} : Bool}, no_tf(hn))
    case 1n+(+p):
      {==}

def pne_j(c: Bool, -a: String, -b: String, ha: {String.is_empty(a) == False{} : Bool}, hb: {String.is_empty(b) == False{} : Bool})
  -> {String.is_empty(Json.pick(String, c, a, b)) == False{} : Bool}:
  match c:
    case True{}:
      ha
    case False{}:
      hb

def ne_ascii(+k: U32) -> {String.is_empty(Json.esc_ascii(k)) == False{} : Bool}:
  pne_j(U32.is_eq(k, 34), "\\\"", Json.esc_ascii.2(k), {==},
  pne_j(U32.is_eq(k, 92), "\\\\", Json.esc_ascii.3(k), {==},
  pne_j(U32.is_eq(k, 10), "\\n", Json.esc_ascii.4(k), {==},
  pne_j(U32.is_eq(k, 13), "\\r", Json.esc_ascii.5(k), {==},
  pne_j(U32.is_eq(k, 9), "\\t", Json.esc_ascii.6(k), {==},
  pne_j(Bool.or(U32.is_lt(k, 32), Bool.or(U32.is_eq(k, 60), Bool.or(U32.is_eq(k, 62), U32.is_eq(k, 38)))),
    "\\u00" ++ Json.hexd((k >> 4n : U32)) ++ Json.hexd((k .&. 15 : U32)), Json.str1(k), {==}, {==}))))))

def eh_ne(+k0: U32, +t0: String, +hn: {Nat.is_eq(Json.utf8_len(SCon{Chr{k0}, t0}), 0n) == False{} : Bool})
  -> {String.is_empty(Json.esc_head(SCon{Chr{k0}, t0})) == False{} : Bool}:
  +s = {SCon{Chr{k0}, t0} : String}
  +n = Json.utf8_len(s)
  +b1 = Json.byte_at(s, 1n)
  +b2 = Json.byte_at(s, 2n)
  pne_j(Nat.is_eq(n, 0n), "\\ufffd", Json.esc_head.3(n, k0, b1, b2, s), {==},
  pne_j(Nat.is_eq(n, 1n), Json.esc_ascii(k0), Json.esc_head.4(n, k0, b1, b2, s), ne_ascii(k0),
  pne_j(Bool.and(Nat.is_eq(n, 3n), Bool.and(U32.is_eq(k0, 226), Bool.and(U32.is_eq(b1, 128), Bool.or(U32.is_eq(b2, 168), U32.is_eq(b2, 169))))),
    "\\u202" ++ Json.esc_sep(b2), String.take(s, n), {==}, take_ne(k0, t0, n, hn))))

def loop_goal(+m: Nat, +s: String, +f: String, +acc: String, +rest: String) -> Type:
  {Json.read.go(f, acc, Json.unit(Json.esc.go(m, s) ++ ("\"" ++ rest)))
   == Some{(String.reverse(String.reverse.go(s, acc)), rest)} : Maybe<&1, String & String>}

def loop(m: Nat, s: String, f: String, +acc: String, +rest: String,
         +hok: {L.utf8_ok.go(m, s) == True{} : Bool},
         +hlen: {Nat.is_le(String.length(s), m) == True{} : Bool},
         +hf: {Nat.is_lt(String.length(Json.esc.go(m, s) ++ ("\"" ++ rest)), String.length(f)) == True{} : Bool})
  -> loop_goal(m, s, f, acc, rest):
  match m:
    case 0n:
      match s:
        case SNil{}:
          match f:
            case SNil{}:
              Empty.absurd(loop_goal(0n, SNil{}, SNil{}, acc, rest), lt_zero(String.length(Json.esc.go(0n, SNil{}) ++ ("\"" ++ rest)), hf))
            case SCon{+c, +fp}:
              {==}
        case SCon{+c0, +t0}:
          Empty.absurd(loop_goal(0n, SCon{c0, t0}, f, acc, rest), no_ft(hlen))
    case 1n+(+mp):
      match s:
        case SNil{}:
          match f:
            case SNil{}:
              Empty.absurd(loop_goal(1n+mp, SNil{}, SNil{}, acc, rest), lt_zero(String.length(Json.esc.go(1n+mp, SNil{}) ++ ("\"" ++ rest)), hf))
            case SCon{+c, +fp}:
              %Equal.sym(String, Json.esc.go(mp, ""), "", esc_nil(mp))
                : {Json.read.go(SCon{c, fp}, acc, Json.unit(_ ++ ("\"" ++ rest))) == Some{(String.reverse(acc), rest)} : Maybe<&1, String & String>}
              {==}
        case SCon{+c0, +t0}:
          match c0:
            case Chr{+k0}:
              match f:
                case SNil{}:
                  Empty.absurd(loop_goal(1n+mp, SCon{Chr{k0}, t0}, SNil{}, acc, rest),
                    lt_zero(String.length(Json.esc.go(1n+mp, SCon{Chr{k0}, t0}) ++ ("\"" ++ rest)), hf))
                case SCon{+c, +fp}:
                  +s = {SCon{Chr{k0}, t0} : String}
                  +n = Json.utf8_len(s)
                  +ln = L.utf8_len(s)
                  +q = "\"" ++ rest
                  +d = String.drop(s, Json.esc_len(s))
                  +e = Json.esc_head(s)
                  +y = Json.esc.go(mp, d)
                  +hands = and_l(Bool.not(Nat.is_eq(ln, 0n)), L.utf8_ok.go(mp, String.drop(s, ln)), hok)
                  +hokl = and_r(Bool.not(Nat.is_eq(ln, 0n)), L.utf8_ok.go(mp, String.drop(s, ln)), hok)
                  +hn = Equal.trans(Bool, Nat.is_eq(n, 0n), Nat.is_eq(ln, 0n), False{},
                          Equal.cong(Nat, Bool, x => Nat.is_eq(x, 0n), n, ln, utf8_len_j(s)),
                          not_t(Nat.is_eq(ln, 0n), hands))
                  +hok2 = Equal.trans(Bool, L.utf8_ok.go(mp, String.drop(s, n)), L.utf8_ok.go(mp, String.drop(s, ln)), True{},
                          Equal.cong(Nat, Bool, x => L.utf8_ok.go(mp, String.drop(s, x)), n, ln, utf8_len_j(s)), hokl)
                  +hlen2 = le_trans(String.length(String.drop(s, n)), String.length(t0), mp, drop_le1(k0, t0, n, hn), hlen)
                  +hf1 = Equal.trans(Bool, Nat.is_lt(String.length(e ++ (y ++ q)), 1n+String.length(fp)),
                          Nat.is_lt(String.length((e ++ y) ++ q), 1n+String.length(fp)), True{},
                          Equal.cong(String, Bool, x => Nat.is_lt(String.length(x), 1n+String.length(fp)), e ++ (y ++ q), (e ++ y) ++ q,
                            Equal.sym(String, (e ++ y) ++ q, e ++ (y ++ q), app_assoc(e, y, q))), hf)
                  +hf2 = lt_app(e, y ++ q, String.length(fp), eh_ne(k0, t0, hn), hf1)
                  +hf3 = Equal.trans(Bool, Nat.is_lt(String.length(Json.esc.go(mp, String.drop(s, n)) ++ q), String.length(fp)),
                          Nat.is_lt(String.length(y ++ q), String.length(fp)), True{},
                          Equal.cong(Nat, Bool, x => Nat.is_lt(String.length(Json.esc.go(mp, String.drop(s, x)) ++ q), String.length(fp)),
                            n, Json.esc_len(s), Equal.sym(Nat, Json.esc_len(s), n, max1(n, hn))), hf2)
                  +acc2 = String.reverse.go(Json.taken(n, s), acc)
                  %Equal.sym(String, (e ++ y) ++ q, e ++ (y ++ q), app_assoc(e, y, q))
                    : {Json.read.go(SCon{c, fp}, acc, Json.unit(_)) == Some{(String.reverse(String.reverse.go(s, acc)), rest)} : Maybe<&1, String & String>}
                  %Equal.sym(Json.JU, Json.unit(e ++ (y ++ q)), Json.JU{Json.taken(n, s), y ++ q, Json.JsMore{}}, unit_esc(k0, t0, y ++ q, hn))
                    : {Json.read.go(SCon{c, fp}, acc, _) == Some{(String.reverse(String.reverse.go(s, acc)), rest)} : Maybe<&1, String & String>}
                  %Equal.sym(Nat, Json.esc_len(s), n, max1(n, hn))
                    : {Json.read.go(fp, acc2, Json.unit(Json.esc.go(mp, String.drop(s, _)) ++ q)) == Some{(String.reverse(String.reverse.go(s, acc)), rest)} : Maybe<&1, String & String>}
                  %rtd(n, s, acc)
                    : {Json.read.go(fp, acc2, Json.unit(Json.esc.go(mp, String.drop(s, n)) ++ q)) == Some{(String.reverse(_), rest)} : Maybe<&1, String & String>}
                  loop(mp, String.drop(s, n), fp, acc2, rest, hok2, hlen2, hf3)

def L.json_read_str(s, rest, h):
  +t = Json.esc(s) ++ ("\"" ++ rest)
  %Equal.sym(String, (Json.esc(s) ++ "\"") ++ rest, t, app_assoc(Json.esc(s), "\"", rest))
    : {Json.read.go(SCon{Chr{0}, _}, "", Json.unit(_)) == Some{(s, rest)} : Maybe<&1, String & String>}
  %rr(s, "") : {Json.read.go(SCon{Chr{0}, t}, "", Json.unit(t)) == Some{(_, rest)} : Maybe<&1, String & String>}
  loop(String.length(s), s, SCon{Chr{0}, t}, "", rest, and_r(L.bytes(s), L.utf8_ok.go(String.length(s), s), h),
    le_refl(String.length(s)), lt_succ_self(String.length(t)))

# ---------------------------------------------------------------------
# CSV reading: a field reads back
# ---------------------------------------------------------------------

def sep(last: Bool) -> String:
  match last:
    case True{}:
      "\n"
    case False{}:
      ","

def cutof(last: Bool) -> Csv.Cut:
  match last:
    case True{}:
      Csv.CsvEnd{}
    case False{}:
      Csv.CsvSep{}

def hc_head(+k: U32, +f: String, +c: U32, h: {Csv.has_char(SCon{Chr{k}, f}, c) == False{} : Bool}) -> {U32.is_eq(k, c) == False{} : Bool}:
  or_l(U32.is_eq(k, c), Csv.has_char(f, c), h)

def hc_tail(+k: U32, +f: String, +c: U32, h: {Csv.has_char(SCon{Chr{k}, f}, c) == False{} : Bool}) -> {Csv.has_char(f, c) == False{} : Bool}:
  or_r(U32.is_eq(k, c), Csv.has_char(f, c), h)

def fgoal_b(+f: String, +fuel: String, +last: Bool, +acc: String, +T: String) -> Type:
  {Csv.field.go(fuel, False{}, Csv.Fld{acc, f ++ (sep(last) ++ T), Csv.CsvMore{}}) == Csv.Fld{String.reverse.go(f, acc), T, cutof(last)} : Csv.Fld}

# a bare field: every byte is copied, then the separator ends it
def bare_loop(f: String, +last: Bool, fuel: String, +acc: String, +T: String,
              +h44: {Csv.has_char(f, 44) == False{} : Bool}, +h10: {Csv.has_char(f, 10) == False{} : Bool},
              +h13: {Csv.has_char(f, 13) == False{} : Bool}, +h34: {Csv.has_char(f, 34) == False{} : Bool},
              +hf: {Nat.is_lt(String.length(f), String.length(fuel)) == True{} : Bool})
  -> fgoal_b(f, fuel, last, acc, T):
  match f:
    case SNil{}:
      match last:
        case True{}:
          match fuel:
            case SNil{}:
              Empty.absurd(fgoal_b(SNil{}, SNil{}, True{}, acc, T), no_ft(hf))
            case SCon{c, +fp}:
              match fp:
                case SNil{}:
                  {==}
                case SCon{c2, fq}:
                  {==}
        case False{}:
          match fuel:
            case SNil{}:
              Empty.absurd(fgoal_b(SNil{}, SNil{}, False{}, acc, T), no_ft(hf))
            case SCon{c, +fp}:
              match fp:
                case SNil{}:
                  {==}
                case SCon{c2, fq}:
                  {==}
    case SCon{c0, +fr}:
      match c0:
        case Chr{+k}:
          match fuel:
            case SNil{}:
              Empty.absurd(fgoal_b(SCon{Chr{k}, fr}, SNil{}, last, acc, T), no_ft(hf))
            case SCon{c, +fp}:
              +x = fr ++ (sep(last) ++ T)
              +r = {Csv.Fld{String.reverse.go(SCon{Chr{k}, fr}, acc), T, cutof(last)} : Csv.Fld}
              %Equal.sym(Bool, U32.is_eq(k, 44), False{}, hc_head(k, fr, 44, h44))
                : {Csv.field.go(fp, False{}, Csv.pick(Csv.Fld, _, Csv.Fld{acc, x, Csv.CsvSep{}}, Csv.bare.byte.2(k, acc, x))) == r : Csv.Fld}
              %Equal.sym(Bool, U32.is_eq(k, 10), False{}, hc_head(k, fr, 10, h10))
                : {Csv.field.go(fp, False{}, Csv.pick(Csv.Fld, _, Csv.Fld{acc, x, Csv.CsvEnd{}}, Csv.bare.byte.3(k, acc, x))) == r : Csv.Fld}
              %Equal.sym(Bool, U32.is_eq(k, 13), False{}, hc_head(k, fr, 13, h13))
                : {Csv.field.go(fp, False{}, Csv.pick(Csv.Fld, Bool.and(_, Bool.or(String.is_empty(x), Csv.first_is(x, 10))),
                     Csv.Fld{acc, Csv.dropn(1n, x), Csv.CsvEnd{}}, Csv.bare.byte.4(k, acc, x))) == r : Csv.Fld}
              %Equal.sym(Bool, U32.is_eq(k, 34), False{}, hc_head(k, fr, 34, h34))
                : {Csv.field.go(fp, False{}, Csv.pick(Csv.Fld, _, Csv.Fld{acc, x, Csv.CsvBad{}}, Csv.Fld{SCon{Chr{k}, acc}, x, Csv.CsvMore{}})) == r : Csv.Fld}
              bare_loop(fr, last, fp, SCon{Chr{k}, acc}, T, hc_tail(k, fr, 44, h44), hc_tail(k, fr, 10, h10),
                hc_tail(k, fr, 13, h13), hc_tail(k, fr, 34, h34), hf)

def ctail.of(b: Bool, +k: U32, +f: String, +e: {String.starts_with(SCon{Chr{k}, f}, "\r\n") == b : Bool},
             +h: {String.contains(SCon{Chr{k}, f}, "\r\n") == False{} : Bool}) -> {String.contains(f, "\r\n") == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({String.contains(f, "\r\n") == False{} : Bool}, no_tf(
        Equal.trans(Bool, True{}, String.contains.if(f, "\r\n", String.starts_with(SCon{Chr{k}, f}, "\r\n")), False{},
          Equal.cong(Bool, Bool, x => String.contains.if(f, "\r\n", x), True{}, String.starts_with(SCon{Chr{k}, f}, "\r\n"),
            Equal.sym(Bool, String.starts_with(SCon{Chr{k}, f}, "\r\n"), True{}, e)), h)))
    case False{}:
      Equal.trans(Bool, String.contains(f, "\r\n"), String.contains.if(f, "\r\n", String.starts_with(SCon{Chr{k}, f}, "\r\n")), False{},
        Equal.cong(Bool, Bool, x => String.contains.if(f, "\r\n", x), False{}, String.starts_with(SCon{Chr{k}, f}, "\r\n"),
          Equal.sym(Bool, String.starts_with(SCon{Chr{k}, f}, "\r\n"), False{}, e)), h)

def ctail(+k: U32, +f: String, +h: {String.contains(SCon{Chr{k}, f}, "\r\n") == False{} : Bool}) -> {String.contains(f, "\r\n") == False{} : Bool}:
  ctail.of(String.starts_with(SCon{Chr{k}, f}, "\r\n"), k, f, {==}, h)

def sw_nil(t: String) -> {String.starts_with(t, "") == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, r}:
      {==}

# after a CR in a field without CRLF, the next byte of the quoted text is not LF
def nfirst.q(b: Bool, +k2: U32, +f2: String, +X: String, +e: {U32.is_eq(k2, 34) == b : Bool}, +h10: {U32.is_eq(k2, 10) == False{} : Bool})
  -> {Csv.first_is(Csv.double_quotes(SCon{Chr{k2}, f2}) ++ ("\"" ++ X), 10) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(k2, 34), True{}, e)
        : {Csv.first_is((Csv.pick(String, _, "\"\"", SCon{Chr{k2}, SNil{}}) ++ Csv.double_quotes(f2)) ++ ("\"" ++ X), 10) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, U32.is_eq(k2, 34), False{}, e)
        : {Csv.first_is((Csv.pick(String, _, "\"\"", SCon{Chr{k2}, SNil{}}) ++ Csv.double_quotes(f2)) ++ ("\"" ++ X), 10) == False{} : Bool}
      h10

def nfirst.of(b: Bool, +k2: U32, +f2: String, +X: String, +e: {U32.is_eq(k2, 10) == b : Bool},
              +h: {String.contains.if(SCon{Chr{k2}, f2}, "\r\n", String.starts_with.if(f2, "", U32.is_eq(k2, 10))) == False{} : Bool})
  -> {Csv.first_is(Csv.double_quotes(SCon{Chr{k2}, f2}) ++ ("\"" ++ X), 10) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Csv.first_is(Csv.double_quotes(SCon{Chr{k2}, f2}) ++ ("\"" ++ X), 10) == False{} : Bool}, no_tf(
        Equal.trans(Bool, True{}, String.contains.if(SCon{Chr{k2}, f2}, "\r\n", String.starts_with.if(f2, "", U32.is_eq(k2, 10))), False{},
          Equal.trans(Bool, True{}, String.contains.if(SCon{Chr{k2}, f2}, "\r\n", String.starts_with.if(f2, "", True{})),
            String.contains.if(SCon{Chr{k2}, f2}, "\r\n", String.starts_with.if(f2, "", U32.is_eq(k2, 10))),
            Equal.cong(Bool, Bool, x => String.contains.if(SCon{Chr{k2}, f2}, "\r\n", x), True{}, String.starts_with(f2, ""),
              Equal.sym(Bool, String.starts_with(f2, ""), True{}, sw_nil(f2))),
            Equal.cong(Bool, Bool, x => String.contains.if(SCon{Chr{k2}, f2}, "\r\n", String.starts_with.if(f2, "", x)), True{}, U32.is_eq(k2, 10),
              Equal.sym(Bool, U32.is_eq(k2, 10), True{}, e))),
          h)))
    case False{}:
      nfirst.q(U32.is_eq(k2, 34), k2, f2, X, {==}, e)

def nfirst(+k: U32, f: String, +X: String, +hk: {U32.is_eq(k, 13) == True{} : Bool},
           +h: {String.contains(SCon{Chr{k}, f}, "\r\n") == False{} : Bool})
  -> {Csv.first_is(Csv.double_quotes(f) ++ ("\"" ++ X), 10) == False{} : Bool}:
  match f:
    case SNil{}:
      {==}
    case SCon{c2, +f2}:
      match c2:
        case Chr{+k2}:
          +y = {SCon{Chr{k2}, f2} : String}
          nfirst.of(U32.is_eq(k2, 10), k2, f2, X, {==},
            Equal.trans(Bool, String.contains.if(y, "\r\n", String.starts_with.if(f2, "", U32.is_eq(k2, 10))),
              String.contains.if(y, "\r\n", String.starts_with.if(y, "\n", U32.is_eq(k, 13))), False{},
              Equal.cong(Bool, Bool, x => String.contains.if(y, "\r\n", String.starts_with.if(y, "\n", x)), True{}, U32.is_eq(k, 13),
                Equal.sym(Bool, U32.is_eq(k, 13), True{}, hk)),
              h))

def qgoal_step(+k: U32, +fr: String, +fp: String, +c: Char, +acc: String, +Z: String) -> Type:
  {Csv.field.go(SCon{c, fp}, True{}, Csv.Fld{acc, Csv.double_quotes(SCon{Chr{k}, fr}) ++ ("\"" ++ Z), Csv.CsvMore{}})
   == Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{k}, acc}, Csv.double_quotes(fr) ++ ("\"" ++ Z), Csv.CsvMore{}}) : Csv.Fld}

def qstep.cr(b: Bool, +k: U32, +fr: String, +fp: String, +c: Char, +acc: String, +Z: String, +e: {U32.is_eq(k, 13) == b : Bool},
             +hcr: {String.contains(SCon{Chr{k}, fr}, "\r\n") == False{} : Bool})
  -> {Csv.field.go(fp, True{}, Csv.quoted.byte.2(k, acc, Csv.double_quotes(fr) ++ ("\"" ++ Z)))
      == Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{k}, acc}, Csv.double_quotes(fr) ++ ("\"" ++ Z), Csv.CsvMore{}}) : Csv.Fld}:
  match b:
    case True{}:
      +y = Csv.double_quotes(fr) ++ ("\"" ++ Z)
      +r = Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{k}, acc}, y, Csv.CsvMore{}})
      %Equal.sym(Bool, Csv.first_is(y, 10), False{}, nfirst(k, fr, Z, e, hcr))
        : {Csv.field.go(fp, True{}, Csv.pick(Csv.Fld, Bool.and(U32.is_eq(k, 13), _), Csv.Fld{SCon{'\n', acc}, Csv.dropn(1n, y), Csv.CsvMore{}},
             Csv.Fld{SCon{Chr{k}, acc}, y, Csv.CsvMore{}})) == r : Csv.Fld}
      %Equal.sym(Bool, U32.is_eq(k, 13), True{}, e)
        : {Csv.field.go(fp, True{}, Csv.pick(Csv.Fld, Bool.and(_, False{}), Csv.Fld{SCon{'\n', acc}, Csv.dropn(1n, y), Csv.CsvMore{}},
             Csv.Fld{SCon{Chr{k}, acc}, y, Csv.CsvMore{}})) == r : Csv.Fld}
      {==}
    case False{}:
      +y = Csv.double_quotes(fr) ++ ("\"" ++ Z)
      +r = Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{k}, acc}, y, Csv.CsvMore{}})
      %Equal.sym(Bool, U32.is_eq(k, 13), False{}, e)
        : {Csv.field.go(fp, True{}, Csv.pick(Csv.Fld, Bool.and(_, Csv.first_is(y, 10)), Csv.Fld{SCon{'\n', acc}, Csv.dropn(1n, y), Csv.CsvMore{}},
             Csv.Fld{SCon{Chr{k}, acc}, y, Csv.CsvMore{}})) == r : Csv.Fld}
      {==}

def qstep.of(b: Bool, +k: U32, +fr: String, +fp: String, +c: Char, +acc: String, +Z: String, +e: {U32.is_eq(k, 34) == b : Bool},
             +hcr: {String.contains(SCon{Chr{k}, fr}, "\r\n") == False{} : Bool}) -> qgoal_step(k, fr, fp, c, acc, Z):
  match b:
    case True{}:
      +q = "\"" ++ Z
      +r = Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{k}, acc}, Csv.double_quotes(fr) ++ q, Csv.CsvMore{}})
      %Equal.sym(Bool, U32.is_eq(k, 34), True{}, e)
        : {Csv.field.go(SCon{c, fp}, True{}, Csv.Fld{acc, (Csv.pick(String, _, "\"\"", SCon{Chr{k}, SNil{}}) ++ Csv.double_quotes(fr)) ++ q, Csv.CsvMore{}}) == r : Csv.Fld}
      %Equal.sym(U32, k, 34, u32_eq(k, 34, e))
        : {Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{34}, acc}, Csv.double_quotes(fr) ++ q, Csv.CsvMore{}})
           == Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{_}, acc}, Csv.double_quotes(fr) ++ q, Csv.CsvMore{}}) : Csv.Fld}
      {==}
    case False{}:
      +q = "\"" ++ Z
      +r = Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{k}, acc}, Csv.double_quotes(fr) ++ q, Csv.CsvMore{}})
      %Equal.sym(Bool, U32.is_eq(k, 34), False{}, e)
        : {Csv.field.go(SCon{c, fp}, True{}, Csv.Fld{acc, (Csv.pick(String, _, "\"\"", SCon{Chr{k}, SNil{}}) ++ Csv.double_quotes(fr)) ++ q, Csv.CsvMore{}}) == r : Csv.Fld}
      %Equal.sym(Bool, U32.is_eq(k, 34), False{}, e)
        : {Csv.field.go(fp, True{}, Csv.quoted.byte.of(_, k, acc, Csv.double_quotes(fr) ++ q)) == r : Csv.Fld}
      qstep.cr(U32.is_eq(k, 13), k, fr, fp, c, acc, Z, {==}, hcr)

def fgoal_q(+f: String, +fuel: String, +last: Bool, +acc: String, +T: String) -> Type:
  {Csv.field.go(fuel, True{}, Csv.Fld{acc, Csv.double_quotes(f) ++ ("\"" ++ (sep(last) ++ T)), Csv.CsvMore{}})
   == Csv.Fld{String.reverse.go(f, acc), T, cutof(last)} : Csv.Fld}

# a quoted field: doubled quotes come back single, the closing quote and
# the separator end it
def quoted_loop(f: String, +last: Bool, fuel: String, +acc: String, +T: String,
                +hcr: {String.contains(f, "\r\n") == False{} : Bool},
                +hf: {Nat.is_lt(String.length(f), String.length(fuel)) == True{} : Bool})
  -> fgoal_q(f, fuel, last, acc, T):
  match f:
    case SNil{}:
      match last:
        case True{}:
          match fuel:
            case SNil{}:
              Empty.absurd(fgoal_q(SNil{}, SNil{}, True{}, acc, T), no_ft(hf))
            case SCon{c, fp}:
              match fp:
                case SNil{}:
                  {==}
                case SCon{c2, fq}:
                  {==}
        case False{}:
          match fuel:
            case SNil{}:
              Empty.absurd(fgoal_q(SNil{}, SNil{}, False{}, acc, T), no_ft(hf))
            case SCon{c, fp}:
              match fp:
                case SNil{}:
                  {==}
                case SCon{c2, fq}:
                  {==}
    case SCon{c0, +fr}:
      match c0:
        case Chr{+k}:
          match fuel:
            case SNil{}:
              Empty.absurd(fgoal_q(SCon{Chr{k}, fr}, SNil{}, last, acc, T), no_ft(hf))
            case SCon{+c, +fp}:
              +z = sep(last) ++ T
              Equal.trans(Csv.Fld,
                Csv.field.go(SCon{c, fp}, True{}, Csv.Fld{acc, Csv.double_quotes(SCon{Chr{k}, fr}) ++ ("\"" ++ z), Csv.CsvMore{}}),
                Csv.field.go(fp, True{}, Csv.Fld{SCon{Chr{k}, acc}, Csv.double_quotes(fr) ++ ("\"" ++ z), Csv.CsvMore{}}),
                Csv.Fld{String.reverse.go(SCon{Chr{k}, fr}, acc), T, cutof(last)},
                qstep.of(U32.is_eq(k, 34), k, fr, fp, c, acc, z, {==}, hcr),
                quoted_loop(fr, last, fp, SCon{Chr{k}, acc}, T, ctail(k, fr, hcr), hf))

def le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_lt_succ(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, 1n) == True{} : Bool}, no_ft(h))
        case 1n+bp:
          le_lt_succ(ap, bp, h)

def pre_le(a: String, +b: String) -> {Nat.is_le(String.length(a), String.length(a ++ b)) == True{} : Bool}:
  match a:
    case SNil{}:
      le0(String.length(b))
    case SCon{h, t}:
      pre_le(t, b)

def dq_step.of(b: Bool, +k: U32, +r: String, +e: {U32.is_eq(k, 34) == b : Bool})
  -> {Nat.is_le(1n+String.length(Csv.double_quotes(r)), String.length(Csv.double_quotes(SCon{Chr{k}, r}))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(k, 34), True{}, e)
        : {Nat.is_le(1n+String.length(Csv.double_quotes(r)), String.length(Csv.pick(String, _, "\"\"", SCon{Chr{k}, SNil{}}) ++ Csv.double_quotes(r))) == True{} : Bool}
      le_succ(String.length(Csv.double_quotes(r)), String.length(Csv.double_quotes(r)), le_refl(String.length(Csv.double_quotes(r))))
    case False{}:
      %Equal.sym(Bool, U32.is_eq(k, 34), False{}, e)
        : {Nat.is_le(1n+String.length(Csv.double_quotes(r)), String.length(Csv.pick(String, _, "\"\"", SCon{Chr{k}, SNil{}}) ++ Csv.double_quotes(r))) == True{} : Bool}
      le_refl(String.length(Csv.double_quotes(r)))

def dq_len(f: String) -> {Nat.is_le(String.length(f), String.length(Csv.double_quotes(f))) == True{} : Bool}:
  match f:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      match c:
        case Chr{+k}:
          le_trans(1n+String.length(r), 1n+String.length(Csv.double_quotes(r)), String.length(Csv.double_quotes(SCon{Chr{k}, r})),
            dq_len(r), dq_step.of(U32.is_eq(k, 34), k, r, {==}))

# a bare field's first rune is still not a space with the separator after it
def fs_app(+k0: U32, r0: String, +last: Bool, +T: String, +h: {Csv.first_space(SCon{Chr{k0}, r0}) == False{} : Bool})
  -> {Csv.first_space(SCon{Chr{k0}, r0} ++ (sep(last) ++ T)) == False{} : Bool}:
  match r0:
    case SNil{}:
      match last:
        case True{}:
          h
        case False{}:
          h
    case SCon{c1, r1}:
      match c1:
        case Chr{k1}:
          match r1:
            case SNil{}:
              match last:
                case True{}:
                  h
                case False{}:
                  h
            case SCon{c2, r2}:
              h

def sl0(+k0: U32, +r: String, +h10: {U32.is_eq(k0, 10) == False{} : Bool}, +hfs: {Csv.first_space(SCon{Chr{k0}, r}) == False{} : Bool})
  -> {Csv.space_len(SCon{Chr{k0}, r}) == 0n : Nat}:
  +s = {SCon{Chr{k0}, r} : String}
  +tl = Csv.pick(Nat, U32.is_lt(k0, 128), 1n, Csv.pick(Nat, U32.is_eq(k0, 194), 2n, 3n))
  %Equal.sym(Bool, U32.is_eq(k0, 10), False{}, h10) : {Csv.pick(Nat, Bool.or(_, Bool.not(Csv.first_space(s))), 0n, tl) == 0n : Nat}
  %Equal.sym(Bool, Csv.first_space(s), False{}, hfs) : {Csv.pick(Nat, Bool.or(False{}, Bool.not(_)), 0n, tl) == 0n : Nat}
  {==}

def trim_id(+c: Char, +r: String, +h: {Csv.space_len(SCon{c, r}) == 0n : Nat}) -> {Csv.trim(SCon{c, r}) == SCon{c, r} : String}:
  %Equal.sym(Nat, Csv.space_len(SCon{c, r}), 0n, h) : {Csv.trim.go(SCon{c, r}, Nat.is_eq(_, 0n), Csv.dropn(_, SCon{c, r})) == SCon{c, r} : String}
  {==}

def rgoal(+f: String, +last: Bool, +T: String) -> Type:
  {Csv.read_field(Csv.field(f) ++ (sep(last) ++ T)) == Csv.Fld{String.reverse.go(f, ""), T, cutof(last)} : Csv.Fld}

# a bare field, nonempty
def rf_bare(+k0: U32, +fr: String, +last: Bool, +T: String,
            +e: {Bool.or(String.eq(SCon{Chr{k0}, fr}, "\\."), Bool.or(Csv.first_space(SCon{Chr{k0}, fr}),
                   Bool.or(Bool.or(Csv.has_char(SCon{Chr{k0}, fr}, 44), Csv.has_char(SCon{Chr{k0}, fr}, 34)),
                   Bool.or(Csv.has_char(SCon{Chr{k0}, fr}, 13), Csv.has_char(SCon{Chr{k0}, fr}, 10))))) == False{} : Bool})
  -> {Csv.read_field(SCon{Chr{k0}, fr} ++ (sep(last) ++ T)) == Csv.Fld{String.reverse.go(SCon{Chr{k0}, fr}, ""), T, cutof(last)} : Csv.Fld}:
  +f = {SCon{Chr{k0}, fr} : String}
  +z = sep(last) ++ T
  +s = {SCon{Chr{k0}, fr ++ z} : String}
  +o1 = or_r(String.eq(f, "\\."), Bool.or(Csv.first_space(f), Bool.or(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10)))), e)
  +hfs = or_l(Csv.first_space(f), Bool.or(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10))), o1)
  +o2 = or_r(Csv.first_space(f), Bool.or(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10))), o1)
  +o3 = or_l(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10)), o2)
  +o4 = or_r(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10)), o2)
  +h44 = or_l(Csv.has_char(f, 44), Csv.has_char(f, 34), o3)
  +h34 = or_r(Csv.has_char(f, 44), Csv.has_char(f, 34), o3)
  +h13 = or_l(Csv.has_char(f, 13), Csv.has_char(f, 10), o4)
  +h10 = or_r(Csv.has_char(f, 13), Csv.has_char(f, 10), o4)
  +r = {Csv.Fld{String.reverse.go(f, ""), T, cutof(last)} : Csv.Fld}
  %Equal.sym(String, Csv.trim(s), s, trim_id(Chr{k0}, fr ++ z, sl0(k0, fr ++ z, hc_head(k0, fr, 10, h10), fs_app(k0, fr, last, T, hfs))))
    : {Csv.read_field.of(Csv.first_is(_, 34), _) == r : Csv.Fld}
  %Equal.sym(Bool, U32.is_eq(k0, 34), False{}, hc_head(k0, fr, 34, h34))
    : {Csv.read_field.of(_, s) == r : Csv.Fld}
  bare_loop(f, last, SCon{Chr{0}, s}, "", T, h44, h10, h13, h34,
    le_lt_succ(String.length(f), String.length(s), pre_le(f, z)))

def rf.of(b: Bool, +f: String, +last: Bool, +T: String, +hcr: {String.contains(f, "\r\n") == False{} : Bool},
          +e: {Csv.needs_quotes(f) == b : Bool}) -> rgoal(f, last, T):
  match b:
    case True{}:
      +z = sep(last) ++ T
      +y = Csv.double_quotes(f) ++ ("\"" ++ z)
      %Equal.sym(Bool, Csv.needs_quotes(f), True{}, e)
        : {Csv.read_field(Csv.pick(String, _, "\"" ++ Csv.double_quotes(f) ++ "\"", f) ++ z) == Csv.Fld{String.reverse.go(f, ""), T, cutof(last)} : Csv.Fld}
      %Equal.sym(String, (Csv.double_quotes(f) ++ "\"") ++ z, y, app_assoc(Csv.double_quotes(f), "\"", z))
        : {Csv.read_field(SCon{Chr{34}, _}) == Csv.Fld{String.reverse.go(f, ""), T, cutof(last)} : Csv.Fld}
      quoted_loop(f, last, SCon{Chr{0}, SCon{Chr{34}, y}}, "", T, hcr,
        le_lt_succ(String.length(f), 1n+String.length(y),
          le_succ(String.length(f), String.length(y),
            le_trans(String.length(f), String.length(Csv.double_quotes(f)), String.length(y), dq_len(f), pre_le(Csv.double_quotes(f), "\"" ++ z)))))
    case False{}:
      match f:
        case SNil{}:
          match last:
            case True{}:
              {==}
            case False{}:
              {==}
        case SCon{c0, +fr}:
          match c0:
            case Chr{+k0}:
              %Equal.sym(Bool, Csv.needs_quotes(SCon{Chr{k0}, fr}), False{}, e)
                : {Csv.read_field(Csv.pick(String, _, "\"" ++ Csv.double_quotes(SCon{Chr{k0}, fr}) ++ "\"", SCon{Chr{k0}, fr}) ++ (sep(last) ++ T))
                   == Csv.Fld{String.reverse.go(SCon{Chr{k0}, fr}, ""), T, cutof(last)} : Csv.Fld}
              rf_bare(k0, fr, last, T, e)

def rf(+f: String, +last: Bool, +T: String, +hcr: {String.contains(f, "\r\n") == False{} : Bool}) -> rgoal(f, last, T):
  rf.of(Csv.needs_quotes(f), f, last, T, hcr, {==})

# ---------------------------------------------------------------------
# CSV reading: a row reads back
# ---------------------------------------------------------------------

def lrr(xs: List<&2, String>, +a: List<&2, String>)
  -> {List.reverse.go(&2, String, List.reverse.go(&2, String, xs, a), []) == List.reverse.go(&2, String, a, xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      lrr(t, Con{h, a})

def ne_app(a: String, +c: Char, +r: String) -> {String.is_empty(a ++ SCon{c, r}) == False{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def rlgoal(+more: List<&2, String>, +f: String, +accl: List<&2, String>, +fuel: String, +rest: String) -> Type:
  {Csv.rec.go(fuel, Csv.Rec{accl, Csv.join_fields(Con{f, more}) ++ ("\n" ++ rest), Csv.CsvSep{}})
   == Some{(List.reverse(&2, String, List.reverse.go(&2, String, Con{f, more}, accl)), rest)} : Maybe<&1, List<&2, String> & String>}

def rev_f(+f: String) -> {f == String.reverse(String.reverse.go(f, "")) : String}:
  Equal.sym(String, String.reverse(String.reverse.go(f, "")), f, rr(f, ""))

# the fields, one after the other
def rec_loop(more: List<&2, String>, +f: String, +accl: List<&2, String>, fuel: String, +rest: String,
             +hnc: {L.no_crlf_pair(Con{f, more}) == True{} : Bool},
             +hf: {Nat.is_lt(List.length(&2, String, Con{f, more}), String.length(fuel)) == True{} : Bool})
  -> rlgoal(more, f, accl, fuel, rest):
  match more:
    case Nil{}:
      match fuel:
        case SNil{}:
          Empty.absurd(rlgoal(Nil{}, f, accl, SNil{}, rest), no_ft(hf))
        case SCon{c, +fp}:
          match fp:
            case SNil{}:
              Empty.absurd(rlgoal(Nil{}, f, accl, SCon{c, SNil{}}, rest), no_ft(hf))
            case SCon{c2, fq}:
              +hcr = not_t(String.contains(f, "\r\n"), and_l(Bool.not(String.contains(f, "\r\n")), L.no_crlf_pair(Nil{}), hnc))
              %rr(f, "")
                : {Csv.rec.go(SCon{c, SCon{c2, fq}}, Csv.Rec{accl, Csv.field(f) ++ ("\n" ++ rest), Csv.CsvSep{}})
                   == Some{(List.reverse(&2, String, Con{_, accl}), rest)} : Maybe<&1, List<&2, String> & String>}
              %Equal.sym(Csv.Fld, Csv.read_field(Csv.field(f) ++ ("\n" ++ rest)), Csv.Fld{String.reverse.go(f, ""), rest, Csv.CsvEnd{}}, rf(f, True{}, rest, hcr))
                : {Csv.rec.go(SCon{c2, fq}, Csv.rec.step(accl, _))
                   == Some{(List.reverse(&2, String, Con{String.reverse(String.reverse.go(f, "")), accl}), rest)} : Maybe<&1, List<&2, String> & String>}
              {==}
    case Con{+g, +m}:
      match fuel:
        case SNil{}:
          Empty.absurd(rlgoal(Con{g, m}, f, accl, SNil{}, rest), no_ft(hf))
        case SCon{c, +fp}:
          +hcr = not_t(String.contains(f, "\r\n"), and_l(Bool.not(String.contains(f, "\r\n")), L.no_crlf_pair(Con{g, m}), hnc))
          +hnc2 = and_r(Bool.not(String.contains(f, "\r\n")), L.no_crlf_pair(Con{g, m}), hnc)
          +j = Csv.join_fields(Con{g, m})
          +q = "\n" ++ rest
          -r = {Some{(List.reverse(&2, String, List.reverse.go(&2, String, Con{g, m}, Con{f, accl})), rest)} : Maybe<&1, List<&2, String> & String>}
          %Equal.sym(String, (Csv.field(f) ++ ("," ++ j)) ++ q, Csv.field(f) ++ (("," ++ j) ++ q), app_assoc(Csv.field(f), "," ++ j, q))
            : {Csv.rec.go(SCon{c, fp}, Csv.Rec{accl, _, Csv.CsvSep{}}) == r : Maybe<&1, List<&2, String> & String>}
          %Equal.sym(Csv.Fld, Csv.read_field(Csv.field(f) ++ ("," ++ (j ++ q))), Csv.Fld{String.reverse.go(f, ""), j ++ q, Csv.CsvSep{}}, rf(f, False{}, j ++ q, hcr))
            : {Csv.rec.go(fp, Csv.rec.step(accl, _)) == r : Maybe<&1, List<&2, String> & String>}
          %rev_f(f)
            : {Csv.rec.go(fp, Csv.Rec{Con{_, accl}, j ++ q, Csv.CsvSep{}}) == r : Maybe<&1, List<&2, String> & String>}
          rec_loop(m, g, Con{f, accl}, fp, rest, hnc2, hf)

def skip_id(s: String, +hne: {String.is_empty(s) == False{} : Bool}, +h: {Csv.blank_len(s) == 0n : Nat})
  -> {Csv.skip_blank.go(SCon{Chr{0}, s}, False{}, s) == s : String}:
  match s:
    case SNil{}:
      Empty.absurd({Csv.skip_blank.go(SCon{Chr{0}, SNil{}}, False{}, SNil{}) == SNil{} : String}, no_tf(hne))
    case SCon{+c, +r}:
      %Equal.sym(Nat, Csv.blank_len(SCon{c, r}), 0n, h)
        : {Csv.skip_blank.go(SCon{c, r}, Nat.is_eq(_, 0n), Csv.dropn(_, SCon{c, r})) == SCon{c, r} : String}
      {==}

def nq_or(+f: String) -> Bool:
  Bool.or(String.eq(f, "\\."), Bool.or(Csv.first_space(f),
    Bool.or(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10)))))

def nq_hc4(+f: String, +e: {nq_or(f) == False{} : Bool}) -> {Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10)) == False{} : Bool}:
  +o1 = or_r(String.eq(f, "\\."), Bool.or(Csv.first_space(f), Bool.or(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10)))), e)
  +o2 = or_r(Csv.first_space(f), Bool.or(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10))), o1)
  or_r(Bool.or(Csv.has_char(f, 44), Csv.has_char(f, 34)), Bool.or(Csv.has_char(f, 13), Csv.has_char(f, 10)), o2)

def bl_bare(+k0: U32, +x: String, +h10: {U32.is_eq(k0, 10) == False{} : Bool}, +h13: {U32.is_eq(k0, 13) == False{} : Bool})
  -> {Csv.blank_len(SCon{Chr{k0}, x}) == 0n : Nat}:
  +s = {SCon{Chr{k0}, x} : String}
  +tl = Nat.min(2n, String.length(String.take(s, 2n)))
  %Equal.sym(Bool, U32.is_eq(k0, 10), False{}, h10)
    : {Csv.pick(Nat, Bool.and(_, Bool.not(String.is_empty(s))), 1n,
         Csv.pick(Nat, Bool.and(U32.is_eq(k0, 13), Bool.or(U32.is_eq(Csv.byte_at(s, 1n), 10), Nat.is_eq(String.length(String.take(s, 2n)), 1n))), tl, 0n)) == 0n : Nat}
  %Equal.sym(Bool, U32.is_eq(k0, 13), False{}, h13)
    : {Csv.pick(Nat, Bool.and(_, Bool.or(U32.is_eq(Csv.byte_at(s, 1n), 10), Nat.is_eq(String.length(String.take(s, 2n)), 1n))), tl, 0n) == 0n : Nat}
  {==}

# a row never starts with a blank line
def bl0.of(b: Bool, more: List<&2, String>, +f: String, +rest: String,
           +hne: {Bool.or(Bool.not(String.is_empty(f)), Bool.not(List.is_empty(&2, String, more))) == True{} : Bool},
           +e: {Csv.needs_quotes(f) == b : Bool})
  -> {Csv.blank_len(Csv.join_fields(Con{f, more}) ++ ("\n" ++ rest)) == 0n : Nat}:
  match b:
    case True{}:
      match more:
        case Nil{}:
          %Equal.sym(Bool, Csv.needs_quotes(f), True{}, e)
            : {Csv.blank_len(Csv.pick(String, _, "\"" ++ Csv.double_quotes(f) ++ "\"", f) ++ ("\n" ++ rest)) == 0n : Nat}
          {==}
        case Con{g, m}:
          %Equal.sym(Bool, Csv.needs_quotes(f), True{}, e)
            : {Csv.blank_len((Csv.pick(String, _, "\"" ++ Csv.double_quotes(f) ++ "\"", f) ++ ("," ++ Csv.join_fields(Con{g, m}))) ++ ("\n" ++ rest)) == 0n : Nat}
          {==}
    case False{}:
      match more:
        case Nil{}:
          match f:
            case SNil{}:
              Empty.absurd({Csv.blank_len(Csv.join_fields(Con{SNil{}, Nil{}}) ++ ("\n" ++ rest)) == 0n : Nat}, no_ft(hne))
            case SCon{c0, +fr}:
              match c0:
                case Chr{+k0}:
                  +o4 = nq_hc4(SCon{Chr{k0}, fr}, e)
                  %Equal.sym(Bool, Csv.needs_quotes(SCon{Chr{k0}, fr}), False{}, e)
                    : {Csv.blank_len(Csv.pick(String, _, "\"" ++ Csv.double_quotes(SCon{Chr{k0}, fr}) ++ "\"", SCon{Chr{k0}, fr}) ++ ("\n" ++ rest)) == 0n : Nat}
                  bl_bare(k0, fr ++ ("\n" ++ rest),
                    hc_head(k0, fr, 10, or_r(Csv.has_char(SCon{Chr{k0}, fr}, 13), Csv.has_char(SCon{Chr{k0}, fr}, 10), o4)),
                    hc_head(k0, fr, 13, or_l(Csv.has_char(SCon{Chr{k0}, fr}, 13), Csv.has_char(SCon{Chr{k0}, fr}, 10), o4)))
        case Con{+g, +m}:
          match f:
            case SNil{}:
              {==}
            case SCon{c0, +fr}:
              match c0:
                case Chr{+k0}:
                  +o4 = nq_hc4(SCon{Chr{k0}, fr}, e)
                  %Equal.sym(Bool, Csv.needs_quotes(SCon{Chr{k0}, fr}), False{}, e)
                    : {Csv.blank_len((Csv.pick(String, _, "\"" ++ Csv.double_quotes(SCon{Chr{k0}, fr}) ++ "\"", SCon{Chr{k0}, fr}) ++ ("," ++ Csv.join_fields(Con{g, m}))) ++ ("\n" ++ rest)) == 0n : Nat}
                  bl_bare(k0, (fr ++ ("," ++ Csv.join_fields(Con{g, m}))) ++ ("\n" ++ rest),
                    hc_head(k0, fr, 10, or_r(Csv.has_char(SCon{Chr{k0}, fr}, 13), Csv.has_char(SCon{Chr{k0}, fr}, 10), o4)),
                    hc_head(k0, fr, 13, or_l(Csv.has_char(SCon{Chr{k0}, fr}, 13), Csv.has_char(SCon{Chr{k0}, fr}, 10), o4)))

# as many fields as bytes, at most
def jl(more: List<&2, String>, +f: String, +x: String)
  -> {Nat.is_le(List.length(&2, String, more), String.length(Csv.join_fields(Con{f, more}) ++ x)) == True{} : Bool}:
  match more:
    case Nil{}:
      le0(String.length(Csv.field(f) ++ x))
    case Con{+g, +m}:
      +j = Csv.join_fields(Con{g, m})
      %Equal.sym(String, (Csv.field(f) ++ ("," ++ j)) ++ x, Csv.field(f) ++ (("," ++ j) ++ x), app_assoc(Csv.field(f), "," ++ j, x))
        : {Nat.is_le(1n+List.length(&2, String, m), String.length(_)) == True{} : Bool}
      le_trans(1n+List.length(&2, String, m), String.length(SCon{',', j ++ x}), String.length(Csv.field(f) ++ SCon{',', j ++ x}),
        jl(m, g, x), le_app(Csv.field(f), SCon{',', j ++ x}))

def parse_rt(fs: List<&2, String>, +rest: String, +h: {L.representable(fs) == True{} : Bool})
  -> {Csv.parse_row(Csv.row(fs) ++ rest) == Some{(fs, rest)} : Maybe<&1, List<&2, String> & String>}:
  match fs:
    case Nil{}:
      Empty.absurd({Csv.parse_row(Csv.row(Nil{}) ++ rest) == Some{(Nil{}, rest)} : Maybe<&1, List<&2, String> & String>}, no_ft(h))
    case Con{+f, +more}:
      +q = "\n" ++ rest
      +s = Csv.join_fields(Con{f, more}) ++ q
      -r = {Some{(Con{f, more}, rest)} : Maybe<&1, List<&2, String> & String>}
      +h1 = and_l(Bool.and(L.all_bytes(Con{f, more}), L.no_crlf_pair(Con{f, more})),
              Bool.or(Bool.not(String.is_empty(f)), Bool.not(List.is_empty(&2, String, more))), h)
      +hne = and_r(Bool.and(L.all_bytes(Con{f, more}), L.no_crlf_pair(Con{f, more})),
              Bool.or(Bool.not(String.is_empty(f)), Bool.not(List.is_empty(&2, String, more))), h)
      +hnc = and_r(L.all_bytes(Con{f, more}), L.no_crlf_pair(Con{f, more}), h1)
      +hs = ne_app(Csv.join_fields(Con{f, more}), '\n', rest)
      %Equal.sym(String, (Csv.join_fields(Con{f, more}) ++ "\n") ++ rest, s, app_assoc(Csv.join_fields(Con{f, more}), "\n", rest))
        : {Csv.parse_row.go(_) == r : Maybe<&1, List<&2, String> & String>}
      %Equal.sym(String, Csv.skip_blank.go(SCon{Chr{0}, s}, False{}, s), s, skip_id(s, hs, bl0.of(Csv.needs_quotes(f), more, f, rest, hne, {==})))
        : {Csv.parse_row.of(String.is_empty(_), _) == r : Maybe<&1, List<&2, String> & String>}
      %Equal.sym(Bool, String.is_empty(s), False{}, hs)
        : {Csv.parse_row.of(_, s) == r : Maybe<&1, List<&2, String> & String>}
      %lrr(Con{f, more}, [])
        : {Csv.parse_row.of(False{}, s) == Some{(_, rest)} : Maybe<&1, List<&2, String> & String>}
      rec_loop(more, f, [], SCon{Chr{0}, SCon{Chr{0}, s}}, rest, hnc,
        le_lt_succ(List.length(&2, String, more), String.length(s), jl(more, f, q)))

def L.csv_parse_row(fs, rest, h):
  parse_rt(fs, rest, h)

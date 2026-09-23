# Proofs of the rate and flags laws (rate_*, flags_*).
import Base
import ../LAWS.bend as L
import ../lib/dec.bend as Dec
import ../lib/dur.bend as Dur
import ../lib/pacer.bend as Pace
import ../lib/flags.bend as Flags
import ../lib/hdr.bend as Hdr
import ./nat.bend as PNat
import ./dec.bend as PDec

def L.flags_attack_defaults():
  {==}

def L.flags_rate():
  ({==}, {==})

# ---------------------------------------------------------------------
# The attack loop: one more unit of fuel changes nothing
# ---------------------------------------------------------------------

def lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_succ(p)

def lt_succ2(n: Nat) -> {Nat.is_lt(n, 2n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_succ2(p)

# x < l and l <= g put x below g
def lt_trans_s(x: Nat, l: Nat, g: Nat, h1: {Nat.is_lt(x, l) == True{} : Bool}, h2: {Nat.is_lt(l, 1n+g) == True{} : Bool})
  -> {Nat.is_lt(x, g) == True{} : Bool}:
  match x:
    case 0n:
      match l:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, g) == True{} : Bool}, PNat.false_ne_true(h1))
        case 1n+lp:
          match g:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, PNat.lt_zero(lp, h2))
            case 1n+gp:
              {==}
    case 1n+xp:
      match l:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+xp, g) == True{} : Bool}, PNat.false_ne_true(h1))
        case 1n+lp:
          match g:
            case 0n:
              Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, PNat.lt_zero(lp, h2))
            case 1n+gp:
              lt_trans_s(xp, lp, gp, h1, h2)

def or_lt(b: Bool, x: Nat, l: Nat, g: Nat, h1: {Bool.or(b, Nat.is_lt(x, l)) == True{} : Bool}, h2: {Nat.is_lt(l, 1n+g) == True{} : Bool})
  -> {Bool.or(b, Nat.is_lt(x, g)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      lt_trans_s(x, l, g, h1, h2)

def slen(xs: List<&2, String>) -> Nat:
  List.length(&2, String, xs)

# a step that does not stop leaves fewer arguments
def dec_ok(+st: Flags.St, +n: Nat) -> Bool:
  Bool.or(Flags.st_stop(st), Nat.is_lt(slen(Flags.st_rest(st)), n))

def st_of_dec(r: Result<&2, &2, String, Flags.Attack>, +rest: List<&2, String>, -n: Nat, h: {Nat.is_lt(slen(rest), n) == True{} : Bool})
  -> {dec_ok(Flags.st_of(r, rest), n) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{a}:
      h

def valued_dec(v: Maybe<&2, String>, +f: Flags.VFlag, +name: String, +rest: List<&2, String>, +a: Flags.Attack)
  -> {dec_ok(Flags.valued(v, f, name, rest, a), 1n+slen(rest)) == True{} : Bool}:
  match v:
    case Some{+x}:
      st_of_dec(Flags.apply(f, x, a), rest, 1n+slen(rest), lt_succ(slen(rest)))
    case None{}:
      match rest:
        case Nil{}:
          {==}
        case Con{+x, +more}:
          st_of_dec(Flags.apply(f, x, a), more, 2n+slen(more), lt_succ2(slen(more)))

def keepalive_of_dec(b: Maybe<&2, Bool>, +v: String, +rest: List<&2, String>, +a: Flags.Attack)
  -> {dec_ok(Flags.keepalive_of(b, v, rest, a), 1n+slen(rest)) == True{} : Bool}:
  match b:
    case None{}:
      {==}
    case Some{x}:
      lt_succ(slen(rest))

def keepalive_dec(v: Maybe<&2, String>, +rest: List<&2, String>, +a: Flags.Attack)
  -> {dec_ok(Flags.keepalive(v, rest, a), 1n+slen(rest)) == True{} : Bool}:
  match v:
    case None{}:
      lt_succ(slen(rest))
    case Some{+x}:
      keepalive_of_dec(Flags.bool_of(x), x, rest, a)

def flag_step_dec(k: Flags.FKind, +name: String, +v: Maybe<&2, String>, +rest: List<&2, String>, +a: Flags.Attack)
  -> {dec_ok(Flags.flag_step(k, name, v, rest, a), 1n+slen(rest)) == True{} : Bool}:
  match k:
    case Flags.KValue{f}:
      valued_dec(v, f, name, rest, a)
    case Flags.KKeepalive{}:
      keepalive_dec(v, rest, a)
    case Flags.KHelp{}:
      {==}
    case Flags.KRefused{}:
      {==}
    case Flags.KUnknown{}:
      {==}

def arg_step_dec(x: Flags.Arg, +s: String, +rest: List<&2, String>, +a: Flags.Attack)
  -> {dec_ok(Flags.arg_step(x, s, rest, a), 1n+slen(rest)) == True{} : Bool}:
  match x:
    case Flags.AStop{}:
      {==}
    case Flags.AEnd{}:
      {==}
    case Flags.ABad{}:
      {==}
    case Flags.AFlag{+name, +v}:
      flag_step_dec(Flags.kind_of(name), name, v, rest, a)

def step_dec(args: List<&2, String>, +a: Flags.Attack) -> {dec_ok(Flags.step(args, a), slen(args)) == True{} : Bool}:
  match args:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      arg_step_dec(Flags.arg_of(s), s, rest, a)

# fuel beyond the arguments' count is not used
def fuel1(+g: Nat, stop: Bool, +args: List<&2, String>, +r: Result<&2, &2, String, Flags.Attack>,
  h: {Bool.or(stop, Nat.is_lt(slen(args), g)) == True{} : Bool})
  -> {Flags.attack_loop(1n+g, stop, args, r) == Flags.attack_loop(g, stop, args, r) : Result<&2, &2, String, Flags.Attack>}:
  match g:
    case 0n:
      match stop:
        case True{}:
          {==}
        case False{}:
          Empty.absurd({Flags.attack_loop(1n, False{}, args, r) == r : Result<&2, &2, String, Flags.Attack>}, PNat.lt_zero(slen(args), h))
    case 1n+gp:
      match stop:
        case True{}:
          {==}
        case False{}:
          +st = Flags.step(args, Flags.attack_of(r))
          fuel1(gp, Flags.st_stop(st), Flags.st_rest(st), Flags.st_res(st),
            or_lt(Flags.st_stop(st), slen(Flags.st_rest(st)), slen(args), gp, step_dec(args, Flags.attack_of(r)), h))

# ---------------------------------------------------------------------
# flags_forms
# ---------------------------------------------------------------------

def forms_gen(+x: Result<&2, &2, String, Flags.Attack>, +rest: List<&2, String>)
  -> {Flags.attack_fin(Flags.attack_loop(2n+slen(rest), Flags.st_stop(Flags.st_of(x, rest)), Flags.st_rest(Flags.st_of(x, rest)), Flags.st_res(Flags.st_of(x, rest))))
      == Flags.attack_fin(Flags.attack_loop(1n+slen(rest), Flags.st_stop(Flags.st_of(x, rest)), Flags.st_rest(Flags.st_of(x, rest)), Flags.st_res(Flags.st_of(x, rest)))) : Result<&2, &2, String, Flags.Attack>}:
  +st = Flags.st_of(x, rest)
  Equal.cong(Result<&2, &2, String, Flags.Attack>, Result<&2, &2, String, Flags.Attack>, Flags.attack_fin,
    Flags.attack_loop(2n+slen(rest), Flags.st_stop(st), Flags.st_rest(st), Flags.st_res(st)),
    Flags.attack_loop(1n+slen(rest), Flags.st_stop(st), Flags.st_rest(st), Flags.st_res(st)),
    fuel1(1n+slen(rest), Flags.st_stop(st), Flags.st_rest(st), Flags.st_res(st), st_of_dec(x, rest, 1n+slen(rest), lt_succ(slen(rest)))))

def forms_one(+f: Flags.VFlag, +v: String, +rest: List<&2, String>)
  -> {Flags.attack_fin(Flags.attack_loop(2n+slen(rest), Flags.st_stop(Flags.st_of(Flags.apply(f, v, Flags.attack_defaults()), rest)), Flags.st_rest(Flags.st_of(Flags.apply(f, v, Flags.attack_defaults()), rest)), Flags.st_res(Flags.st_of(Flags.apply(f, v, Flags.attack_defaults()), rest))))
      == Flags.attack_fin(Flags.attack_loop(1n+slen(rest), Flags.st_stop(Flags.st_of(Flags.apply(f, v, Flags.attack_defaults()), rest)), Flags.st_rest(Flags.st_of(Flags.apply(f, v, Flags.attack_defaults()), rest)), Flags.st_res(Flags.st_of(Flags.apply(f, v, Flags.attack_defaults()), rest)))) : Result<&2, &2, String, Flags.Attack>}:
  forms_gen(Flags.apply(f, v, Flags.attack_defaults()), rest)

def forms_t(-j: Nat, -v: String, -rest: List<&2, String>) -> Type:
  {Flags.parse_attack(Con{"-" ++ L.nth_str(14n+j, L.value_flags()), Con{v, rest}}) == Flags.parse_attack(Con{"-" ++ L.nth_str(14n+j, L.value_flags()) ++ "=" ++ v, rest}) : Result<&2, &2, String, Flags.Attack>}
  & {Flags.parse_attack(Con{"--" ++ L.nth_str(14n+j, L.value_flags()) ++ "=" ++ v, rest}) == Flags.parse_attack(Con{"-" ++ L.nth_str(14n+j, L.value_flags()) ++ "=" ++ v, rest}) : Result<&2, &2, String, Flags.Attack>}
  & {Flags.parse_attack(["-keepalive"]) == Flags.parse_attack(["-keepalive=true"]) : Result<&2, &2, String, Flags.Attack>}

def L.flags_forms(i, v, rest, h):
  match i:
    case 0n:
      (forms_one(Flags.VRate{}, v, rest), {==}, {==})
    case 1n+i1:
      match i1:
        case 0n:
          (forms_one(Flags.VDuration{}, v, rest), {==}, {==})
        case 1n+i2:
          match i2:
            case 0n:
              (forms_one(Flags.VTargets{}, v, rest), {==}, {==})
            case 1n+i3:
              match i3:
                case 0n:
                  (forms_one(Flags.VFormat{}, v, rest), {==}, {==})
                case 1n+i4:
                  match i4:
                    case 0n:
                      (forms_one(Flags.VOutput{}, v, rest), {==}, {==})
                    case 1n+i5:
                      match i5:
                        case 0n:
                          (forms_one(Flags.VName{}, v, rest), {==}, {==})
                        case 1n+i6:
                          match i6:
                            case 0n:
                              (forms_one(Flags.VWorkers{}, v, rest), {==}, {==})
                            case 1n+i7:
                              match i7:
                                case 0n:
                                  (forms_one(Flags.VMaxWorkers{}, v, rest), {==}, {==})
                                case 1n+i8:
                                  match i8:
                                    case 0n:
                                      (forms_one(Flags.VTimeout{}, v, rest), {==}, {==})
                                    case 1n+i9:
                                      match i9:
                                        case 0n:
                                          (forms_one(Flags.VHeader{}, v, rest), {==}, {==})
                                        case 1n+i10:
                                          match i10:
                                            case 0n:
                                              (forms_one(Flags.VBody{}, v, rest), {==}, {==})
                                            case 1n+i11:
                                              match i11:
                                                case 0n:
                                                  (forms_one(Flags.VMaxBody{}, v, rest), {==}, {==})
                                                case 1n+i12:
                                                  match i12:
                                                    case 0n:
                                                      (forms_one(Flags.VRedirects{}, v, rest), {==}, {==})
                                                    case 1n+i13:
                                                      match i13:
                                                        case 0n:
                                                          (forms_one(Flags.VEncoding{}, v, rest), {==}, {==})
                                                        case 1n+j:
                                                          Empty.absurd(forms_t(j, v, rest), PNat.lt_zero(j, h))

# ---------------------------------------------------------------------
# Booleans
# ---------------------------------------------------------------------

def true_ne_false(e: {True{} == False{} : Bool}) -> Empty:
  PNat.false_ne_true(Equal.sym(Bool, True{}, False{}, e))

def andT_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(h))

def andT_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, PNat.false_ne_true(h))

def notT(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PNat.false_ne_true(h))

def orF_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, true_ne_false(h))

def orF_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      Empty.absurd({b == False{} : Bool}, true_ne_false(h))

def pick_f(-A: Data, c: Bool, -a: A, -b: A, e: {c == False{} : Bool}) -> {Flags.pick(A, c, a, b) == b : A}:
  %Equal.sym(Bool, c, False{}, e) : {Flags.pick(A, _, a, b) == b : A}
  {==}

# the i-th name of a list x is not in
def hs_at(+x: String, xs: List<&2, String>, +i: Nat, h: {L.has_str(x, xs) == False{} : Bool})
  -> {Bool.and(Nat.is_lt(i, slen(xs)), String.eq(x, L.nth_str(i, xs))) == False{} : Bool}:
  match xs:
    case Nil{}:
      match i:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case Con{+y, +rest}:
      match i:
        case 0n:
          orF_l(String.eq(x, y), L.has_str(x, rest), h)
        case 1n+j:
          hs_at(x, rest, j, orF_r(String.eq(x, y), L.has_str(x, rest), h))

# ---------------------------------------------------------------------
# One flag argument "-f"
# ---------------------------------------------------------------------

def cut_none(s: String, +q: U32, +h: {L.has_char(s, q) == False{} : Bool}) -> {Flags.cut(q, s) == Flags.Cut{s, None{}} : Flags.Cut}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +rest}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, q), False{}, orF_l(U32.is_eq(k, q), L.has_char(rest, q), h))
            : {Flags.pick(Flags.Cut, _, Flags.Cut{"", Some{rest}}, Flags.cut_cons(Chr{k}, Flags.cut(q, rest))) == Flags.Cut{SCon{Chr{k}, rest}, None{}} : Flags.Cut}
          %Equal.sym(Flags.Cut, Flags.cut(q, rest), Flags.Cut{rest, None{}}, cut_none(rest, q, orF_r(U32.is_eq(k, q), L.has_char(rest, q), h)))
            : {Flags.cut_cons(Chr{k}, _) == Flags.Cut{SCon{Chr{k}, rest}, None{}} : Flags.Cut}
          {==}

def dd_fin(cm: Cmp, +k: U32, +r: String, h: {Cmp.is_eq(cm) == False{} : Bool})
  -> {String.eq.fin(String.cmp.rec(Chr{45}, Chr{45}, String.cmp.fin(r, SNil{}, ((Chr{k}, Chr{45}), cm)))) == False{} : Bool}:
  match cm:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({String.eq.fin(String.cmp.rec(Chr{45}, Chr{45}, String.cmp.fin(r, SNil{}, ((Chr{k}, Chr{45}), EQ{})))) == False{} : Bool}, true_ne_false(h))
    case GT{}:
      {==}

def lt0f(n: Nat) -> {Nat.is_lt(n, 0n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# arg_of with its tests as parameters
def arg_sw(+s: String, sw: Bool) -> Flags.Arg:
  +name = String.drop(s, Flags.pick(Nat, sw, 2n, 1n))
  Flags.pick(Flags.Arg, Bool.or(Nat.is_lt(String.length(s), 2n), Bool.not(Flags.first_is(s, 45))), Flags.AStop{},
  Flags.pick(Flags.Arg, String.eq(s, "--"), Flags.AEnd{},
  Flags.pick(Flags.Arg, Bool.or(String.is_empty(name), Bool.or(Flags.first_is(name, 45), Flags.first_is(name, 61))), Flags.ABad{},
    Flags.AFlag{Flags.cut_head(Flags.cut(61, name)), Flags.cut_tail(Flags.cut(61, name))})))

def arg_sw2(+s: String, dd: Bool, b1: Bool, b2: Bool, +ct: Flags.Cut) -> Flags.Arg:
  Flags.pick(Flags.Arg, Bool.or(Nat.is_lt(String.length(s), 2n), Bool.not(Flags.first_is(s, 45))), Flags.AStop{},
  Flags.pick(Flags.Arg, dd, Flags.AEnd{},
  Flags.pick(Flags.Arg, Bool.or(b1, b2), Flags.ABad{},
    Flags.AFlag{Flags.cut_head(ct), Flags.cut_tail(ct)})))

# "-f" for a flag name f that has no "=" and does not start with "-"
def arg_flag(+k: U32, +r: String, +h45: {U32.is_eq(k, 45) == False{} : Bool}, +h61: {L.has_char(SCon{Chr{k}, r}, 61) == False{} : Bool})
  -> {Flags.arg_of(SCon{Chr{45}, SCon{Chr{k}, r}}) == Flags.AFlag{SCon{Chr{k}, r}, None{}} : Flags.Arg}:
  %Equal.sym(Bool, U32.is_eq(k, 45), False{}, h45) : {arg_sw(SCon{Chr{45}, SCon{Chr{k}, r}}, String.starts_with.if(r, SNil{}, _)) == Flags.AFlag{SCon{Chr{k}, r}, None{}} : Flags.Arg}
  %Equal.sym(Bool, String.eq(SCon{Chr{45}, SCon{Chr{k}, r}}, "--"), False{}, dd_fin(U32.cmp(k, 45), k, r, h45))
    : {arg_sw2(SCon{Chr{45}, SCon{Chr{k}, r}}, _, U32.is_eq(k, 45), U32.is_eq(k, 61), Flags.cut(61, SCon{Chr{k}, r})) == Flags.AFlag{SCon{Chr{k}, r}, None{}} : Flags.Arg}
  %Equal.sym(Bool, U32.is_eq(k, 45), False{}, h45)
    : {arg_sw2(SCon{Chr{45}, SCon{Chr{k}, r}}, False{}, _, U32.is_eq(k, 61), Flags.cut(61, SCon{Chr{k}, r})) == Flags.AFlag{SCon{Chr{k}, r}, None{}} : Flags.Arg}
  %Equal.sym(Bool, U32.is_eq(k, 61), False{}, orF_l(U32.is_eq(k, 61), L.has_char(r, 61), h61))
    : {arg_sw2(SCon{Chr{45}, SCon{Chr{k}, r}}, False{}, False{}, _, Flags.cut(61, SCon{Chr{k}, r})) == Flags.AFlag{SCon{Chr{k}, r}, None{}} : Flags.Arg}
  %Equal.sym(Flags.Cut, Flags.cut(61, SCon{Chr{k}, r}), Flags.Cut{SCon{Chr{k}, r}, None{}}, cut_none(SCon{Chr{k}, r}, 61, h61))
    : {arg_sw2(SCon{Chr{45}, SCon{Chr{k}, r}}, False{}, False{}, False{}, _) == Flags.AFlag{SCon{Chr{k}, r}, None{}} : Flags.Arg}
  %Equal.sym(Bool, Nat.is_lt(String.length(r), 0n), False{}, lt0f(String.length(r)))
    : {Flags.pick(Flags.Arg, Bool.or(_, False{}), Flags.AStop{}, Flags.AFlag{SCon{Chr{k}, r}, None{}}) == Flags.AFlag{SCon{Chr{k}, r}, None{}} : Flags.Arg}
  {==}

# kind_of with its tests as parameters
def kind_sel(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, b9: Bool, b10: Bool, b11: Bool, b12: Bool, b13: Bool, b14: Bool, b15: Bool, b16: Bool) -> Flags.FKind:
  Flags.pick(Flags.FKind, b0, Flags.KValue{Flags.VRate{}},
  Flags.pick(Flags.FKind, b1, Flags.KValue{Flags.VDuration{}},
  Flags.pick(Flags.FKind, b2, Flags.KValue{Flags.VTargets{}},
  Flags.pick(Flags.FKind, b3, Flags.KValue{Flags.VFormat{}},
  Flags.pick(Flags.FKind, b4, Flags.KValue{Flags.VOutput{}},
  Flags.pick(Flags.FKind, b5, Flags.KValue{Flags.VName{}},
  Flags.pick(Flags.FKind, b6, Flags.KValue{Flags.VWorkers{}},
  Flags.pick(Flags.FKind, b7, Flags.KValue{Flags.VMaxWorkers{}},
  Flags.pick(Flags.FKind, b8, Flags.KValue{Flags.VTimeout{}},
  Flags.pick(Flags.FKind, b9, Flags.KValue{Flags.VHeader{}},
  Flags.pick(Flags.FKind, b10, Flags.KValue{Flags.VBody{}},
  Flags.pick(Flags.FKind, b11, Flags.KValue{Flags.VMaxBody{}},
  Flags.pick(Flags.FKind, b12, Flags.KValue{Flags.VRedirects{}},
  Flags.pick(Flags.FKind, b13, Flags.KValue{Flags.VEncoding{}},
  Flags.pick(Flags.FKind, b14, Flags.KKeepalive{},
  Flags.pick(Flags.FKind, b15, Flags.KHelp{},
  Flags.pick(Flags.FKind, b16, Flags.KRefused{}, Flags.KUnknown{})))))))))))))))))

def kind_sel_f(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, b9: Bool, b10: Bool, b11: Bool, b12: Bool, b13: Bool, b14: Bool, b15: Bool, b16: Bool, e0: {b0 == False{} : Bool}, e1: {b1 == False{} : Bool}, e2: {b2 == False{} : Bool}, e3: {b3 == False{} : Bool}, e4: {b4 == False{} : Bool}, e5: {b5 == False{} : Bool}, e6: {b6 == False{} : Bool}, e7: {b7 == False{} : Bool}, e8: {b8 == False{} : Bool}, e9: {b9 == False{} : Bool}, e10: {b10 == False{} : Bool}, e11: {b11 == False{} : Bool}, e12: {b12 == False{} : Bool}, e13: {b13 == False{} : Bool}, e14: {b14 == False{} : Bool}, e15: {b15 == False{} : Bool}, e16: {b16 == False{} : Bool})
  -> {kind_sel(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}:
  %Equal.sym(Bool, b0, False{}, e0) : {kind_sel(_, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b1, False{}, e1) : {kind_sel(False{}, _, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b2, False{}, e2) : {kind_sel(False{}, False{}, _, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b3, False{}, e3) : {kind_sel(False{}, False{}, False{}, _, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b4, False{}, e4) : {kind_sel(False{}, False{}, False{}, False{}, _, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b5, False{}, e5) : {kind_sel(False{}, False{}, False{}, False{}, False{}, _, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b6, False{}, e6) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, _, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b7, False{}, e7) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b8, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b8, False{}, e8) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b9, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b9, False{}, e9) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b10, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b10, False{}, e10) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b11, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b11, False{}, e11) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b12, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b12, False{}, e12) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b13, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b13, False{}, e13) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b14, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b14, False{}, e14) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b15, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b15, False{}, e15) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _, b16) == Flags.KUnknown{} : Flags.FKind}
  %Equal.sym(Bool, b16, False{}, e16) : {kind_sel(False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, _) == Flags.KUnknown{} : Flags.FKind}
  {==}

# ---------------------------------------------------------------------
# flags_refused
# ---------------------------------------------------------------------

def refused1_t(-i: Nat, -rest: List<&2, String>) -> Type:
  {Flags.parse_attack(Con{"-" ++ L.nth_str(i, L.unsupported()), rest}) == Fail{"flag not supported in the Bend port: -" ++ L.nth_str(i, L.unsupported())} : Result<&2, &2, String, Flags.Attack>}

def refused1(i: Nat, +rest: List<&2, String>, h: {Nat.is_lt(i, 18n) == True{} : Bool}) -> refused1_t(i, rest):
  match i:
    case 0n:
      {==}
    case 1n+i1:
      match i1:
        case 0n:
          {==}
        case 1n+i2:
          match i2:
            case 0n:
              {==}
            case 1n+i3:
              match i3:
                case 0n:
                  {==}
                case 1n+i4:
                  match i4:
                    case 0n:
                      {==}
                    case 1n+i5:
                      match i5:
                        case 0n:
                          {==}
                        case 1n+i6:
                          match i6:
                            case 0n:
                              {==}
                            case 1n+i7:
                              match i7:
                                case 0n:
                                  {==}
                                case 1n+i8:
                                  match i8:
                                    case 0n:
                                      {==}
                                    case 1n+i9:
                                      match i9:
                                        case 0n:
                                          {==}
                                        case 1n+i10:
                                          match i10:
                                            case 0n:
                                              {==}
                                            case 1n+i11:
                                              match i11:
                                                case 0n:
                                                  {==}
                                                case 1n+i12:
                                                  match i12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+i13:
                                                      match i13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+i14:
                                                          match i14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+i15:
                                                              match i15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+i16:
                                                                  match i16:
                                                                    case 0n:
                                                                      {==}
                                                                    case 1n+i17:
                                                                      match i17:
                                                                        case 0n:
                                                                          {==}
                                                                        case 1n+j:
                                                                          Empty.absurd(refused1_t(18n+j, rest), PNat.lt_zero(j, h))

# the parse after the first argument's Arg, and after its flag's kind
def after(x: Flags.Arg, +s: String, +rest: List<&2, String>) -> Result<&2, &2, String, Flags.Attack>:
  +st = Flags.arg_step(x, s, rest, Flags.attack_defaults())
  Flags.attack_fin(Flags.attack_loop(1n+slen(rest), Flags.st_stop(st), Flags.st_rest(st), Flags.st_res(st)))

def after_k(k: Flags.FKind, +f: String, +rest: List<&2, String>) -> Result<&2, &2, String, Flags.Attack>:
  +st = Flags.flag_step(k, f, None{}, rest, Flags.attack_defaults())
  Flags.attack_fin(Flags.attack_loop(1n+slen(rest), Flags.st_stop(st), Flags.st_rest(st), Flags.st_res(st)))

def unknown_t(-f: String, -rest: List<&2, String>) -> Type:
  {Flags.parse_attack(Con{"-" ++ f, rest}) == Fail{"flag provided but not defined: -" ++ f} : Result<&2, &2, String, Flags.Attack>}

def refused2(f: String, +rest: List<&2, String>,
  +h1: {Bool.and(Bool.and(Bool.and(L.flag_str_ok(f), Bool.not(L.has_char(f, 61))), Bool.not(L.first_is(f, 45))),
     Bool.not(Bool.or(Bool.or(L.has_str(f, L.value_flags()), L.has_str(f, L.unsupported())),
       Bool.or(String.eq(f, "keepalive"), Bool.or(String.eq(f, "h"), String.eq(f, "help")))))) == True{} : Bool})
  -> unknown_t(f, rest):
  match f:
    case SNil{}:
      Empty.absurd(unknown_t(SNil{}, rest), PNat.false_ne_true(h1))
    case SCon{+c, +r}:
      match c:
        case Chr{+k}:
          +fso = L.flag_str_ok(SCon{Chr{k}, r})
          +nhc = Bool.not(L.has_char(SCon{Chr{k}, r}, 61))
          +nfi = Bool.not(L.first_is(SCon{Chr{k}, r}, 45))
          +hsv = L.has_str(SCon{Chr{k}, r}, L.value_flags())
          +hsu = L.has_str(SCon{Chr{k}, r}, L.unsupported())
          +ehh = Bool.or(String.eq(SCon{Chr{k}, r}, "h"), String.eq(SCon{Chr{k}, r}, "help"))
          +oth = Bool.or(String.eq(SCon{Chr{k}, r}, "keepalive"), ehh)
          +dd = Bool.or(Bool.or(hsv, hsu), oth)
          +a3 = andT_l(Bool.and(Bool.and(fso, nhc), nfi), Bool.not(dd), h1)
          +a2 = andT_l(Bool.and(fso, nhc), nfi, a3)
          +e61 = notT(L.has_char(SCon{Chr{k}, r}, 61), andT_r(fso, nhc, a2))
          +e45 = notT(L.first_is(SCon{Chr{k}, r}, 45), andT_r(Bool.and(fso, nhc), nfi, a3))
          +df = notT(dd, andT_r(Bool.and(Bool.and(fso, nhc), nfi), Bool.not(dd), h1))
          +ehs = orF_l(Bool.or(hsv, hsu), oth, df)
          +eoth = orF_r(Bool.or(hsv, hsu), oth, df)
          +ev = orF_l(hsv, hsu, ehs)
          +eu = orF_r(hsv, hsu, ehs)
          %Equal.sym(Flags.Arg, Flags.arg_of(SCon{Chr{45}, SCon{Chr{k}, r}}), Flags.AFlag{SCon{Chr{k}, r}, None{}}, arg_flag(k, r, e45, e61))
            : {after(_, SCon{Chr{45}, SCon{Chr{k}, r}}, rest) == Fail{"flag provided but not defined: -" ++ SCon{Chr{k}, r}} : Result<&2, &2, String, Flags.Attack>}
          %Equal.sym(Flags.FKind, Flags.kind_of(SCon{Chr{k}, r}), Flags.KUnknown{},
              kind_sel_f(String.eq(SCon{Chr{k}, r}, "rate"), String.eq(SCon{Chr{k}, r}, "duration"), String.eq(SCon{Chr{k}, r}, "targets"), String.eq(SCon{Chr{k}, r}, "format"), String.eq(SCon{Chr{k}, r}, "output"), String.eq(SCon{Chr{k}, r}, "name"), String.eq(SCon{Chr{k}, r}, "workers"), String.eq(SCon{Chr{k}, r}, "max-workers"), String.eq(SCon{Chr{k}, r}, "timeout"), String.eq(SCon{Chr{k}, r}, "header"), String.eq(SCon{Chr{k}, r}, "body"), String.eq(SCon{Chr{k}, r}, "max-body"), String.eq(SCon{Chr{k}, r}, "redirects"), String.eq(SCon{Chr{k}, r}, "encoding"), String.eq(SCon{Chr{k}, r}, "keepalive"), ehh, L.has_str(SCon{Chr{k}, r}, L.unsupported()),
                hs_at(SCon{Chr{k}, r}, L.value_flags(), 0n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 1n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 2n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 3n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 4n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 5n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 6n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 7n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 8n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 9n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 10n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 11n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 12n, ev), hs_at(SCon{Chr{k}, r}, L.value_flags(), 13n, ev),
                orF_l(String.eq(SCon{Chr{k}, r}, "keepalive"), ehh, eoth), orF_r(String.eq(SCon{Chr{k}, r}, "keepalive"), ehh, eoth), eu))
            : {after_k(_, SCon{Chr{k}, r}, rest) == Fail{"flag provided but not defined: -" ++ SCon{Chr{k}, r}} : Result<&2, &2, String, Flags.Attack>}
          {==}

def L.flags_refused(i, f, rest, h0, h1):
  (refused1(i, rest, h0), refused2(f, rest, h1))

# ---------------------------------------------------------------------
# rate_parse_error
# ---------------------------------------------------------------------

def app_assoc(a: String, +b: String, +c: String) -> {(a ++ b) ++ c == a ++ (b ++ c) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %app_assoc(t, b, c) : {SCon{h, (t ++ b) ++ c} == SCon{h, _} : String}
      {==}

def app_nil(a: String) -> {a ++ "" == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %app_nil(t) : {SCon{h, t ++ ""} == SCon{h, _} : String}
      {==}

def pick_fp(-A: Data, c: Bool, -a: A, -b: A, e: {c == False{} : Bool}) -> {Pace.pick(A, c, a, b) == b : A}:
  %Equal.sym(Bool, c, False{}, e) : {Pace.pick(A, _, a, b) == b : A}
  {==}

def pick_fps(-A: Data, c: Bool, -a: A, -b: A, e: {c == False{} : Bool}) -> {b == Pace.pick(A, c, a, b) : A}:
  %Equal.sym(Bool, c, False{}, e) : {b == Pace.pick(A, _, a, b) : A}
  {==}

def pick_tp(-A: Data, c: Bool, -a: A, -b: A, e: {c == True{} : Bool}) -> {Pace.pick(A, c, a, b) == a : A}:
  %Equal.sym(Bool, c, True{}, e) : {Pace.pick(A, _, a, b) == a : A}
  {==}

# a text without "/" is all head
def pcut_pre(f: String, +t: String, -m: Maybe<&2, String>, +e: {Pace.cut(t) == Pace.Cut{"", m} : Pace.Cut}, +h: {L.has_char(f, 47) == False{} : Bool})
  -> {Pace.cut(f ++ t) == Pace.Cut{f, m} : Pace.Cut}:
  match f:
    case SNil{}:
      e
    case SCon{+c, +r}:
      match c:
        case Chr{+k}:
          %pick_fps(Pace.Cut, U32.is_eq(k, 47), Pace.Cut{"", Some{r ++ t}}, Pace.cut_cons(Chr{k}, Pace.cut(r ++ t)), orF_l(U32.is_eq(k, 47), L.has_char(r, 47), h))
            : {_ == Pace.Cut{SCon{Chr{k}, r}, m} : Pace.Cut}
          %Equal.sym(Pace.Cut, Pace.cut(r ++ t), Pace.Cut{r, m}, pcut_pre(r, t, m, e, orF_r(U32.is_eq(k, 47), L.has_char(r, 47), h)))
            : {Pace.cut_cons(Chr{k}, _) == Pace.Cut{SCon{Chr{k}, r}, m} : Pace.Cut}
          {==}

def swif_t(b: Bool, -r: String, h: {String.starts_with.if(r, "", b) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(h))

def rest_cut_t(rest: String) -> Maybe<&2, String>:
  match rest:
    case SNil{}:
      None{}
    case SCon{c, r}:
      Some{r}

# "" and "/..." cut at once
def rest_cut(rest: String, h: {Bool.or(String.is_empty(rest), String.starts_with(rest, "/")) == True{} : Bool})
  -> {Pace.cut(rest) == Pace.Cut{"", rest_cut_t(rest)} : Pace.Cut}:
  match rest:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      match c:
        case Chr{+k}:
          pick_tp(Pace.Cut, U32.is_eq(k, 47), Pace.Cut{"", Some{r}}, Pace.cut_cons(Chr{k}, Pace.cut(r)), swif_t(U32.is_eq(k, 47), r, h))

def unsigned_id(f: String, h: {Bool.not(Bool.or(L.first_is(f, 43), L.first_is(f, 45))) == True{} : Bool}) -> {Pace.unsigned(f) == f : String}:
  match f:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      match c:
        case Chr{+k}:
          pick_fp(String, Bool.or(U32.is_eq(k, 43), U32.is_eq(k, 45)), String.drop(r, 0n), SCon{Chr{k}, r},
            notT(Bool.or(U32.is_eq(k, 43), U32.is_eq(k, 45)), h))

# %q changes nothing without quotes and backslashes
def quote_id(f: String, +h34: {L.has_char(f, 34) == False{} : Bool}, +h92: {L.has_char(f, 92) == False{} : Bool}) -> {Pace.quote.go(f) == f : String}:
  match f:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      match c:
        case Chr{+k}:
          +b34 = U32.is_eq(k, 34)
          +b92 = U32.is_eq(k, 92)
          %pick_fps(String, Bool.or(b34, b92), "\\" ++ SCon{Chr{k}, SNil{}}, SCon{Chr{k}, SNil{}},
              Equal.sym(Bool, False{}, Bool.or(b34, b92),
                %Equal.sym(Bool, b34, False{}, orF_l(b34, L.has_char(r, 34), h34)) : {False{} == Bool.or(_, b92) : Bool}
                %Equal.sym(Bool, b92, False{}, orF_l(b92, L.has_char(r, 92), h92)) : {False{} == Bool.or(False{}, _) : Bool}
                {==}))
            : {_ ++ Pace.quote.go(r) == SCon{Chr{k}, r} : String}
          %Equal.sym(String, Pace.quote.go(r), r, quote_id(r, orF_r(b34, L.has_char(r, 34), h34), orF_r(b92, L.has_char(r, 92), h92)))
            : {SCon{Chr{k}, _} == SCon{Chr{k}, r} : String}
          {==}

def pr_of(+c: Pace.Cut) -> Result<&2, &2, String, Pace.Rate>:
  Pace.of_number(Dec.all_digits(Pace.unsigned(Pace.cut_head(c))), Pace.cut_head(c), Pace.cut_tail(c))

def rpe(+f: String, +rest: String,
  +h0: {Bool.and(Bool.and(L.printable(f), Bool.not(L.all_digits(f))),
     Bool.not(Bool.or(Bool.or(L.has_char(f, 47), L.has_char(f, 34)), Bool.or(L.has_char(f, 92), String.eq(f, "infinity"))))) == True{} : Bool},
  +h1: {Bool.or(String.is_empty(rest), String.starts_with(rest, "/")) == True{} : Bool},
  +h2: {Bool.not(Bool.or(L.first_is(f, 43), L.first_is(f, 45))) == True{} : Bool})
  -> {Pace.parse_rate(f ++ rest) == Fail{"strconv.Atoi: parsing \"" ++ f ++ "\": invalid syntax"} : Result<&2, &2, String, Pace.Rate>}:
  +pa = Bool.and(L.printable(f), Bool.not(L.all_digits(f)))
  +cs = Bool.or(Bool.or(L.has_char(f, 47), L.has_char(f, 34)), Bool.or(L.has_char(f, 92), String.eq(f, "infinity")))
  +ec = notT(cs, andT_r(pa, Bool.not(cs), h0))
  +e1 = orF_l(Bool.or(L.has_char(f, 47), L.has_char(f, 34)), Bool.or(L.has_char(f, 92), String.eq(f, "infinity")), ec)
  +e47 = orF_l(L.has_char(f, 47), L.has_char(f, 34), e1)
  +e34 = orF_r(L.has_char(f, 47), L.has_char(f, 34), e1)
  +e92 = orF_l(L.has_char(f, 92), String.eq(f, "infinity"), orF_r(Bool.or(L.has_char(f, 47), L.has_char(f, 34)), Bool.or(L.has_char(f, 92), String.eq(f, "infinity")), ec))
  +ed = notT(L.all_digits(f), andT_r(L.printable(f), Bool.not(L.all_digits(f)), andT_l(pa, Bool.not(cs), h0)))
  %Equal.sym(Pace.Cut, Pace.cut(f ++ rest), Pace.Cut{f, rest_cut_t(rest)}, pcut_pre(f, rest, rest_cut_t(rest), rest_cut(rest, h1), e47))
    : {pr_of(_) == Fail{"strconv.Atoi: parsing \"" ++ f ++ "\": invalid syntax"} : Result<&2, &2, String, Pace.Rate>}
  %Equal.sym(String, Pace.unsigned(f), f, unsigned_id(f, h2))
    : {Pace.of_number(Dec.all_digits(_), f, rest_cut_t(rest)) == Fail{"strconv.Atoi: parsing \"" ++ f ++ "\": invalid syntax"} : Result<&2, &2, String, Pace.Rate>}
  %Equal.sym(Bool, Dec.all_digits(f), False{}, Equal.trans(Bool, Dec.all_digits(f), L.all_digits(f), False{}, Equal.sym(Bool, L.all_digits(f), Dec.all_digits(f), PDec.all_same(f)), ed))
    : {Pace.of_number(_, f, rest_cut_t(rest)) == Fail{"strconv.Atoi: parsing \"" ++ f ++ "\": invalid syntax"} : Result<&2, &2, String, Pace.Rate>}
  %Equal.sym(String, Pace.quote.go(f), f, quote_id(f, e34, e92))
    : {Fail{"strconv.Atoi: parsing " ++ ("\"" ++ _ ++ "\"") ++ ": invalid syntax"} == Fail{"strconv.Atoi: parsing \"" ++ f ++ "\": invalid syntax"} : Result<&2, &2, String, Pace.Rate>}
  %Equal.sym(String, (f ++ "\"") ++ ": invalid syntax", f ++ ("\"" ++ ": invalid syntax"), app_assoc(f, "\"", ": invalid syntax"))
    : {Fail{"strconv.Atoi: parsing \"" ++ _} == Fail{"strconv.Atoi: parsing \"" ++ f ++ "\": invalid syntax"} : Result<&2, &2, String, Pace.Rate>}
  {==}

# ---------------------------------------------------------------------
# Equal bytes, equal strings (after proofs/codec.bend's weq)
# ---------------------------------------------------------------------

def fin_eq_t(t: Cmp, -ah: Bool, -bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, PNat.false_ne_true(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, PNat.false_ne_true(h))

def fin_eq_h(t: Cmp, ah: Bool, bh: Bool, h: {Cmp.is_eq(Word.cmp.fin(ah, bh, t)) == True{} : Bool}) -> {ah == bh : Bool}:
  match t:
    case LT{}:
      Empty.absurd({ah == bh : Bool}, PNat.false_ne_true(h))
    case GT{}:
      Empty.absurd({ah == bh : Bool}, PNat.false_ne_true(h))
    case EQ{}:
      match ah bh:
        case False{} False{}:
          {==}
        case True{} True{}:
          {==}
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(h))
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, PNat.false_ne_true(h))

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

def rec_eq(+c1: Char, +c2: Char, p: (String & String) & Cmp)
  -> {String.eq.fin(String.cmp.rec(c1, c2, p)) == String.eq.fin(p) : Bool}:
  ((a2, b2), c) = p
  {==}

def seq_fin(cm: Cmp, +x: U32, +y: U32, +ra: String, +rb: String, hc: {U32.cmp(x, y) == cm : Cmp},
  h: {String.eq.fin(String.cmp.fin(ra, rb, ((Chr{x}, Chr{y}), cm))) == True{} : Bool},
  ih: {String.eq(ra, rb) == True{} : Bool} -> {ra == rb : String})
  -> {SCon{Chr{x}, ra} == SCon{Chr{y}, rb} : String}:
  match cm:
    case LT{}:
      Empty.absurd({SCon{Chr{x}, ra} == SCon{Chr{y}, rb} : String}, PNat.false_ne_true(h))
    case GT{}:
      Empty.absurd({SCon{Chr{x}, ra} == SCon{Chr{y}, rb} : String}, PNat.false_ne_true(h))
    case EQ{}:
      %u32_eq(x, y, Equal.cong(Cmp, Bool, Cmp.is_eq, U32.cmp(x, y), EQ{}, hc)) : {SCon{Chr{x}, ra} == SCon{Chr{_}, rb} : String}
      %ih(Equal.trans(Bool, String.eq(ra, rb), String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(ra, rb))), True{},
          Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(ra, rb))), String.eq(ra, rb), rec_eq(Chr{x}, Chr{y}, String.cmp(ra, rb))), h))
        : {SCon{Chr{x}, ra} == SCon{Chr{x}, _} : String}
      {==}

def seq_c(ca: Char, cb: Char, +ra: String, +rb: String, h: {String.eq(SCon{ca, ra}, SCon{cb, rb}) == True{} : Bool},
  ih: {String.eq(ra, rb) == True{} : Bool} -> {ra == rb : String}) -> {SCon{ca, ra} == SCon{cb, rb} : String}:
  match ca cb:
    case Chr{+x} Chr{+y}:
      seq_fin(U32.cmp(x, y), x, y, ra, rb, {==}, h, ih)

def str_eq_sound(a: String, b: String, h: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{cb, rb}:
      Empty.absurd({SNil{} == SCon{cb, rb} : String}, PNat.false_ne_true(h))
    case SCon{ca, ra} SNil{}:
      Empty.absurd({SCon{ca, ra} == SNil{} : String}, PNat.false_ne_true(h))
    case SCon{ca, +ra} SCon{cb, +rb}:
      seq_c(ca, cb, ra, rb, h, e => str_eq_sound(ra, rb, e))

# ---------------------------------------------------------------------
# rate_parse
# ---------------------------------------------------------------------

def eqr(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eqr(p)

def and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the units with mu's atom as g
def iu(+s: String, g: Bool) -> Bool:
  Bool.or(Bool.or(Bool.or(String.eq(s, "ns"), String.eq(s, "us")), Bool.or(String.eq(s, L.micro() ++ "s"), g)),
    Bool.or(Bool.or(String.eq(s, "ms"), String.eq(s, "s")), Bool.or(String.eq(s, "m"), String.eq(s, "h"))))

def bool_id(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, +f: Bool, +g: Bool)
  -> {Bool.or(Bool.or(Bool.or(a, b), Bool.or(c, d)), Bool.or(Bool.or(e, f), g))
      == Bool.or(Bool.or(Bool.or(a, b), Bool.or(c, False{})), Bool.or(Bool.or(d, e), Bool.or(f, g))) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              match d:
                case True{}:
                  {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

def be_fin(g: Bool, +s: String, hg: {String.eq(s, L.greek_mu() ++ "s") == g : Bool})
  -> {Pace.bare_unit(s) == Bool.and(iu(s, g), Bool.not(g)) : Bool}:
  match g:
    case True{}:
      %Equal.sym(String, s, L.greek_mu() ++ "s", str_eq_sound(s, L.greek_mu() ++ "s", hg))
        : {Pace.bare_unit(_) == Bool.and(iu(_, True{}), False{}) : Bool}
      {==}
    case False{}:
      +a = String.eq(s, "ns")
      +b = String.eq(s, "us")
      +c = String.eq(s, L.micro() ++ "s")
      +d = String.eq(s, "ms")
      +e = String.eq(s, "s")
      +f = String.eq(s, "m")
      +h = String.eq(s, "h")
      Equal.trans(Bool, Pace.bare_unit(s), iu(s, False{}), Bool.and(iu(s, False{}), True{}),
        bool_id(a, b, c, d, e, f, h), Equal.sym(Bool, Bool.and(iu(s, False{}), True{}), iu(s, False{}), and_true(iu(s, False{}))))

# the port's count-of-one units are LAWS' unit names but "μs"
def bare_eq(+s: String) -> {Pace.bare_unit(s) == Bool.and(L.is_unit_name(s), Bool.not(String.eq(s, L.greek_mu() ++ "s"))) : Bool}:
  be_fin(String.eq(s, L.greek_mu() ++ "s"), s, {==})

# a digit is not the byte c, a non-digit
def dn_x(-k: U32, -c: U32, ek: {k == c : U32}, hn: {L.is_digit(Chr{c}) == False{} : Bool}) -> {L.is_digit(Chr{k}) == False{} : Bool}:
  %Equal.sym(U32, k, c, ek) : {L.is_digit(Chr{_}) == False{} : Bool}
  hn

def dn_fin(b: Bool, +k: U32, +c: U32, hb: {U32.is_eq(k, c) == b : Bool}, hd: {L.is_digit(Chr{k}) == True{} : Bool}, hn: {L.is_digit(Chr{c}) == False{} : Bool})
  -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Bool, True{}, L.is_digit(Chr{k}), False{}, Equal.sym(Bool, L.is_digit(Chr{k}), True{}, hd), dn_x(k, c, u32_eq(k, c, hb), hn))

def dig_ne(+k: U32, +c: U32, hd: {L.is_digit(Chr{k}) == True{} : Bool}, hn: {L.is_digit(Chr{c}) == False{} : Bool}) -> {U32.is_eq(k, c) == False{} : Bool}:
  dn_fin(U32.is_eq(k, c), k, c, {==}, hd, hn)

def digits_nochar(s: String, +c: U32, +hn: {L.is_digit(Chr{c}) == False{} : Bool}, +h: {L.all_digits.go(s) == True{} : Bool}) -> {L.has_char(s, c) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+ch, +r}:
      match ch:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, c), False{}, dig_ne(k, c, andT_l(L.is_digit(Chr{k}), L.all_digits.go(r), h), hn))
            : {Bool.or(_, L.has_char(r, c)) == False{} : Bool}
          digits_nochar(r, c, hn, andT_r(L.is_digit(Chr{k}), L.all_digits.go(r), h))

def nosign(+k: U32, +hd: {L.is_digit(Chr{k}) == True{} : Bool}) -> {Bool.not(Bool.or(U32.is_eq(k, 43), U32.is_eq(k, 45))) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(k, 43), False{}, dig_ne(k, 43, hd, {==})) : {Bool.not(Bool.or(_, U32.is_eq(k, 45))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(k, 45), False{}, dig_ne(k, 45, hd, {==})) : {Bool.not(Bool.or(False{}, _)) == True{} : Bool}
  {==}

def wf_of(+u: String, +b: Bool, +x: String, +m: Maybe<&2, String>) -> Result<&2, &2, String, Pace.Rate>:
  Pace.with_freq(Nat.is_eq(Dec.value(u), 0n), b, Dec.value(u), x, m)

def digits_ok(+x: String, h: {L.all_digits(x) == True{} : Bool}) -> {Dec.all_digits(x) == True{} : Bool}:
  Equal.trans(Bool, Dec.all_digits(x), L.all_digits(x), True{}, Equal.sym(Bool, L.all_digits(x), Dec.all_digits(x), PDec.all_same(x)), h)

# a run of digits, then "" or "/..."
def num_parse(x: String, +t: String, -m: Maybe<&2, String>, +e: {Pace.cut(t) == Pace.Cut{"", m} : Pace.Cut}, +hd: {L.all_digits(x) == True{} : Bool})
  -> {Pace.parse_rate(x ++ t) == wf_of(x, False{}, x, m) : Result<&2, &2, String, Pace.Rate>}:
  match x:
    case SNil{}:
      Empty.absurd({Pace.parse_rate(t) == wf_of(SNil{}, False{}, SNil{}, m) : Result<&2, &2, String, Pace.Rate>}, PNat.false_ne_true(hd))
    case SCon{+ch, +r}:
      match ch:
        case Chr{+k}:
          +hk = andT_l(L.is_digit(Chr{k}), L.all_digits.go(r), hd)
          %Equal.sym(Pace.Cut, Pace.cut(SCon{Chr{k}, r} ++ t), Pace.Cut{SCon{Chr{k}, r}, m},
              pcut_pre(SCon{Chr{k}, r}, t, m, e, digits_nochar(SCon{Chr{k}, r}, 47, {==}, hd)))
            : {pr_of(_) == wf_of(SCon{Chr{k}, r}, False{}, SCon{Chr{k}, r}, m) : Result<&2, &2, String, Pace.Rate>}
          %Equal.sym(Bool, Dec.all_digits(Pace.unsigned(SCon{Chr{k}, r})), True{},
              Equal.trans(Bool, Dec.all_digits(Pace.unsigned(SCon{Chr{k}, r})), Dec.all_digits(SCon{Chr{k}, r}), True{},
                Equal.cong(String, Bool, Dec.all_digits, Pace.unsigned(SCon{Chr{k}, r}), SCon{Chr{k}, r}, unsigned_id(SCon{Chr{k}, r}, nosign(k, hk))),
                digits_ok(SCon{Chr{k}, r}, hd)))
            : {Pace.of_number(_, SCon{Chr{k}, r}, m) == wf_of(SCon{Chr{k}, r}, False{}, SCon{Chr{k}, r}, m) : Result<&2, &2, String, Pace.Rate>}
          %Equal.sym(String, Pace.unsigned(SCon{Chr{k}, r}), SCon{Chr{k}, r}, unsigned_id(SCon{Chr{k}, r}, nosign(k, hk)))
            : {wf_of(_, U32.is_eq(k, 45), SCon{Chr{k}, r}, m) == wf_of(SCon{Chr{k}, r}, False{}, SCon{Chr{k}, r}, m) : Result<&2, &2, String, Pace.Rate>}
          %Equal.sym(Bool, U32.is_eq(k, 45), False{}, dig_ne(k, 45, hk, {==}))
            : {wf_of(SCon{Chr{k}, r}, _, SCon{Chr{k}, r}, m) == wf_of(SCon{Chr{k}, r}, False{}, SCon{Chr{k}, r}, m) : Result<&2, &2, String, Pace.Rate>}
          {==}

def show_digits(+n: Nat) -> {L.all_digits(Dec.show(n)) == True{} : Bool}:
  +s = Dec.show(n)
  andT_l(L.all_digits(s), Bool.or(String.eq(s, "0"), Bool.not(String.starts_with(s, "0"))), L.dec_show_canonical(n))

def show_value(+n: Nat) -> {Dec.value(Dec.show(n)) == n : Nat}:
  Equal.trans(Nat, Dec.value(Dec.show(n)), L.digits_value(Dec.show(n)), n,
    Equal.sym(Nat, L.digits_value(Dec.show(n)), Dec.value(Dec.show(n)), PDec.value_go_same(Dec.show(n), 0n)), L.dec_show_value(n))

def wf_pos(+x: String, +n: Nat, +m: Maybe<&2, String>) -> Result<&2, &2, String, Pace.Rate>:
  Pace.with_freq(Nat.is_eq(n, 0n), False{}, n, x, m)

# "N" and "N/..." for a positive N
def pr_n(+n: Nat, +t: String, -m: Maybe<&2, String>, +e: {Pace.cut(t) == Pace.Cut{"", m} : Pace.Cut})
  -> {Pace.parse_rate(Dec.show(1n+n) ++ t) == Pace.with_tail(m, 1n+n) : Result<&2, &2, String, Pace.Rate>}:
  %Equal.sym(Result<&2, &2, String, Pace.Rate>, Pace.parse_rate(Dec.show(1n+n) ++ t), wf_of(Dec.show(1n+n), False{}, Dec.show(1n+n), m), num_parse(Dec.show(1n+n), t, m, e, show_digits(1n+n)))
    : {_ == Pace.with_tail(m, 1n+n) : Result<&2, &2, String, Pace.Rate>}
  %Equal.sym(Nat, Dec.value(Dec.show(1n+n)), 1n+n, show_value(1n+n))
    : {wf_pos(Dec.show(1n+n), _, m) == Pace.with_tail(m, 1n+n) : Result<&2, &2, String, Pace.Rate>}
  {==}

def rp3(+n: Nat) -> {Pace.parse_rate(Dec.show(1n+n)) == Done{Pace.Rate{1n+n, L.sec()}} : Result<&2, &2, String, Pace.Rate>}:
  %app_nil(Dec.show(1n+n)) : {Pace.parse_rate(_) == Done{Pace.Rate{1n+n, L.sec()}} : Result<&2, &2, String, Pace.Rate>}
  pr_n(n, "", None{}, {==})

def rw_per(m: Maybe<&2, Nat>, +f: Nat, +s: String) -> {L.rate_with(f, m, Pace.with_per(m, f, s)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+p}:
      %Equal.sym(Bool, Nat.is_eq(f, f), True{}, eqr(f)) : {Bool.and(_, Nat.is_eq(p, p)) == True{} : Bool}
      eqr(p)

def c4(b: Bool, +n: Nat, +s: String)
  -> {Bool.or(b, L.rate_with(1n+n, Dur.parse(s), Pace.with_per(Dur.parse(Pace.pick(String, b, "1" ++ s, s)), 1n+n, Pace.pick(String, b, "1" ++ s, s)))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      rw_per(Dur.parse(s), 1n+n, s)

def bc_of(+s: String) -> Bool:
  Bool.and(L.is_unit_name(s), Bool.not(String.eq(s, L.greek_mu() ++ "s")))

def c4_of(+n: Nat, +b: Bool, +s: String) -> Bool:
  Bool.or(bc_of(s), L.rate_with(1n+n, Dur.parse(s), Pace.with_per(Dur.parse(Pace.pick(String, b, "1" ++ s, s)), 1n+n, Pace.pick(String, b, "1" ++ s, s))))

def rp4(+n: Nat, +s: String)
  -> {Bool.or(bc_of(s), L.rate_with(1n+n, Dur.parse(s), Pace.parse_rate(Dec.show(1n+n) ++ "/" ++ s))) == True{} : Bool}:
  %Equal.sym(Result<&2, &2, String, Pace.Rate>, Pace.parse_rate(Dec.show(1n+n) ++ "/" ++ s), Pace.with_tail(Some{s}, 1n+n), pr_n(n, "/" ++ s, Some{s}, {==}))
    : {Bool.or(bc_of(s), L.rate_with(1n+n, Dur.parse(s), _)) == True{} : Bool}
  %Equal.sym(Bool, Pace.bare_unit(s), bc_of(s), bare_eq(s)) : {c4_of(n, _, s) == True{} : Bool}
  c4(bc_of(s), n, s)

def rs_refl(m: Maybe<&2, Nat>, +f: Nat, +t: String) -> {L.rate_same(Pace.with_per(m, f, t), Pace.with_per(m, f, t)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+p}:
      %Equal.sym(Bool, Nat.is_eq(f, f), True{}, eqr(f)) : {Bool.and(_, Nat.is_eq(p, p)) == True{} : Bool}
      eqr(p)

def c5(b: Bool, +n: Nat, +s: String)
  -> {L.pick(Bool, b, L.rate_same(Pace.with_per(Dur.parse(Pace.pick(String, b, "1" ++ s, s)), 1n+n, Pace.pick(String, b, "1" ++ s, s)),
        Pace.with_per(Dur.parse("1" ++ s), 1n+n, "1" ++ s)), True{}) == True{} : Bool}:
  match b:
    case True{}:
      rs_refl(Dur.parse("1" ++ s), 1n+n, "1" ++ s)
    case False{}:
      {==}

def c5_of(+n: Nat, +b: Bool, +s: String) -> Bool:
  L.pick(Bool, bc_of(s), L.rate_same(Pace.with_per(Dur.parse(Pace.pick(String, b, "1" ++ s, s)), 1n+n, Pace.pick(String, b, "1" ++ s, s)),
    Pace.with_per(Dur.parse("1" ++ s), 1n+n, "1" ++ s)), True{})

def rp5(+n: Nat, +s: String)
  -> {L.pick(Bool, bc_of(s), L.rate_same(Pace.parse_rate(Dec.show(1n+n) ++ "/" ++ s), Pace.parse_rate(Dec.show(1n+n) ++ "/1" ++ s)), True{}) == True{} : Bool}:
  %Equal.sym(Result<&2, &2, String, Pace.Rate>, Pace.parse_rate(Dec.show(1n+n) ++ "/" ++ s), Pace.with_tail(Some{s}, 1n+n), pr_n(n, "/" ++ s, Some{s}, {==}))
    : {L.pick(Bool, bc_of(s), L.rate_same(_, Pace.parse_rate(Dec.show(1n+n) ++ "/1" ++ s)), True{}) == True{} : Bool}
  %Equal.sym(Result<&2, &2, String, Pace.Rate>, Pace.parse_rate(Dec.show(1n+n) ++ "/1" ++ s), Pace.with_tail(Some{"1" ++ s}, 1n+n), pr_n(n, "/1" ++ s, Some{"1" ++ s}, {==}))
    : {L.pick(Bool, bc_of(s), L.rate_same(Pace.with_tail(Some{s}, 1n+n), _), True{}) == True{} : Bool}
  %Equal.sym(Bool, Pace.bare_unit(s), bc_of(s), bare_eq(s)) : {c5_of(n, _, s) == True{} : Bool}
  c5(bc_of(s), n, s)



# ---------------------------------------------------------------------
# Bytes, bit by bit: facts about one U32 checked on every byte value
# ---------------------------------------------------------------------

def beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}

def beq_sound(a: Bool, b: Bool, h: {beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, PNat.false_ne_true(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, PNat.false_ne_true(h))

def ows(+k: U32) -> Bool:
  Bool.or(U32.is_eq(k, 32), U32.is_eq(k, 9))

def mku(+b0: Bool, +b1: Bool, +b2: Bool, +b3: Bool, +b4: Bool, +b5: Bool, +b6: Bool, +b7: Bool, +b8: Bool, +b9: Bool, +b10: Bool, +b11: Bool, +b12: Bool, +b13: Bool, +b14: Bool, +b15: Bool, +b16: Bool, +b17: Bool, +b18: Bool, +b19: Bool, +b20: Bool, +b21: Bool, +b22: Bool, +b23: Bool, +b24: Bool, +b25: Bool, +b26: Bool, +b27: Bool, +b28: Bool, +b29: Bool, +b30: Bool, +b31: Bool) -> U32:
  U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def bl_space.go(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) -> {Bool.or(Bool.not(L.in_range32(mku(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31), 32, 126)), beq(Flags.is_space(mku(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)), ows(mku(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)))) == True{} : Bool}:
  match b31:
    case True{}:
      {==}
    case False{}:
      match b30:
        case True{}:
          {==}
        case False{}:
          match b29:
            case True{}:
              {==}
            case False{}:
              match b28:
                case True{}:
                  {==}
                case False{}:
                  match b27:
                    case True{}:
                      {==}
                    case False{}:
                      match b26:
                        case True{}:
                          {==}
                        case False{}:
                          match b25:
                            case True{}:
                              {==}
                            case False{}:
                              match b24:
                                case True{}:
                                  {==}
                                case False{}:
                                  match b23:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b22:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match b21:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              match b20:
                                                case True{}:
                                                  {==}
                                                case False{}:
                                                  match b19:
                                                    case True{}:
                                                      {==}
                                                    case False{}:
                                                      match b18:
                                                        case True{}:
                                                          {==}
                                                        case False{}:
                                                          match b17:
                                                            case True{}:
                                                              {==}
                                                            case False{}:
                                                              match b16:
                                                                case True{}:
                                                                  {==}
                                                                case False{}:
                                                                  match b15:
                                                                    case True{}:
                                                                      {==}
                                                                    case False{}:
                                                                      match b14:
                                                                        case True{}:
                                                                          {==}
                                                                        case False{}:
                                                                          match b13:
                                                                            case True{}:
                                                                              {==}
                                                                            case False{}:
                                                                              match b12:
                                                                                case True{}:
                                                                                  {==}
                                                                                case False{}:
                                                                                  match b11:
                                                                                    case True{}:
                                                                                      {==}
                                                                                    case False{}:
                                                                                      match b10:
                                                                                        case True{}:
                                                                                          {==}
                                                                                        case False{}:
                                                                                          match b9:
                                                                                            case True{}:
                                                                                              {==}
                                                                                            case False{}:
                                                                                              match b8:
                                                                                                case True{}:
                                                                                                  {==}
                                                                                                case False{}:
                                                                                                  match b7:
                                                                                                    case True{}:
                                                                                                      {==}
                                                                                                    case False{}:
                                                                                                      match b6:
                                                                                                        case True{}:
                                                                                                          match b5:
                                                                                                            case True{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                            case False{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                        case False{}:
                                                                                                          match b5:
                                                                                                            case True{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                            case False{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}

def bl_space(k: U32) -> {Bool.or(Bool.not(L.in_range32(k, 32, 126)), beq(Flags.is_space(k), ows(k))) == True{} : Bool}:
  match k:
    case U32{w}:
      match w:
        case WCon{b0, t0}:
          match t0:
            case WCon{b1, t1}:
              match t1:
                case WCon{b2, t2}:
                  match t2:
                    case WCon{b3, t3}:
                      match t3:
                        case WCon{b4, t4}:
                          match t4:
                            case WCon{b5, t5}:
                              match t5:
                                case WCon{b6, t6}:
                                  match t6:
                                    case WCon{b7, t7}:
                                      match t7:
                                        case WCon{b8, t8}:
                                          match t8:
                                            case WCon{b9, t9}:
                                              match t9:
                                                case WCon{b10, t10}:
                                                  match t10:
                                                    case WCon{b11, t11}:
                                                      match t11:
                                                        case WCon{b12, t12}:
                                                          match t12:
                                                            case WCon{b13, t13}:
                                                              match t13:
                                                                case WCon{b14, t14}:
                                                                  match t14:
                                                                    case WCon{b15, t15}:
                                                                      match t15:
                                                                        case WCon{b16, t16}:
                                                                          match t16:
                                                                            case WCon{b17, t17}:
                                                                              match t17:
                                                                                case WCon{b18, t18}:
                                                                                  match t18:
                                                                                    case WCon{b19, t19}:
                                                                                      match t19:
                                                                                        case WCon{b20, t20}:
                                                                                          match t20:
                                                                                            case WCon{b21, t21}:
                                                                                              match t21:
                                                                                                case WCon{b22, t22}:
                                                                                                  match t22:
                                                                                                    case WCon{b23, t23}:
                                                                                                      match t23:
                                                                                                        case WCon{b24, t24}:
                                                                                                          match t24:
                                                                                                            case WCon{b25, t25}:
                                                                                                              match t25:
                                                                                                                case WCon{b26, t26}:
                                                                                                                  match t26:
                                                                                                                    case WCon{b27, t27}:
                                                                                                                      match t27:
                                                                                                                        case WCon{b28, t28}:
                                                                                                                          match t28:
                                                                                                                            case WCon{b29, t29}:
                                                                                                                              match t29:
                                                                                                                                case WCon{b30, t30}:
                                                                                                                                  match t30:
                                                                                                                                    case WCon{b31, t31}:
                                                                                                                                      match t31:
                                                                                                                                        case WNil{}:
                                                                                                                                          bl_space.go(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

def bl_token.go(+b31: Bool, +b30: Bool, +b29: Bool, +b28: Bool, +b27: Bool, +b26: Bool, +b25: Bool, +b24: Bool, +b23: Bool, +b22: Bool, +b21: Bool, +b20: Bool, +b19: Bool, +b18: Bool, +b17: Bool, +b16: Bool, +b15: Bool, +b14: Bool, +b13: Bool, +b12: Bool, +b11: Bool, +b10: Bool, +b9: Bool, +b8: Bool, +b7: Bool, +b6: Bool, +b5: Bool, +b4: Bool, +b3: Bool, +b2: Bool, +b1: Bool, +b0: Bool) -> {Bool.or(Bool.not(L.token_byte(mku(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31))), Bool.and(Bool.and(L.in_range32(mku(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31), 32, 126), Bool.not(ows(mku(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31)))), Bool.not(U32.is_eq(mku(b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31), 58)))) == True{} : Bool}:
  match b31:
    case True{}:
      {==}
    case False{}:
      match b30:
        case True{}:
          {==}
        case False{}:
          match b29:
            case True{}:
              {==}
            case False{}:
              match b28:
                case True{}:
                  {==}
                case False{}:
                  match b27:
                    case True{}:
                      {==}
                    case False{}:
                      match b26:
                        case True{}:
                          {==}
                        case False{}:
                          match b25:
                            case True{}:
                              {==}
                            case False{}:
                              match b24:
                                case True{}:
                                  {==}
                                case False{}:
                                  match b23:
                                    case True{}:
                                      {==}
                                    case False{}:
                                      match b22:
                                        case True{}:
                                          {==}
                                        case False{}:
                                          match b21:
                                            case True{}:
                                              {==}
                                            case False{}:
                                              match b20:
                                                case True{}:
                                                  {==}
                                                case False{}:
                                                  match b19:
                                                    case True{}:
                                                      {==}
                                                    case False{}:
                                                      match b18:
                                                        case True{}:
                                                          {==}
                                                        case False{}:
                                                          match b17:
                                                            case True{}:
                                                              {==}
                                                            case False{}:
                                                              match b16:
                                                                case True{}:
                                                                  {==}
                                                                case False{}:
                                                                  match b15:
                                                                    case True{}:
                                                                      {==}
                                                                    case False{}:
                                                                      match b14:
                                                                        case True{}:
                                                                          {==}
                                                                        case False{}:
                                                                          match b13:
                                                                            case True{}:
                                                                              {==}
                                                                            case False{}:
                                                                              match b12:
                                                                                case True{}:
                                                                                  {==}
                                                                                case False{}:
                                                                                  match b11:
                                                                                    case True{}:
                                                                                      {==}
                                                                                    case False{}:
                                                                                      match b10:
                                                                                        case True{}:
                                                                                          {==}
                                                                                        case False{}:
                                                                                          match b9:
                                                                                            case True{}:
                                                                                              {==}
                                                                                            case False{}:
                                                                                              match b8:
                                                                                                case True{}:
                                                                                                  {==}
                                                                                                case False{}:
                                                                                                  match b7:
                                                                                                    case True{}:
                                                                                                      {==}
                                                                                                    case False{}:
                                                                                                      match b6:
                                                                                                        case True{}:
                                                                                                          match b5:
                                                                                                            case True{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                            case False{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                        case False{}:
                                                                                                          match b5:
                                                                                                            case True{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                            case False{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                    case False{}:
                                                                                                                      match b2:
                                                                                                                        case True{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                        case False{}:
                                                                                                                          match b1:
                                                                                                                            case True{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}
                                                                                                                            case False{}:
                                                                                                                              match b0:
                                                                                                                                case True{}:
                                                                                                                                  {==}
                                                                                                                                case False{}:
                                                                                                                                  {==}

def bl_token(k: U32) -> {Bool.or(Bool.not(L.token_byte(k)), Bool.and(Bool.and(L.in_range32(k, 32, 126), Bool.not(ows(k))), Bool.not(U32.is_eq(k, 58)))) == True{} : Bool}:
  match k:
    case U32{w}:
      match w:
        case WCon{b0, t0}:
          match t0:
            case WCon{b1, t1}:
              match t1:
                case WCon{b2, t2}:
                  match t2:
                    case WCon{b3, t3}:
                      match t3:
                        case WCon{b4, t4}:
                          match t4:
                            case WCon{b5, t5}:
                              match t5:
                                case WCon{b6, t6}:
                                  match t6:
                                    case WCon{b7, t7}:
                                      match t7:
                                        case WCon{b8, t8}:
                                          match t8:
                                            case WCon{b9, t9}:
                                              match t9:
                                                case WCon{b10, t10}:
                                                  match t10:
                                                    case WCon{b11, t11}:
                                                      match t11:
                                                        case WCon{b12, t12}:
                                                          match t12:
                                                            case WCon{b13, t13}:
                                                              match t13:
                                                                case WCon{b14, t14}:
                                                                  match t14:
                                                                    case WCon{b15, t15}:
                                                                      match t15:
                                                                        case WCon{b16, t16}:
                                                                          match t16:
                                                                            case WCon{b17, t17}:
                                                                              match t17:
                                                                                case WCon{b18, t18}:
                                                                                  match t18:
                                                                                    case WCon{b19, t19}:
                                                                                      match t19:
                                                                                        case WCon{b20, t20}:
                                                                                          match t20:
                                                                                            case WCon{b21, t21}:
                                                                                              match t21:
                                                                                                case WCon{b22, t22}:
                                                                                                  match t22:
                                                                                                    case WCon{b23, t23}:
                                                                                                      match t23:
                                                                                                        case WCon{b24, t24}:
                                                                                                          match t24:
                                                                                                            case WCon{b25, t25}:
                                                                                                              match t25:
                                                                                                                case WCon{b26, t26}:
                                                                                                                  match t26:
                                                                                                                    case WCon{b27, t27}:
                                                                                                                      match t27:
                                                                                                                        case WCon{b28, t28}:
                                                                                                                          match t28:
                                                                                                                            case WCon{b29, t29}:
                                                                                                                              match t29:
                                                                                                                                case WCon{b30, t30}:
                                                                                                                                  match t30:
                                                                                                                                    case WCon{b31, t31}:
                                                                                                                                      match t31:
                                                                                                                                        case WNil{}:
                                                                                                                                          bl_token.go(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0)

# ---------------------------------------------------------------------
# flags_header
# ---------------------------------------------------------------------

def or_not_t(a: Bool, -b: Bool, h1: {Bool.or(Bool.not(a), b) == True{} : Bool}, h2: {a == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h1
    case False{}:
      Empty.absurd({b == True{} : Bool}, PNat.false_ne_true(h2))

def and_i(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def tb_all(+k: U32, h: {L.token_byte(k) == True{} : Bool})
  -> {Bool.and(Bool.and(L.in_range32(k, 32, 126), Bool.not(ows(k))), Bool.not(U32.is_eq(k, 58))) == True{} : Bool}:
  or_not_t(L.token_byte(k), Bool.and(Bool.and(L.in_range32(k, 32, 126), Bool.not(ows(k))), Bool.not(U32.is_eq(k, 58))), bl_token(k), h)

def tb_inr(+k: U32, h: {L.token_byte(k) == True{} : Bool}) -> {L.in_range32(k, 32, 126) == True{} : Bool}:
  andT_l(L.in_range32(k, 32, 126), Bool.not(ows(k)), andT_l(Bool.and(L.in_range32(k, 32, 126), Bool.not(ows(k))), Bool.not(U32.is_eq(k, 58)), tb_all(k, h)))

def tb_ows(+k: U32, h: {L.token_byte(k) == True{} : Bool}) -> {ows(k) == False{} : Bool}:
  notT(ows(k), andT_r(L.in_range32(k, 32, 126), Bool.not(ows(k)), andT_l(Bool.and(L.in_range32(k, 32, 126), Bool.not(ows(k))), Bool.not(U32.is_eq(k, 58)), tb_all(k, h))))

def tb_58(+k: U32, h: {L.token_byte(k) == True{} : Bool}) -> {U32.is_eq(k, 58) == False{} : Bool}:
  notT(U32.is_eq(k, 58), andT_r(Bool.and(L.in_range32(k, 32, 126), Bool.not(ows(k))), Bool.not(U32.is_eq(k, 58)), tb_all(k, h)))

# on printable bytes Go's TrimSpace and textproto's trim agree
def sp_eq(+k: U32, h: {L.in_range32(k, 32, 126) == True{} : Bool}) -> {Flags.is_space(k) == ows(k) : Bool}:
  beq_sound(Flags.is_space(k), ows(k), or_not_t(L.in_range32(k, 32, 126), beq(Flags.is_space(k), ows(k)), bl_space(k), h))

def picks_eq(-A: Data, c: Bool, +x: A, +y: A) -> {Flags.pick(A, c, x, y) == L.pick(A, c, x, y) : A}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tl_eq(s: String, +h: {L.printable(s) == True{} : Bool}) -> {Flags.trim_l(s) == L.trim_ows_l(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, Flags.is_space(k), ows(k), sp_eq(k, andT_l(L.in_range32(k, 32, 126), L.printable(r), h)))
            : {Flags.pick(String, _, Flags.trim_l(r), SCon{Chr{k}, r}) == L.pick(String, ows(k), L.trim_ows_l(r), SCon{Chr{k}, r}) : String}
          %Equal.sym(String, Flags.trim_l(r), L.trim_ows_l(r), tl_eq(r, andT_r(L.in_range32(k, 32, 126), L.printable(r), h)))
            : {Flags.pick(String, ows(k), _, SCon{Chr{k}, r}) == L.pick(String, ows(k), L.trim_ows_l(r), SCon{Chr{k}, r}) : String}
          picks_eq(String, ows(k), L.trim_ows_l(r), SCon{Chr{k}, r})

def pick_pr(c: Bool, -x: String, -y: String, hx: {L.printable(x) == True{} : Bool}, hy: {L.printable(y) == True{} : Bool})
  -> {L.printable(L.pick(String, c, x, y)) == True{} : Bool}:
  match c:
    case True{}:
      hx
    case False{}:
      hy

def pr_tlo(s: String, +h: {L.printable(s) == True{} : Bool}) -> {L.printable(L.trim_ows_l(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      pick_pr(Bool.or(U32.is_eq(L.code(c), 32), U32.is_eq(L.code(c), 9)), L.trim_ows_l(r), SCon{c, r},
        pr_tlo(r, andT_r(L.in_range32(L.code(c), 32, 126), L.printable(r), h)), h)

def pr_rev(s: String, +acc: String, +hs: {L.printable(s) == True{} : Bool}, +ha: {L.printable(acc) == True{} : Bool})
  -> {L.printable(String.reverse.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      ha
    case SCon{+c, +r}:
      pr_rev(r, SCon{c, acc}, andT_r(L.in_range32(L.code(c), 32, 126), L.printable(r), hs),
        and_i(L.in_range32(L.code(c), 32, 126), L.printable(acc), andT_l(L.in_range32(L.code(c), 32, 126), L.printable(r), hs), ha))

# Go's TrimSpace is textproto's trim on printable text
def trim_eq(+s: String, +h: {L.printable(s) == True{} : Bool}) -> {Flags.trim(s) == L.trim_ows(s) : String}:
  %Equal.sym(String, Flags.trim_l(s), L.trim_ows_l(s), tl_eq(s, h))
    : {String.reverse(Flags.trim_l(String.reverse(_))) == L.trim_ows(s) : String}
  %Equal.sym(String, Flags.trim_l(String.reverse(L.trim_ows_l(s))), L.trim_ows_l(String.reverse(L.trim_ows_l(s))),
      tl_eq(String.reverse(L.trim_ows_l(s)), pr_rev(L.trim_ows_l(s), "", pr_tlo(s, h), {==})))
    : {String.reverse(_) == L.trim_ows(s) : String}
  {==}

# no space or tab anywhere
def nows(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +r}:
      Bool.and(Bool.not(ows(L.code(c))), nows(r))

def pick_fL(-A: Data, c: Bool, -a: A, -b: A, e: {c == False{} : Bool}) -> {L.pick(A, c, a, b) == b : A}:
  %Equal.sym(Bool, c, False{}, e) : {L.pick(A, _, a, b) == b : A}
  {==}

def tlo_id(s: String, h: {nows(s) == True{} : Bool}) -> {L.trim_ows_l(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      pick_fL(String, ows(L.code(c)), L.trim_ows_l(r), SCon{c, r}, notT(ows(L.code(c)), andT_l(Bool.not(ows(L.code(c))), nows(r), h)))

def nows_rev(s: String, +acc: String, +hs: {nows(s) == True{} : Bool}, +ha: {nows(acc) == True{} : Bool})
  -> {nows(String.reverse.go(s, acc)) == True{} : Bool}:
  match s:
    case SNil{}:
      ha
    case SCon{+c, +r}:
      nows_rev(r, SCon{c, acc}, andT_r(Bool.not(ows(L.code(c))), nows(r), hs),
        and_i(Bool.not(ows(L.code(c))), nows(acc), andT_l(Bool.not(ows(L.code(c))), nows(r), hs), ha))

def rr(s: String, +a: String) -> {String.reverse.go(String.reverse.go(s, a), "") == String.reverse.go(a, s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      rr(t, SCon{h, a})

def tows_id(+k: String, +h: {nows(k) == True{} : Bool}) -> {L.trim_ows(k) == k : String}:
  %Equal.sym(String, L.trim_ows_l(k), k, tlo_id(k, h))
    : {String.reverse(L.trim_ows_l(String.reverse(_))) == k : String}
  %Equal.sym(String, L.trim_ows_l(String.reverse(k)), String.reverse(k), tlo_id(String.reverse(k), nows_rev(k, "", h, {==})))
    : {String.reverse(_) == k : String}
  rr(k, "")

def tok_pr(s: String, +h: {L.all_token(s) == True{} : Bool}) -> {L.printable(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      %Equal.sym(Bool, L.in_range32(L.code(c), 32, 126), True{}, tb_inr(L.code(c), andT_l(L.token_byte(L.code(c)), L.all_token(r), h)))
        : {Bool.and(_, L.printable(r)) == True{} : Bool}
      tok_pr(r, andT_r(L.token_byte(L.code(c)), L.all_token(r), h))

def tok_nows(s: String, +h: {L.all_token(s) == True{} : Bool}) -> {nows(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      %Equal.sym(Bool, ows(L.code(c)), False{}, tb_ows(L.code(c), andT_l(L.token_byte(L.code(c)), L.all_token(r), h)))
        : {Bool.and(Bool.not(_), nows(r)) == True{} : Bool}
      tok_nows(r, andT_r(L.token_byte(L.code(c)), L.all_token(r), h))

def tok_58(s: String, +h: {L.all_token(s) == True{} : Bool}) -> {L.has_char(s, 58) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      %Equal.sym(Bool, U32.is_eq(L.code(c), 58), False{}, tb_58(L.code(c), andT_l(L.token_byte(L.code(c)), L.all_token(r), h)))
        : {Bool.or(_, L.has_char(r, 58)) == False{} : Bool}
      tok_58(r, andT_r(L.token_byte(L.code(c)), L.all_token(r), h))

def bfin_refl(b: Bool) -> {Word.cmp.fin(b, b, EQ{}) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def w_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, w_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          bfin_refl(b)

def u_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      w_refl(32n, w)

def s_refl(s: String) -> {String.eq(s, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +r}:
      match c:
        case Chr{+x}:
          %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u_refl(x))
            : {String.eq.fin(String.cmp.fin(r, r, ((Chr{x}, Chr{x}), _))) == True{} : Bool}
          %Equal.sym(Bool, String.eq.fin(String.cmp.rec(Chr{x}, Chr{x}, String.cmp(r, r))), String.eq(r, r), rec_eq(Chr{x}, Chr{x}, String.cmp(r, r)))
            : {_ == True{} : Bool}
          s_refl(r)

def fcut_pre(f: String, +q: U32, +t: String, -m: Maybe<&2, String>, +e: {Flags.cut(q, t) == Flags.Cut{"", m} : Flags.Cut}, +h: {L.has_char(f, q) == False{} : Bool})
  -> {Flags.cut(q, f ++ t) == Flags.Cut{f, m} : Flags.Cut}:
  match f:
    case SNil{}:
      e
    case SCon{+c, +r}:
      match c:
        case Chr{+k}:
          %Equal.sym(Bool, U32.is_eq(k, q), False{}, orF_l(U32.is_eq(k, q), L.has_char(r, q), h))
            : {Flags.pick(Flags.Cut, _, Flags.Cut{"", Some{r ++ t}}, Flags.cut_cons(Chr{k}, Flags.cut(q, r ++ t))) == Flags.Cut{SCon{Chr{k}, r}, m} : Flags.Cut}
          %Equal.sym(Flags.Cut, Flags.cut(q, r ++ t), Flags.Cut{r, m}, fcut_pre(r, q, t, m, e, orF_r(U32.is_eq(k, q), L.has_char(r, q), h)))
            : {Flags.cut_cons(Chr{k}, _) == Flags.Cut{SCon{Chr{k}, r}, m} : Flags.Cut}
          {==}

# hdr_val with the cut as a parameter
def hv(+c: Flags.Cut, +s: String, +a: Flags.Attack) -> Result<&2, &2, String, Flags.Attack>:
  +k = Flags.trim(Flags.cut_head(c))
  +val = Flags.trim(Maybe.default(&2, String, Flags.cut_tail(c), ""))
  Flags.hdr_of(Bool.and(Maybe.is_some(&2, String, Flags.cut_tail(c)), Bool.and(Bool.not(String.is_empty(k)), Bool.not(String.is_empty(val)))), k, val, s, a)

def hv2(+tk: String, +tr: String, +s: String, +a: Flags.Attack) -> Result<&2, &2, String, Flags.Attack>:
  Flags.hdr_of(Bool.and(Bool.not(String.is_empty(tk)), Bool.not(String.is_empty(tr))), tk, tr, s, a)

def hv3(+ek: Bool, +ev: Bool, +k: String, +v: String, +s: String, +a: Flags.Attack) -> Result<&2, &2, String, Flags.Attack>:
  Flags.hdr_of(Bool.and(Bool.not(ek), Bool.not(ev)), k, v, s, a)

# a good "k:r" header adds the value under its name
def hv_ok(+k: String, +r: String, +v: String, +a: Flags.Attack,
  +hk58: {L.has_char(k, 58) == False{} : Bool}, +etk: {Flags.trim(k) == k : String}, +etv: {Flags.trim(r) == v : String},
  +ek: {String.is_empty(k) == False{} : Bool}, +ev: {String.is_empty(v) == False{} : Bool})
  -> {Flags.hdr_val(k ++ ":" ++ r, a) == Done{Flags.set_headers(a, Flags.hdr_add(Flags.headers_of(a), k, v))} : Result<&2, &2, String, Flags.Attack>}:
  %Equal.sym(Flags.Cut, Flags.cut(58, k ++ ":" ++ r), Flags.Cut{k, Some{r}}, fcut_pre(k, 58, ":" ++ r, Some{r}, {==}, hk58))
    : {hv(_, k ++ ":" ++ r, a) == Done{Flags.set_headers(a, Flags.hdr_add(Flags.headers_of(a), k, v))} : Result<&2, &2, String, Flags.Attack>}
  %Equal.sym(String, Flags.trim(k), k, etk)
    : {hv2(_, Flags.trim(r), k ++ ":" ++ r, a) == Done{Flags.set_headers(a, Flags.hdr_add(Flags.headers_of(a), k, v))} : Result<&2, &2, String, Flags.Attack>}
  %Equal.sym(String, Flags.trim(r), v, etv)
    : {hv2(k, _, k ++ ":" ++ r, a) == Done{Flags.set_headers(a, Flags.hdr_add(Flags.headers_of(a), k, v))} : Result<&2, &2, String, Flags.Attack>}
  %Equal.sym(Bool, String.is_empty(k), False{}, ek)
    : {hv3(_, String.is_empty(v), k, v, k ++ ":" ++ r, a) == Done{Flags.set_headers(a, Flags.hdr_add(Flags.headers_of(a), k, v))} : Result<&2, &2, String, Flags.Attack>}
  %Equal.sym(Bool, String.is_empty(v), False{}, ev)
    : {hv3(False{}, _, k, v, k ++ ":" ++ r, a) == Done{Flags.set_headers(a, Flags.hdr_add(Flags.headers_of(a), k, v))} : Result<&2, &2, String, Flags.Attack>}
  {==}

def hdr_goal(+k: String, +v: String) -> Result<&2, &2, String, Flags.Attack>:
  Done{Flags.Attack{Pace.Rate{50n, L.sec()}, 0n, "stdin", "http", "stdout", "", 10n, None{}, None{},
        [Hdr.Header{k, [v, v]}], None{}, True{}, None{}, Some{10n}, "csv"}}

def w1(+r: Result<&2, &2, String, Flags.Attack>, +k: String, +v: String) -> Result<&2, &2, String, Flags.Attack>:
  +st = Flags.st_of(r, ["-header", k ++ ":" ++ v])
  Flags.attack_fin(Flags.attack_loop(4n, Flags.st_stop(st), Flags.st_rest(st), Flags.st_res(st)))

def wn(+n: Nat, +r: Result<&2, &2, String, Flags.Attack>) -> Result<&2, &2, String, Flags.Attack>:
  +st = Flags.st_of(r, [])
  Flags.attack_fin(Flags.attack_loop(n, Flags.st_stop(st), Flags.st_rest(st), Flags.st_res(st)))

def a1(+k: String, +v: String) -> Flags.Attack:
  Flags.set_headers(Flags.attack_defaults(), Flags.hdr_add([], k, v))

def af(+b: Bool, +k: String, +v: String) -> Result<&2, &2, String, Flags.Attack>:
  Done{Flags.Attack{Pace.Rate{50n, 1000000000n}, 0n, "stdin", "http", "stdout", "", 10n, None{}, None{},
    Flags.pick(List<&2, Hdr.Header>, b, Con{Hdr.Header{k, List.append(&2, String, [v], [v])}, []}, Con{Hdr.Header{k, [v]}, Flags.hdr_add([], k, v)}),
    None{}, True{}, None{}, Some{10n}, "csv"}}

def header1(+k: String, +v: String,
  +h0: {Bool.and(L.tgt_key_ok(k), Bool.and(L.flag_str_ok(v), String.eq(L.trim_ows(v), v))) == True{} : Bool})
  -> {Flags.parse_attack(["-header", k ++ ": " ++ v, "-header", k ++ ":" ++ v]) == hdr_goal(k, v) : Result<&2, &2, String, Flags.Attack>}:
  +hk = andT_l(L.tgt_key_ok(k), Bool.and(L.flag_str_ok(v), String.eq(L.trim_ows(v), v)), h0)
  +hvv = andT_r(L.tgt_key_ok(k), Bool.and(L.flag_str_ok(v), String.eq(L.trim_ows(v), v)), h0)
  +htok = andT_l(L.token(k), Bool.not(Bool.or(String.starts_with(k, "#"), String.starts_with(k, "@"))), hk)
  +ek = notT(String.is_empty(k), andT_l(Bool.not(String.is_empty(k)), L.all_token(k), htok))
  +at = andT_r(Bool.not(String.is_empty(k)), L.all_token(k), htok)
  +hfs = andT_l(L.flag_str_ok(v), String.eq(L.trim_ows(v), v), hvv)
  +pv = andT_l(L.printable(v), Bool.not(String.is_empty(v)), hfs)
  +ev = notT(String.is_empty(v), andT_r(L.printable(v), Bool.not(String.is_empty(v)), hfs))
  +etv0 = str_eq_sound(L.trim_ows(v), v, andT_r(L.flag_str_ok(v), String.eq(L.trim_ows(v), v), hvv))
  +etv = Equal.trans(String, Flags.trim(v), L.trim_ows(v), v, trim_eq(v, pv), etv0)
  +etk = Equal.trans(String, Flags.trim(k), L.trim_ows(k), k, trim_eq(k, tok_pr(k, at)), tows_id(k, tok_nows(k, at)))
  +hk58 = tok_58(k, at)
  %Equal.sym(Result<&2, &2, String, Flags.Attack>, Flags.hdr_val(k ++ ":" ++ " " ++ v, Flags.attack_defaults()), Done{a1(k, v)},
      hv_ok(k, " " ++ v, v, Flags.attack_defaults(), hk58, etk, etv, ek, ev))
    : {w1(_, k, v) == hdr_goal(k, v) : Result<&2, &2, String, Flags.Attack>}
  %Equal.sym(Result<&2, &2, String, Flags.Attack>, Flags.hdr_val(k ++ ":" ++ v, a1(k, v)), Done{Flags.set_headers(a1(k, v), Flags.hdr_add(Flags.headers_of(a1(k, v)), k, v))},
      hv_ok(k, v, v, a1(k, v), hk58, etk, etv, ek, ev))
    : {wn(3n, _) == hdr_goal(k, v) : Result<&2, &2, String, Flags.Attack>}
  %Equal.sym(Bool, String.eq(k, k), True{}, s_refl(k))
    : {af(_, k, v) == hdr_goal(k, v) : Result<&2, &2, String, Flags.Attack>}
  {==}

def hdr_bad(+x: String) -> String:
  "invalid value \"" ++ x ++ "\" for flag -header: header '" ++ x ++ "' has a wrong format"

def header2(+x: String,
  +h1: {Bool.and(Bool.and(L.printable(x), Bool.not(L.has_char(x, 58))), Bool.not(Bool.or(L.has_char(x, 34), L.has_char(x, 92)))) == True{} : Bool})
  -> {Flags.parse_attack(["-header", x]) == Fail{hdr_bad(x)} : Result<&2, &2, String, Flags.Attack>}:
  +pa = Bool.and(L.printable(x), Bool.not(L.has_char(x, 58)))
  +qb = Bool.or(L.has_char(x, 34), L.has_char(x, 92))
  +e58 = notT(L.has_char(x, 58), andT_r(L.printable(x), Bool.not(L.has_char(x, 58)), andT_l(pa, Bool.not(qb), h1)))
  +eq = notT(qb, andT_r(pa, Bool.not(qb), h1))
  %Equal.sym(Flags.Cut, Flags.cut(58, x), Flags.Cut{x, None{}}, cut_none(x, 58, e58))
    : {wn(2n, hv(_, x, Flags.attack_defaults())) == Fail{hdr_bad(x)} : Result<&2, &2, String, Flags.Attack>}
  %Equal.sym(String, Pace.quote.go(x), x, quote_id(x, orF_l(L.has_char(x, 34), L.has_char(x, 92), eq), orF_r(L.has_char(x, 34), L.has_char(x, 92), eq)))
    : {Fail{"invalid value " ++ ("\"" ++ _ ++ "\"") ++ " for flag -" ++ "header" ++ ": " ++ ("header '" ++ x ++ "' has a wrong format")} == Fail{hdr_bad(x)} : Result<&2, &2, String, Flags.Attack>}
  %Equal.sym(String, (x ++ "\"") ++ " for flag -header: header '" ++ x ++ "' has a wrong format", x ++ ("\"" ++ " for flag -header: header '" ++ x ++ "' has a wrong format"),
      app_assoc(x, "\"", " for flag -header: header '" ++ x ++ "' has a wrong format"))
    : {Fail{"invalid value \"" ++ _} == Fail{hdr_bad(x)} : Result<&2, &2, String, Flags.Attack>}
  {==}

def L.rate_parse_error(f, rest, h0, h1, h2):
  rpe(f, rest, h0, h1, h2)

def L.rate_parse(n, d, s):
  ({==}, {==}, rp3(n), rp4(n, s), rp5(n, s))


def L.flags_header(k, v, x, h0, h1):
  (header1(k, v, h0), header2(x, h1))

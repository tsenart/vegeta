HEAD = '''# Proofs of the engine laws (eng_*).
#
# Each checker of LAWS.bend is a fold over the timeline. For each one, the
# engine's state determines the checker's state (the seq is `next`, the
# busy list is the engine's own, ...), and the proof walks the engine's
# loops: settle, the dispatch to new workers (grow_*), the dispatch to
# idle workers (idle_*), then the events (steps_*) by induction. A loop
# lemma reads {chk(T, K(final state)) == chk(cmds ++ T, K(state))}.
import Base
import ../LAWS.bend as L
import ../lib/engine.bend as Eng
import ./nat.bend as N

# ---------------------------------------------------------------------
# Basics
# ---------------------------------------------------------------------

def eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

def nx(s: Eng.State) -> Nat:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      next

def nw(s: Eng.State) -> Nat:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      now

def lst(s: Eng.State) -> Maybe<&2, Nat>:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      last

def bool_absurd(-x: Bool, -y: Bool, e: {False{} == True{} : Bool}) -> {x == y : Bool}:
  Empty.absurd({x == y : Bool}, N.false_ne_true(e))

def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      bool_absurd(b, True{}, e)

def not_t(a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      bool_absurd(True{}, False{}, e)
    case False{}:
      {==}

# LAWS' config readers and the engine's agree
def slot_same(c: Eng.Cfg, +i: Nat) -> {Eng.slot(c, i) == L.slot(c, i) : Nat}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}

def bounded_same(c: Eng.Cfg) -> {Eng.bounded(c) == L.bounded(c) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}

def dur_same(c: Eng.Cfg) -> {Eng.dur(c) == L.e_dur(c) : Nat}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}

# not (a >= b) is a < b
def cmp_lt(x: Cmp, e: {Bool.not(Cmp.is_ge(x)) == True{} : Bool}) -> {True{} == Cmp.is_lt(x) : Bool}:
  match x:
    case LT{}:
      {==}
    case EQ{}:
      bool_absurd(True{}, False{}, e)
    case GT{}:
      bool_absurd(True{}, False{}, e)

# the start, spelled out
def i0(+c: Eng.Cfg) -> Nat:
  Eng.initial(c)

def r0(+c: Eng.Cfg) -> Nat:
  Nat.sub(Eng.max_workers(c), Eng.initial(c))

def ok0(+c: Eng.Cfg) -> Bool:
  Eng.may(c, 0n, 0n, None{})

def ic0(+c: Eng.Cfg) -> List<&2, Eng.Cmd>:
  Eng.idle_cs(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{})

def is0(+c: Eng.Cfg) -> Eng.State:
  Eng.idle_st(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{})
'''

HEAD += '''
def initial_same(c: Eng.Cfg) -> {Eng.initial(c) == L.initial(c) : Nat}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      {==}
'''
HEAD += open('lists.bend').read() + open('winv.bend').read() + open('arith.bend').read()

def std_settle(n, chk, KF, K0, hd='', hp='', quit_true='{==}', quit_false='{==}', nap_true='{==}', nap_false='{==}', ty='Bool'):
    A = n + 'A'
    return f'''def settle_{n}.nap(b: Bool, {F}, +T: List<&2, L.Item>{hd}, en: {{Eng.wants_nap(c, now, next, nap) == b : Bool}})
  -> {{{chk}(T{KF('Eng.settle.nap_st(b, now, next, grown, room, busy, idle, nap, last)')}) == {A}(Eng.settle.nap_cs(b, c, next), T{K0}) : {ty}}}:
  match b:
    case True{{}}:
      {nap_true}
    case False{{}}:
      {nap_false}

def settle_{n}.quit(b: Bool, {F}, +T: List<&2, L.Item>{hd}, es: {{Eng.stop_due(Eng.dur(c), last) == True{{}} : Bool}}, eq: {{List.is_empty(&2, Nat, busy) == b : Bool}})
  -> {{{chk}(T{KF('Eng.EState{now, next, grown, room, busy, idle, nap, last, b}')}) == {A}(Eng.settle.quit_cs(b, c, next), T{K0}) : {ty}}}:
  match b:
    case True{{}}:
      {quit_true}
    case False{{}}:
      {quit_false}

def settle_{n}.of(b: Bool, {F}, +T: List<&2, L.Item>{hd}, es: {{Eng.stop_due(Eng.dur(c), last) == b : Bool}})
  -> {{{chk}(T{KF('Eng.settle.of_st(b, c, now, next, grown, room, busy, idle, nap, last)')}) == {A}(Eng.settle.of_cs(b, c, now, next, busy, nap), T{K0}) : {ty}}}:
  match b:
    case True{{}}:
      settle_{n}.quit(List.is_empty(&2, Nat, busy), c, now, next, grown, room, busy, idle, nap, last, T{hp}, es, {{==}})
    case False{{}}:
      settle_{n}.nap(Eng.wants_nap(c, now, next, nap), c, now, next, grown, room, busy, idle, nap, last, T{hp}, {{==}})

def settle_{n}({F}, +T: List<&2, L.Item>{hd})
  -> {{{chk}(T{KF('Eng.settle_st(c, now, next, grown, room, busy, idle, nap, last)')}) == {A}(Eng.settle_cs(c, now, next, busy, nap, last), T{K0}) : {ty}}}:
  settle_{n}.of(Eng.stop_due(Eng.dur(c), last), c, now, next, grown, room, busy, idle, nap, last, T{hp}, {{==}})
'''

def seq_fire(st, cs, ih):
    return f'''          %eq_refl(next) : {{L.chk_seq(T, nx({st})) == Bool.and(_, seqA({cs}, T, 1n+next)) : Bool}}
          {ih}'''

checker(dict(name='seq', chk='L.chk_seq', A_params=', n: Nat', A_args=', n', K0=', next',
  KF=lambda st: f', nx({st})', KS=lambda s: f', nx({s})',
  settle=std_settle('seq', 'L.chk_seq', lambda st: f', nx({st})', ', next'),
  fire_grow=seq_fire, fire_idle=seq_fire,
  law='''def pre_seq(n: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +k: Nat)
  -> {seqA(X, T, k) == seqA(List.append(&2, Eng.Cmd, Eng.grows(n, from), X), T, k) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pre_seq(p, 1n+from, X, T, k)

def L.eng_seq(c, evs):
  %pre_seq(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), 0n) : {_ == True{} : Bool}
  %idle_seq(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c))) : {_ == True{} : Bool}
  steps_seq(evs, is0(c), c)
'''))

def pre_law(n):
    A = n + 'A'
    return f'''def pre_{n}(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {{{A}(X, T{{K}}) == {A}(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T{{K}}) : Bool}}:
  match k:
    case 0n:
      {{==}}
    case 1n+p:
      pre_{n}(p, 1n+from, X, T, c)
'''

def law_text(n, law, params, K, hp=''):
    return pre_law(n).replace('{K}', K) + f'''
def L.{law}(c, evs{params}):
  %pre_{n}(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {{_ == True{{}} : Bool}}
  %idle_{n}(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{{}}, None{{}}, L.steps(evs, c, is0(c)){hp}) : {{_ == True{{}} : Bool}}
  steps_{n}(evs, is0(c), c{hp.replace(', {==}', '')})
'''

# --- round robin
def rr_fire(st, cs, ih):
    return f'''          %rr_ok(c, next) : {{L.chk_rr(T, L.e_targets(c)) == Bool.and(_, rrA({cs}, T, L.e_targets(c))) : Bool}}
          {ih}'''
HEAD += """
def rr_ok(c: Eng.Cfg, +q: Nat) -> {True{} == Nat.is_eq(Nat.mod(q, Eng.targets(c)), Nat.mod(q, L.e_targets(c))) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      eq_refl(Nat.mod(q, t))
"""
checker(dict(name='rr', chk='L.chk_rr', A_params=', n: Nat', A_args=', n', K0=', L.e_targets(c)',
  KF=lambda st: ', L.e_targets(c)', KS=lambda s: ', L.e_targets(c)',
  settle=std_settle('rr', 'L.chk_rr', lambda st: ', L.e_targets(c)', ', L.e_targets(c)'),
  fire_grow=rr_fire, fire_idle=rr_fire,
  law=law_text('rr', 'eng_round_robin', ', h', ', L.e_targets(c)')))

# --- now
def now_fire(st, cs, ih):
    return f'''          %eq_refl(now) : {{L.chk_now(T, nw({st})) == Bool.and(_, nowA({cs}, T, now)) : Bool}}
          {ih}'''
checker(dict(name='now', chk='L.chk_now', A_params=', n: Nat', A_args=', n', K0=', now',
  KF=lambda st: f', nw({st})', KS=lambda s: f', nw({s})',
  settle=std_settle('now', 'L.chk_now', lambda st: f', nw({st})', ', now'),
  fire_grow=now_fire, fire_idle=now_fire,
  law=law_text('now', 'eng_now', '', ', 0n')))

# --- unbounded
HEAD += """
# no nap at an unbounded rate
def wn_false(c: Eng.Cfg, +now: Nat, +next: Nat, +nap: Bool, hb: {Eng.bounded(c) == False{} : Bool})
  -> {Eng.wants_nap(c, now, next, nap) == False{} : Bool}:
  %Equal.sym(Bool, Eng.bounded(c), False{}, hb) : {Bool.and(_, Bool.and(Bool.not(nap), Nat.is_gt(Eng.slot(c, next), now))) == False{} : Bool}
  {==}

def unb_bounded.go(f: Nat, p: Nat, h: {Bool.or(Nat.is_eq(f, 0n), Nat.is_eq(p, 0n)) == True{} : Bool})
  -> {Bool.and(Nat.is_gt(f, 0n), Nat.is_ge(p, f)) == False{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+g:
      match p:
        case 0n:
          {==}
        case 1n+q:
          bool_absurd(Bool.and(True{}, Nat.is_ge(1n+q, 1n+g)), False{}, h)

def unb_bounded(c: Eng.Cfg, h: {Bool.or(Nat.is_eq(L.e_freq(c), 0n), Nat.is_eq(L.e_per(c), 0n)) == True{} : Bool}) -> {Eng.bounded(c) == False{} : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      unb_bounded.go(f, p, h)
"""
def unb_fire(st, cs, ih):
    return f'          {ih}'
unb_hd = ', +hb: {Eng.bounded(c) == False{} : Bool}'
checker(dict(name='unb', chk='L.no_nap', A_params='', A_args='', K0='',
  KF=lambda st: '', KS=lambda s: '', hyps_decl=unb_hd, hyps_pass=', hb',
  settle=std_settle('unb', 'L.no_nap', lambda st: '', '', unb_hd, ', hb',
    nap_true='bool_absurd(L.no_nap(T), unbA(Eng.settle.nap_cs(True{}, c, next), T), Equal.trans(Bool, False{}, Eng.wants_nap(c, now, next, nap), True{}, Equal.sym(Bool, Eng.wants_nap(c, now, next, nap), False{}, wn_false(c, now, next, nap, hb)), en))'),
  fire_grow=unb_fire, fire_idle=unb_fire,
  law=pre_law('unb').replace('{K}', '') + """
def L.eng_unbounded(c, evs, h):
  +hb = unb_bounded(c, h)
  %pre_unb(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_unb(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), hb) : {_ == True{} : Bool}
  steps_unb(evs, is0(c), c, hb)
"""))

HEAD += """
def slot_eqt(c: Eng.Cfg, +i: Nat) -> {True{} == Nat.is_eq(Eng.slot(c, i), L.slot(c, i)) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      eq_refl(Nat.mul(1n+i, Nat.div(p, f)))

def wn_gt(+c: Eng.Cfg, +now: Nat, +next: Nat, +nap: Bool, en: {Eng.wants_nap(c, now, next, nap) == True{} : Bool})
  -> {True{} == Nat.is_gt(Eng.slot(c, next), now) : Bool}:
  Equal.sym(Bool, Nat.is_gt(Eng.slot(c, next), now), True{},
    and_r(Bool.not(nap), Nat.is_gt(Eng.slot(c, next), now), and_r(Eng.bounded(c), Bool.and(Bool.not(nap), Nat.is_gt(Eng.slot(c, next), now)), en)))

def due_ge(b: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, hb: {b == True{} : Bool}, e: {Eng.due.of(b, c, now, next) == True{} : Bool})
  -> {True{} == Nat.is_ge(now, Eng.slot(c, next)) : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, Nat.is_ge(now, Eng.slot(c, next)), True{}, e)
    case False{}:
      bool_absurd(True{}, Nat.is_ge(now, Eng.slot(c, next)), hb)

def early_ok(+c: Eng.Cfg, +now: Nat, +next: Nat, +last: Maybe<&2, Nat>, h: {L.bounded(c) == True{} : Bool}, e: {Eng.may(c, now, next, last) == True{} : Bool})
  -> {True{} == Nat.is_ge(now, L.slot(c, next)) : Bool}:
  %slot_same(c, next) : {True{} == Nat.is_ge(now, _) : Bool}
  due_ge(Eng.bounded(c), c, now, next, Equal.trans(Bool, Eng.bounded(c), L.bounded(c), True{}, bounded_same(c), h),
    and_r(Bool.not(Eng.stop_due(Eng.dur(c), last)), Eng.due(c, now, next), e))

def dl_ok.go(d: Nat, last: Maybe<&2, Nat>, h: {Nat.is_gt(d, 0n) == True{} : Bool}, e: {Bool.not(Eng.stop_due(d, last)) == True{} : Bool})
  -> {True{} == Nat.is_lt(Maybe.default(&2, Nat, last, 0n), d) : Bool}:
  match d:
    case 0n:
      bool_absurd(True{}, Nat.is_lt(Maybe.default(&2, Nat, last, 0n), 0n), h)
    case 1n+q:
      match last:
        case None{}:
          {==}
        case Some{t}:
          cmp_lt(Nat.cmp(t, 1n+q), e)

def dl_ok(c: Eng.Cfg, +last: Maybe<&2, Nat>, h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}, e: {Bool.not(Eng.stop_due(Eng.dur(c), last)) == True{} : Bool})
  -> {True{} == Nat.is_lt(Maybe.default(&2, Nat, last, 0n), L.e_dur(c)) : Bool}:
  match c:
    case Eng.ECfg{f, p, d, w, m, t}:
      dl_ok.go(d, last, h, e)
"""

def law_h(n, law, K, hp):
    return pre_law(n).replace('{K}', K) + f'''
def L.{law}(c, evs, h):
  +hh = h
  %pre_{n}(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {{_ == True{{}} : Bool}}
  %idle_{n}(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{{}}, None{{}}, L.steps(evs, c, is0(c)), hh{hp}) : {{_ == True{{}} : Bool}}
  steps_{n}(evs, is0(c), c, hh)
'''

# --- nap
def nap_fire(st, cs, ih):
    return f'          {ih}'
checker(dict(name='nap', chk='L.chk_nap', A_params=', c2: Eng.Cfg, n: Nat, t: Nat', A_args=', c2, n, t', K0=', c, next, now',
  KF=lambda st: f', c, nx({st}), nw({st})', KS=lambda s: f', c, nx({s}), nw({s})',
  settle=std_settle('nap', 'L.chk_nap', lambda st: f', c, nx({st}), nw({st})', ', c, next, now',
    nap_true='''%slot_eqt(c, next) : {L.chk_nap(T, c, next, now) == Bool.and(Bool.and(_, Nat.is_gt(Eng.slot(c, next), now)), L.chk_nap(T, c, next, now)) : Bool}
      %wn_gt(c, now, next, nap, en) : {L.chk_nap(T, c, next, now) == Bool.and(Bool.and(True{}, _), L.chk_nap(T, c, next, now)) : Bool}
      {==}'''),
  fire_grow=nap_fire, fire_idle=nap_fire,
  law=pre_law('nap').replace('{K}', ', c, 0n, 0n') + """
def L.eng_nap(c, evs, h):
  %pre_nap(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_nap(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c))) : {_ == True{} : Bool}
  steps_nap(evs, is0(c), c)
"""))

# --- never early
early_hd = ', +h: {L.bounded(c) == True{} : Bool}'
def early_fire(st, cs, ih):
    return f'''          %early_ok(c, now, next, last, h, eok) : {{L.chk_early(T, c) == Bool.and(_, earlyA({cs}, T, c)) : Bool}}
          {ih}'''
checker(dict(name='early', chk='L.chk_early', A_params=', c2: Eng.Cfg', A_args=', c2', K0=', c',
  KF=lambda st: ', c', KS=lambda s: ', c', hyps_decl=early_hd, hyps_pass=', h', ok=True,
  settle=std_settle('early', 'L.chk_early', lambda st: ', c', ', c', early_hd, ', h'),
  fire_grow=early_fire, fire_idle=early_fire,
  law=law_h('early', 'eng_never_early', ', c', ', {==}')))

# --- deadline
dl_hd = ', +h: {Nat.is_gt(L.e_dur(c), 0n) == True{} : Bool}'
def dl_fire(st, cs, ih):
    return f'''          %dl_ok(c, last, h, and_l(Bool.not(Eng.stop_due(Eng.dur(c), last)), Eng.due(c, now, next), eok))
            : {{L.chk_deadline(T, L.e_dur(c), Maybe.default(&2, Nat, lst({st}), 0n)) == Bool.and(_, dlA({cs}, T, L.e_dur(c), now)) : Bool}}
          {ih}'''
dlK = lambda st: f', L.e_dur(c), Maybe.default(&2, Nat, lst({st}), 0n)'
checker(dict(name='dl', chk='L.chk_deadline', A_params=', d: Nat, l: Nat', A_args=', d, l', K0=', L.e_dur(c), Maybe.default(&2, Nat, last, 0n)',
  KF=dlK, KS=dlK, hyps_decl=dl_hd, hyps_pass=', h', ok=True,
  settle=std_settle('dl', 'L.chk_deadline', dlK, ', L.e_dur(c), Maybe.default(&2, Nat, last, 0n)', dl_hd, ', h'),
  fire_grow=dl_fire, fire_idle=dl_fire,
  law=law_h('dl', 'eng_deadline', ', L.e_dur(c), 0n', ', {==}')))

emit('''# ---------------------------------------------------------------------
# eng_initial
# ---------------------------------------------------------------------

def take_zero(xs: List<&2, L.Item>) -> {List.take(&2, L.Item, xs, 0n) == [] : List<&2, L.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      {==}

def take_gr(n: Nat, +f: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>)
  -> {List.take(&2, L.Item, List.append(&2, L.Item, L.cmds_items(List.append(&2, Eng.Cmd, Eng.grows(n, f), X)), T), n) == L.grows(n, f) : List<&2, L.Item>}:
  match n:
    case 0n:
      take_zero(List.append(&2, L.Item, L.cmds_items(X), T))
    case 1n+p:
      %take_gr(p, 1n+f, X, T) : {Con{L.ICmd{Eng.Grow{f}}, List.take(&2, L.Item, List.append(&2, L.Item, L.cmds_items(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X)), T), p)}
        == Con{L.ICmd{Eng.Grow{f}}, _} : List<&2, L.Item>}
      {==}


def L.eng_initial(c, evs):
  %initial_same(c) : {List.take(&2, L.Item, L.timeline(c, evs), _) == L.grows(_, 0n) : List<&2, L.Item>}
  take_gr(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)))
''')

HEAD += """
def gr(s: Eng.State) -> Nat:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      grown

def bz(s: Eng.State) -> List<&2, Nat>:
  match s:
    case Eng.EState{now, next, grown, room, busy, idle, nap, last, over}:
      busy

def le_lt(f: Nat, +p: Nat, m: Nat, e: {Nat.is_le(Nat.add(f, 1n+p), m) == True{} : Bool}) -> {Nat.is_lt(f, m) == True{} : Bool}:
  match f m:
    case 0n 0n:
      bool_absurd(False{}, True{}, e)
    case 0n 1n+q:
      {==}
    case 1n+g 0n:
      bool_absurd(False{}, True{}, e)
    case 1n+g 1n+q:
      le_lt(g, p, q, e)

def or_ok(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# with no idle worker, every grown worker is busy
def len_g(+c: Eng.Cfg, +g: Nat, +room: Nat, +busy: List<&2, Nat>, hv: {winv(c, g, room, busy, []) == True{} : Bool})
  -> {Nat.is_eq(List.length(&2, Nat, busy), g) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, busy), Nat.add(List.length(&2, Nat, busy), 0n), N.add_zero(List.length(&2, Nat, busy))) : {Nat.is_eq(_, g) == True{} : Bool}
  wv2(c, g, room, busy, [], hv)
"""

wk_hd = ', +hv: {winv(c, grown, room, busy, $idle) == True{} : Bool}'
def wk_steps(kind, args, st, over_st, chk, A, K):
    if kind == 'clock':
        return ('', '', ', hv', ', hv', f', inv_idle({args}, hv)')
    pre = '                  +hv2 = wv_freed(c, grown, room, busy, idle, w, hv)\n'
    pro = pre + f'                  %drop_same(w, busy) : {{{chk}(L.steps(rest, c, {over_st}), {K}, grown, _) == True{{}} : Bool}}\n'
    ics = f'Eng.idle_cs({args})'
    prc = pre + f'                  %drop_same(w, busy) : {{{A}({ics}, L.steps(rest, c, {st}), {K}, grown, _) == True{{}} : Bool}}\n'
    return (pro, prc, ', hv2', ', hv2', f', inv_idle({args}, hv2)')

def wk_fire_grow(st, cs, ih):
    L_ = f'L.chk_workers(T, L.e_max(c), gr({st}), bz({st}))'
    A_ = f'workersA({cs}, T, L.e_max(c), 1n+grown, Con{{grown, busy}})'
    return f'''          %eq_refl(grown) : {{{L_} == Bool.and(Bool.and(_, Nat.is_lt(grown, L.e_max(c))), Bool.and(Bool.and(Nat.is_lt(grown, 1n+grown), Bool.not(L.has_nat(grown, busy))), {A_})) : Bool}}
          %Equal.sym(Bool, Nat.is_lt(grown, L.e_max(c)), True{{}}, room_lt(r, grown, L.e_max(c), wv1(c, grown, 1n+r, busy, [], hv)))
            : {{{L_} == Bool.and(Bool.and(True{{}}, _), Bool.and(Bool.and(Nat.is_lt(grown, 1n+grown), Bool.not(L.has_nat(grown, busy))), {A_})) : Bool}}
          %Equal.sym(Bool, Nat.is_lt(grown, 1n+grown), True{{}}, lt_succ(grown)) : {{{L_} == Bool.and(Bool.and(_, Bool.not(L.has_nat(grown, busy))), {A_}) : Bool}}
          %Equal.sym(Bool, Bool.not(L.has_nat(grown, busy)), True{{}}, not_i(L.has_nat(grown, busy), lt_nhas(busy, grown, wv3(c, grown, 1n+r, busy, [], hv))))
            : {{{L_} == Bool.and(Bool.and(True{{}}, _), {A_}) : Bool}}
          {ih}'''

def wk_fire_idle(st, cs, ih):
    L_ = f'L.chk_workers(T, L.e_max(c), gr({st}), bz({st}))'
    A_ = f'workersA({cs}, T, L.e_max(c), grown, Con{{w, busy}})'
    ei = 'wv5(c, grown, room, busy, Con{w, rest}, hv)'
    return f'''          %Equal.sym(Bool, Nat.is_lt(w, grown), True{{}}, ik1(w, rest, busy, grown, {ei})) : {{{L_} == Bool.and(Bool.and(_, Bool.not(L.has_nat(w, busy))), {A_}) : Bool}}
          %Equal.sym(Bool, Bool.not(L.has_nat(w, busy)), True{{}}, not_i(L.has_nat(w, busy), ik2(w, rest, busy, grown, {ei}))) : {{{L_} == Bool.and(Bool.and(True{{}}, _), {A_}) : Bool}}
          {ih}'''

wkK = lambda st: f', L.e_max(c), gr({st}), bz({st})'
checker(dict(name='workers', chk='L.chk_workers', A_params=', m: Nat, g: Nat, b: List<&2, Nat>', A_args=', m, g, b', K0=', L.e_max(c), grown, busy',
  KF=wkK, KS=wkK, hyps_decl=wk_hd, hyps_pass=', hv',
  hp_grow_rec=', wv_fire_grow(c, grown, r, busy, hv)', hp_idle_rec=', wv_fire_idle(c, grown, room, busy, w, rest, hv)',
  steps_hd=', +hv: {sinv(c, s) == True{} : Bool}',
  steps_hp=lambda kind, args, st, over_st: wk_steps(kind, args, st, over_st, 'L.chk_workers', 'workersA', 'L.e_max(c)'),
  settle=std_settle('workers', 'L.chk_workers', wkK, ', L.e_max(c), grown, busy', wk_hd.replace('$idle', 'idle'), ', hv'),
  fire_grow=wk_fire_grow, fire_idle=wk_fire_idle,
  law='''def pre_workers(k: Nat, +f: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg, +e: {Nat.is_le(Nat.add(f, k), L.e_max(c)) == True{} : Bool})
  -> {workersA(X, T, L.e_max(c), Nat.add(f, k), []) == workersA(List.append(&2, Eng.Cmd, Eng.grows(k, f), X), T, L.e_max(c), f, []) : Bool}:
  match k:
    case 0n:
      %N.add_zero(f) : {workersA(X, T, L.e_max(c), _, []) == workersA(X, T, L.e_max(c), f, []) : Bool}
      {==}
    case 1n+(+p):
      %N.add_succ(f, p) : {workersA(X, T, L.e_max(c), _, [])
        == Bool.and(Bool.and(Nat.is_eq(f, f), Nat.is_lt(f, L.e_max(c))), workersA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.e_max(c), 1n+f, [])) : Bool}
      %eq_refl(f) : {workersA(X, T, L.e_max(c), 1n+Nat.add(f, p), [])
        == Bool.and(Bool.and(_, Nat.is_lt(f, L.e_max(c))), workersA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.e_max(c), 1n+f, [])) : Bool}
      %Equal.sym(Bool, Nat.is_lt(f, L.e_max(c)), True{}, le_lt(f, p, L.e_max(c), e)) : {workersA(X, T, L.e_max(c), 1n+Nat.add(f, p), [])
        == Bool.and(Bool.and(True{}, _), workersA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.e_max(c), 1n+f, [])) : Bool}
      pre_workers(p, 1n+f, X, T, c, Equal.trans(Bool, Nat.is_le(1n+Nat.add(f, p), L.e_max(c)), Nat.is_le(Nat.add(f, 1n+p), L.e_max(c)), True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, L.e_max(c)), 1n+Nat.add(f, p), Nat.add(f, 1n+p), N.add_succ(f, p)), e))

def L.eng_workers(c, evs):
  %pre_workers(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c, le0(c)) : {_ == True{} : Bool}
  %idle_workers(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), winv0(c)) : {_ == True{} : Bool}
  steps_workers(evs, is0(c), c, is0_inv(c))
'''))

def gw_fire_grow(st, cs, ih):
    L_ = f'L.chk_grow(T, L.initial(c), gr({st}), bz({st}))'
    A_ = f'growA({cs}, T, L.initial(c), 1n+grown, Con{{grown, busy}})'
    cond = f'Bool.or(Nat.is_lt(grown, L.initial(c)), Bool.and(Nat.is_eq(List.length(&2, Nat, busy), grown), Nat.is_eq(grown, grown)))'
    pf = (f'or_ok(Nat.is_lt(grown, L.initial(c)), Bool.and(Nat.is_eq(List.length(&2, Nat, busy), grown), Nat.is_eq(grown, grown)), '
          f'and_i(Nat.is_eq(List.length(&2, Nat, busy), grown), Nat.is_eq(grown, grown), len_g(c, grown, 1n+r, busy, hv), Equal.sym(Bool, True{{}}, Nat.is_eq(grown, grown), eq_refl(grown))))')
    return f'''          %Equal.sym(Bool, {cond}, True{{}}, {pf})
            : {{{L_} == Bool.and(_, {A_}) : Bool}}
          {ih}'''

def gw_fire_idle(st, cs, ih):
    return f'          {ih}'

gwK = lambda st: f', L.initial(c), gr({st}), bz({st})'
checker(dict(name='grow', chk='L.chk_grow', A_params=', w0: Nat, g: Nat, b: List<&2, Nat>', A_args=', w0, g, b', K0=', L.initial(c), grown, busy',
  KF=gwK, KS=gwK, hyps_decl=wk_hd, hyps_pass=', hv',
  hp_grow_rec=', wv_fire_grow(c, grown, r, busy, hv)', hp_idle_rec=', wv_fire_idle(c, grown, room, busy, w, rest, hv)',
  steps_hd=', +hv: {sinv(c, s) == True{} : Bool}',
  steps_hp=lambda kind, args, st, over_st: wk_steps(kind, args, st, over_st, 'L.chk_grow', 'growA', 'L.initial(c)'),
  settle=std_settle('grow', 'L.chk_grow', gwK, ', L.initial(c), grown, busy', wk_hd.replace('$idle', 'idle'), ', hv'),
  fire_grow=gw_fire_grow, fire_idle=gw_fire_idle,
  law='''def pre_grow(k: Nat, +f: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg, +e: {Nat.add(f, k) == L.initial(c) : Nat})
  -> {growA(X, T, L.initial(c), Nat.add(f, k), []) == growA(List.append(&2, Eng.Cmd, Eng.grows(k, f), X), T, L.initial(c), f, []) : Bool}:
  match k:
    case 0n:
      %N.add_zero(f) : {growA(X, T, L.initial(c), _, []) == growA(X, T, L.initial(c), f, []) : Bool}
      {==}
    case 1n+(+p):
      %N.add_succ(f, p) : {growA(X, T, L.initial(c), _, [])
        == Bool.and(Bool.or(Nat.is_lt(f, L.initial(c)), Bool.and(Nat.is_eq(0n, f), L.next_fires(f, List.append(&2, L.Item, L.cmds_items(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X)), T)))),
          growA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.initial(c), 1n+f, [])) : Bool}
      %Equal.sym(Bool, Nat.is_lt(f, L.initial(c)), True{}, lt_add1(f, p, L.initial(c), e)) : {growA(X, T, L.initial(c), 1n+Nat.add(f, p), [])
        == Bool.and(Bool.or(_, Bool.and(Nat.is_eq(0n, f), L.next_fires(f, List.append(&2, L.Item, L.cmds_items(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X)), T)))),
          growA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+f), X), T, L.initial(c), 1n+f, [])) : Bool}
      pre_grow(p, 1n+f, X, T, c, Equal.trans(Nat, 1n+Nat.add(f, p), Nat.add(f, 1n+p), L.initial(c), N.add_succ(f, p), e))

def L.eng_grow(c, evs):
  %pre_grow(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c, initial_same(c)) : {_ == True{} : Bool}
  %idle_grow(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), winv0(c)) : {_ == True{} : Bool}
  steps_grow(evs, is0(c), c, is0_inv(c))
'''))

HEAD += open('quitlem.bend').read()

qK = lambda st: f', c, nx({st}), ov({st}), lst({st}), bz({st})'
q_hd = ', +hq: {qinv(c, next, last) == True{} : Bool}'
CHKQ = 'L.chk_quit(T, c, next, True{}, last, busy)'
PICK = 'L.pick(Bool, L.bounded(c), Nat.is_eq(Nat.add(next, Eng.dropped(c, next)), L.scheduled(c)), Nat.is_eq(Eng.dropped(c, next), 0n))'
q_quit_true = f'''%Equal.sym(Bool, L.stop_due(L.e_dur(c), last), True{{}}, Equal.trans(Bool, L.stop_due(L.e_dur(c), last), Eng.stop_due(Eng.dur(c), last), True{{}},
        Equal.sym(Bool, Eng.stop_due(Eng.dur(c), last), L.stop_due(L.e_dur(c), last), stopdue_same(c, last)), es))
        : {{{CHKQ} == Bool.and(Bool.and(_, List.is_empty(&2, Nat, busy)), Bool.and(Bool.and(Nat.is_eq(next, next), {PICK}), {CHKQ})) : Bool}}
      %Equal.sym(Bool, List.is_empty(&2, Nat, busy), True{{}}, eq) : {{{CHKQ} == Bool.and(Bool.and(True{{}}, _), Bool.and(Bool.and(Nat.is_eq(next, next), {PICK}), {CHKQ})) : Bool}}
      %eq_refl(next) : {{{CHKQ} == Bool.and(Bool.and(_, {PICK}), {CHKQ}) : Bool}}
      %drop_ok(c, next, last, es, hq) : {{{CHKQ} == Bool.and(Bool.and(True{{}}, _), {CHKQ}) : Bool}}
      {{==}}'''
qsettle = std_settle('quit', 'L.chk_quit', qK, ', c, next, False{}, last, busy', q_hd, ', hq', quit_true=q_quit_true).replace(
  'es: {{Eng.stop_due(Eng.dur(c), last) == True{{}} : Bool}}, eq:', '+es: {{Eng.stop_due(Eng.dur(c), last) == True{{}} : Bool}}, eq:').replace(
  ', es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq:', ', +es: {Eng.stop_due(Eng.dur(c), last) == True{} : Bool}, eq:')
def q_steps(kind, args, st, over_st):
    if kind == 'clock':
        return ('', '', ', hq', ', hq', f', q_idle({args}, hq, {{==}})')
    pro = f'                  %drop_same(w, busy) : {{L.chk_quit(L.steps(rest, c, {over_st}), c, next, True{{}}, last, _) == True{{}} : Bool}}\n'
    prc = f'                  %drop_same(w, busy) : {{quitA(Eng.idle_cs({args}), L.steps(rest, c, {st}), c, next, False{{}}, last, _) == True{{}} : Bool}}\n'
    return (pro, prc, ', hq', ', hq', f', q_idle({args}, hq, {{==}})')
def q_fire(st, cs, ih):
    return f'          {ih}'
checker(dict(name='quit', chk='L.chk_quit', A_params=', c2: Eng.Cfg, s: Nat, q: Bool, l: Maybe<&2, Nat>, b: List<&2, Nat>', A_args=', c2, s, q, l, b',
  K0=', c, next, False{}, last, busy', KF=qK, KS=qK, hyps_decl=q_hd, hyps_pass=', hq', ok=True,
  hp_grow_rec=', qfire(c, now, next, last, eok, hq)', hp_idle_rec=', qfire(c, now, next, last, eok, hq)',
  steps_hd=', +hq: {sq(c, s) == True{} : Bool}', steps_hp=q_steps,
  settle=qsettle, fire_grow=q_fire, fire_idle=q_fire,
  law=pre_law('quit').replace('{K}', ', c, 0n, False{}, None{}, []') + """
def L.eng_quit(c, evs):
  %pre_quit(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_quit(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c)), q0.of(Bool.and(L.bounded(c), Nat.is_gt(L.e_dur(c), 0n)), c), {==}) : {_ == True{} : Bool}
  steps_quit(evs, is0(c), c, is0_q(c))
"""))

HEAD += open('livelem.bend').read()
lvK = lambda st: f', c, np({st}), gr({st}), bz({st}), ov({st}), lst({st})'
def lv_fire(st, cs, ih):
    return f'          {ih}'
def live_steps():
    def branch(kind):
        t = 't'
        if kind == 'clock':
            busy, idle, nap = 'busy', 'idle', 'False{}'
            cbusy = 'busy'; hv = 'hv'; pre = ''
        else:
            busy, idle, nap = 'Eng.drop_nat(w, busy)', 'Eng.freed_idle(Eng.has_nat(w, busy), w, idle)', 'nap'
            cbusy = 'L.drop_nat(w, busy)'; hv = 'hv2'
            pre = '                  +hv2 = wv_freed(c, grown, room, busy, idle, w, hv)\n'
        okx = f"Eng.may(c, {t}, next, last)"
        args = f"{idle}, {okx}, c, {t}, next, grown, room, {busy}, {nap}, last"
        st = f"Eng.idle_st({args})"
        over_st = f"Eng.EState{{{t}, next, grown, room, {busy}, {idle}, {nap}, last, True{{}}}}"
        pend = 'L.pending(c, nap, grown, busy, over, last)'
        # X over
        Xo = f'L.chk_live(L.steps(rest, c, {over_st}), c, {nap}, grown, {{B}}, True{{}}, last)'
        Xc = f'liveA(Eng.idle_cs({args}), L.steps(rest, c, {st}), c, {nap}, grown, {{B}}, False{{}}, last)'
        def drop_rw(X):
            if kind == 'clock': return ''
            return f'                  %drop_same(w, busy) : {{{X.replace("{B}", "_")} == True{{}} : Bool}}\n'
        return f"""              match over:
                case True{{}}:
{pre}                  %Equal.sym(Bool, L.pending(c, nap, grown, busy, True{{}}, last), True{{}}, hp) : {{Bool.and(_, {Xo.replace('{B}', cbusy)}) == True{{}} : Bool}}
{drop_rw(Xo)}                  steps_live(rest, {over_st}, c, hok, {hv}, {{==}})
                case False{{}}:
{pre}                  %Equal.sym(Bool, L.pending(c, nap, grown, busy, False{{}}, last), True{{}}, hp) : {{Bool.and(_, {Xc.replace('{B}', cbusy)}) == True{{}} : Bool}}
{drop_rw(Xc)}                  %idle_live({args}, L.steps(rest, c, {st})) : {{_ == True{{}} : Bool}}
                  steps_live(rest, {st}, c, hok, inv_idle({args}, {hv}), pend_idle({args}, hok, {hv}, {{==}}))"""
    return f"""def steps_live(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg, +hok: {{L.cfg_ok(c) == True{{}} : Bool}}, +hv: {{sinv(c, s) == True{{}} : Bool}}, +hp: {{spend(c, s) == True{{}} : Bool}})
  -> {{L.chk_live(L.steps(evs, c, s){lvK('s')}) == True{{}} : Bool}}:
  match evs:
    case Nil{{}}:
      match s:
        case Eng.EState{{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}}:
          hp
    case Con{{+e, +rest}}:
      match e:
        case Eng.Clock{{+t}}:
          match s:
            case Eng.EState{{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}}:
{branch('clock')}
        case Eng.Freed{{+w, +t}}:
          match s:
            case Eng.EState{{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}}:
{branch('freed')}
"""
lv_law = pre_law('live').replace('{K}', ', c, False{}, {G}, [], False{}, None{}') 
lv_law = '''def pre_live(k: Nat, +from: Nat, +X: List<&2, Eng.Cmd>, +T: List<&2, L.Item>, +c: Eng.Cfg)
  -> {liveA(X, T, c, False{}, Nat.add(from, k), [], False{}, None{}) == liveA(List.append(&2, Eng.Cmd, Eng.grows(k, from), X), T, c, False{}, from, [], False{}, None{}) : Bool}:
  match k:
    case 0n:
      %N.add_zero(from) : {liveA(X, T, c, False{}, _, [], False{}, None{}) == liveA(X, T, c, False{}, from, [], False{}, None{}) : Bool}
      {==}
    case 1n+(+p):
      %N.add_succ(from, p) : {liveA(X, T, c, False{}, _, [], False{}, None{}) == liveA(List.append(&2, Eng.Cmd, Eng.grows(p, 1n+from), X), T, c, False{}, 1n+from, [], False{}, None{}) : Bool}
      pre_live(p, 1n+from, X, T, c)

def L.eng_live(c, evs, h):
  +hh = h
  %pre_live(i0(c), 0n, ic0(c), L.steps(evs, c, is0(c)), c) : {_ == True{} : Bool}
  %idle_live(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, L.steps(evs, c, is0(c))) : {_ == True{} : Bool}
  steps_live(evs, is0(c), c, hh, is0_inv(c), pend_idle(Eng.ids(i0(c), 0n), ok0(c), c, 0n, 0n, i0(c), r0(c), [], False{}, None{}, hh, winv0(c), {==}))
'''
checker(dict(name='live', chk='L.chk_live', A_params=', c2: Eng.Cfg, n: Bool, g: Nat, b: List<&2, Nat>, q: Bool, l: Maybe<&2, Nat>', A_args=', c2, n, g, b, q, l',
  K0=', c, nap, grown, busy, False{}, last', KF=lvK, KS=lvK,
  settle=std_settle('live', 'L.chk_live', lvK, ', c, nap, grown, busy, False{}, last'),
  fire_grow=lv_fire, fire_idle=lv_fire, law=None, no_steps=True))
emit(live_steps())
emit(lv_law)

HEAD += open('ends1.bend').read()
def nofire(st, cs, ih):
    return f'          {ih}'
checker(dict(name='hq', chk='hqc', A_params=', o: Bool', A_args=', o', K0=', False{}', KF=lambda st: f', ov({st})', KS=lambda s: '',
  settle=std_settle('hq', 'hqc', lambda st: f', ov({st})', ', False{}'), fire_grow=nofire, fire_idle=nofire, law=pre_law('hq').replace('{K}', ', False{}'), no_steps=True))
checker(dict(name='bo', chk='L.busy_of', A_params=', b: List<&2, Nat>', A_args=', b', K0=', busy', KF=lambda st: f', bz({st})', KS=lambda s: '', ty='List<&2, Nat>',
  settle=std_settle('bo', 'L.busy_of', lambda st: f', bz({st})', ', busy', ty='List<&2, Nat>'), fire_grow=nofire, fire_idle=nofire, law=None, no_steps=True))
emit(open('ends2.bend').read())
emit(open('ends3.bend').read())
emit(open('ends4.bend').read())
emit(open('ends5.bend').read())

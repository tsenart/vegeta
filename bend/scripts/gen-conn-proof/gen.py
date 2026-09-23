import sys
from emit import Law
import tree

C = 'Conn.CCfg{ka, to, mb, rd}'
SF = 'q, o, False{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr'
S0 = 'Conn.CState{%s}' % SF
ARGS = 'ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr'
CP = '+ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>'
SP = '+q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat'

def R():
    return 'Conn.step.ev(e, %s, %s)' % (C, S0)

def app_items(r, T):
    return 'List.append(&2, L.CItem, L.ccmds_items(L.ccs_of(%s)), %s)' % (r, T)

def steps(name, chk, flag, over, ev_extra='', hyps=''):
    """chk(T, flag) -> text; flag(s) -> the state's flag; over: text for the over case"""
    T = 'L.csteps(rest, %s, L.cst_of(%s))' % (C, R())
    st = 'L.cst_of(%s)' % R()
    return f'''def {name}_steps(evs: List<&2, Conn.Ev>, {CP}, s: Conn.State) -> {{{chk('L.csteps(evs, %s, s)' % C, flag('s'))} == True{{}} : Bool}}:
  match evs:
    case Nil{{}}:
      {{==}}
    case Con{{+e, +rest}}:
      match s:
        case Conn.CState{{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}}:
          match v:
            case True{{}}:
              match x:
                case Conn.Rx{{+xb, +xhd, +xp, +xp0, +xmet}}:
                  {over}
            case False{{}}:
              match x:
                case Conn.Rx{{+xb, +xhd, +xp, +xp0, +xmet}}:
                  %Equal.sym(Bool, {chk('Con{L.CIEv{e}, %s}' % app_items(R(), T), flag(S0))},
                      {chk(T, flag(st))},
                      {name}_ev(e, {ARGS}, {T}))
                    : {{_ == True{{}} : Bool}}
                  {name}_steps(rest, ka, to, mb, rd, {st})
'''

out = [open('head.bend').read(), open('ans_pre.bend').read()]

# conn_finish: the over flag is the checker's done
def fin_goal(r, E, name):
    return ('{L.chk_cfinish(%s, False{}) == L.chk_cfinish(T, ov(L.cst_of(%s))) : Bool}' % (app_items(r, 'T'), r))

out.append('# ---------------------------------------------------------------------\n# conn_finish: one lemma per dispatcher of Conn.step.ev\n# ---------------------------------------------------------------------\n')
FIN = Law('fin', fin_goal, lambda tag, E, name: '{==}')
out.append(FIN.all())
out.append(steps('fin', lambda xs, f: 'L.chk_cfinish(%s, %s)' % (xs, f), lambda s: 'ov(%s)' % s,
                 'fin_steps(rest, ka, to, mb, rd, Conn.CState{q, o, True{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr})'))
out.append(open('fin.bend').read())

# conn_send_open
def op_goal(r, E, name):
    if name == 'ev':
        lhs = 'L.chk_open(Con{L.CIEv{e}, %s}, o)' % app_items(r, 'T')
    else:
        lhs = 'L.chk_open(%s, %s)' % (app_items(r, 'T'), E['o'])
    return '{%s == L.chk_open(T, op(L.cst_of(%s))) : Bool}' % (lhs, r)

def op_leaf(tag, E, name):
    if tag == 'hopkept':
        H = dict(E); H['o'] = '_'
        P = op_goal(tree.N[name]['call'](H), H, name)
        return ('%%Equal.sym(Bool, o, True{}, and_r(Bool.and(Conn.kept_of(Conn.c_ka(c), Http.done(xp0)), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(k))))), o, ev))\n  : %s\n{==}' % P)
    return '{==}'

out.append('# ---------------------------------------------------------------------\n# conn_send_open: one lemma per dispatcher\n# ---------------------------------------------------------------------\n')
OP = Law('op', op_goal, op_leaf)
out.append(OP.all())
out.append(open('open_pre.bend').read())
out.append(steps('op', lambda xs, f: 'L.chk_open(%s, %s)' % (xs, f), lambda s: 'op(%s)' % s,
                 'op_over(Con{e, rest}, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, o)'))
out.append(open('open.bend').read())


# conn_live
W = 'L.Wait{rs, op, sd, rv, out, dn}'
RELAX = {'opened': 'op', 'sendpend': 'op', 'sent': 'sd', 'sendfailed': 'sd', 'resolved': 'rs', 'resolvefailed': 'rs'}
WF = ['rs', 'op', 'sd', 'rv', 'out']

def wl(E):
    return 'L.Wait{%s}' % ', '.join(E[f] for f in WF + ['dn'])

def lv_goal(r, E, name):
    w = wl(E)
    if name == 'ev':
        w = 'L.w_ev(%s, e)' % w
    return '{inv(L.cst_of(%s), wcmds(L.ccs_of(%s), %s)) == True{} : Bool}' % (r, r, w)

def hp_lhs(E, name):
    rl = RELAX.get(name, 'rv')
    return 'ph_ok(%s, %s)' % (E['ph'], ', '.join('True{}' if f == rl else E[f] for f in WF))

def lv_hyps(name, E):
    if name == 'ev':
        return [('hI', '{Bool.and(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph)) == True{} : Bool}')]
    return [('hP', '{%s == True{} : Bool}' % hp_lhs(E, name)), ('hM', '{met_ok(%s, %s) == True{} : Bool}' % (E['xmet'], E['ph']))]

UP = {'opened': 'up_op', 'sent': 'up_sent', 'sendfailed': 'up_sd', 'resolved': 'up_rs', 'resolvefailed': 'up_rs'}

def lv_hyparg(h, parent, pat, child, E):
    if parent != 'ev':
        return h
    hi = 'Bool.and(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph))'
    if h == 'hP':
        return '%s(ph, rs, op, sd, rv, out, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI))' % UP.get(child, 'up_rv')
    return 'and_r(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), hI)'

def lv_case_extra(name, pat, E):
    if name != 'ev':
        return {}
    ev = pat.split('{')[0]
    return {'Conn.Opened': {'op': 'False{}'}, 'Conn.Sent': {'sd': 'False{}'}, 'Conn.SendFailed': {'sd': 'False{}'},
            'Conn.Resolved': {'rs': 'False{}'}, 'Conn.ResolveFailed': {'rs': 'False{}'}}.get(ev, {'rv': 'False{}'})

def lv_leaf(tag, E, name):
    if tag in ('stay', 'recv'):
        return 'and_i(%s, met_ok(%s, %s), hP, hM)' % (hp_lhs(E, name), E['xmet'], E['ph'])
    if tag == 'sent':
        return 'met_sr(%s, hM)' % E['xmet']
    if tag in ('retry', 'resolved'):
        return 'met_popen(%s)' % E['xmet']
    if tag in ('ans_none', 'ans_fail'):
        return 'Empty.absurd(%s, N.false_ne_true(hf))' % lv_goal(tree.N[name]['call'](E), E, name)
    if tag == 'metstay':
        out = 'match ph:\n'
        for p in tree.PH:
            C = dict(E); C['ph'] = p
            out += '  case %s:\n' % p
            if p in ('Conn.PResolve{}', 'Conn.POpen{}'):
                out += '    and_i(%s, met_ok(True{}, %s), hP, hM)\n' % (hp_lhs(C, name), p)
            else:
                out += '    Empty.absurd(%s, N.false_ne_true(hM))\n' % lv_goal(tree.N[name]['call'](C), C, name)
        return out.rstrip('\n')
    return '{==}'

out.append('# ---------------------------------------------------------------------\n# conn_live: one lemma per dispatcher (the invariant holds after a batch)\n# ---------------------------------------------------------------------\n')
LV = Law('lv', lv_goal, lv_leaf, extra=[(f, 'Bool') for f in WF + ['dn']], efix=lambda name: {'out': 'True{}'} if name == 'sent' else {},
         case_extra=lv_case_extra, hyps=lv_hyps, hyparg=lv_hyparg)
out.append(LV.all())
out.append(open('live.bend').read())
T = 'L.csteps(rest, %s, L.cst_of(%s))' % (C, R())
W6 = 'L.Wait{rs, op, sd, rv, out, dn}'
HI = 'Bool.and(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph))'
CSR = 'L.ccs_of(%s)' % R()
WE = 'L.w_ev(%s, e)' % W6
out.append(f'''def lv_steps(evs: List<&2, Conn.Ev>, {CP}, s: Conn.State, w: L.Wait, +h: {{inv(s, w) == True{{}} : Bool}})
  -> {{L.chk_pending(L.csteps(evs, {C}, s), w) == True{{}} : Bool}}:
  match evs:
    case Nil{{}}:
      inv_live(s, w, h)
    case Con{{+e, +rest}}:
      match s:
        case Conn.CState{{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}}:
          match v:
            case True{{}}:
              match w:
                case L.Wait{{+rs, +op, +sd, +rv, +out, +dn}}:
                  %Equal.sym(Bool, dn, True{{}}, h) : {{L.chk_pending(L.csteps(Con{{e, rest}}, {C}, Conn.CState{{q, o, True{{}}, k, x, ph, pd, pt, hp, ip, pr}}), L.Wait{{rs, op, sd, rv, out, _}}) == True{{}} : Bool}}
                  lv_over(Con{{e, rest}}, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, sd, rv, out)
            case False{{}}:
              match x:
                case Conn.Rx{{+xb, +xhd, +xp, +xp0, +xmet}}:
                  match w:
                    case L.Wait{{+rs, +op, +sd, +rv, +out, +dn}}:
                      %Equal.sym(Bool, L.w_live({W6}), True{{}}, live_of(ph, rs, op, sd, rv, out, dn, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(xmet, ph), h)))
                        : {{Bool.and(_, L.chk_pending({app_items(R(), T)}, {WE})) == True{{}} : Bool}}
                      %Equal.sym(Bool, L.chk_pending({app_items(R(), T)}, {WE}), L.chk_pending({T}, wcmds({CSR}, {WE})), pend_app({CSR}, {T}, {WE}))
                        : {{Bool.and(True{{}}, _) == True{{}} : Bool}}
                      lv_steps(rest, ka, to, mb, rd, L.cst_of({R()}), wcmds({CSR}, {WE}), lv_ev(e, {ARGS}, rs, op, sd, rv, out, dn, {T}, h))

def lv_start(open: Bool, {CP}, +r: Conn.Req, +evs: List<&2, Conn.Ev>)
  -> {{L.chk_pending(L.ctimeline({C}, r, open, evs), L.Wait{{False{{}}, False{{}}, False{{}}, False{{}}, False{{}}, False{{}}}}) == True{{}} : Bool}}:
  match open:
    case True{{}}:
      lv_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start({C}, r, True{{}})), L.Wait{{False{{}}, False{{}}, True{{}}, False{{}}, False{{}}, False{{}}}}, {{==}})
    case False{{}}:
      lv_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start({C}, r, False{{}})), L.Wait{{False{{}}, True{{}}, False{{}}, False{{}}, False{{}}, False{{}}}}, {{==}})

def lv_law(c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>)
  -> {{L.chk_pending(L.ctimeline(c, r, open, evs), L.Wait{{False{{}}, False{{}}, False{{}}, False{{}}, False{{}}, False{{}}}}) == True{{}} : Bool}}:
  match c:
    case Conn.CCfg{{+ka, +to, +mb, +rd}}:
      lv_start(open, ka, to, mb, rd, r, evs)

def L.conn_live(c, r, open, evs):
  lv_law(c, r, open, evs)
''')

# conn_answer
M = 'Maybe<&1, Result<&1, &1, String, Http.Resp & String>>'
MA = ('gotfin', 'eoffin', 'answer')

def pet(E):
    return 'PE(mb, %s, %s, %s)' % (E['hd'], E['bf'], E['ef'])

def an_rhs(r, E, name, done=None):
    bf, ef = (('ev_bf(e, %s)' % E['bf'], 'ev_ef(e, %s)' % E['ef']) if name == 'ev' else (E['bf'], E['ef']))
    cs = 'L.ccs_of(%s)' % r
    return 'L.chk_answer(T, c, a_hd(%s, %s), a_bf(%s, %s), a_ef(%s, %s), ov(L.cst_of(%s)))' % (cs, E['hd'], cs, bf, cs, ef, r)

def an_lhs(r, E, name):
    A = app_items(r, 'T')
    chk = 'L.chk_answer(%s, c, %s, %s, %s, False{})' % (A, E['hd'], E['bf'], E['ef'])
    if name == 'ev':
        return 'L.chk_answer(Con{L.CIEv{e}, %s}, c, %s, %s, %s, False{})' % (A, E['hd'], E['bf'], E['ef'])
    if name in MA:
        return 'Bool.and(L.must_answer(c, %s, %s, %s, %s), %s)' % (E['hd'], E['bf'], E['ef'], A, chk)
    return chk

def an_goal(r, E, name):
    return '{%s == %s : Bool}' % (an_lhs(r, E, name), an_rhs(r, E, name))

def hq_term(E):
    return ('Equal.trans(Http.Parse, Http.feed(xp, d), Http.feed(PE(mb, hd, bf, ef), d), PE(mb, hd, bf ++ d, ef), '
            'Equal.cong(Http.Parse, Http.Parse, p => Http.feed(p, d), xp, PE(mb, hd, bf, ef), hX), pe_feed(ef, mb, hd, bf, d))')

def hxe_term(E):
    return ('Equal.trans(Http.Parse, Http.eof(xp), Http.eof(PE(mb, hd, bf, ef)), PE(mb, hd, bf, True{}), '
            'Equal.cong(Http.Parse, Http.Parse, p => Http.eof(p), xp, PE(mb, hd, bf, ef), hX), pe_eof(ef, mb, hd, bf))')

def hpb_term(p, h):
    return ('Equal.trans(%s, Http.done(%s), Http.done(PE(mb, hd, bf, ef)), L.parse_buf(ef, mb, hd, bf), '
            'Equal.cong(Http.Parse, %s, q => Http.done(q), %s, PE(mb, hd, bf, ef), %s), '
            'Equal.sym(%s, L.parse_buf(ef, mb, hd, bf), Http.done(PE(mb, hd, bf, ef)), pb_pe(ef, mb, hd, bf)))' % (M, p, M, p, h, M))

def an_hyps(name, E):
    if name in ('ev', 'eoffin'):
        return [('hX', '{%s == %s : Http.Parse}' % (E['xp'], pet(E)))]
    if name == 'gotfin':
        return [('hQ', '{p2 == %s : Http.Parse}' % pet(E))]
    if name == 'answer':
        return [('hPB', '{%s == L.parse_buf(%s, mb, %s, %s) : %s}' % (E['m'], E['ef'], E['hd'], E['bf'], M))]
    return []

def an_hyparg(h, parent, pat, child, E):
    if parent == 'ev' and child == 'gotfin':
        return hq_term(E)
    if parent == 'ev' and child == 'eoffin':
        return hxe_term(E)
    if parent == 'gotfin' and child == 'answer':
        return hpb_term('p2', 'hQ')
    if parent == 'eoffin' and child == 'answer':
        return hpb_term('xp', 'hX')
    return h

def an_case_extra(name, pat, E):
    if name != 'ev':
        return {}
    if pat.startswith('Conn.Got'):
        return {'bf': 'bf ++ d'}
    if pat.startswith('Conn.Eof'):
        return {'ef': 'True{}'}
    return {}

def an_pre(name, pat, CE):
    if name in ('gotfin', 'eoffin') and pat == 'False{}':
        p, h = ('p2', 'hQ') if name == 'gotfin' else ('xp', 'hX')
        call = tree.N[name]['call'](CE)
        A = app_items(call, 'T')
        P = '{Bool.and(Bool.or(Bool.not(_), L.answers(c, hd, bf, ef, L.batch(%s))), L.chk_answer(%s, c, hd, bf, ef, False{})) == %s : Bool}' % (A, A, an_rhs(call, CE, name))
        return ('%%Equal.sym(Bool, L.final_resp(c, L.parse_buf(ef, mb, hd, bf)), False{}, fr_eq(ka, to, mb, rd, hd, bf, ef, %s, False{}, %s, ev))\n  : %s' % (p, h, P))
    return ''

def an_leaf(tag, E, name):
    if tag in ('ans_none', 'ans_fail'):
        return 'Empty.absurd(%s, N.false_ne_true(hf))' % an_goal(tree.N[name]['call'](E), E, name)
    if tag == 'answer':
        SD = 'Some{Done{(r0, lo0)}}'
        KEEP = 'Bool.and(Bool.and(Conn.r_keep(r0), ka), String.is_empty(lo0))'
        AO = lambda m: 'L.answer_of(ka, %s, r0, %s)' % (m, KEEP)
        CHKT = 'L.chk_answer(T, c, hd, bf, ef, True{})'
        RDC = 'Bool.or(Maybe.is_none(&2, Nat, rd), Bool.not(L.is_redirect(r0)))'
        G = lambda fr, a1, a2, rdc: '{Bool.and(Bool.or(Bool.not(%s), %s), Bool.and(%s, Bool.and(%s, %s))) == %s : Bool}' % (fr, a1, a2, rdc, CHKT, CHKT)
        return '\n'.join([
            '%%hPB : %s' % G('L.final_resp(c, _)', AO('_'), AO('_'), RDC),
            '%%Equal.sym(Bool, %s, True{}, aok(ka, r0, lo0)) : %s' % (AO(SD), G('L.final_resp(c, %s)' % SD, '_', '_', RDC)),
            '%%Equal.sym(Bool, Bool.or(Bool.not(L.final_resp(c, %s)), True{}), True{}, or_t(Bool.not(L.final_resp(c, %s)))) : {Bool.and(_, Bool.and(True{}, Bool.and(%s, %s))) == %s : Bool}' % (SD, SD, RDC, CHKT, CHKT),
            '%%Equal.sym(Bool, %s, True{}, rd_ok(rd, r0, hf)) : {Bool.and(True{}, Bool.and(True{}, Bool.and(_, %s))) == %s : Bool}' % (RDC, CHKT, CHKT),
            '{==}'])
    return '{==}'

out.append('# ---------------------------------------------------------------------\n# conn_answer: the checker after a batch (an_*), and the parse invariant (ai_*)\n# ---------------------------------------------------------------------\n')
AN = Law('an', an_goal, an_leaf, extra=[('hd', 'Bool'), ('bf', 'String'), ('ef', 'Bool')], case_extra=an_case_extra,
         hyps=an_hyps, hyparg=an_hyparg, pre=an_pre)
out.append(AN.all())

def ai_goal(r, E, name):
    bf, ef = (('ev_bf(e, %s)' % E['bf'], 'ev_ef(e, %s)' % E['ef']) if name == 'ev' else (E['bf'], E['ef']))
    cs = 'L.ccs_of(%s)' % r
    return 'inv_a(L.cst_of(%s), mb, a_hd(%s, %s), a_bf(%s, %s), a_ef(%s, %s))' % (r, cs, E['hd'], cs, bf, cs, ef)

def ai_hyps(name, E):
    if name == 'gotfin':
        return [('hQ', '{p2 == %s : Http.Parse}' % pet(E))]
    if name == 'answer':
        return []
    return [('hX', '{%s == %s : Http.Parse}' % (E['xp'], pet(E)))]

def ai_hyparg(h, parent, pat, child, E):
    if parent == 'ev' and child == 'gotfin':
        return hq_term(E)
    if parent == 'ev' and child == 'eoffin':
        return hxe_term(E)
    if parent == 'gotfin':
        return 'hQ'
    return h

def ai_leaf(tag, E, name):
    if tag in ('fail', 'openfailed', 'answer'):
        return 'Unit{}'
    if tag in ('hop', 'resend', 'hopkept'):
        return '{==}'
    if tag in ('ans_none', 'ans_fail'):
        return 'Empty.absurd(%s, N.false_ne_true(hf))' % ai_goal(tree.N[name]['call'](E), E, name)
    return 'hX'

AI = Law('ai', ai_goal, ai_leaf, extra=[('hd', 'Bool'), ('bf', 'String'), ('ef', 'Bool')], case_extra=an_case_extra,
         hyps=ai_hyps, hyparg=ai_hyparg)
out.append(AI.all())

T = 'L.csteps(rest, %s, L.cst_of(%s))' % (C, R())
CSR = 'L.ccs_of(%s)' % R()
ST = 'L.cst_of(%s)' % R()
OVF = 'q, o, k, x, ph, pd, pt, hp, ip, pr'
out.append(f'''def an_over(evs: List<&2, Conn.Ev>, {CP}, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +x: Conn.Rx, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +hd: Bool, +bf: String, +ef: Bool)
  -> {{L.chk_answer(L.csteps(evs, {C}, Conn.CState{{q, o, True{{}}, k, x, ph, pd, pt, hp, ip, pr}}), {C}, hd, bf, ef, True{{}}) == True{{}} : Bool}}:
  match evs:
    case Nil{{}}:
      {{==}}
    case Con{{+e, +rest}}:
      match e:
        case Conn.Got{{+d}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf ++ d, ef)
        case Conn.Eof{{}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf, True{{}})
        case Conn.Opened{{}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf, ef)
        case Conn.OpenFailed{{m}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf, ef)
        case Conn.Sent{{}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf, ef)
        case Conn.SendFailed{{m}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf, ef)
        case Conn.Late{{}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf, ef)
        case Conn.Resolved{{i}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf, ef)
        case Conn.ResolveFailed{{m}}:
          an_over(rest, ka, to, mb, rd, {OVF}, hd, bf, ef)

def an_steps(evs: List<&2, Conn.Ev>, {CP}, s: Conn.State, +hd: Bool, +bf: String, +ef: Bool, +hX: inv_a(s, mb, hd, bf, ef))
  -> {{L.chk_answer(L.csteps(evs, {C}, s), {C}, hd, bf, ef, ov(s)) == True{{}} : Bool}}:
  match evs:
    case Nil{{}}:
      {{==}}
    case Con{{+e, +rest}}:
      match s:
        case Conn.CState{{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}}:
          match v:
            case True{{}}:
              an_over(Con{{e, rest}}, ka, to, mb, rd, {OVF}, hd, bf, ef)
            case False{{}}:
              match x:
                case Conn.Rx{{+xb, +xhd, +xp, +xp0, +xmet}}:
                  %Equal.sym(Bool, L.chk_answer(Con{{L.CIEv{{e}}, {app_items(R(), T)}}}, {C}, hd, bf, ef, False{{}}),
                      L.chk_answer({T}, {C}, a_hd({CSR}, hd), a_bf({CSR}, ev_bf(e, bf)), a_ef({CSR}, ev_ef(e, ef)), ov({ST})),
                      an_ev(e, {ARGS}, hd, bf, ef, {T}, hX))
                    : {{_ == True{{}} : Bool}}
                  an_steps(rest, ka, to, mb, rd, {ST}, a_hd({CSR}, hd), a_bf({CSR}, ev_bf(e, bf)), a_ef({CSR}, ev_ef(e, ef)),
                    ai_ev(e, {ARGS}, hd, bf, ef, {T}, hX))

def an_start(open: Bool, {CP}, +r: Conn.Req, +evs: List<&2, Conn.Ev>)
  -> {{L.chk_answer(L.ctimeline({C}, r, open, evs), {C}, False{{}}, "", False{{}}, False{{}}) == True{{}} : Bool}}:
  match open:
    case True{{}}:
      an_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start({C}, r, True{{}})),
        String.starts_with(Http.request(Conn.q_target(r), Conn.q_url(r), Conn.q_body(r), Conn.q_seq(r), Conn.q_name(r), ka), "HEAD "), "", False{{}}, {{==}})
    case False{{}}:
      an_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start({C}, r, False{{}})), False{{}}, "", False{{}}, {{==}})

def an_law(c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>)
  -> {{L.chk_answer(L.ctimeline(c, r, open, evs), c, False{{}}, "", False{{}}, False{{}}) == True{{}} : Bool}}:
  match c:
    case Conn.CCfg{{+ka, +to, +mb, +rd}}:
      an_start(open, ka, to, mb, rd, r, evs)

def L.conn_answer(c, r, open, evs):
  an_law(c, r, open, evs)
''')

open(sys.argv[1], 'w').write('\n'.join(out))

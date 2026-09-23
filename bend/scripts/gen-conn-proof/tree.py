# The dispatch tree of Conn.step.ev: every def of lib/conn.bend that
# matches a computed value, down to the leaves (the moves). A law's proof
# instantiates it with its goal G(result) and its leaf proofs.

FIELDS = [('q', 'Conn.Req'), ('o', 'Bool'), ('kq', 'Conn.Req'), ('kt', 'String'), ('kn', 'Nat'), ('kg', 'Bool'), ('ku', 'Bool'), ('kh', 'Nat'), ('xb', 'String'), ('xhd', 'Conn.Head'), ('xp', 'Http.Parse'), ('xp0', 'Http.Parse'), ('xmet', 'Bool'), ('ph', 'Conn.Phase'),
          ('pd', 'Conn.Req'), ('pt', 'String'), ('hp', 'Bool'), ('ip', 'String'), ('pr', 'Nat')]

def K(env):
    return 'Conn.Cur{%s}' % ', '.join(env[f] for f in ['kq', 'kt', 'kn', 'kg', 'ku', 'kh'])

def X(env):
    return 'Conn.Rx{%s, %s, %s, %s, %s}' % tuple(env[f] for f in ['xb', 'xhd', 'xp', 'xp0', 'xmet'])

def S(env):
    return 'Conn.CState{%s, %s, False{}, %s, %s, %s, %s, %s, %s, %s, %s}' % tuple([env['q'], env['o'], K(env), X(env)] + [env[f] for f in ['ph', 'pd', 'pt', 'hp', 'ip', 'pr']])

MRES = 'Maybe<&1, Result<&1, &1, String, Http.Resp & String>>'

def NT(E):
    return ('Conn.redirect_target(Conn.u_host(Conn.q_url(%s)), Conn.q_target(Conn.cur_req(%s)), Conn.q_url(Conn.cur_req(%s)), Conn.hd_code(Conn.rx_hd(%s)), Conn.hd_loc(Conn.rx_hd(%s)))'
            % (E['q'], K(E), K(E), X(E), X(E)))

def NQ(E):
    return ('Conn.Req{nt, Conn.url_or(Conn.q_url(Conn.cur_req(%s)), pu), "", Conn.redirect_body(kk, Conn.q_body(Conn.cur_req(%s))), Conn.q_seq(%s), Conn.q_name(%s)}'
            % (K(E), K(E), E['q'], E['q']))

def TEXT(E):
    nq = NQ(E)
    return 'Http.request(Conn.q_target(%s), Conn.q_url(%s), Conn.q_body(%s), Conn.q_seq(%s), Conn.q_name(%s), Conn.c_ka(c))' % (nq, nq, nq, E['q'], E['q'])

def KEPT(E):
    return ('Bool.and(Bool.and(Conn.kept_of(Conn.c_ka(c), Http.done(Conn.rx_p0(%s))), Nat.is_eq(Conn.u_port(Conn.q_url(nq)), Conn.u_port(Conn.q_url(Conn.cur_req(%s))))), %s)'
            % (X(E), K(E), E['o']))

def LH(E):
    return 'Conn.late.head(%s, c, %s)' % (E['xhd'], E['xb'])

def TT(E):
    return 'Conn.rx_feed.hd(%s, c, %s, p2, %s, %s, d)' % (E['xhd'], E['xb'], E['xp0'], E['xmet'])

# node: name -> dict(mv, mt, extra=[(n,t)], call=lambda env: expr, cases=[(pat, val, action)])
# action: ('leaf', tag) or ('sub', name, {field overrides}, {extra args}, match-value expr)
N = {}

def node(name, mv, mt, call, cases, extra=(), fix=None, eqv=None, hyp=()):
    N[name] = dict(mv=mv, mt=mt, call=call, cases=cases, extra=list(extra), fix=fix or {}, eqv=eqv, hyp=list(hyp))

def sub(name, val, fo=None, ex=None, hy=None):
    return ('sub', name, fo or {}, ex or {}, val, hy or {})

def leaf(tag):
    return ('leaf', tag)

node('ev', 'e', 'Conn.Ev', lambda E: 'Conn.step.ev(%s, c, %s)' % (E['e'], S(E)), [
    ('Conn.Opened{}', None, sub('opened', lambda E: E['ph'], {'o': 'True{}'})),
    ('Conn.OpenFailed{+m}', None, leaf('openfailed')),
    ('Conn.Sent{}', None, sub('sent', lambda E: E['ph'])),
    ('Conn.SendFailed{+m}', None, sub('sendfailed', lambda E: 'Conn.lost(%s)' % S(E), {'o': 'False{}'}, {'m': 'm'})),
    ('Conn.Got{+d}', None, sub('gotfin', lambda E: 'Conn.final_of(c, Http.done(Http.feed(Conn.rx_p(%s), d)))' % X(E),
        {'kg': lambda E: 'Bool.or(%s, Bool.not(String.is_empty(d)))' % E['kg']}, {'p2': lambda E: 'Http.feed(Conn.rx_p(%s), d)' % X(E), 'd': 'd'})),
    ('Conn.Eof{}', None, sub('eoffin', lambda E: 'Conn.final_of(c, Http.done(Conn.rx_p(Conn.rx_eof(%s))))' % X(E),
        {'o': 'False{}', 'xp': lambda E: 'Http.eof(%s)' % E['xp']})),
    ('Conn.Late{}', None, sub('lateredir', lambda E: 'Conn.hd_redir(%s)' % LH(E))),
    ('Conn.Resolved{+ip2}', None, sub('resolved', lambda E: E['ph'], {'ip': 'ip2'})),
    ('Conn.ResolveFailed{+m}', None, sub('resolvefailed', lambda E: E['ph'], {}, {'m': 'm'})),
])

PH = ['Conn.PResolve{}', 'Conn.POpen{}', 'Conn.PSend{}', 'Conn.PRecv{}']

def phcases(hit, act, other):
    return [(p, 'ph', act if p == hit else other) for p in PH]

node('opened', 'ph', 'Conn.Phase', lambda E: 'Conn.on_opened(%s, c, %s)' % (E['ph'], S(E)),
     phcases('Conn.POpen{}', sub('sendpend', lambda E: E['hp']), leaf('stay')), fix={'o': 'True{}'})
node('sendpend', 'hp', 'Bool', lambda E: 'Conn.send_pend(%s, c, %s)' % (E['hp'], S(E)),
     [('True{}', 'hp', leaf('hop')), ('False{}', 'hp', leaf('resend'))], fix={'o': 'True{}'})
node('sent', 'ph', 'Conn.Phase', lambda E: 'Conn.on_sent(%s, %s)' % (E['ph'], S(E)),
     phcases('Conn.PSend{}', leaf('sent'), leaf('stay')))
node('sendfailed', 'l', 'Bool', lambda E: 'Conn.on_send_failed(%s, %s, m)' % (E['l'], S(E)),
     [('True{}', 'l', leaf('retry')), ('False{}', 'l', leaf('fail'))], extra=[('m', 'String')], eqv=lambda E: 'Conn.lost(%s)' % S(E))

node('gotfin', 'f', 'Bool', lambda E: 'Conn.got.fin(%s, c, %s, p2, d)' % (E['f'], S(E)),
     [('True{}', 'f', sub('answer', lambda E: 'Http.done(p2)', hy={'hf': 'ev'})),
      ('False{}', 'f', sub('gotdue', lambda E: 'Conn.due(Conn.rx_feed(c, %s, p2, d))' % X(E),
          {'xb': lambda E: 'Conn.rx_buf(%s)' % TT(E), 'xhd': lambda E: 'Conn.rx_hd(%s)' % TT(E), 'xp': 'p2', 'xp0': lambda E: 'Conn.rx_p0(%s)' % TT(E)},
          {'old': lambda E: E['xp'], 'data': 'd'}))],
     extra=[('p2', 'Http.Parse'), ('d', 'String')], eqv=lambda E: 'Conn.final_of(c, Http.done(p2))')
node('gotdue', 'dd', 'Bool', lambda E: 'Conn.got.due(%s, c, %s, old, data)' % (E['dd'], S(E)),
     [('True{}', 'dd', sub('redirect', lambda E: 'Nat.is_ge(Conn.cur_hops(%s), Conn.rd_limit(Conn.c_rd(c)))' % K(E))),
      ('False{}', 'dd', sub('gotbad', lambda E: 'Conn.is_fail(Http.done(Conn.rx_p(%s)))' % X(E), {}, {'old': 'old', 'data': 'data'}))],
     extra=[('old', 'Http.Parse'), ('data', 'String')], eqv=lambda E: 'Conn.due(%s)' % X(E))

node('gotbad', 'b', 'Bool', lambda E: 'Conn.got.bad(%s, %s, old, data)' % (E['b'], S(E)),
     [('True{}', 'b', sub('badof', lambda E: 'Conn.p_body(Conn.upto(data, False{}, old, old))', {},
          {'good': 'Conn.upto(data, False{}, old, old)',
           'msg': lambda E: 'Conn.bad.msg(Conn.p_stat(Conn.upto(data, False{}, old, old)), %s, Conn.fail_msg(Http.done(Conn.rx_p(%s))))' % (S(E), X(E))})),
      ('False{}', 'b', sub('gotmore', lambda E: E['ph']))],
     extra=[('old', 'Http.Parse'), ('data', 'String')], eqv=lambda E: 'Conn.is_fail(Http.done(Conn.rx_p(%s)))' % X(E))

node('badof', 'body', 'Bool', lambda E: 'Conn.bad.of(%s, %s, good, msg)' % (E['body'], S(E)),
     [('True{}', 'body', leaf('fail')), ('False{}', 'body', leaf('fail'))], extra=[('good', 'Http.Parse'), ('msg', 'String')])
node('gotmore', 'ph', 'Conn.Phase', lambda E: 'Conn.got.more(%s, %s)' % (E['ph'], S(E)),
     phcases('Conn.PRecv{}', leaf('recv'), leaf('stay')))
node('redirect', 'stop', 'Bool', lambda E: 'Conn.redirect.of(%s, c, %s)' % (E['stop'], S(E)),
     [('True{}', 'stop', leaf('fail')),
      ('False{}', 'stop', sub('followok', lambda E: 'Result.is_done(&2, &2, String, Tgt.Url, Tgt.parse_url(Conn.tgt_url(%s)))' % NT(E), {},
          {'nt': NT, 'pu': lambda E: 'Tgt.parse_url(Conn.tgt_url(%s))' % NT(E), 'kk': lambda E: 'Conn.hd_code(Conn.rx_hd(%s))' % X(E)}))])

node('followok', 'ok', 'Bool', lambda E: 'Conn.follow.ok(%s, c, %s, nt, pu, kk)' % (E['ok'], S(E)),
     [('True{}', 'ok', sub('followhost', lambda E: 'Conn.same_host(Conn.u_host(Conn.q_url(%s)), Conn.u_host(Conn.q_url(Conn.cur_req(%s))))' % (NQ(E), K(E)), {},
          {'nq': NQ, 'text': TEXT})),
      ('False{}', 'ok', leaf('fail'))],
     extra=[('nt', 'Tgt.Target'), ('pu', 'Result<&2, &2, String, Tgt.Url>'), ('kk', 'Nat')])
node('followhost', 'same', 'Bool', lambda E: 'Conn.follow.host(%s, c, %s, nq, text)' % (E['same'], S(E)),
     [('True{}', 'same', sub('followopen', lambda E: KEPT(E), {}, {'nq': 'nq', 'text': 'text', 'hp2': 'Conn.u_port(Conn.q_url(nq))'})),
      ('False{}', 'same', leaf('resolve'))],
     extra=[('nq', 'Conn.Req'), ('text', 'String')])

node('followopen', 'kept', 'Bool', lambda E: 'Conn.follow.open(%s, c, %s, nq, text, hp2)' % (E['kept'], S(E)),
     [('True{}', 'kept', leaf('hopkept')), ('False{}', 'kept', leaf('shutopen'))],
     extra=[('nq', 'Conn.Req'), ('text', 'String'), ('hp2', 'Nat')], eqv=KEPT)
node('answer', 'm', MRES, lambda E: 'Conn.answer(c, %s, %s)' % (S(E), E['m']), 'ANSWER',
     hyp=[('hf', lambda E: '{Conn.final_of(c, %s) == True{} : Bool}' % E['m'])])
node('eoffin', 'f', 'Bool', lambda E: 'Conn.eof.fin(%s, c, %s)' % (E['f'], S(E)),
     [('True{}', 'f', sub('answer', lambda E: 'Http.done(%s)' % E['xp'], hy={'hf': 'ev'})),
      ('False{}', 'f', sub('eoflost', lambda E: 'Conn.lost(%s)' % S(E)))], eqv=lambda E: 'Conn.final_of(c, Http.done(%s))' % E['xp'])
node('eoflost', 'l', 'Bool', lambda E: 'Conn.eof.lost(%s, c, %s)' % (E['l'], S(E)),
     [('True{}', 'l', leaf('retry')), ('False{}', 'l', sub('eofmet', lambda E: E['xmet']))], eqv=lambda E: 'Conn.lost(%s)' % S(E))

node('eofmet', 'xmet', 'Bool', lambda E: 'Conn.eof.met(%s, c, %s)' % (E['xmet'], S(E)),
     [('True{}', 'xmet', leaf('metstay')), ('False{}', 'xmet', sub('eofredir', lambda E: 'Conn.hd_redir(Conn.rx_hd(%s))' % X(E)))])
node('eofredir', 'r', 'Bool', lambda E: 'Conn.eof.redir(%s, c, %s)' % (E['r'], S(E)),
     [('True{}', 'r', sub('redirect', lambda E: 'Nat.is_ge(Conn.cur_hops(%s), Conn.rd_limit(Conn.c_rd(c)))' % K(E))),
      ('False{}', 'r', sub('eoftext', lambda E: 'Conn.in_of(Conn.rx_hd(%s), Conn.rx_buf(%s))' % (X(E), X(E))))], eqv=lambda E: 'Conn.hd_redir(Conn.rx_hd(%s))' % X(E))

node('eoftext', 'hin', 'Bool', lambda E: 'Conn.eof.text(%s, %s)' % (E['hin'], S(E)),
     [('True{}', 'hin', leaf('fail')), ('False{}', 'hin', sub('eofempty', lambda E: 'String.is_empty(Conn.rx_buf(%s))' % X(E)))], eqv=lambda E: 'Conn.in_of(Conn.rx_hd(%s), Conn.rx_buf(%s))' % (X(E), X(E)))

node('eofempty', 'em', 'Bool', lambda E: 'Conn.eof.text.empty(%s, %s)' % (E['em'], S(E)),
     [('True{}', 'em', leaf('fail')),
      ('False{}', 'em', sub('eofnl', lambda E: 'String.ends_with(Conn.final_from(String.reverse(Conn.rx_buf(%s))), "\\n")' % X(E)))], eqv=lambda E: 'String.is_empty(Conn.rx_buf(%s))' % X(E))

node('eofnl', 'nl', 'Bool', lambda E: 'Conn.eof.text.nl(%s, %s)' % (E['nl'], S(E)),
     [('True{}', 'nl', leaf('fail')), ('False{}', 'nl', leaf('fail'))], eqv=lambda E: 'String.ends_with(Conn.final_from(String.reverse(Conn.rx_buf(%s))), "\\n")' % X(E))

node('lateredir', 'r', 'Bool', lambda E: 'Conn.late.redir(%s, c, %s, %s)' % (E['r'], S(E), LH(E)),
     [('True{}', 'r', leaf('fail')), ('False{}', 'r', sub('latein', lambda E: 'Conn.in_of(Conn.rx_hd(%s), Conn.rx_buf(%s))' % (X(E), X(E))))], eqv=lambda E: 'Conn.hd_redir(%s)' % LH(E))

node('latein', 'hin', 'Bool', lambda E: 'Conn.late.in(%s, %s)' % (E['hin'], S(E)),
     [('True{}', 'hin', leaf('fail')), ('False{}', 'hin', leaf('fail'))], eqv=lambda E: 'Conn.in_of(Conn.rx_hd(%s), Conn.rx_buf(%s))' % (X(E), X(E)))

node('resolved', 'ph', 'Conn.Phase', lambda E: 'Conn.on_resolved(%s, %s)' % (E['ph'], S(E)),
     phcases('Conn.PResolve{}', leaf('resolved'), leaf('stay')))
node('resolvefailed', 'ph', 'Conn.Phase', lambda E: 'Conn.on_resolve_failed(%s, %s, m)' % (E['ph'], S(E)),
     phcases('Conn.PResolve{}', leaf('fail'), leaf('stay')), extra=[('m', 'String')])

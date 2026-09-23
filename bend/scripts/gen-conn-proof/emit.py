import re
import tree
from tree import N, FIELDS, S

def ind(s, n):
    return '\n'.join((' ' * n + l) if l.strip() else l for l in s.split('\n'))

def val(v, E):
    return v(E) if callable(v) else v

class Law:
    """One law's walk of the dispatch tree.
    goal(R, E, name) -> the lemma's type for result R;
    leaf(tag, E, name) -> a leaf's proof;
    extra: law-wide params (name, type); efix(name) -> {extra: value} fixed in a lemma;
    case_extra(name, pat, E) -> {extra: value} passed to the child of a case;
    hyps(name, E) -> [(hname, type)]; hyparg(hname, parent, pat, child, CE) -> proof text."""
    def __init__(self, prefix, goal, leaf, extra=(), efix=None, case_extra=None, hyps=None, hyparg=None, pre=None, wrap=None):
        self.pre = pre or (lambda name, pat, CE: '')
        self.wrap = wrap or (lambda name, pat, CE, s: s)
        self.prefix, self.goal, self.leaf = prefix, goal, leaf
        self.extra = list(extra)
        self.efix = efix or (lambda name: {})
        self.case_extra = case_extra or (lambda name, pat, E: {})
        self.hyps = hyps or (lambda name, E: [])
        self.hyparg = hyparg or (lambda h, parent, pat, child, CE: h)

    def env(self, name):
        nd = N[name]
        E = {f: f for f, _ in FIELDS}
        E.update(nd['fix'])
        E[nd['mv']] = nd['mv']
        for n, _ in nd['extra']:
            E[n] = n
        for n, _ in self.extra:
            E[n] = n
        E.update(self.efix(name))
        return E

    def params(self, name, E):
        nd = N[name]
        ps = ['%s: %s' % (nd['mv'], nd['mt']), '+ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>']
        ps += ['+%s: %s' % (f, t) for f, t in FIELDS if f != nd['mv'] and f not in nd['fix']]
        ps += ['+%s: %s' % (n, t) for n, t in nd['extra']]
        ps += ['+%s: %s' % (n, t) for n, t in self.extra if n not in self.efix(name)]
        ps += ['+T: List<&2, L.CItem>']
        if nd['eqv']:
            ps += ['+ev: {%s == %s : %s}' % (nd['eqv'](E), nd['mv'], nd['mt'])]
        for n, t in nd['hyp']:
            ps += ['+%s: %s' % (n, t(E))]
        ps += ['+%s: %s' % (n, t) for n, t in self.hyps(name, E)]
        return ps

    def call(self, parent, E, sname, args_mv, fo, ex, hy, pat):
        C = dict(E)
        for f, v in fo.items():
            C[f] = val(v, E)
        sn = N[sname]
        C[sn['mv']] = val(args_mv, E)
        a = [C[sn['mv']], 'ka, to, mb, rd'] + [C[f] for f, _ in FIELDS if f != sn['mv'] and f not in sn['fix']]
        for n, _ in sn['extra']:
            C[n] = val(ex[n], E) if n in ex else n
            a.append(C[n])
        cx = self.case_extra(parent, pat, E)
        fx = self.efix(sname)
        for n, _ in self.extra:
            if n not in fx:
                a.append(cx.get(n, C[n]))
        a.append('T')
        if sn['eqv']:
            a.append('{==}')
        for n, _ in sn['hyp']:
            a.append(hy[n])
        for n, _ in self.hyps(sname, C):
            a.append(self.hyparg(n, parent, pat, sname, E))
        return '%s_%s(%s)' % (self.prefix, sname, ', '.join(a))

    def lemma(self, name):
        return re.sub(r'\bc\b', 'Conn.CCfg{ka, to, mb, rd}', self.lemma0(name))

    def lemma0(self, name):
        nd = N[name]
        E = self.env(name)
        out = 'def %s_%s(%s)\n  -> %s:\n' % (self.prefix, name, ', '.join(self.params(name, E)), self.goal(nd['call'](E), E, name))
        if nd['cases'] == 'ANSWER':
            def ce(m):
                C = dict(E); C['m'] = m; return C
            body = 'match m:\n  case None{}:\n%s\n  case Some{res}:\n    match res:\n      case Fail{e}:\n%s\n      case Done{pr}:\n        match pr:\n          case (+r0, +lo0):\n%s' % (
                ind(self.leaf('ans_none', ce('None{}'), name), 4), ind(self.leaf('ans_fail', ce('Some{Fail{e}}'), name), 8),
                ind(self.leaf('answer', ce('Some{Done{(r0, lo0)}}'), name), 12))
            return out + ind(body, 2) + '\n'
        body = 'match %s:\n' % nd['mv']
        for pat, _, act in nd['cases']:
            CE = dict(E)
            CE[nd['mv']] = pat.replace('+', '')
            body += '  case %s:\n' % pat
            if act[0] == 'leaf':
                body += ind(self.leaf(act[1], CE, name), 4) + '\n'
            else:
                _, sname, fo, ex, v, hy = act
                pr = self.pre(name, pat, CE)
                if pr:
                    body += ind(pr, 4) + '\n'
                body += ind(self.wrap(name, pat, CE, self.call(name, CE, sname, v, fo, ex, hy, pat)), 4) + '\n'
        return out + ind(body, 2) + '\n'

    def all(self):
        order, seen = [], set()
        def visit(n):
            if n in seen:
                return
            seen.add(n)
            cs = N[n]['cases']
            if cs != 'ANSWER':
                for _, _, act in cs:
                    if act[0] == 'sub':
                        visit(act[1])
            order.append(n)
        for n in N:
            visit(n)
        return '\n'.join(self.lemma(n) for n in order)

import sys
F = "+c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +room: Nat, +busy: List<&2, Nat>, +idle: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>"
OKN = "Eng.may(c, now, 1n+next, Some{now})"
def G_ARGS(): return f"r, {OKN}, c, now, 1n+next, 1n+grown, Con{{grown, busy}}, nap, Some{{now}}"
def I_ARGS(): return f"rest, {OKN}, c, now, 1n+next, grown, room, Con{{w, busy}}, nap, Some{{now}}"

out = []
def emit(s): out.append(s)

def checker(X):
    n = X['name']; chk = X['chk']; A = n + 'A'
    hd0 = X.get('hyps_decl', ''); hp = X.get('hyps_pass', '')
    hdg = hd0.replace('$idle', '[]'); hd = hd0.replace('$idle', 'idle')
    hpg = X.get('hp_grow_rec', hp); hpi = X.get('hp_idle_rec', hp)
    okd = ", eok: {Eng.may(c, now, next, last) == ok : Bool}" if X.get('ok') else ""
    KF = X['KF']; K0 = X['K0']; ty = X.get('ty', 'Bool')
    emit(f"# ---------------------------------------------------------------------\n# eng: {n}\n# ---------------------------------------------------------------------\n")
    emit(f"def {A}(xs: List<&2, Eng.Cmd>, T: List<&2, L.Item>{X['A_params']}) -> {ty}:\n  {chk}(List.append(&2, L.Item, L.cmds_items(xs), T){X['A_args']})\n")
    emit(X['settle'])
    # grow
    gst = f"Eng.grow_st(r, {OKN}, c, now, 1n+next, 1n+grown, Con{{grown, busy}}, nap, Some{{now}})"
    gcs = f"Eng.grow_cs(r, {OKN}, c, now, 1n+next, 1n+grown, Con{{grown, busy}}, nap, Some{{now}})"
    gih = f"grow_{n}({G_ARGS()}, T{hpg}{', {==}' if X.get('ok') else ''})"
    emit(f"""def grow_{n}(room: Nat, ok: Bool, +c: Eng.Cfg, +now: Nat, +next: Nat, +grown: Nat, +busy: List<&2, Nat>, +nap: Bool, +last: Maybe<&2, Nat>, +T: List<&2, L.Item>{hdg}{okd})
  -> {{{chk}(T{KF('Eng.grow_st(room, ok, c, now, next, grown, busy, nap, last)')}) == {A}(Eng.grow_cs(room, ok, c, now, next, grown, busy, nap, last), T{X['K0'].replace('$idle', '[]')}) : {ty}}}:
  match room:
    case 0n:
      settle_{n}(c, now, next, grown, 0n, busy, [], nap, last, T{hp})
    case 1n+(+r):
      match ok:
        case True{{}}:
{X['fire_grow'](gst, gcs, gih)}
        case False{{}}:
          settle_{n}(c, now, next, grown, 1n+r, busy, [], nap, last, T{hp})
""")
    ist = f"Eng.idle_st(rest, {OKN}, c, now, 1n+next, grown, room, Con{{w, busy}}, nap, Some{{now}})"
    ics = f"Eng.idle_cs(rest, {OKN}, c, now, 1n+next, grown, room, Con{{w, busy}}, nap, Some{{now}})"
    iih = f"idle_{n}({I_ARGS()}, T{hpi}{', {==}' if X.get('ok') else ''})"
    emit(f"""def idle_{n}(idle: List<&2, Nat>, ok: Bool, {F.replace('+idle: List<&2, Nat>, ', '')}, +T: List<&2, L.Item>{hd}{okd})
  -> {{{chk}(T{KF('Eng.idle_st(idle, ok, c, now, next, grown, room, busy, nap, last)')}) == {A}(Eng.idle_cs(idle, ok, c, now, next, grown, room, busy, nap, last), T{X['K0'].replace('$idle', 'idle')}) : {ty}}}:
  match idle:
    case Nil{{}}:
      grow_{n}(room, ok, c, now, next, grown, busy, nap, last, T{hp}{', eok' if X.get('ok') else ''})
    case Con{{+w, +rest}}:
      match ok:
        case True{{}}:
{X['fire_idle'](ist, ics, iih)}
        case False{{}}:
          settle_{n}(c, now, next, grown, room, busy, Con{{w, rest}}, nap, last, T{hp})
""")
    # steps
    if X.get('no_steps'):
        if X.get('law'):
            emit(X['law'])
        return
    shd = X.get('steps_hd', hd)
    def branch(kind, t, busy, idle, nap):
        okx = f"Eng.may(c, {t}, next, last)"
        args = f"{idle}, {okx}, c, {t}, next, grown, room, {busy}, {nap}, last"
        st = f"Eng.idle_st({args})"
        over_st = f"Eng.EState{{{t}, next, grown, room, {busy}, {idle}, {nap}, last, True{{}}}}"
        if 'steps_hp' in X:
            pro, prc, ohp, chp, ihp = X['steps_hp'](kind, args, st, over_st)
        else:
            pro, prc, ohp, chp, ihp = '', '', hp, hp, hp
        return f"""              match over:
                case True{{}}:
{pro}                  steps_{n}(rest, {over_st}, c{ohp})
                case False{{}}:
{prc}                  %idle_{n}({args}, L.steps(rest, c, {st}){chp}{', {==}' if X.get('ok') else ''}) : {{_ == True{{}} : Bool}}
                  steps_{n}(rest, {st}, c{ihp})"""
    emit(f"""def steps_{n}(evs: List<&2, Eng.Ev>, +s: Eng.State, +c: Eng.Cfg{shd}) -> {{{chk}(L.steps(evs, c, s){X['KS']('s')}) == True{{}} : Bool}}:
  match evs:
    case Nil{{}}:
      {X.get('nil', '{==}')}
    case Con{{+e, +rest}}:
      match e:
        case Eng.Clock{{+t}}:
          match s:
            case Eng.EState{{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}}:
{branch('clock', 't', 'busy', 'idle', 'False{}')}
        case Eng.Freed{{+w, +t}}:
          match s:
            case Eng.EState{{+now, +next, +grown, +room, +busy, +idle, +nap, +last, +over}}:
{branch('freed', 't', 'Eng.drop_nat(w, busy)', 'Eng.freed_idle(Eng.has_nat(w, busy), w, idle)', 'nap')}
""")
    if X.get('law'):
        emit(X['law'])

exec(open(sys.argv[1]).read())
open(sys.argv[2], 'w').write(HEAD + "\n" + "\n".join(out))

# ---------------------------------------------------------------------
# conn_finish: the machine's over flag is the checker's done
# ---------------------------------------------------------------------

def fin_start(open: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +r: Conn.Req, +evs: List<&2, Conn.Ev>)
  -> {L.chk_cfinish(L.ctimeline(Conn.CCfg{ka, to, mb, rd}, r, open, evs), False{}) == True{} : Bool}:
  match open:
    case True{}:
      fin_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, True{})))
    case False{}:
      fin_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, False{})))

def fin_law(c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>) -> {L.chk_cfinish(L.ctimeline(c, r, open, evs), False{}) == True{} : Bool}:
  match c:
    case Conn.CCfg{+ka, +to, +mb, +rd}:
      fin_start(open, ka, to, mb, rd, r, evs)

def L.conn_finish(c, r, open, evs):
  fin_law(c, r, open, evs)

def op_start(open: Bool, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +r: Conn.Req, +evs: List<&2, Conn.Ev>)
  -> {L.chk_open(L.ctimeline(Conn.CCfg{ka, to, mb, rd}, r, open, evs), open) == True{} : Bool}:
  match open:
    case True{}:
      op_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, True{})))
    case False{}:
      op_steps(evs, ka, to, mb, rd, L.cst_of(Conn.start(Conn.CCfg{ka, to, mb, rd}, r, False{})))

def op_law(c: Conn.Cfg, +r: Conn.Req, +open: Bool, +evs: List<&2, Conn.Ev>) -> {L.chk_open(L.ctimeline(c, r, open, evs), open) == True{} : Bool}:
  match c:
    case Conn.CCfg{+ka, +to, +mb, +rd}:
      op_start(open, ka, to, mb, rd, r, evs)

def L.conn_send_open(c, r, open, evs):
  op_law(c, r, open, evs)

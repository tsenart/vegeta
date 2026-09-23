# ---------------------------------------------------------------------
# conn_send_open: the machine's open flag is the checker's, until Finish
# ---------------------------------------------------------------------

def op_over(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +xb: String, +xhd: Conn.Head, +xp: Http.Parse, +xp0: Http.Parse, +xmet: Bool, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +f: Bool)
  -> {L.chk_open(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, True{}, k, Conn.Rx{xb, xhd, xp, xp0, xmet}, ph, pd, pt, hp, ip, pr}), f) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Conn.Opened{}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, True{})
        case Conn.OpenFailed{m}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, False{})
        case Conn.Sent{}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)
        case Conn.SendFailed{m}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, False{})
        case Conn.Got{d}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)
        case Conn.Eof{}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, False{})
        case Conn.Late{}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)
        case Conn.Resolved{i}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)
        case Conn.ResolveFailed{m}:
          op_over(rest, ka, to, mb, rd, q, o, k, xb, xhd, xp, xp0, xmet, ph, pd, pt, hp, ip, pr, f)


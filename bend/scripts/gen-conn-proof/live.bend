# ---------------------------------------------------------------------
# conn_live: the walk over the timeline
# ---------------------------------------------------------------------

def pend_app(cs: List<&2, Conn.Cmd>, +T: List<&2, L.CItem>, +w: L.Wait)
  -> {L.chk_pending(List.append(&2, L.CItem, L.ccmds_items(cs), T), w) == L.chk_pending(T, wcmds(cs, w)) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+k, +rest}:
      pend_app(rest, T, L.w_cmd(w, k))

def or_l(a: Bool, -b: Bool, e: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      bool_absurd(b, True{}, e)

def or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# a phase's wait makes the request live
def live_of(ph: Conn.Phase, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool, +dn: Bool, +h: {ph_ok(ph, rs, op, sd, rv, out) == True{} : Bool})
  -> {L.w_live(L.Wait{rs, op, sd, rv, out, dn}) == True{} : Bool}:
  match ph:
    case Conn.PResolve{}:
      or_l(Bool.or(dn, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)), or_r(dn, rs, h))
    case Conn.POpen{}:
      or_r(Bool.or(dn, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)), or_l(Bool.or(op, sd), Bool.and(out, rv), or_l(op, sd, h)))
    case Conn.PSend{}:
      or_r(Bool.or(dn, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)), or_l(Bool.or(op, sd), Bool.and(out, rv), or_r(op, sd, h)))
    case Conn.PRecv{}:
      or_r(Bool.or(dn, rs), Bool.or(Bool.or(op, sd), Bool.and(out, rv)), or_r(Bool.or(op, sd), Bool.and(out, rv), and_i(out, rv, and_r(rv, out, h), and_l(rv, out, h))))

# once finished, the request is done and stays so
def lv_over(evs: List<&2, Conn.Ev>, +ka: Bool, +to: Nat, +mb: Maybe<&2, Nat>, +rd: Maybe<&2, Nat>, +q: Conn.Req, +o: Bool, +k: Conn.Cur, +x: Conn.Rx, +ph: Conn.Phase, +pd: Conn.Req, +pt: String, +hp: Bool, +ip: String, +pr: Nat, +rs: Bool, +op: Bool, +sd: Bool, +rv: Bool, +out: Bool)
  -> {L.chk_pending(L.csteps(evs, Conn.CCfg{ka, to, mb, rd}, Conn.CState{q, o, True{}, k, x, ph, pd, pt, hp, ip, pr}), L.Wait{rs, op, sd, rv, out, True{}}) == True{} : Bool}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      match e:
        case Conn.Opened{}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, False{}, sd, rv, out)
        case Conn.OpenFailed{m}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, False{}, sd, rv, out)
        case Conn.Sent{}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, False{}, rv, True{})
        case Conn.SendFailed{m}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, False{}, rv, out)
        case Conn.Got{d}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, sd, False{}, out)
        case Conn.Eof{}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, sd, False{}, out)
        case Conn.Late{}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, rs, op, sd, False{}, out)
        case Conn.Resolved{i}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, False{}, op, sd, rv, out)
        case Conn.ResolveFailed{m}:
          lv_over(rest, ka, to, mb, rd, q, o, k, x, ph, pd, pt, hp, ip, pr, False{}, op, sd, rv, out)

def inv_live(s: Conn.State, w: L.Wait, h: {inv(s, w) == True{} : Bool}) -> {L.w_live(w) == True{} : Bool}:
  match s:
    case Conn.CState{+q, +o, +v, +k, +x, +ph, +pd, +pt, +hp, +ip, +pr}:
      match v:
        case True{}:
          match w:
            case L.Wait{+rs, +op, +sd, +rv, +out, +dn}:
              %Equal.sym(Bool, dn, True{}, h) : {L.w_live(L.Wait{rs, op, sd, rv, out, _}) == True{} : Bool}
              {==}
        case False{}:
          match w:
            case L.Wait{+rs, +op, +sd, +rv, +out, +dn}:
              live_of(ph, rs, op, sd, rv, out, dn, and_l(ph_ok(ph, rs, op, sd, rv, out), met_ok(Conn.rx_met(x), ph), h))

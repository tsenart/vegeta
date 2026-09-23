# Byte-faithful IO: every byte 0..255 goes out and comes back as one Chr
# of the same code, through a loopback socket (Net.send, Net.recv on the
# server, Net.poll on the client), through a file (Files.write,
# Files.read, also past the 64 KiB first read), and out (Out.write and
# Out.write_err write Chr{0xC3} Chr{0xA9} as the two bytes of "é", where
# IO.write would encode each Chr as UTF-8). Stdin.read answers "" at EOF
# (the runner's stdin is /dev/null); Net.poll answers None when the peer
# is idle, and Net.recv "" once the peer closes.
import Base
import ../lib/sys.bend as Sys

# the Chrs i, i+1, ..., n of them
def bytes(n: Nat, +i: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      SCon{Chr{i}, bytes(p, (i + 1 : U32))}

def all_bytes() -> String:
  bytes(256n, 0)

def show_fail(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{s}:
      "done"
    case Fail{(code, msg)}:
      "fail " ++ U32.show(code) ++ " " ++ msg

def done_eq(r: Result<&1, &1, U32 & String, String>, +want: String) -> Bool:
  match r:
    case Done{s}:
      String.eq(s, want)
    case Fail{e}:
      False{}

def done_unit(r: Result<&1, &1, U32 & String, Unit>) -> Bool:
  match r:
    case Done{u}:
      True{}
    case Fail{e}:
      False{}

def none(r: Result<&1, &1, U32 & String, Maybe<&1, String>>) -> Bool:
  match r:
    case Done{None{}}:
      True{}
    case Done{Some{s}}:
      False{}
    case Fail{e}:
      False{}

# Reading until 256 bytes, the peer's close, or (poll) a quiet 1 s
# ------------------------------------------------------------------

def fill.step(done: Bool, s: Socket, acc: String,
  k: Socket -> String -> IO(Socket & String)) -> IO(Socket & String):
  match done:
    case True{}:
      IO.pure(Socket & String, (s, acc))
    case False{}:
      k(s, acc)

def fill.more(s: Socket, acc: String, +chunk: String,
  k: Socket -> String -> IO(Socket & String)) -> IO(Socket & String):
  +all = acc ++ chunk
  fill.step(String.is_empty(chunk) || Nat.is_le(256n, String.length(all)), s, all, k)

def recv.got(acc: String, k: Socket -> String -> IO(Socket & String),
  m: Socket & Result<&1, &1, U32 & String, String>) -> IO(Socket & String):
  (s, r) = m
  match r:
    case Done{+chunk}:
      fill.more(s, acc, chunk, k)
    case Fail{(code, msg)}:
      IO.die(Socket & String, code, msg)

def poll.got(acc: String, k: Socket -> String -> IO(Socket & String),
  m: Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>) ->
  IO(Socket & String):
  (s, r) = m
  match r:
    case Done{Some{+chunk}}:
      fill.more(s, acc, chunk, k)
    case Done{None{}}:
      IO.pure(Socket & String, (s, acc))
    case Fail{(code, msg)}:
      IO.die(Socket & String, code, msg)

def recv_fill(fuel: Nat, s: Socket, acc: String) -> IO(Socket & String):
  match fuel:
    case 0n:
      IO.pure(Socket & String, (s, acc))
    case 1n+p:
      IO.bind(Socket & Result<&1, &1, U32 & String, String>, Socket & String,
        Sys.Net.recv(s, 64), recv.got(acc, s2 => a2 => recv_fill(p, s2, a2)))

def poll_fill(fuel: Nat, s: Socket, acc: String) -> IO(Socket & String):
  match fuel:
    case 0n:
      IO.pure(Socket & String, (s, acc))
    case 1n+p:
      IO.bind(Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>,
        Socket & String, Sys.Net.poll(s, 64, 1000),
        poll.got(acc, s2 => a2 => poll_fill(p, s2, a2)))

# The server: echo 256 bytes back, wait for the client's "!", close
# -----------------------------------------------------------------

def server.close(n: Socket & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (s, r) = n
  Socket.close(s)

def server.wait(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (s, r) = m
  do IO<Unit>:
    n : Socket & Result<&1, &1, U32 & String, String> <- Sys.Net.recv(s, 16)
    server.close(n)

def server.echo(got: Socket & String) -> IO(Unit):
  (s, data) = got
  do IO<Unit>:
    m : Socket & Result<&1, &1, U32 & String, Unit> <- Sys.Net.send(s, data)
    server.wait(m)

def server.got(m: Listener & Result<&1, &1, U32 & String, Socket>) -> IO(Unit):
  (l, r) = m
  match r:
    case Done{s}:
      do IO<Unit>:
        Listener.close(l)
        got : Socket & String <- recv_fill(300n, s, "")
        server.echo(got)
    case Fail{(code, msg)}:
      IO.die(Unit, code, msg)

def server(l: Listener) -> IO(Unit):
  IO.bind(Listener & Result<&1, &1, U32 & String, Socket>, Unit,
    TCP.accept(l), server.got)

# The client
# ----------

def client.eof(n: Socket & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (s, r) = n
  do IO<Unit>:
    IO.print("eof " ++ Bool.show(done_eq(r, "")))
    Socket.close(s)

def client.bye(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (s, r) = m
  do IO<Unit>:
    n : Socket & Result<&1, &1, U32 & String, String> <- Sys.Net.recv(s, 16)
    client.eof(n)

def client.idle(p: Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>) -> IO(Unit):
  (s, r) = p
  do IO<Unit>:
    IO.print("poll none " ++ Bool.show(none(r)))
    m : Socket & Result<&1, &1, U32 & String, Unit> <- Sys.Net.send(s, "!")
    client.bye(m)

def client.check(got: Socket & String) -> IO(Unit):
  (s, +data) = got
  do IO<Unit>:
    IO.print("tcp " ++ Nat.show(String.length(data)) ++ " " ++ Bool.show(String.eq(data, all_bytes())))
    p : Socket & Result<&1, &1, U32 & String, Maybe<&1, String>> <- Sys.Net.poll(s, 16, 20)
    client.idle(p)

def client.sent(m: Socket & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  (s, r) = m
  do IO<Unit>:
    IO.pass(Unit, r)
    got : Socket & String <- poll_fill(300n, s, "")
    client.check(got)

def tcp(b: Listener & U32) -> IO(Unit):
  (l, +port) = b
  do IO<Unit>:
    IO.spawn(Unit, server(l))
    s : Socket <- IO.try(Socket, Sys.Net.connect("127.0.0.1", port))
    m : Socket & Result<&1, &1, U32 & String, Unit> <- Sys.Net.send(s, all_bytes())
    client.sent(m)

def listen.retry(port: U32, r: Result<&1, &1, U32 & String, Listener>,
  rest: IO(Listener & U32)) -> IO(Listener & U32):
  match r:
    case Done{l}:
      IO.pure(Listener & U32, (l, port))
    case Fail{e}:
      rest

def listen(tries: Nat, +port: U32) -> IO(Listener & U32):
  match tries:
    case 0n:
      IO.die(Listener & U32, 1, "no free tcp port")
    case 1n+t:
      rest = listen(t, (port + 1 : U32))
      do IO<Listener & U32>:
        r : Result<&1, &1, U32 & String, Listener> <- TCP.listen(port)
        listen.retry(port, r, rest)

# Files, stdin, stdout, stderr
# ----------------------------

def files() -> IO(Unit):
  +big = String.repeat(all_bytes(), 300n)
  do IO<Unit>:
    w : Result<&1, &1, U32 & String, Unit> <- Sys.Files.write("effects_bytes.tmp", all_bytes())
    IO.print("write " ++ Bool.show(done_unit(w)))
    r : Result<&1, &1, U32 & String, String> <- Sys.Files.read("effects_bytes.tmp")
    IO.print("file " ++ Bool.show(done_eq(r, all_bytes())))
    v : Result<&1, &1, U32 & String, Unit> <- Sys.Files.write("effects_bytes.tmp", big)
    IO.print("write big " ++ Bool.show(done_unit(v)))
    q : Result<&1, &1, U32 & String, String> <- Sys.Files.read("effects_bytes.tmp")
    IO.print("file big " ++ Bool.show(done_eq(q, big)))
    x : Result<&1, &1, U32 & String, String> <- Sys.Files.read("effects_bytes.missing")
    IO.print("missing " ++ show_fail(x))
    i : Result<&1, &1, U32 & String, String> <- Sys.Stdin.read(64)
    IO.print("stdin " ++ Bool.show(done_eq(i, "")))
    Sys.Out.write("out " ++ bytes(1n, 195) ++ bytes(1n, 169) ++ "\n")
    Sys.Out.write_err("err " ++ bytes(1n, 195) ++ bytes(1n, 169) ++ "\n")

def main() -> IO(Unit):
  do IO<Unit>:
    b : Listener & U32 <- listen(32n, 47700)
    tcp(b)
    files()

#|tcp 256 True
#|poll none True
#|eof True
#|write True
#|file True
#|write big True
#|file big True
#|missing fail 2 No such file or directory
#|stdin True
#|out é
#|err é

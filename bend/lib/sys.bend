# Effects the shell needs beyond Base: a ns clock, wall time with the local
# offset, precise sleep, DNS, and byte-faithful IO. Every String in or out
# of the byte effects holds one Chr per byte (0..255): bytes read become
# one Chr each, and each Chr written goes out as its low byte. Base's
# TCP.recv/send, File.read/write and IO.write decode and encode UTF-8
# instead (io_str, io_cstr), so they are not used for payloads. Native
# lane only: the .js twins fail. Offsets are seconds + 86400 (never
# negative).
import Base

# Clock
# -----

# ns since the process started (monotonic)
def Clock.mono_ns() -> IO(Nat):
  import "../effs/clock.c"
  import "../effs/clock.js"

# (unix seconds, nanoseconds, local UTC offset in seconds + 86400)
def Clock.wall() -> IO(Nat & Nat & U32):
  import "../effs/clock.c"
  import "../effs/clock.js"

# local UTC offset + 86400 at a unix second (localtime_r)
def Clock.offset_at(sec: Nat) -> IO(Nat):
  import "../effs/clock.c"
  import "../effs/clock.js"

# sleeps ns on a helper thread; the other computations keep running
def Clock.sleep_ns(ns: Nat) -> IO(Unit):
  import "../effs/clock.c"
  import "../effs/clock.js"

# Dns
# ---

# the first IPv4 address of host (an IP literal is itself); a failure
# carries getaddrinfo's code and text
def Dns.resolve(host: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# Net
# ---

# Base's TCP.connect: the IP only goes through inet_pton, and a valid one
# is ASCII, so its UTF-8 edge is byte-faithful here
def Net.connect(ip: String, port: U32) -> IO(Result<&1, &1, U32 & String, Socket>):
  TCP.connect(ip, port)

def Net.send(sock: Socket, data: String) ->
  IO(Socket & Result<&1, &1, U32 & String, Unit>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# up to max bytes; "" at EOF
def Net.recv(sock: Socket, max: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, String>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# Net.recv with a deadline of ms: None{} when nothing arrived in time
def Net.poll(sock: Socket, max: U32, ms: U32) ->
  IO(Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# Fd: sockets as plain descriptors, for the attack's event loop
# ---------------------------------------------------------------

# a TCP connection to ip:port (TCP_NODELAY), as a descriptor
def Fd.connect(ip: String, port: U32) -> IO(Result<&1, &1, U32 & String, U32>):
  import "../effs/bytes.c"
  import "../effs/fd.c"
  import "../effs/fd.js"

# all of data, or the failure
def Fd.send(fd: U32, data: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "../effs/bytes.c"
  import "../effs/fd.c"
  import "../effs/fd.js"

def Fd.close(fd: U32) -> IO(Unit):
  import "../effs/fd.c"
  import "../effs/fd.js"

# waits up to ms for any of fds to be readable, then reads up to max bytes
# from each ready one: (fd, bytes) per ready descriptor, "" at a close or
# an error; [] when ms passed with none ready
def Fd.wait(fds: List<&2, U32>, max: U32, ms: U32) -> IO(List<&2, Sigma<&2, &2, U32, _ => String>>):
  import "../effs/bytes.c"
  import "../effs/fd.c"
  import "../effs/fd.js"

# Out, Stdin, Files
# -----------------

def Out.write(data: String) -> IO(Unit):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

def Out.write_err(data: String) -> IO(Unit):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# points stdout at path (created or truncated), so Out.write streams there
def Out.to_file(path: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# up to max bytes of stdin; "" at EOF
def Stdin.read(max: U32) -> IO(Result<&1, &1, U32 & String, String>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# the whole file at path (a byte string)
def Files.read(path: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# Input in pieces, for work in parallel. A piece runs through the last LF
# in its first size bytes, or through the first LF after them. Its bytes
# come packed, for Packed.bytes to unpack (fast, and on any core): the
# count of bytes in the last word (0 for none), then the words, last
# first, four bytes each, the first byte lowest.

# the whole file at path in pieces; the bytes after the last piece come
# last (maybe none)
def Files.read_pieces(path: String, size: U32) -> IO(Result<&1, &1, U32 & String, List<&2, List<&2, U32>>>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

# at least max bytes of stdin (or all that is left) in pieces; a line not
# ended yet waits for the next call, and the last one comes at EOF (ended
# or not); [] only at EOF
def Stdin.read_pieces(max: U32, size: U32) -> IO(Result<&1, &1, U32 & String, List<&2, List<&2, U32>>>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

def Packed.byte(+w: U32, n: Nat) -> Char:
  Chr{((w >> n) .&. 255 : U32)}

def Packed.word(+w: U32, acc: String) -> String:
  SCon{Packed.byte(w, 0n), SCon{Packed.byte(w, 8n), SCon{Packed.byte(w, 16n), SCon{Packed.byte(w, 24n), acc}}}}

def Packed.last.n(n: Nat, +w: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+a:
      match a:
        case 0n:
          SCon{Packed.byte(w, 0n), SNil{}}
        case 1n+b:
          match b:
            case 0n:
              SCon{Packed.byte(w, 0n), SCon{Packed.byte(w, 8n), SNil{}}}
            case 1n+c:
              match c:
                case 0n:
                  SCon{Packed.byte(w, 0n), SCon{Packed.byte(w, 8n), SCon{Packed.byte(w, 16n), SNil{}}}}
                case 1n+d:
                  Packed.word(w, SNil{})

def Packed.last(+k: U32, +w: U32) -> String:
  Packed.last.n(U32.to_nat(k), w)

def Packed.go(ws: List<&2, U32>, acc: String) -> String:
  match ws:
    case Nil{}:
      acc
    case Con{+w, rest}:
      Packed.go(rest, Packed.word(w, acc))

# the bytes of a packed piece
def Packed.bytes(ws: List<&2, U32>) -> String:
  match ws:
    case Nil{}:
      ""
    case Con{+k, rest}:
      match rest:
        case Nil{}:
          ""
        case Con{+w, more}:
          Packed.go(more, Packed.last(k, w))

# creates or truncates path, then writes data
def Files.write(path: String, data: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

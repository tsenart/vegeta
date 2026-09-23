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

# Out, Stdin, Files
# -----------------

def Out.write(data: String) -> IO(Unit):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

def Out.write_err(data: String) -> IO(Unit):
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

# creates or truncates path, then writes data
def Files.write(path: String, data: String) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "../effs/bytes.c"
  import "../effs/bytes.js"

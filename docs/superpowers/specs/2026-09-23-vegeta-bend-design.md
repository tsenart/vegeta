# Vegeta in Bend — design

Status: approved decisions, 2026-09-23. Scope: `attack` and `report`.

## Goal

A working port of Vegeta's `attack` and `report` commands to Bend 2
(bend-lang.com, v2.0.25), living in `bend/` next to the Go reference,
interoperable with Go Vegeta through its CSV and JSON result formats, with
the pure core specified by laws in `bend/LAWS.bend` and proven in
`bend/PROOF.bend`.

## Decisions

| Topic | Decision |
|---|---|
| Transport | HTTP/1.1 over plain TCP, keep-alive. No TLS, no HTTP/2 in v1. |
| DNS | Custom effect over `getaddrinfo`, run on a helper thread (`io_work`). |
| Result formats | CSV (default) and JSON lines, byte-compatible with Go's `NewCSVEncoder`/`NewJSONEncoder`. No gob. |
| Laws | `bend/LAWS.bend` is the spec: 124 laws over the whole pure core, written before the code against stub signatures, owned by the human. IO code is exempt. |
| Location | `bend/` directory, branch `bend-port`. |
| Percentiles | Exact nearest-rank on a proven sort. Go uses a t-digest (approximate), so differential tests compare percentiles with a tolerance and all other fields exactly. |
| Law style | Bend's: laws state properties that characterize the code (sorted and a permutation; the exact value rounded to nearest even; any interleaving of events), not twin implementations. Byte formats that must match Go are stated as definitions of the text, since there the format is the spec. Every helper a law uses lives in `LAWS.bend`, so the implementer cannot redefine what a law means. |
| Fast to check | `bend LAWS.bend` ≤ 10 s, `bend PROOF.bend` ≤ 60 s, enforced by the gate. Theory `Nat`s are unary in the checker (`3.6e15 < 2^60` does not finish in 2 min), so laws never force big closed numbers: anything big is a `Big`. The checker also unfolds closed arithmetic on literals past ~10^5 (`1e6 + 86400` overflows), so neither laws nor implementation code a proof evaluates may do closed arithmetic on big literals; constants are literal limbs, and multiples are written with the symbolic factor first. |
| Strings | Bytes: one `Chr` per byte, as on the wire. Bend strings are code points and its IO encodes UTF-8, so the shell converts arguments with `Text.utf8` and uses byte-faithful effects. |
| Architecture | Sans-IO. The HTTP client (`lib/conn.bend`) and the attack scheduler (`lib/engine.bend`) are pure state machines `step(state, event) -> (state, commands)`, proven over every event interleaving. The only unproven code is the C effects and `shell.bend`, a small interpreter of commands. |
| Error set | Sorted, not first-seen. Go's first-seen order depends on result arrival order, which makes `report` nondeterministic and breaks the order-independence law. |
| Dropped slots | Counted (law `eng_quit`: sent + dropped = scheduled) and reported by `attack` on stderr when non-zero. Go drops them silently. The results format has no place for them, so `report` cannot show them. |
| Parallel report | `report` reduces results with `Met.merge` in a balanced parallel tree; the monoid laws make any tree shape correct. |

## Research findings that shape the design

- Bend 2 is dependently typed and affine; termination is checked (loops take
  `Nat` fuel, or `@unsafe` for server-style loops), no mutual recursion, no
  `if` (match on `Bool`), and a `let` may not precede a `match` on a parameter.
- Numbers: `U32`, `F32`, and `Nat` (unbounded in the theory, 48-bit at
  runtime: a `Nat` past 2^48-1 fail-stops). No 64-bit integer, no F64.
  Hence:
  - timestamps are `(sec, nsec)` pairs, never one Nat of Unix nanoseconds
    (≈1.7e18 > 2^48);
  - report aggregates (latency sums, byte totals, products for rate) use a
    `Big` natural (little-endian base-10^4 limbs) whose laws are stated
    against theory `Nat`;
  - float output (`%.2f`, JSON floats) goes through an F64 emulation built on
    `Big`, so it rounds exactly as Go does.
- Strings are cons lists of `Chr`. Fine for protocol text; bodies are kept
  only up to `-max-body`.
- Base IO: TCP connect/send/recv/poll (IP only), `IO.spawn`, `Chan`, files,
  args, env, ms clock, ms sleep. Custom effects are a `.c` + `.js` pair. The
  C side uses runtime internals with no ABI promise: pin Bend 2.0.25.
- The native link line is fixed (`-lpthread -lm`), which is why TLS is out.
- Base has almost no lemmas (no `Nat.add_comm`, nothing on `show`/`sort`),
  so the port carries its own lemma file and writes proof-facing code in
  structural recursion over its own definitions (own decimal codec, own
  merge sort), not Base's `Nat.show`/`List.sort`.
- Probe: 50 concurrent keep-alive workers in Bend drove ≈91–98k req/s on a
  local Go server; Go Vegeta drove ≈97k req/s on the same machine.
- Law syntax that checks: `for x: M.T`, preconditions as erased hypotheses
  `for -h: {P(x) == True{} : Bool}`, claims `{lhs == rhs : T}`. Types from
  an imported module need the alias prefix.

## Components (`bend/`)

| File | Responsibility |
|---|---|
| `effs/*.c`, `effs/*.js` | `Clock.mono_ns`, `Clock.wall`, `Clock.sleep_ns`, `Dns.resolve`, `Stdin.read` |
| `lib/lemma.bend` | Nat/List/String lemmas the proofs share |
| `lib/dec.bend` | Decimal show/read of `Nat`, zero padding |
| `lib/big.bend` | `Big` naturals: add, mul, divmod, compare, show |
| `lib/f64.bend` | Nearest-double of a rational, `%.Nf` formatting, shortest repr |
| `lib/dur.bend` | Go `time.Duration.String()` and Vegeta's `round` |
| `lib/civil.bend` | Unix seconds ⇄ civil date, RFC3339Nano |
| `lib/b64.bend` | Standard base64 |
| `lib/csv.bend` | RFC 4180 field quoting/splitting as Go's `encoding/csv` |
| `lib/json.bend` | JSON string escaping (Go-compatible) and a small reader |
| `lib/target.bend` | URL split and the `http` targets format |
| `lib/http.bend` | Request rendering, incremental HTTP/1.1 response parser |
| `lib/sort.bend` | Merge sort with sortedness and permutation laws |
| `lib/metrics.bend` | Metrics accumulation, percentiles, histogram |
| `lib/pacer.bend` | Constant pacer schedule, `-rate` parsing |
| `lib/conn.bend` | Pure HTTP client machine per worker: connect, write, read, reuse, timeout, retry, redirects |
| `lib/engine.bend` | Pure attack scheduler: pacing, dispatch, worker growth, drop accounting, result emission |
| `lib/text.bend` | Code points to UTF-8 bytes, for arguments |
| `lib/tab.bend` | Go's text/tabwriter |
| `lib/hdr.bend` | Headers |
| `lib/hit.bend` | Results (Go's vegeta.Result) and their CSV/JSON codecs |
| `lib/report.bend` | Text, JSON and histogram reporters |
| `shell.bend` | The only IO loop: runs `Conn`/`Engine` commands as effects and feeds back events |
| `attack.bend` | The attack command: flags, targets, DNS, then `shell` |
| `report.bend` | The report command (IO) |
| `main.bend` | CLI dispatch |
| `LAWS.bend`, `PROOF.bend` | The laws and their proofs |
| `tests/*.bend` | Unit tests; expected output in trailing `#|` lines |
| `scripts/` | Test runner, golden generators (Go), differential tests |

## Out of scope for v1

TLS/HTTPS, HTTP/2 and h2c, gob, `-lazy`, JSON target format, `-unix-socket`,
`-laddr`, `-connect-to`, `-proxy-header`, `-chunked`, Prometheus,
`report -every`, `hdrplot`, `plot`, `encode`, `dump`.

## Known deviations from Go Vegeta

- Percentiles are exact nearest-rank; Go's are t-digest estimates.
- The report's error set is sorted; Go's is first-seen.
- Dropped slots are reported by `attack` on stderr (only when non-zero); Go drops them silently.
- The latency minimum is the true minimum; Go's treats 0 as unset, so a 0 ns latency makes its minimum depend on arrival order.
- Response headers in JSON results are in sorted key order; Go's are in random map order.
- Negative durations (`-duration=-1s`) are rejected; Go accepts them. PENDING the owner's approval.
- A `-rate` with a bare multi-second unit (`50/m`) behaves as Go's, but no law can state its period (a closed number past the checker's reach); Go goldens pin it.
- Dial error strings follow Go's shape (`Get "URL": dial tcp IP:PORT:
  connect: connection refused`) but not every Go error text is reproduced.
- No `Accept-Encoding: gzip` is sent, so bodies arrive uncompressed (Go
  decompresses transparently; `bytes_in` matches either way).

The scheduled hit count matches Go: a hit due exactly at the deadline is not
sent (50/s for 2s is 100 hits), because Go checks the deadline just after
the previous hit. Seq/timestamp ordering and worker growth match Go exactly: the engine assigns
both seq and timestamp in one step (law `seq_ts_monotone`) and spawns a worker
only when every worker is busy at a due slot (law `spawn_only_when_saturated`).

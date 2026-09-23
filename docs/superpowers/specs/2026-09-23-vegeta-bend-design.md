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
| Laws | The whole pure core: codecs, parsers, number/time formatting, big-number arithmetic, pacer, metrics, histogram, sort. IO code is exempt. |
| Location | `bend/` directory, branch `bend-port`. |
| Percentiles | Exact nearest-rank on a proven sort. Go uses a t-digest (approximate), so differential tests compare percentiles with a tolerance and all other fields exactly. |

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
| `lib/result.bend` | `Result` and its CSV/JSON codecs |
| `lib/target.bend` | URL split and the `http` targets format |
| `lib/http.bend` | Request rendering, incremental HTTP/1.1 response parser |
| `lib/sort.bend` | Merge sort with sortedness and permutation laws |
| `lib/metrics.bend` | Metrics accumulation, percentiles, histogram |
| `lib/pacer.bend` | Constant pacer, `-rate` parsing |
| `lib/report.bend` | Text, JSON and histogram reporters |
| `attack.bend` | The attack engine (IO) |
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

- Percentiles are exact nearest-rank, Go's are t-digest estimates.
- `Seq` is assigned by the pacer, `Timestamp` by the worker at request start;
  Go assigns both under one lock, so under heavy concurrency a later seq may
  carry an earlier timestamp by up to one scheduling quantum.
- Worker growth past `-workers` (up to `-max-workers`) triggers when the pacer
  falls behind by more than one interval, instead of on a blocked send.
- Dial error strings follow Go's shape (`Get "URL": dial tcp IP:PORT:
  connect: connection refused`) but not every Go error text is reproduced.
- No `Accept-Encoding: gzip` is sent, so bodies arrive uncompressed (Go
  decompresses transparently; `bytes_in` matches either way).

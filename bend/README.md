# Vegeta in Bend

A port of [Vegeta](https://github.com/tsenart/vegeta)'s `attack` and
`report` commands to [Bend](https://bend-lang.com/) 2.0.25. Bend is a
dependently typed language that compiles to native code with automatic
parallelism. The port has two sides:

- **A spec.** 124 laws in `LAWS.bend` say what the pure core must do.
  Bend's checker verifies proofs against them, and 95 are proven.
- **A working tool.** The binary speaks Go Vegeta's result formats byte
  for byte. An end-to-end suite runs it next to Go Vegeta against the
  same test server, and the two agree on every case: status, bytes and
  error text.

This README is the field report: what works, what's rough, what's proven
and what isn't, and what we learned about Bend.

```sh
sh scripts/install-bend.sh                # pins Bend 2.0.25 under .build/
bend main.bend -o .build/vegeta           # a native binary, via clang

echo "GET http://localhost:8080/" | .build/vegeta attack -rate=50 -duration=5s > results.csv
.build/vegeta report results.csv
.build/vegeta report -type=json results.csv
.build/vegeta report -type='hist[0,1ms,5ms,10ms]' results.csv

# mixes with Go Vegeta either way
.build/vegeta attack ... | vegeta report
vegeta attack ... | vegeta encode -to=csv | .build/vegeta report
```

`attack` takes Go Vegeta's flags:
- `-rate`: `N`, `N/duration`, or `0` together with `-max-workers`
- `-duration`, `-targets`, `-format=http`, `-output`, `-name`
- `-workers`, `-max-workers`, `-timeout`
- `-header`, `-body`, `-keepalive`, `-max-body`, `-redirects`
- `-encoding=csv|json`

Go flags the port lacks (TLS, HTTP/2, `-lazy`, `-laddr`, …) are refused
by name.

`report` takes `-type=text|json|hist[…]`, `-buckets` and `-output`, and
reads files or stdin, in CSV or JSON.

## The idea: laws first, then code

`LAWS.bend` was written before any implementation, against stub
signatures. Its helpers are owned by the human and read-only to whoever
implements. Each law is a property the code must have, never a second
copy of the code:

```python
# decoding inverts encoding
law b64_decode:
  for +s: String
  for h: {bytes(s) == True{} : Bool}
  {B64.decode(B64.encode(s)) == Some{s} : Maybe<&2, String>}

# at a bounded rate, no hit ever goes out before its slot
law eng_never_early:
  for +c: Eng.Cfg
  for +evs: List<&2, Eng.Ev>
  for h: {bounded(c) == True{} : Bool}
  {chk_early(timeline(c, evs), c) == True{} : Bool}

# however an accumulator is built -- one by one, merged in halves on
# every core, in any tree -- its report is the report of its results
law met_build:
  for +bs: List<&2, Nat>
  for +t: Build
  {Met.close(build(bs, t)) == summary(bs, leaves(t)) : Met.Summary}
```

Where Go's bytes are the spec (a result's CSV line, the report text), the
law defines the text itself.

**Sans-IO architecture.** The attack scheduler (`lib/engine.bend`) and the
HTTP client (`lib/conn.bend`) are pure state machines,
`step(state, event) -> (state, commands)`. Their laws quantify over any
list of events, so they cover every ordering of timeouts, closes, partial
reads and retries, not just the ones a test thought of. The only
unproven code is the IO loop that runs the commands, and the C effects.

## What's proven

95 of 124 laws.

| Area | Proven | What the laws say |
|---|---|---|
| Attack scheduler | **13/13** | pacing (never early, at the exact slot), seq and time order, round-robin, worker growth only when all are busy, sent + dropped = scheduled, liveness, the attack always ends |
| Decimals, big naturals | **11/11** | show/read round trips, canonical form, exact add/mul/divmod/compare |
| Codecs | **17/17** | base64, CSV fields and rows (Go's quoting and reading), JSON strings, UTF-8, URL parsing, the targets file format |
| HTTP/1.1 | 15/16 | request bytes as Go writes them; the incremental parser for Content-Length, chunked and until-close bodies, split at any byte; 1xx, HEAD/204/304, HTTP/1.0, `Connection`, `Pragma`, max-body, garbage |
| HTTP client | 7/10 | the request sent first, nothing after a request finishes, sends only on open connections, liveness, answering as soon as a response is complete, EOF errors, the result recorded |
| Metrics, reports | 10/13 | counts, error set, totals, true min/max, nearest-rank percentiles, histogram, any merge tree gives the same report, the JSON report bytes, tabwriter |
| Flags, rates | 7/9 | defaults, `-k v`/`-k=v`/`--k` forms, refused flags, `-header`, `-rate` parsing with Go's error texts |
| Durations, calendar | 10/16 | Go's `Duration.String()`, rounding, parse domain and sign, days↔dates, RFC 3339 output, compare, add/sub |
| float64 | 2/12 | conversion and truncation |
| Result round trips | 3/7 | the CSV and JSON result bytes, format detection |

**Still open (29):**
- **Checker cost.** Most of these need the checker to compute with a
  closed number near 10^9, or with a float constant built from big
  naturals. Its naturals are unary, so these don't finish. This blocks:
  - rounding (`f64_*`) and duration parsing (`dur_parse_*`);
  - `civil_unix_nanos`, `met_floats`, `report_text`, `report_hist`;
  - decoding results back (`hit_of_*`).
- **Missing theory.** The other three client laws (failures, retries,
  redirects) need a theory relating the client's cached view of a
  response head to the laws' reading of the raw bytes.
- **Just out of reach.** `http_lenient` needs facts about 32-bit
  arithmetic, and the two remaining flags laws wait on the duration
  proofs.

**No law is known to be false.** The client laws were also checked
against the implementation over every event sequence up to length 4:
56,247 timelines, 0 failures.

`bend PROOF.bend` checks everything in about 30 s. `bend LAWS.bend` states
the laws in under 1 s.

## Laws caught real bugs, and so did the code

Two reviewers, one on ordering and one on proof, reviewed the laws
adversarially until both signed off. Implementers checked them against
Go's actual behavior. Laws that looked right were not. Some examples:
- **HTTP `Connection` handling.** On HTTP/1.1, Go deletes the *whole*
  `Connection` header when any value carries `close`. The first laws
  expected the other values to survive.
- **CSV line endings.** Go's CSV reader turns `\r\n` inside a quoted field
  into `\n`, so a result doesn't round-trip if its error text contains
  one.
- **Retries and redirects.** The client laws told a retry from a redirect
  by comparing request text, so a self-redirect looked like a retry. Now
  it's by position: a send is a redirect hop exactly when a redirect is
  due.
- **The first request.** No law pinned the text of the first request on a
  fresh connection, so a client sending the wrong bytes would have passed.
- **Flags round trips.** `-rate=infinity` means "keep the default" to
  Go's flag package. A round-trip law had assumed it meant unbounded.

## Performance

Measured on an M-series Mac against a local Go server
(`scripts/bench.sh`), with Go Vegeta built from this repo:

| | Go Vegeta | Bend |
|---|---|---|
| attack, unbounded rate, 1 worker | 15k req/s | 10k req/s |
| attack, unbounded rate, 10 workers | 56k req/s | 12k req/s |
| attack, unbounded rate, 50 workers | 86k req/s | 17k req/s |
| attack, 10,000/s with 8 workers | exact | exact |
| per-hit latency, 1 worker (p50) | ~45 µs | ~45 µs |
| report, 1M results (CSV / JSON) | 1.9 s / 1.3 s | ~4 s / ~7 s |

At the start of the performance work, `attack` did about 4k req/s and
`report` took 78 s on 1M CSV results. See below for how that changed and
where the ceiling is.

## What's good

- **Proofs over every interleaving.** The scheduler's 13 laws hold for
  any event order, and they're proven. A test suite can't say that.
- **Laws as a shared spec.** When the code and a law disagreed, it was
  clear which side to fix and why. Several times it was the law.
- **Go compatibility you can check.** Goldens come from running Go, and
  the end-to-end suite runs both binaries against the same server.
- **Parallel pure code really is parallel.** An 8-way parallel call tree
  ran 6.6× faster with 8 threads, and `report` decodes pieces of its
  input this way.
- **Native binaries and C effects are straightforward.** Clock, DNS,
  byte-faithful IO and kqueue/epoll are small C files.

## What's rough

**The checker**
- **Naturals are unary.** Any closed arithmetic past about 10^5 overflows
  or never finishes, even for `x == x`. Big constants have to stay
  symbolic or be written as limb literals, and 29 laws are open mostly
  for this reason.
- **Base has almost no lemmas.** We wrote our own arithmetic, string,
  list and sort theory. `proofs/` is about 31.6k lines against 11k in
  `lib/`.
- **Mechanical proofs had to be generated.** The engine and client proofs
  come from scripts in `scripts/gen-engine-proof/` and
  `scripts/gen-conn-proof/`.

**The language**
- Termination is checked, so loops carry fuel, with the shrinking
  argument first.
- No mutual recursion.
- A `match` may only inspect a parameter, never a computed value, and a
  `let` may not come before a `match`. The result is many small `.of`
  helper defs.
- **`pick(A, c, x, y)` evaluates both branches.** A recursive call inside
  one always runs to the end of its input. `scripts/lint-pick.py` found
  46 of these, and fixing them made hot paths 2–7× faster.
- **A miscompile.** Bend 2.0.25's native compiler gets
  `Bool.or(x, pick(Bool, <computed>, a, b))` wrong.
  `tests/compiler_canary.bend` pins the wrong output so we notice when it
  changes.

**The runtime**
- Runtime naturals are 48 bits and abort past 2^48, hence the port's
  duration bound of about 78 h.
- A `String` is a cons list of one-byte cells: about 36 ns per byte to
  walk and 11–17 ns per byte for `++`. Text is packed four bytes to a
  word wherever it crosses into C.
- **The attack's ceiling.** IO computations share one core, and while any
  pure code runs, even in a forked computation, the event loop makes no
  progress. So the attack is one event loop that waits on every
  connection with kqueue/epoll, then steps the ready connections'
  machines in a parallel call tree. It can't overlap its IO with that
  step. Getting closer to Go would need a runtime change.

`docs/IMPLEMENTING.md` has all of these rules, with the measurements.

## Deviations from Go Vegeta

- HTTP/1.1 over plain TCP only: no TLS, no HTTP/2.
- **Exact percentiles.** They're exact nearest-rank; Go's are t-digest
  estimates.
- **Sorted error set.** The error set is sorted, not in first-seen order.
- **Dropped hits** are counted and reported on stderr. Go drops them
  silently.
- **Bounds from the 48-bit runtime naturals:**
  - durations are non-negative and under 281,474 s;
  - `report` refuses results spanning 78 h or more;
  - numbers of 2^48−1 or more in results are rejected.
- **Unproven fast paths.**
  - `report` decodes lines in Go's exact shapes with `lib/rdec.bend`,
    which has no laws of its own. `tests/result_fast.bend` checks it
    field by field against the proven decoder, and any other line goes
    through the proven one.
  - The attack's event loop and C effects are unproven too.

The full list, with the reasons, is in
[`../docs/superpowers/specs/2026-09-23-vegeta-bend-design.md`](../docs/superpowers/specs/2026-09-23-vegeta-bend-design.md).

## Layout

| Path | What |
|---|---|
| `LAWS.bend` | the 124 laws and their helpers (the spec) |
| `PROOF.bend`, `proofs/*.bend` | the proofs: `def L.<law>` per law, one file per module |
| `lib/engine`, `lib/conn` | the attack scheduler and the HTTP client, as pure machines |
| `lib/http`, `lib/target`, `lib/hdr` | request rendering, the incremental response parser, URLs, the targets format |
| `lib/hit`, `lib/b64`, `lib/csv`, `lib/json`, `lib/text` | results and their codecs |
| `lib/metrics`, `lib/tab`, `lib/report` | metrics, Go's tabwriter, the text, JSON and histogram reports |
| `lib/dec`, `lib/big`, `lib/f64`, `lib/dur`, `lib/civil` | decimals, big naturals, float64 with Go's rounding, durations, calendar time |
| `lib/pacer`, `lib/flags` | `-rate` and the command lines |
| `lib/sys`, `effs/*.c` | effects: clock, DNS, byte-faithful IO, sockets over kqueue/epoll |
| `shell.bend`, `attack.bend`, `report.bend`, `main.bend` | the IO: the attack's event loop and the commands |

## Tests

- **`sh scripts/test.sh [pattern]`** is the gate:
  - the laws are stated;
  - 32 test files print their expected lines, most of them goldens
    produced by Go programs in `scripts/`;
  - the proofs check within budget.
- **`sh scripts/e2e.sh`** runs the binary against a Go test server next to
  Go Vegeta. It checks:
  - pacing;
  - each binary reading the other's results;
  - report output;
  - the client's result per endpoint: keep-alive, close, chunked, 1 MiB
    bodies, `-max-body`, redirects, stale connections, timeouts, refused
    connections, headers and bodies.
- **`sh scripts/bench.sh`** produces the numbers above.

## How it was built

The port was built in a day with Claude Code, following this process:
- **Research.** A probe checked that raw TCP from Bend could keep up with
  Go.
- **Laws, then review.** The laws came first, over stubs. Adversarial
  review rounds repaired them.
- **Implementation.** Parallel agents implemented the modules against the
  laws and Go goldens.
- **Proofs.** Other agents wrote them, and the reviewers re-checked every
  law change.
- **Performance.** Profiling with `sample` drove a final pass.

The history is on the `bend-port` branch.

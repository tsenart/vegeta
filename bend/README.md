# Vegeta in Bend

A port of Vegeta's `attack` and `report` commands to
[Bend](https://bend-lang.com/) 2.0.25. Its pure core is specified by laws,
which are properties checked by Bend's dependent type checker, and proven
against them. It interoperates with Go Vegeta through the CSV and JSON
result formats, byte for byte.

```sh
sh scripts/install-bend.sh                # pins Bend 2.0.25 under .build/
bend main.bend -o .build/vegeta           # native binary (clang)

echo "GET http://localhost:8080/" | .build/vegeta attack -rate=50 -duration=5s > results.csv
.build/vegeta report results.csv
.build/vegeta report -type=json results.csv
.build/vegeta report -type='hist[0,1ms,5ms,10ms]' results.csv

# mix with Go Vegeta either way
.build/vegeta attack ... | vegeta report
vegeta attack ... | vegeta encode -to=csv | .build/vegeta report
```

`attack` takes Go Vegeta's flags: `-rate` (`N`, `N/duration`, or `0`
with `-max-workers`), `-duration`, `-targets`, `-format=http`,
`-output`, `-name`, `-workers`, `-max-workers`, `-timeout`, `-header`,
`-body`, `-keepalive`, `-max-body`, `-redirects`, and `-encoding=csv|json`.
Go flags the port lacks (TLS, HTTP/2, `-lazy`, `-laddr`, …) are refused by
name. `report` takes `-type=text|json|hist[…]`, `-buckets` and `-output`,
and reads files or stdin, in CSV or JSON.

## Laws and proofs

- **`LAWS.bend`** is the spec: 124 laws over the whole pure core. The
  human owns it. Laws state properties rather than twin implementations:
  - the scheduler over every interleaving of events;
  - the HTTP client's obligations: answering, liveness, retries, redirects;
  - round trips of every codec;
  - exact float64 rounding;
  - metrics that don't depend on the order results arrive in.

  Where Go's output bytes are the spec (result CSV, report text), the law
  defines the text. Every helper a law uses lives in `LAWS.bend`.
- **`PROOF.bend`** proves them: one `proofs/<module>.bend` per module, one
  `def L.<law>` per law. `bend LAWS.bend` states the laws and
  `bend PROOF.bend` checks the proofs. Both are kept fast: under 10 s and
  under 60 s.
- **Unproven code** is only the IO shell. That is `shell.bend`,
  `attack.bend`, `report.bend` and `main.bend`, plus the C effects in
  `effs/`: clock, sleep, DNS and byte-faithful IO.

## Architecture

The port is sans-IO: the HTTP client (`lib/conn.bend`) and the attack
scheduler (`lib/engine.bend`) are pure state machines,
`step(state, event) -> (state, commands)`.

`shell.bend` is a small interpreter:
- one computation runs the engine;
- each worker the engine grows is its own computation, with an inbox of
  hits and a kept connection;
- naps are sleepers that post to the same channel the workers answer on.

| Module | What |
|---|---|
| `lib/dec`, `big`, `f64` | decimals, big naturals, float64 emulation with Go's rounding |
| `lib/dur`, `civil` | Go durations, calendar time and RFC 3339 |
| `lib/b64`, `csv`, `json`, `text` | the codecs, as Go's |
| `lib/target`, `hdr` | URLs and the http targets format |
| `lib/http` | request rendering and an incremental HTTP/1.1 response parser |
| `lib/hit` | results and their CSV/JSON codecs |
| `lib/conn`, `engine` | the client and the scheduler |
| `lib/metrics`, `tab`, `report` | metrics, tabwriter, the text/JSON/histogram reports |
| `lib/pacer`, `flags` | `-rate` and the command lines |
| `lib/sys` | the effects |

## Tests

- **`sh scripts/test.sh [pattern]`** is the gate:
  - LAWS states every law in time;
  - every `tests/*.bend` prints its expected `#|` lines, mostly goldens
    made by Go programs in `scripts/`;
  - PROOF checks in time.
- **`sh scripts/e2e.sh [pattern]`** runs the Bend binary against a Go test
  server (`scripts/e2e-server`) next to Go Vegeta built from this repo. It
  checks:
  - pacing;
  - that each implementation reads the other's results;
  - that `report` output matches Go's, except the percentiles;
  - that the client gives the same result as Go's (code, bytes, error text)
    endpoint by endpoint: keep-alive, close, chunked, big bodies,
    `-max-body`, redirects, stale connections, timeouts, refused
    connections, headers and bodies.
- **`sh scripts/bench.sh [seconds] [results]`** compares throughput,
  latency and report speed with Go Vegeta.

## Deviations from Go Vegeta

HTTP/1.1 over plain TCP only. Percentiles are exact nearest-rank, where
Go uses t-digest estimates. The error set is sorted, not in first-seen
order. Durations are bounded below 281474 s (about 78 h) by the runtime's
48-bit naturals.

The full list, with reasons, is in
`../docs/superpowers/specs/2026-09-23-vegeta-bend-design.md`, and
`docs/IMPLEMENTING.md` has the rules learned about Bend's runtime and
checker.

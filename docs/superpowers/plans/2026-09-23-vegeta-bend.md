# Vegeta in Bend Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement `bend/lib/` so that every law in `bend/LAWS.bend` is proven in `bend/PROOF.bend`, then wire the IO shell so `vegeta attack` and `vegeta report` work end to end and interoperate with Go Vegeta.

**Architecture:** `LAWS.bend` is the spec (124 laws over stub signatures, human-owned). `lib/` modules are pure and proven; `engine.bend` and `conn.bend` are pure state machines; `shell.bend` is the only IO loop and runs their commands. Go goldens pin byte formats; end-to-end tests pin behavior on real sockets.

**Tech Stack:** Bend 2.0.25 (pinned in `bend/.bend-version`), clang, Go (goldens and differential tests).

**Spec:** `docs/superpowers/specs/2026-09-23-vegeta-bend-design.md` and, above all, `bend/LAWS.bend`.

## Global Constraints

- `bend/LAWS.bend` is read-only for implementers. A law that cannot be proven is reported to the human, never weakened or deleted. Helpers in it are part of the statement and change only with the human's approval.
- The only edits allowed to a stub signature are ones that keep `LAWS.bend` typechecking unchanged. The stubs' types and constructor shapes are part of the spec.
- Fast to check: `bend LAWS.bend` ≤ 10 s and `bend PROOF.bend` ≤ 60 s on an Apple M-series machine (enforced by `bend/scripts/test.sh`). Theory `Nat`s are unary in the checker: closed arithmetic on literals past ~10^5 does not finish. So no law, proof, or implementation code a proof unfolds may compute with big closed numbers: write multiples symbolic-factor-first (`Nat.mul(Nat.mul(k, 60n), 1000000000n)`), big constants as `Big` limb literals, and prove lemmas symbolically (induction, rewriting).
- Runtime `Nat`s must stay below 2^48; values that can grow past that are `Big`.
- Strings in `lib/` are bytes (one `Chr` per byte, 0–255). Only the shell converts (`Text.utf8` for arguments; byte-faithful effects for IO).
- No `@unsafe` in `lib/`; `@unsafe` only in `shell.bend`.
- Bend 2.0.25's native compiler miscompiles `Bool.or(x, pick(Bool, <computed condition>, a, b))` (see `bend/tests/compiler_canary.bend`): a proof guarantees the source, not the binary. In `lib/`, give such a `pick` a def of its own, and treat compiled unit tests, Go goldens and `scripts/e2e.sh` as the last word on behavior. When the canary fails, the compiler changed: re-check and update it.
- HTTP/1.1 over plain TCP only.
- `sh bend/scripts/test.sh` passes at the end of every task (with `PROOF.bend` counted as passing once the task's laws are proven: until the last task, run `sh bend/scripts/test.sh <pattern>` for the task's tests and check the task's laws have proof defs).

## Review Focus

- A response split across `recv`s at every byte: pinned by `http_split` and `http_waits`; add `tests/http_split.bend` feeding a pipelined chunked response one byte at a time.
- Server closes an idle keep-alive connection: pinned by `conn_retry`; add e2e case `idle-close` (Task 15).
- DNS name targets (`localhost`): e2e case `dns` (Task 15).
- Reports of 0 and 1 results: `met_empty`, and golden cases `empty`, `single` (Task 13).
- Sums past 2^48: `met_totals` with `Big`; golden case `huge-sums` (Task 13).

## Law map

| Task | Module | Laws (LAWS.bend) |
|---|---|---|
| 2 | `lib/dec.bend` | `dec_*` |
| 3 | `lib/big.bend` | `big_*` |
| 4 | `lib/f64.bend` | `f64_*` |
| 5 | `lib/dur.bend`, `lib/civil.bend` | `dur_*`, `civil_*` |
| 6 | `lib/b64.bend`, `lib/csv.bend`, `lib/json.bend`, `lib/text.bend` | `b64_*`, `csv_*`, `json_*`, `text_utf8` |
| 7 | `lib/hit.bend` | `hit_*` |
| 8 | `lib/target.bend` | `url_*`, `targets_*`, `target_apply` |
| 9 | `lib/http.bend` | `http_*` |
| 10 | `lib/sort.bend`, `lib/metrics.bend` | `sort_*`, `met_*` |
| 11 | `lib/pacer.bend`, `lib/engine.bend` | `rate_*`, `eng_*` |
| 12 | `lib/conn.bend` | `conn_*` |
| 13 | `lib/tab.bend`, `lib/report.bend` | `tab_render`, `report_*` |
| 14 | `lib/flags.bend` | `flags_*` |

Every task follows the same loop, TDD-style: (1) write the unit test with Go-derived `#|` expectations and see it fail against the stub; (2) implement; (3) see the test pass; (4) write the proofs in `PROOF.bend` (lemmas as `def P.name` with equality types; each law as `def L.<law>`); (5) run the gate and check the time budget; (6) commit.

---

### Task 1: Effects and byte-faithful IO

**Files:** Create `bend/lib/sys.bend`, `bend/effs/*.{c,js}`, `bend/tests/effects*.bend`.

**Interfaces (produces):** `Clock.mono_ns() -> IO(Nat)`, `Clock.wall() -> IO(Nat & Nat & U32)` (sec, nsec, offset+86400), `Clock.offset_at(sec: Nat) -> IO(Nat)` (local offset+86400 at that instant, for report times), `Clock.sleep_ns(ns: Nat) -> IO(Unit)`, `Dns.resolve(host: String) -> IO(Result<&1, &1, U32 & String, String>)`, `Stdin.read(max: U32)`, and byte-faithful `Net.send(sock, bytes)`, `Net.recv(sock, max)`, `Net.poll(sock, max, ms)`, `Out.write(bytes)`, `Out.write_err(bytes)`, `Files.read(path) -> IO(Result<..., String>)`: every String in or out holds one `Chr` per byte.

- [ ] **Step 1: Probe how Base's `TCP.recv`, `File.read` and `IO.write` treat bytes ≥ 0x80.** Write a test that sends the bytes `c3 a9 ff` through a local socket pair and prints `String.length` of what `TCP.recv` returns, and writes `Chr{255}` with `IO.write` to a file, then `od` it. If `recv` decodes UTF-8 or `write` encodes it (strings are code points: `String.length("µs")` is 2 and printing it emits UTF-8), write the `Net.*`/`Out.*` effects below as byte-faithful copies of `bend2/effs/tcp_*.c`/`write.c`. Build the String term from bytes with the runtime's constructors for `SCon`/`Chr` (read `comp.ts` for how `io_str` builds strings; copy it without the UTF-8 step).
- [ ] **Step 2: Write the effects**

`bend/lib/sys.bend`:
```python
import Base

def Clock.mono_ns() -> IO(Nat):
  import "../effs/clock_mono_ns.c"
  import "../effs/clock_mono_ns.js"

def Clock.wall() -> IO(Nat & Nat & U32):
  import "../effs/clock_wall.c"
  import "../effs/clock_wall.js"

def Clock.sleep_ns(ns: Nat) -> IO(Unit):
  import "../effs/clock_sleep_ns.c"
  import "../effs/clock_sleep_ns.js"

def Dns.resolve(host: String) -> IO(Result<&1, &1, U32 & String, String>):
  import "../effs/dns_resolve.c"
  import "../effs/dns_resolve.js"

def Stdin.read(max: U32) -> IO(Result<&1, &1, U32 & String, String>):
  import "../effs/stdin_read.c"
  import "../effs/stdin_read.js"
```

`bend/effs/clock_mono_ns.c`:
```c
static u64 clock_mono_ns_t0;

Term clock_mono_ns_run(Env e, Term* f, IoWork* w) {
  return (Term)(io_tick() - clock_mono_ns_t0);
}

static void __attribute__((constructor)) clock_mono_ns_use(void) {
  clock_mono_ns_t0 = io_tick();
  io_eff(CID_CLOCK_MONO_NS, clock_mono_ns_run, 0);
}
```

`bend/effs/clock_wall.c`:
```c
#include <time.h>

Term clock_wall_run(Env e, Term* f, IoWork* w) {
  struct timespec ts;
  struct tm       lt;
  clock_gettime(CLOCK_REALTIME, &ts);
  time_t t = ts.tv_sec;
  localtime_r(&t, &lt);
  u32 off = (u32)(lt.tm_gmtoff + 86400);
  return io_tup(e, (Term)(u64)ts.tv_sec, io_tup(e, (Term)(u64)ts.tv_nsec, (Term)off));
}

static void __attribute__((constructor)) clock_wall_use(void) {
  io_eff(CID_CLOCK_WALL, clock_wall_run, 0);
}
```

`bend/effs/clock_sleep_ns.c`:
```c
static void clock_sleep_ns_call(IoWork* w) {
  struct timespec ts = { (time_t)(w->word / 1000000000ull), (long)(w->word % 1000000000ull) };
  while (nanosleep(&ts, &ts) != 0 && errno == EINTR) {}
}

static Term clock_sleep_ns_pack(Env e, IoWork* w) {
  return term_pak(CID_UNIT, 0);
}

Term clock_sleep_ns_run(Env e, Term* f, IoWork* w) {
  w->word = (u64)f[0];
  return io_work(w, clock_sleep_ns_call, clock_sleep_ns_pack);
}

static void __attribute__((constructor)) clock_sleep_ns_use(void) {
  io_eff(CID_CLOCK_SLEEP_NS, clock_sleep_ns_run, 0);
}
```

`bend/effs/dns_resolve.c`:
```c
#include <netdb.h>
#include <arpa/inet.h>

static void dns_resolve_call(IoWork* w) {
  struct addrinfo hints, *res = NULL;
  memset(&hints, 0, sizeof(hints));
  hints.ai_family   = AF_INET;
  hints.ai_socktype = SOCK_STREAM;
  int rc = getaddrinfo((const char*)w->data, NULL, &hints, &res);
  free(w->data);
  w->data = NULL;
  if (rc != 0) {
    w->code = (u32)rc;
    return;
  }
  char* ip = malloc(INET_ADDRSTRLEN);
  inet_ntop(AF_INET, &((struct sockaddr_in*)res->ai_addr)->sin_addr, ip, INET_ADDRSTRLEN);
  freeaddrinfo(res);
  w->data = ip;
  w->size = strlen(ip);
  w->code = 0;
}

static Term dns_resolve_pack(Env e, IoWork* w) {
  Term r = w->code
    ? io_fail(e, w->code, gai_strerror((int)w->code))
    : io_done(e, io_str(e, w->data, w->size));
  free(w->data);
  return r;
}

Term dns_resolve_run(Env e, Term* f, IoWork* w) {
  w->data = io_cstr(e, f[0], &w->size);
  return io_work(w, dns_resolve_call, dns_resolve_pack);
}

static void __attribute__((constructor)) dns_resolve_use(void) {
  io_eff(CID_DNS_RESOLVE, dns_resolve_run, 0);
}
```

`bend/effs/stdin_read.c` follows `bend2/effs/file_read.c` (`io_work` pattern) with fd 0: `call` does `read(0, w->data, w->made)` into a `malloc(max)` buffer, `pack` answers `io_done(io_str(...))` or `io_fail(e, code, NULL)`. Read `file_read.c` from the installed `bend2/effs/` first and copy its field usage exactly.

Each `.js` twin is:
```js
function clock_mono_ns() {
  return io_fail(95, "unsupported on the JS lane");
}
```
with the function named after its def (`clock_wall`, `clock_sleep_ns`, `dns_resolve`, `stdin_read`). For defs whose type is not a `Result` (`Clock.mono_ns`, `Clock.wall`, `Clock.sleep_ns`) throw instead: `throw new Error("unsupported on the JS lane")`.


- [ ] **Step 3: Tests** — `tests/effects.bend` (clock monotone, wall sane, `Dns.resolve("localhost") == 127.0.0.1`), `tests/effects_sleep.bend` (3 ms sleep takes 3–50 ms), `tests/effects_bytes.bend` (bytes `0..255` round-trip through `Net.send`/`Net.recv` on a loopback listener and through `Out.write` to a file). Run `sh bend/scripts/test.sh effects`.
- [ ] **Step 4: Commit** — `git commit -m "bend: add clock, DNS and byte-faithful IO effects"`

### Task 2: Lemmas and decimals

**Files:** Create `bend/lib/lemma.bend` (shared lemmas: `add_zero`, `add_succ`, `add_comm`, `add_assoc`, `mul_*`, `append_assoc`, `append_nil`, `length_append`, div/mod by a positive constant); implement `bend/lib/dec.bend`; test `bend/tests/dec.bend`.

- [ ] **Step 1: Test** — prints `Dec.show` of 0, 7, 10, 4294967295; `Dec.pad(9n, 42n)`, `Dec.pad(2n, 12345n)`; `Dec.read` of "007", "", "1a":
```
#|0
#|7
#|10
#|4294967295
#|000000042
#|12345
#|Some{7}
#|None
#|None
```
(Check `Maybe.show`'s rendering with a one-line program first and match it.)
- [ ] **Step 2: Implement** — `show` by structural recursion on a fuel of `n` (each step divides by 10), `read` as a left fold that fails on a non-digit, `pad` as zeros ++ show.
- [ ] **Step 3: Prove** `dec_show_canonical`, `dec_show_value`, `dec_read_accepts`, `dec_read_rejects`, `dec_pad`. The key lemma is `digits_value(s ++ [d]) == 10·digits_value(s) + d`; prove it first.
- [ ] **Step 4: Gate, commit** — `git commit -m "bend: decimals, proven"`

### Task 3: Big naturals

- [ ] Test `tests/big.bend`: `Big.show(Big.mul(Big.of(4294967295n), Big.of(4294967295n)))` → `#|18446744065119617025`; `9999 + 1` → `#|10000`; `10^12 / 7` → `#|142857142857`, remainder `#|1` (build 10^12 as `Big.mul(Big.of(1000000n), Big.of(1000000n))`); `Big.show(Big.of(0n))` → `#|0`.
- [ ] Implement schoolbook `add`/`mul` over base-10000 limbs; `div`/`mod` by long division, finding each quotient limb by binary search over 0..9999 with `cmp`; `show` = strip high zero limbs, then `Dec.show(top) ++ Dec.pad(4n, limb)`.
- [ ] Prove `big_of`, `big_add`, `big_mul`, `big_divmod`, `big_cmp`, `big_show` (the value laws against `big_val`, and each op keeping `big_ok`). Gate, commit.

### Task 4: Float64

**Goldens:** `bend/scripts/gen-f64-golden.go` (run from the repo root, writes `bend/tests/golden/f64.txt`):
`bend/scripts/gen-f64-golden.go`:
```go
// Prints "p q fixed2 json" rows: float64(p)/float64(q) as Go formats it.
package main

import (
	"encoding/json"
	"fmt"
	"strconv"
)

func main() {
	pairs := [][2]uint64{{0, 1}, {1, 3}, {2, 3}, {10, 4}, {1, 8}, {5, 1000}, {194329, 2}, {3, 7},
		{1000000, 3}, {1, 1000000000}, {123456789, 1000}, {7, 3}, {125, 1000}, {135, 1000}, {1 << 52, 3},
		{999999999999, 1000000000}, {1, 7000000}}
	for _, p := range pairs {
		f := float64(p[0]) / float64(p[1])
		j, _ := json.Marshal(f)
		fmt.Printf("%d %d %s %s\n", p[0], p[1], strconv.FormatFloat(f, 'f', 2, 64), j)
	}
}
```

- [ ] Test `tests/f64.bend` embeds the same pairs and prints `p q fixed2 json` with `F64.div(F64.of_nat(p), F64.of_nat(q))`; its `#|` lines are `golden/f64.txt`.
- [ ] Also add a helper test `tests/laws_f64.bend` (compiled; Big is real now) checking the LAWS float helpers on 0.1 = `F64{Big{[6397, 189, 8797, 3602]}, 55, True}` and its successor `F64{Big{[8199, 5094, 4398, 1801]}, 54, True}`: `is_double` both True; `rounds_to(1/10, 0.1)` True, `rounds_to(1/10, succ)` False; `json_layout(0.1, "0.1")` True, with `"1e-1"` and `"0.10"` False; `sig("0.1") == 1`; the literal `"0.10000000000000002"` rounds to succ and not to 0.1.
- [ ] Implement `of_big` (round to 53 bits, ties to even, normalize to odd mantissa), `add`/`mul`/`div` (exact rational result, then the same rounding), `trunc`, `fixed` (exact decimal expansion, ties to even), `json` (shortest digits: try 1..17 significant digits, first that `rounds_to` x, closest among those; Go's layout).
- [ ] Prove `f64_*`. Gate, commit.

### Task 5: Durations and calendar time

**Goldens:** `bend/scripts/gen-dur-golden.go` prints `ns show round parse(show)` rows:
```go
package main

import (
	"fmt"
	"time"
)

var durations = [...]time.Duration{time.Hour, time.Minute, time.Second, time.Millisecond, time.Microsecond, time.Nanosecond}

func round(d time.Duration) time.Duration {
	for i, unit := range durations {
		if d >= unit && i < len(durations)-1 {
			return d.Round(durations[i+1])
		}
	}
	return d
}

func main() {
	for _, n := range []int64{0, 1, 999, 1000, 1001, 25833, 326000, 364103, 423778, 999999, 1000000, 1519000,
		16501000, 999999999, 1000000000, 1000000001, 1500000000, 59999999999, 60000000000, 61500000000,
		3599999999999, 3600000000000, 3661500000000, 90061000000000, 281474976710655} {
		d := time.Duration(n)
		p, _ := time.ParseDuration(d.String())
		fmt.Printf("%d %s %d %d\n", n, d, round(d), p)
	}
}
```

Also `bend/scripts/gen-civil-golden.go` prints `sec nsec off rfc3339` for epoch, 2000-02-29T23:59:59.5Z, 2026-09-23T02:09:47.935870875+02:00, 2100-03-01T00:00:00Z and 2038-01-19T03:14:08.000000001-07:00 (zone `time.FixedZone("", off)`, or `time.UTC` for offset 0 so Go prints `Z`; `MarshalJSON` with the quotes stripped).
- [ ] Tests `tests/dur.bend`, `tests/civil.bend` print the same columns; `#|` lines from the goldens.
- [ ] Implement `Dur.show` (port of Go's `Duration.String` for n ≥ 0), `Dur.round`, `Dur.parse` (Go's `ParseDuration`, non-negative, fraction via `F64` exactly as the `dur_parse_frac` law states), and `lib/civil.bend` (Hinnant's `days_from_civil`/`civil_from_days`, RFC3339Nano text and parser, `unix_nanos`, `cmp`, `add_ns`, `sub_ns`).
- [ ] Prove `dur_*`, `civil_*`. Gate, commit.

### Task 6: Base64, CSV, JSON strings, text

- [ ] Tests: `b64.bend` (`""`, `"f"`→`Zg==`, `"foobar"`→`Zm9vYmFy`, decode of `Zm9vYg==`); `csv.bend` (`Csv.row(["a", "b,c", "d\"e", "", " x"])` → `a,"b,c","d""e",," x"`, confirmed with Go's `csv.Writer`); `json_str.bend` (the escaping case already checked against Go in `tests/laws_helpers2.bend`, now through `Json.str`); `text.bend` (`Text.utf8("µ")` is bytes `c2 b5`).
- [ ] Implement; prove `b64_*`, `csv_*`, `json_*`, `text_utf8`. Gate, commit.

### Task 7: Result codecs

**Goldens:** `bend/scripts/gen-result-golden.go` builds six `vegeta.Result`s (success with body and headers incl. two `Set-Cookie` values; connection refused with nil body and headers; a 500 with its status as error; an error with comma, quote and newline; seq 4294967296; timestamps in UTC and at +02:00), and writes them with `NewCSVEncoder` to `bend/tests/golden/results.csv` and `NewJSONEncoder` to `results.json`. Headers with one key only per result (Go's JSON map order is random; ours is sorted).
- [ ] Tests `result_csv.bend`, `result_json.bend`: decode each golden, re-encode, compare byte for byte (`#|True`), and print each result's `seq code`.
- [ ] Implement; prove `hit_*`. Gate, commit.

### Task 8: Targets

- [ ] Test `target.bend`: parse the targets text below, printing `METHOD URL|k=v,k=v|body` per target, then the errors for `"get http://x/"` and `"GET"`:
```
GET http://127.0.0.1:8080/a?b=c
X-A: 1
X-A: 2

# comment
POST http://localhost/x
@tests/golden/body.txt
PUT http://h:1/
```
→ `#|GET http://127.0.0.1:8080/a?b=c|X-A=1,X-A=2|`, `#|POST http://localhost/x||@tests/golden/body.txt`, `#|PUT http://h:1/||`, `#|bad method: get`, `#|bad target: GET`.
- [ ] Implement; prove `url_*`, `targets_*`, `target_apply`. Gate, commit.

### Task 9: HTTP/1.1

- [ ] Tests: `http.bend` (the request text for a target, `\r` shown as `\\r`; five responses: Content-Length, chunked, close-delimited 500, `100 Continue` then 204, max-body 2 of an 8-byte body, printing `code|status|body|body_len|keep`); `http_split.bend` (a pipelined chunked response fed one byte at a time equals feeding it whole: `#|True`).
- [ ] Implement `Parse` as a byte-at-a-time state machine (`feed(p, c <> s) = feed(step(p, c), s)`) so `http_split` is a short induction; accumulate the body in reverse and flip once.
- [ ] Prove `http_*`. Gate, commit.

### Task 10: Sort and metrics

- [ ] Tests: `sort.bend` (`[5, 3, 9, 1, 3, 0]` sorted, and the first and last of 200,000 descending numbers sorted, to catch O(n²)); `metrics.bend` (decode `golden/results.csv`, summarize with buckets `[0, 1ms, 10ms]`, print requests, success, codes, errors, p50, max, histogram; `#|` lines from `gen-result-golden.go`, which also writes `golden/results.metrics` using Go's `Metrics` for all fields but p50, computed as exact nearest rank).
- [ ] Implement merge sort with parallel halves (`a b = sort(l) sort(r)`); `Acc` as a mergeable record (counts, a code→count map as an ascending list, the error set as an ascending list, `Big` totals, min/max, the list of latencies, time extremes as `(sec, nsec)`, histogram counts); `close` per the `met_*` laws.
- [ ] Prove `sort_*`, `met_*` (`met_build` and `met_swap` follow from `merge` being a commutative monoid homomorphism of the multiset of results; prove that first). Gate, commit.

### Task 11: Pacer and engine

- [ ] Test `engine.bend`: drive `Eng.start`/`Eng.step` with a punctual scripted environment for 50/s over 200 ms with 2 workers and print the fires as `seq@t` and the final `Quit` (expect 10 fires at 20 ms steps and `Quit{10, 0}`); then a late clock (every nap answered 50 ms late) and print the `Quit` (dropped > 0, sent + dropped = 10).
- [ ] Implement `parse_rate` and the engine. State: next seq, grown workers, busy set, open nap, last fire time, stopped flag; one command batch per event.
- [ ] Prove `rate_*`, `eng_*`. `eng_exact` and `eng_ends` are the hardest; prove `eng_seq`, `eng_now`, `eng_workers` first and reuse their invariants. Gate, commit.

### Task 12: The HTTP client machine

- [ ] Test `conn.bend`: scripted events for (a) a fresh request answered in two `Got`s; (b) a reused connection that EOFs before any byte (a GET is retried; a POST fails with `Post "URL": EOF`); (c) a `Late` before headers (Go's timeout text); (d) a 302 to `/b` followed (the second `Send` is the GET to `/b`); (e) `OpenFailed{"Connection refused"}` (Go's dial text). Print each timeline's commands.
- [ ] Implement `Conn.start`/`Conn.step`/`Conn.to_hit`.
- [ ] Prove `conn_*`. Gate, commit.

### Task 13: Tables and reports

**Goldens:** `bend/scripts/gen-report-golden.go` writes `golden/report-<case>.csv` and Go's `text`/`json`/`hist` (buckets `0,1ms,10ms,100ms`) output for cases `empty`, `single`, `mixed` (100 results, codes 200/500/0, 3 errors, latencies 1..100 ms), `huge-sums` (3 results, 200 h latency and 2^47 bytes each), `two-zones`; plus exact nearest-rank percentiles for `mixed` in `report-mixed.pct`.
- [ ] Tests `report_text.bend`, `report_json.bend`, `report_hist.bend` compare ours to Go's with the percentile fields masked (and the error set compared as a sorted set), and print our exact percentiles for `mixed` against `report-mixed.pct`.
- [ ] Implement `Tab.render` and the reporters; prove `tab_render`, `report_*`. Gate, commit.

### Task 14: Flags

- [ ] Test `flags.bend`: defaults; `["-rate=100/1s", "-duration", "2s", "-header", "A: 1", "-header", "B: 2", "-keepalive=false", "-encoding", "json"]`; `["-http2"]` → the refusal text; report flags for `-type=hist[1ms,10ms]` (buckets `[0, 1ms, 10ms]`).
- [ ] Implement; prove `flags_*`. Gate, commit.

### Task 15: The shell, attack and report

**Files:** `bend/shell.bend` (the only `@unsafe` code), `bend/attack.bend`, `bend/report.bend`, `bend/main.bend`, `bend/scripts/e2e.sh`, `bend/scripts/e2e-server.go`.

- **Attack:** parse flags (arguments through `Text.utf8`); read and parse targets; read bodies; resolve each distinct host once; take `Clock.wall` and `Clock.mono_ns` at start. Run `Eng`: `Nap` → `Clock.sleep_ns` then feed `Clock{now}`; `Grow` → spawn a worker computation with its own `Conn` loop and connection; `Fire` → send the job over the worker's channel; a worker's `Finish` → `Conn.to_hit`, the result to the writer channel, and `Freed` back to the engine; `Quit{sent, dropped}` → close channels, wait for the writer, and print `vegeta: dropped N of M scheduled hits` to stderr only when N > 0. The writer encodes with `Hit.to_csv`/`Hit.to_json` and writes bytes with `Out.write`.
- **Report:** decode each input (stdin or files) incrementally into accumulators, merge them in a balanced parallel tree (`met_build` makes any shape correct), close, resolve the three zone offsets with `Clock.offset_at`, and render.
- [ ] **Step 2: E2E server** — `bend/scripts/e2e-server.go` listens on `127.0.0.1:$PORT` with handlers:
  - `/ok` → 200 `ok\n`
  - `/big` → 200 with 1 MiB of `x` and `Content-Length`
  - `/chunked` → 200 streamed in 3 flushes (chunked)
  - `/500` → 500 `boom`
  - `/slow` → sleeps 2 s
  - `/redirect` → 302 to `/ok`
  - `/close` → 200 with `Connection: close`

  It uses a custom `http.Server` with `IdleTimeout: 50ms` (for the idle-close case) and counts requests per path, printing the counts on SIGTERM.

- [ ] **Step 3: E2E script** — `bend/scripts/e2e.sh` builds `bend/.build/vegeta`, `go build`s the Go vegeta to `bend/.build/vegeta-go`, starts the server, and runs each case, checking with `bend/.build/vegeta-go report -type=json` (Go decodes our CSV/JSON output; this is the interop check) plus `jq`:

| case | command | assertion |
|---|---|---|
| `rate` | `echo "GET http://127.0.0.1:$P/ok" \| vegeta attack -rate=200/1s -duration=2s` | requests within 400±4, success 1 |
| `max` | `-rate=0 -workers=20 -duration=1s` | requests > 1000, success 1 |
| `codes` | targets `/ok` and `/500`, `-rate=100/1s -duration=1s` | `status_codes` has `200` and `500`, errors = `["500 Internal Server Error"]` |
| `timeout` | `/slow`, `-timeout=100ms -rate=10/1s -duration=500ms` | all errors contain `Client.Timeout exceeded` |
| `redirect` | `/redirect` | codes `{"200": n}` |
| `chunked` / `big` | each | `bytes_in.mean` 30 / 1048576 |
| `max-body` | `/big -max-body=10`, `-encoding json` | every result's `body` decodes to 10 bytes, `bytes_in` 1048576 |
| `idle-close` | `/ok -rate=5/1s -duration=2s` (200 ms gaps > 50 ms idle timeout) | success 1, no errors |
| `dns` | `http://localhost:$P/ok` | success 1 |
| `refused` | `http://127.0.0.1:1/` | code 0, error starts with `Get "http://127.0.0.1:1/": dial tcp` and ends with `connect: connection refused` |
| `json-out` | `-encoding json` | Go report decodes it; requests matches |
| `headers` | `-header "X-T: 1"`, server echoes `X-T` and `X-Vegeta-Seq` into the body | bodies contain `X-T=1` and seqs 0..n−1, each once |

Run: `sh bend/scripts/e2e.sh` — first run fails (no `attack.bend`).

- [ ] Implement; run `sh bend/scripts/test.sh && sh bend/scripts/e2e.sh`. Commit.

### Task 16: Benchmarks, docs, final gate

- [ ] `bend/scripts/bench.sh`: `-rate=0 -workers=50 -duration=5s` against `/ok` for Go and Bend; `report` over 1,000,000 results for both (Bend with `--threads 1` and all threads, to show the parallel merge).
- [ ] `bend/README.md`: install, build, usage, supported flags, the spec's out-of-scope list and deviations, how `LAWS.bend`/`PROOF.bend` are organized, the fast-to-check rule, the bench table.
- [ ] Final gate: `sh bend/scripts/test.sh` (all laws proven within budget), `sh bend/scripts/e2e.sh`, `grep -l '@unsafe' bend/lib/*.bend` prints nothing. Commit.

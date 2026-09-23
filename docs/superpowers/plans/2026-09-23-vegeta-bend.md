# Vegeta in Bend Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port Vegeta's `attack` and `report` commands to Bend 2 in `bend/`, interoperable with Go Vegeta via CSV/JSON results, with the pure core specified by laws and proven.

**Architecture:** A pure core (codecs, parsers, number/time formatting, big-number arithmetic, pacer, metrics, sort), each module with laws in `bend/LAWS.bend` proven in `bend/PROOF.bend`; a thin IO shell (`attack.bend`, `report.bend`, `main.bend`) over Base TCP/channels plus five custom C effects. Attack = one pacer computation feeding ticks over a `Chan` to N worker computations, each owning one keep-alive connection, feeding results to one writer computation.

**Tech Stack:** Bend 2.0.25 (pinned), clang (Homebrew LLVM), Go 1.2x for golden generation and differential tests.

**Spec:** `docs/superpowers/specs/2026-09-23-vegeta-bend-design.md`

## Global Constraints

- Bend version: exactly 2.0.25. The C effects use runtime internals with no ABI promise.
- Native lane only for tests and the binary (`bend X.bend -o X`); JS effect twins exist but only fail with `"unsupported on the JS lane"`.
- Every loop is fuel-bounded or `@unsafe`; `@unsafe` only in IO loops (`attack.bend`, `report.bend`), never in `lib/`.
- No runtime `Nat` may exceed 2^48-1: timestamps are `(sec, nsec)`; sums/products in reports use `Big`.
- Laws live in `bend/LAWS.bend` (human-owned: add, never weaken); proofs in `bend/PROOF.bend`. `bend PROOF.bend` must print `All terms check` at the end of every task that touches `lib/`.
- A law's precondition is an erased hypothesis `for -h: {P == True{} : Bool}`, never `where` (it binds a pair).
- Types from an imported module carry the alias: `for t: T.Target`.
- Result wire formats are byte-identical to Go's `NewCSVEncoder`/`NewJSONEncoder` output for the same `Result`.
- HTTP/1.1, plain TCP only. `https://` targets fail with error `"https is not supported"`.
- Output of `report -type=text` is byte-identical to Go's for the same metrics, except percentile values.

## Review Focus

- Response split across many `recv`s at every byte boundary (headers split mid-`\r\n\r\n`, chunked sizes split): the parsed response must equal the one-piece parse. Pinned by the `http_feed_split` law (Task 11) and `tests/http_split.bend`.
- Server closes a keep-alive connection between requests (idle timeout): the worker must reconnect and the next request succeed, not record an error. Pinned by `scripts/e2e.sh` case `idle-close` (Task 15).
- Target host is a DNS name (`localhost`), not an IP: attack must resolve and succeed. Pinned by `scripts/e2e.sh` case `dns` (Task 15).
- A results file with 0 results, or 1 result: report must print Go's output (zeros, `0s` durations, `NaN`-free). Pinned by golden cases `empty` and `single` (Task 16).
- Latencies/bytes sums past 2^48 (e.g. 10^6 results × 10^9 ns): report must not fail-stop. Pinned by golden case `huge-sums` (Task 16).

---

### Task 1: Scaffold, toolchain pin, test runner, lemma file

**Files:**
- Create: `bend/README.md`, `bend/.bend-version`, `bend/scripts/install-bend.sh`, `bend/scripts/test.sh`, `bend/lib/lemma.bend`, `bend/LAWS.bend`, `bend/PROOF.bend`, `bend/tests/smoke.bend`
- Modify: `Makefile` (add `bend-test` target), `.gitignore` (add `bend/.build/`)

**Interfaces:**
- Produces: `bend/scripts/test.sh [pattern]` — compiles every `bend/tests/*<pattern>*.bend` to `bend/.build/<name>`, runs it from `bend/`, compares stdout with the file's `#|` lines (each `#|X` expects line `X`), then runs `bend PROOF.bend` and requires `All terms check`. Exit 0 only if everything passes.
- Produces: lemmas in `lib/lemma.bend` (Lm alias), proven in place (they are ordinary defs with equality return types, not laws): `Lm.add_zero(n)`, `Lm.add_succ(a, b)`, `Lm.add_comm(a, b)`, `Lm.add_assoc(a, b, c)`, `Lm.append_nil(s)`, `Lm.append_assoc(a, b, c)` (for `String` via `++`).

- [ ] **Step 1: Pin and install Bend**

`bend/.bend-version`:
```
2.0.25
```

`bend/scripts/install-bend.sh`:
```sh
#!/bin/sh
# Installs the pinned Bend into bend/.build/bendhome (no ~ writes, no telemetry).
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
want=$(cat "$here/.bend-version")
home="$here/.build/bendhome"
if [ -x "$home/bin/bend" ] && [ "$(cat "$home/.ver" 2>/dev/null)" = "$want" ]; then exit 0; fi
mkdir -p "$home"
curl -fsSL https://bend-lang.com/install.sh | sed "s/^VER=.*/VER=\"$want\"/" > "$here/.build/install.sh"
grep -q "VER=\"$want\"" "$here/.build/install.sh"
BEND_HOME="$home" BEND_NO_TELEMETRY=1 sh "$here/.build/install.sh" >/dev/null
echo "$want" > "$home/.ver"
```
Note: the upstream script embeds per-version sha256 values; if the served script is newer than 2.0.25 its hashes will not match the 2.0.25 archive and the install fails loudly. In that case fetch the script from the `v2.0.25` tag of `bendlang/bend-lang.com` instead. Do not remove the checksum check.

Run: `sh bend/scripts/install-bend.sh && bend/.build/bendhome/bin/bend --help | head -1`
Expected: a usage line, exit 0.

- [ ] **Step 2: Write the test runner**

`bend/scripts/test.sh`:
```sh
#!/bin/sh
# Compiles and runs bend/tests/*.bend, comparing stdout to the `#|` lines,
# then runs the proof gate.
set -eu
here=$(cd "$(dirname "$0")/.." && pwd)
sh "$here/scripts/install-bend.sh"
export PATH="$here/.build/bendhome/bin:$PATH" BEND_NO_TELEMETRY=1
cd "$here"
mkdir -p .build/tests
pat=${1:-}
fail=0; n=0
for t in tests/*"$pat"*.bend; do
  name=$(basename "$t" .bend); n=$((n+1))
  grep '^#|' "$t" | sed 's/^#|//' > ".build/tests/$name.want"
  if ! bend "$t" -o ".build/tests/$name" > ".build/tests/$name.cc" 2>&1; then
    echo "FAIL $name (compile)"; sed 's/^/  /' ".build/tests/$name.cc"; fail=$((fail+1)); continue
  fi
  ".build/tests/$name" > ".build/tests/$name.got" 2>&1 || true
  if diff -u ".build/tests/$name.want" ".build/tests/$name.got" > ".build/tests/$name.diff"; then
    echo "ok   $name"
  else
    echo "FAIL $name"; sed 's/^/  /' ".build/tests/$name.diff"; fail=$((fail+1))
  fi
done
if [ -z "$pat" ]; then
  if bend PROOF.bend 2>&1 | tee .build/proof.out | grep -q 'All terms check'; then
    echo "ok   PROOF.bend"
  else
    echo "FAIL PROOF.bend"; sed 's/^/  /' .build/proof.out; fail=$((fail+1))
  fi
fi
echo "$((n-fail))/$n tests passed"
[ "$fail" -eq 0 ]
```

- [ ] **Step 3: Write the smoke test (failing: no lemma file yet)**

`bend/tests/smoke.bend`:
```python
import Base
import ../lib/lemma.bend as Lm

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Nat.show(Nat.add(40n, 2n)))

#|42
```
Run: `sh bend/scripts/test.sh smoke`
Expected: `FAIL smoke (compile)` mentioning the missing `lib/lemma.bend`.

- [ ] **Step 4: Write `lib/lemma.bend`, `LAWS.bend`, `PROOF.bend`**

`bend/lib/lemma.bend` holds proven helper equalities used by later proofs. Write them in the style of the Guide's `add_zero` (match, `{==}`, `%ih : P`):
```python
import Base

# 0 is a right unit of addition
def Lm.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Lm.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
```
Add `Lm.add_succ : {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}`, `Lm.add_comm`, `Lm.add_assoc`, `Lm.append_nil : {s ++ "" == s : String}`, `Lm.append_assoc : {(a ++ b) ++ c == a ++ (b ++ c) : String}` the same way (induction on the first argument; `add_comm` uses `add_zero` and `add_succ` through `Equal.trans`). Check the exact reduction of `Nat.add` and `String.append` in `bend base Nat.add` / `bend base String.append` before writing each step: a proof step must match how the def actually reduces.

`bend/LAWS.bend` (grows every task):
```python
# Vegeta in Bend -- the laws. Humans state them; PROOF.bend proves them.
# A law is never weakened to make a proof go through: fix the code.
import Base
import ./lib/lemma.bend as Lm
```

`bend/PROOF.bend`:
```python
import Base
import ./LAWS.bend as L
```

- [ ] **Step 5: Run the tests**

Run: `sh bend/scripts/test.sh`
Expected: `ok   smoke`, `ok   PROOF.bend`, `1/1 tests passed`.

- [ ] **Step 6: Wire into Make, ignore build dir, README stub, commit**

Append to `Makefile`:
```make
bend-test:
	sh bend/scripts/test.sh
```
Append `bend/.build/` to `.gitignore`. `bend/README.md`: one paragraph ("Vegeta's attack and report in Bend; see docs/superpowers/specs/2026-09-23-vegeta-bend-design.md; run `make bend-test`").

```bash
git add bend Makefile .gitignore
git commit -m "bend: scaffold port, pin Bend 2.0.25, add test runner and lemmas"
```

---

### Task 2: Custom effects (mono clock, wall clock, ns sleep, DNS, stdin)

**Files:**
- Create: `bend/lib/sys.bend`, `bend/effs/clock_mono_ns.{c,js}`, `bend/effs/clock_wall.{c,js}`, `bend/effs/clock_sleep_ns.{c,js}`, `bend/effs/dns_resolve.{c,js}`, `bend/effs/stdin_read.{c,js}`
- Test: `bend/tests/effects.bend`, `bend/tests/effects_sleep.bend`

**Interfaces:**
- Produces (`lib/sys.bend`, alias `Sys`):
  - `Clock.mono_ns() -> IO(Nat)` — ns since process start (fits 48 bits for 78 h).
  - `Clock.wall() -> IO(Nat & Nat & U32)` — `(unix_sec, nsec, tz_off_plus_86400)`: local UTC offset in seconds plus 86400 (always ≥ 0).
  - `Clock.sleep_ns(ns: Nat) -> IO(Unit)` — sleeps on a helper thread.
  - `Dns.resolve(host: String) -> IO(Result<&1, &1, U32 & String, String>)` — first IPv4 as dotted quad; an IP literal resolves to itself.
  - `Stdin.read(max: U32) -> IO(Result<&1, &1, U32 & String, String>)` — up to `max` bytes; `""` at EOF.

- [ ] **Step 1: Write the failing test**

`bend/tests/effects.bend`:
```python
import Base
import ../lib/sys.bend as Sys

def ip(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{s}:
      s
    case Fail{(c, m)}:
      "fail: " ++ m

def main() -> IO(Unit):
  do IO<Unit>:
    a : Nat <- Clock.mono_ns()
    b : Nat <- Clock.mono_ns()
    IO.print(Bool.show(Nat.is_le(a, b)))
    w : Nat & Nat & U32 <- Clock.wall()
    (s, rest) = w
    (ns, off) = rest
    IO.print(Bool.show(Nat.is_gt(s, 1700000000n)))
    IO.print(Bool.show(Nat.is_lt(ns, 1000000000n)))
    r1 : Result<&1, &1, U32 & String, String> <- Dns.resolve("127.0.0.1")
    IO.print(ip(r1))
    r2 : Result<&1, &1, U32 & String, String> <- Dns.resolve("localhost")
    IO.print(ip(r2))

#|True
#|True
#|True
#|127.0.0.1
#|127.0.0.1
```
(If `(s, rest) = w` is rejected inside a `do` block, move the destructuring into a helper def taking `w`, as `demos/io_http_fetch` does.)

`bend/tests/effects_sleep.bend` sleeps 3 ms with `Clock.sleep_ns(3000000n)` between two `Clock.mono_ns()` reads and prints `Bool.show(elapsed >= 3000000n && elapsed < 50000000n)`; expects `#|True`.

Run: `sh bend/scripts/test.sh effects`
Expected: both FAIL (compile: `lib/sys.bend` missing).

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

- [ ] **Step 3: Run tests**

Run: `sh bend/scripts/test.sh effects`
Expected: `ok   effects`, `ok   effects_sleep`. If `io_work`'s helper-thread `call` may not touch `errno`/`memset` due to missing headers, add the `#include` at the top of that `.c` (the file is spliced after the runtime).

- [ ] **Step 4: Check stdin**

Add `bend/tests/effects_stdin.bend`: reads `Stdin.read(64)` twice and prints each result's length. The runner runs binaries with stdin from `/dev/null`, so expect `#|0` twice. Manually: `printf abc | bend/.build/tests/effects_stdin` prints `3` then `0`.

- [ ] **Step 5: Commit**

```bash
git add bend/lib/sys.bend bend/effs bend/tests/effects*.bend
git commit -m "bend: add clock, sleep, DNS and stdin effects"
```

---

### Task 3: Decimal codec (`lib/dec.bend`)

**Files:**
- Create: `bend/lib/dec.bend`, `bend/tests/dec.bend`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Dec`): `Dec.show(n: Nat) -> String` (no leading zeros; `"0"` for 0), `Dec.read(s: String) -> Maybe<&2, Nat>` (one or more ASCII digits, leading zeros allowed, nothing else), `Dec.pad(w: Nat, n: Nat) -> String` (left-padded with `0` to width `w`; wider numbers are not truncated), `Dec.digits(n: Nat) -> Nat` (count, ≥ 1).

Write `Dec.show` by structural recursion on a fuel equal to `n` (each step divides by 10, so `n` steps always suffice), not by Base's `Nat.show`; the laws are proven against these definitions.

- [ ] **Step 1: State the laws**

Append to `bend/LAWS.bend`:
```python
import ./lib/dec.bend as Dec

# LAW: reading what show wrote gives the number back
law dec_roundtrip:
  for +n: Nat
  {Dec.read(Dec.show(n)) == Some{n} : Maybe<&2, Nat>}

# LAW: show writes exactly digits(n) characters
law dec_show_len:
  for +n: Nat
  {String.length(Dec.show(n)) == Dec.digits(n) : Nat}

# LAW: a padded number reads back, whatever the width
law dec_pad_read:
  for +w: Nat
  for +n: Nat
  {Dec.read(Dec.pad(w, n)) == Some{n} : Maybe<&2, Nat>}

# LAW: padding to a width that fits yields exactly that width
law dec_pad_len:
  for +w: Nat
  for +n: Nat
  for -h: {Nat.is_le(Dec.digits(n), w) == True{} : Bool}
  {String.length(Dec.pad(w, n)) == w : Nat}

# LAW: seconds and a 9-digit nanosecond field print as the nanosecond total
law dec_sec_nsec:
  for +s: Nat
  for +ns: Nat
  for -h0: {Nat.is_gt(s, 0n) == True{} : Bool}
  for -h1: {Nat.is_lt(ns, 1000000000n) == True{} : Bool}
  {Dec.show(s) ++ Dec.pad(9n, ns) == Dec.show(Nat.add(Nat.mul(s, 1000000000n), ns)) : String}
```
Run: `bend/.build/bendhome/bin/bend bend/LAWS.bend`
Expected: fails to resolve `Dec.*` (module missing).

- [ ] **Step 2: Write the failing unit test**

`bend/tests/dec.bend` prints `Dec.show` of `0n`, `7n`, `10n`, `4294967295n`, `Dec.pad(9n, 42n)`, `Dec.pad(2n, 12345n)`, `Maybe.show` of `Dec.read("007")`, `Dec.read("")`, `Dec.read("1a")`:
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
(Check the exact `Maybe.show` rendering with a one-line program first and adjust the three expectations to it.)

- [ ] **Step 3: Implement `lib/dec.bend`, then prove each law in `PROOF.bend`**

Proof shape: `dec_roundtrip` by strong induction via fuel on `n`, needing `Dec.read(a ++ [d]) == 10·read(a) + d`. State that helper as a def in `PROOF.bend` (e.g. `def P.read_snoc(...)`) and prove it first. `dec_sec_nsec` follows from the snoc lemma iterated 9 times over the padded digits. Write each proof as a def named `L.<law>` (the LAWS alias), in `PROOF.bend`.

- [ ] **Step 4: Run**

Run: `sh bend/scripts/test.sh`
Expected: all ok including `PROOF.bend`.

- [ ] **Step 5: Commit** — `git commit -m "bend: add decimal codec with roundtrip laws"`

---

### Task 4: Big naturals (`lib/big.bend`)

**Files:**
- Create: `bend/lib/big.bend`, `bend/tests/big.bend`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Big`): `type Big is Data: Big{limbs: List<&2, Nat>}` little-endian base-10000 limbs (each < 10000, possibly with high zero limbs); `Big.val(+b) -> Nat` (the theory value: Σ limb_i·10000^i); `Big.of(n: Nat) -> Big`; `Big.add(+a, +b) -> Big`; `Big.mul(+a, +b) -> Big`; `Big.cmp(+a, +b) -> Cmp`; `Big.div(+a, +b) -> Big`; `Big.mod(+a, +b) -> Big`; `Big.show(+b) -> String`; `Big.to_nat(+b) -> Nat` (only valid below 2^48; used for final small values).
- Runtime rule: every intermediate `Nat` stays < 2^48: limb products are < 10^8, and carries stay small.

- [ ] **Step 1: State the laws** (append to `LAWS.bend`; import `./lib/big.bend as Big`)
```python
law big_of:
  for +n: Nat
  {Big.val(Big.of(n)) == n : Nat}

law big_add:
  for +a: Big.Big
  for +b: Big.Big
  {Big.val(Big.add(a, b)) == Nat.add(Big.val(a), Big.val(b)) : Nat}

law big_mul:
  for +a: Big.Big
  for +b: Big.Big
  {Big.val(Big.mul(a, b)) == Nat.mul(Big.val(a), Big.val(b)) : Nat}

law big_cmp:
  for +a: Big.Big
  for +b: Big.Big
  {Big.cmp(a, b) == Nat.cmp(Big.val(a), Big.val(b)) : Cmp}

# LAW: division is Euclidean for a non-zero divisor
law big_divmod:
  for +a: Big.Big
  for +b: Big.Big
  for -h: {Nat.is_gt(Big.val(b), 0n) == True{} : Bool}
  {Nat.add(Nat.mul(Big.val(Big.div(a, b)), Big.val(b)), Big.val(Big.mod(a, b))) == Big.val(a) : Nat}

law big_mod_lt:
  for +a: Big.Big
  for +b: Big.Big
  for -h: {Nat.is_gt(Big.val(b), 0n) == True{} : Bool}
  {Nat.is_lt(Big.val(Big.mod(a, b)), Big.val(b)) == True{} : Bool}

law big_show:
  for +b: Big.Big
  {Big.show(b) == Dec.show(Big.val(b)) : String}
```
The laws hold for limbs ≥ 10000 too only if the code never relies on the limb bound. If a proof needs the bound, add `Big.ok(b)` (all limbs < 10000) as a hypothesis on that law, plus a law `big_ok_closed` that `add`, `mul`, `div`, `mod`, `of` all produce `ok` values.

- [ ] **Step 2: Failing test** `bend/tests/big.bend`: prints `Big.show` of `Big.mul(Big.of(4294967295n), Big.of(4294967295n))` → `#|18446744065119617025`; `Big.show(Big.add(Big.of(9999n), Big.of(1n)))` → `#|10000`; `Big.show(Big.div(Big.of(1000000000000n), Big.of(7n)))` → `#|142857142857`; `Big.show(Big.mod(...same...))` → `#|1`; `Big.show(Big.of(0n))` → `#|0`.

- [ ] **Step 3: Implement** — schoolbook add/mul over limbs; long division by `Big` divisor with the quotient limb found by binary search on 0..9999 using `Big.cmp(Big.mul_small(b, q), rem)`; `Big.show` = strip high zero limbs, `Dec.show(top) ++ Dec.pad(4n, limb)` for the rest.

- [ ] **Step 4: Prove the laws, run `sh bend/scripts/test.sh`** — all ok.

- [ ] **Step 5: Commit** — `git commit -m "bend: add Big naturals with arithmetic laws"`

---

### Task 5: F64 emulation (`lib/f64.bend`)

Go computes `Rate`, `Throughput`, `Success`, `BytesIn.Mean`, `BytesOut.Mean` as float64 divisions and prints them with `%.2f` (text) or shortest-roundtrip (JSON). To match byte for byte, compute the float64 Go would compute, exactly, then format it exactly.

**Files:**
- Create: `bend/lib/f64.bend`, `bend/tests/f64.bend`, `bend/scripts/gen-f64-golden.go`, `bend/tests/golden/f64.txt`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `F64`): `type F64 is Data: F64{m: Big.Big, e: Nat, neg_e: Bool}` = m·2^(±e), non-negative, finite; `F64.of_nat(n) -> F64` (exact below 2^53, rounded otherwise); `F64.div(+a: F64, +b: F64) -> F64` (IEEE round-half-even of the exact quotient to 53 bits; `b` non-zero); `F64.mul(+a, +b) -> F64` (same rounding); `F64.fixed(d: Nat, +x: F64) -> String` (= Go `strconv.FormatFloat(x, 'f', d, 64)`); `F64.json(+x: F64) -> String` (= Go `encoding/json` float64 output: shortest roundtrip, `'f'` format unless exponent < -6 or ≥ 21, then `'e'` with `e-07` → `e-7` cleanup); `F64.read(s: String) -> Maybe<&2, F64>` (nearest double to a decimal literal); `F64.val_num`, `F64.val_den` (`Big`s with `val(x) = num/den` exactly); `F64.zero`.
- Special case: Go's `m.Rate` etc. are `0` when `Requests == 0`; the reporter handles that, not `F64`.

- [ ] **Step 1: Golden generator**

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
Run: `go run bend/scripts/gen-f64-golden.go > bend/tests/golden/f64.txt`

- [ ] **Step 2: Laws** (append; import `./lib/f64.bend as F64`)
```python
# LAW: a double built from a small natural is that natural exactly
law f64_of_nat_exact:
  for +n: Nat
  for -h: {Nat.is_lt(n, Nat.pow(2n, 53n)) == True{} : Bool}
  {Nat.mul(n, Big.val(F64.val_den(F64.of_nat(n)))) == Big.val(F64.val_num(F64.of_nat(n))) : Nat}

# LAW: the JSON text of a double reads back as the same double
law f64_json_roundtrip:
  for +x: F64.F64
  {F64.read(F64.json(x)) == Some{x} : Maybe<&2, F64.F64>}

# LAW: fixed notation of a whole number is its digits, a dot and d zeros
law f64_fixed_int:
  for +n: Nat
  for +d: Nat
  for -h: {Nat.is_lt(n, Nat.pow(2n, 53n)) == True{} : Bool}
  {F64.fixed(1n+d, F64.of_nat(n)) == Dec.show(n) ++ "." ++ String.repeat("0", 1n+d) : String}
```
(`F64` values must be normalized, with m odd or zero and e canonical, so that `Some{x}` equality is structural. Make `F64.read`/`div`/`mul` always normalize, and add law `f64_norm` if the proofs need it. Check `String.repeat`'s argument order with `bend base String.repeat`.)

- [ ] **Step 3: Failing test** — `bend/tests/f64.bend` embeds the same `(p, q)` pairs as the Go generator, printing `p q fixed2 json` per row with `F64.div(F64.of_nat(p), F64.of_nat(q))`. Its `#|` lines are exactly `bend/tests/golden/f64.txt` prefixed by `#|` (`sed 's/^/#|/' bend/tests/golden/f64.txt >> bend/tests/f64.bend`).

- [ ] **Step 4: Implement**
  - `div`: exact quotient `num/den` as `Big`s; scale by 2^k until the quotient has 54 significant bits; round half to even on the remainder; normalize.
  - `fixed(d)`: exact decimal expansion of m·2^(−e) (multiply the numerator by 10^d, divide by 2^e, round half to even on the exact remainder). This is what `strconv` does for `'f'` with a precision.
  - `json`: shortest digits: generate the digit string of increasing length n = 1..17 from the exact value (correctly rounded), and stop at the first that `F64.read` maps back to `x`. Then lay it out in `'f'`, or in `'e'` when the decimal exponent < -6 or ≥ 21, as Go does.

- [ ] **Step 5: Prove, run all tests, commit** — `git commit -m "bend: add exact float64 emulation for Go-compatible float output"`

---

### Task 6: Go durations (`lib/dur.bend`)

**Files:**
- Create: `bend/lib/dur.bend`, `bend/tests/dur.bend`, `bend/scripts/gen-dur-golden.go`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Dur`): `Dur.show(ns: Nat) -> String` (= Go `time.Duration(ns).String()` for ns ≥ 0), `Dur.round(ns: Nat) -> Nat` (= Vegeta `round` in `lib/reporters.go`: ≥1h→round to 1m, ≥1m→1s, ≥1s→1ms, ≥1ms→1µs, else unchanged; half away from zero), `Dur.parse(s: String) -> Maybe<&2, Nat>` (Go `time.ParseDuration` for non-negative inputs: units `ns us µs ms s m h`, decimals, concatenation such as `1m30s`).

- [ ] **Step 1: Golden generator** `bend/scripts/gen-dur-golden.go` prints `ns show round parse(show)` for ns in: 0, 1, 999, 1000, 1001, 25833, 326000, 364103, 423778, 999999, 1000000, 1519000, 16501000, 999999999, 1000000000, 1000000001, 1500000000, 59999999999, 60000000000, 61500000000, 3599999999999, 3600000000000, 3661500000000, 90061000000000, 281474976710655:
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
Run: `go run bend/scripts/gen-dur-golden.go > bend/tests/golden/dur.txt`

- [ ] **Step 2: Laws**
```python
law dur_parse_show:
  for +n: Nat
  {Dur.parse(Dur.show(n)) == Some{n} : Maybe<&2, Nat>}

law dur_round_idem:
  for +n: Nat
  {Dur.round(Dur.round(n)) == Dur.round(n) : Nat}

# LAW: rounding moves a duration by at most half its rounding unit
law dur_round_close:
  for +n: Nat
  {Nat.is_le(Nat.mul(2n, Nat.sub(Nat.max(n, Dur.round(n)), Nat.min(n, Dur.round(n)))), Dur.unit(n)) == True{} : Bool}
```
where `Dur.unit(n)` is the rounding unit `round` uses for `n` (export it). (Note: `round(3599999999999)` rounds to `1h0m0s`; the idempotence law still holds because `round` of an exact hour is itself.)

- [ ] **Step 3: Failing test** — `bend/tests/dur.bend` prints the same four columns for the same inputs; `#|` lines from `golden/dur.txt`.

- [ ] **Step 4: Implement** — port `time.Duration.String` (`fmtFrac`/`fmtInt` in Go's `time/time.go`) for non-negative values: `< 1s` picks `ns`/`µs`/`ms` with fraction trimming; otherwise `h`/`m` then seconds with a trimmed fraction; `0` → `0s`. Use `µ` (U+00B5) as Go does.

- [ ] **Step 5: Prove, test, commit** — `git commit -m "bend: add Go-compatible duration formatting, rounding and parsing"`

---

### Task 7: Civil time and RFC3339Nano (`lib/civil.bend`)

**Files:**
- Create: `bend/lib/civil.bend`, `bend/tests/civil.bend`, `bend/scripts/gen-civil-golden.go`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Civil`): `type Time is Data: Time{sec: Nat, nsec: Nat, off: U32}` (UTC seconds since epoch, nanoseconds, offset+86400 as from `Clock.wall`); `Civil.days_to_ymd(days: Nat) -> Nat & Nat & Nat`; `Civil.ymd_to_days(y, m, d) -> Nat` (Howard Hinnant's algorithms, epoch-relative, dates ≥ 1970); `Civil.rfc3339nano(+t: Time) -> String` (= Go `time.Time.MarshalJSON` without the quotes: local time with the offset applied, trailing fraction zeros trimmed, `Z` when offset is 0, `+hh:mm` otherwise); `Civil.parse_rfc3339(s: String) -> Maybe<&2, Time>`; `Civil.unix_nanos_show(+t: Time) -> String` (= `Dec.show(sec) ++ Dec.pad(9n, nsec)`, or `Dec.show(nsec)` when `sec = 0`); `Civil.cmp(+a: Time, +b: Time) -> Cmp` (by `(sec, nsec)`); `Civil.add_ns(+t: Time, ns: Nat) -> Time`; `Civil.sub_ns(+a: Time, +b: Time) -> Nat` (a − b in ns, 0 if negative; values stay < 2^48 ns ≈ 78 h).

- [ ] **Step 1: Golden generator** prints for several instants (epoch, 2000-02-29T23:59:59.5Z, 2026-09-23T02:09:47.935870875+02:00, 2100-03-01T00:00:00Z, 2038-01-19T03:14:08.000000001-07:00) the line `sec nsec off rfc3339nano`, using `time.Date(...).In(time.FixedZone("", off))` and `MarshalJSON` with the quotes stripped. For zero offset it must be `time.UTC` so Go prints `Z`.

- [ ] **Step 2: Laws**
```python
law civil_days_roundtrip:
  for +d: Nat
  {Civil.ymd_to_days(Civil.days_to_ymd(d)) == d : Nat}

law civil_rfc3339_roundtrip:
  for +t: Civil.Time
  for -h: {Civil.valid(t) == True{} : Bool}
  {Civil.parse_rfc3339(Civil.rfc3339nano(t)) == Some{t} : Maybe<&2, Civil.Time>}

law civil_add_sub:
  for +t: Civil.Time
  for +ns: Nat
  {Civil.sub_ns(Civil.add_ns(t, ns), t) == ns : Nat}
```
(`Civil.valid(t)`: `nsec < 10^9`, offset within ±24 h, and the local time not before 1970. If `ymd_to_days` takes a triple, write the law with `Civil.days_to_ymd(d)` passed as the triple; adjust the signature so it typechecks.)

- [ ] **Step 3: Failing test, Step 4: implement, Step 5: prove, test, commit** — `git commit -m "bend: add civil time and RFC3339Nano"`

---

### Task 8: Base64 and CSV fields (`lib/b64.bend`, `lib/csv.bend`)

**Files:**
- Create: `bend/lib/b64.bend`, `bend/lib/csv.bend`, `bend/tests/b64.bend`, `bend/tests/csv.bend`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces: `B64.encode(s: String) -> String`, `B64.decode(s: String) -> Maybe<&2, String>` (standard alphabet, `=` padding; every character is treated as one byte 0–255, since Bend strings from `TCP.recv` hold one byte per `Chr`).
- Produces: `Csv.field(s: String) -> String` (Go `encoding/csv` `fieldNeedsQuotes`: an empty field is written bare; a field is quoted when it equals `\.`, contains `,` `"` `\r` or `\n`, or its first character is a space or tab; inside quotes each `"` is doubled), `Csv.row(fs: List<&2, String>) -> String` (fields joined by `,`, ending in `\n`), `Csv.parse_row(s: String) -> Maybe<&2, List<&2, String> & String>` (one record and the rest; honours quotes; `TrimLeadingSpace = true` as the decoder sets it).

- [ ] **Step 1: Laws**
```python
law b64_roundtrip:
  for +s: String
  for -h: {B64.bytes(s) == True{} : Bool}
  {B64.decode(B64.encode(s)) == Some{s} : Maybe<&2, String>}

# LAW: a row parses back into its fields and the rest of the input
law csv_row_roundtrip:
  for +fs: List<&2, String>
  for +rest: String
  for -h: {Csv.fields_ok(fs) == True{} : Bool}
  {Csv.parse_row(Csv.row(fs) ++ rest) == Some{(fs, rest)} : Maybe<&2, List<&2, String> & String>}
```
`B64.bytes(s)`: every char < 256. `Csv.fields_ok(fs)`: non-empty list, and no field starts with a space or tab. Leading spaces are trimmed by the decoder; Go quotes such fields when encoding, so they survive, and the code must quote them too. Once the quoting rule is implemented, drop that clause from `fields_ok` and keep the law true.

- [ ] **Step 2: Failing tests** — `b64.bend`: `encode("")`→`#|` (empty line), `encode("f")`→`#|Zg==`, `encode("foobar")`→`#|Zm9vYmFy`, `decode("Zm9vYg==")`→`#|Some{"foob"}` (check `Maybe.show` rendering first). `csv.bend`: `Csv.row(["a", "b,c", "d\"e", "", " x"])` → `#|a,"b,c","d""e",," x"`. Confirm that expectation first with a Go one-liner using `csv.NewWriter`.

- [ ] **Step 3: Implement, Step 4: prove, Step 5: test, commit** — `git commit -m "bend: add base64 and Go-compatible CSV fields"`

---

### Task 9: Result codecs (`lib/json.bend`, `lib/result.bend`)

**Files:**
- Create: `bend/lib/json.bend`, `bend/lib/result.bend`, `bend/tests/result_csv.bend`, `bend/tests/result_json.bend`, `bend/scripts/gen-result-golden.go`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Res`):
```python
type Header is Data:
  Header{key: String, vals: List<&2, String>}

type Result is Data:
  Result{attack: String, seq: Nat, code: U32, ts: Civil.Time, latency: Nat,
         bytes_out: Nat, bytes_in: Nat, error: String, body: String,
         method: String, url: String, headers: Maybe<&2, List<&2, Header>>}
```
  `headers` is `None` for Go's `nil` header map (CSV: empty field; JSON: `null`) and `Some` otherwise. Header order is Go's `http.Header.Write` order (sorted by key; values in order).
  `Res.to_csv(+r: Result) -> String` (one line incl. `\n`: Go's column order `timestamp(unix ns), code, latency, bytes_out, bytes_in, error, base64(body), attack, seq, method, url, base64(header block)`); `Res.of_csv(s: String) -> Maybe<&2, Result & String>`; `Res.to_json(+r: Result) -> String` (one line incl. `\n`, easyjson field order `attack, seq, code, timestamp, latency, bytes_out, bytes_in, error, body, method, url, headers`; `body` base64 or `null` when empty; `headers` object of arrays or `null`); `Res.of_json(s: String) -> Maybe<&2, Result & String>`; `Res.decode(s: String) -> Maybe<&2, Result & String>` picks JSON when the first non-space char is `{`, CSV otherwise.
- Produces (alias `Json`): `Json.str(s: String) -> String` (Go `encoding/json` string escaping with HTML escaping on, as easyjson does: `<` `>` `&` → `<` `>` `&`, control chars `\u00XX` except `\n` `\r` `\t`, which use short escapes; also ` `/` `), and a small tokenizer used by `of_json` and the report's JSON reader.

- [ ] **Step 1: Golden generator** — `bend/scripts/gen-result-golden.go` builds 6 `vegeta.Result`s (import `vegeta "github.com/tsenart/vegeta/v12/lib"`): a success with body and headers (`Content-Type`, two `Set-Cookie` values), a connection-refused error with `Code 0`, `nil` headers, `nil` body; a 500 with `Error: "500 Internal Server Error"`; a result with a comma, quote and newline in `Error`; a result with `seq` 4294967296; a result with timestamp in UTC and one at `+02:00`. It writes each with `NewCSVEncoder` to `bend/tests/golden/results.csv` and with `NewJSONEncoder` to `bend/tests/golden/results.json`. Run it from the repo root: `go run ./bend/scripts/gen-result-golden.go`.

- [ ] **Step 2: Laws**
```python
law result_csv_roundtrip:
  for +r: Res.Result
  for +rest: String
  for -h: {Res.valid(r) == True{} : Bool}
  {Res.of_csv(Res.to_csv(r) ++ rest) == Some{(r, rest)} : Maybe<&2, Res.Result & String>}

law result_json_roundtrip:
  for +r: Res.Result
  for +rest: String
  for -h: {Res.valid(r) == True{} : Bool}
  {Res.of_json(Res.to_json(r) ++ rest) == Some{(r, rest)} : Maybe<&2, Res.Result & String>}

law result_decode_picks:
  for +r: Res.Result
  for +rest: String
  for -h: {Res.valid(r) == True{} : Bool}
  {Res.decode(Res.to_json(r) ++ rest) == Res.of_json(Res.to_json(r) ++ rest) : Maybe<&2, Res.Result & String>}
```
`Res.valid`: `Civil.valid(ts)`, bytes-only strings, code < 65536, header keys non-empty and without `:`/CR/LF/leading space, and header values without CR/LF. CSV cannot distinguish an empty-but-present header map from `nil`, and Go's decoder yields `nil` for an empty field. So `valid` also requires `headers` to be `None` or a non-empty `Some`.

- [ ] **Step 3: Failing tests** — `result_csv.bend` reads `tests/golden/results.csv` with `File.open`/`File.read` (path relative to `bend/`, as the runner `cd`s there), decodes every row, re-encodes it, and prints `Bool.show(String.eq(out, golden))` → `#|True`. It then prints `seq` and `code` of each result, one per line (e.g. `#|0 200`), taking the values from the generator. `result_json.bend` does the same for `results.json`.

- [ ] **Step 4: Implement, prove, test, commit** — `git commit -m "bend: add Go-compatible CSV and JSON result codecs"`

---

### Task 10: URLs and targets (`lib/target.bend`)

**Files:**
- Create: `bend/lib/target.bend`, `bend/tests/target.bend`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Tgt`):
```python
type Url is Data:
  Url{scheme: String, host: String, port: U32, path: String}   # path includes ?query, "/" if empty

type Target is Data:
  Target{method: String, url: String, headers: List<&2, Res.Header>, body: Maybe<&2, String>}
```
  `body` is `Some{path}` for an `@path` line (read later by the IO layer), `None` for the global `-body`.
  `Tgt.parse_url(s: String) -> Result<&2, &2, String, Url>` (scheme `http` → default port 80; `https` → `Fail{"https is not supported"}`; `host:port`; IPv6 literals → `Fail{"ipv6 is not supported"}`); `Tgt.show_url(+u: Url) -> String`; `Tgt.parse_all(src: String) -> Result<&2, &2, String, List<&2, Target>>` (Go `NewHTTPTargeter` rules: skip blank/`#` lines between targets, `METHOD URL` line where METHOD is `[A-Z]+` then a space, then header lines `Key: Value` (both trimmed, non-empty) until a blank line, a line starting with an uppercase method and a space, `@file`, or EOF; `#` lines inside skipped; error texts `bad target: <line>`, `bad method: <tok>`, `bad URL: <url>`, `bad header: <line>`); `Tgt.show_all(+ts: List<&2, Target>) -> String` (canonical: `METHOD URL\n`, headers `Key: Value\n`, `@path\n`, blank line between targets).

- [ ] **Step 1: Laws**
```python
law url_roundtrip:
  for +u: Tgt.Url
  for -h: {Tgt.url_ok(u) == True{} : Bool}
  {Tgt.parse_url(Tgt.show_url(u)) == Done{u} : Result<&2, &2, String, Tgt.Url>}

law targets_roundtrip:
  for +ts: List<&2, Tgt.Target>
  for -h: {Tgt.targets_ok(ts) == True{} : Bool}
  {Tgt.parse_all(Tgt.show_all(ts)) == Done{ts} : Result<&2, &2, String, List<&2, Tgt.Target>>}
```
(`url_ok`: scheme `http`, non-empty host without `:/@[]`, port 1–65535, path starting with `/` and without spaces. `targets_ok`: every URL is `url_ok`-shaped, methods are `[A-Z]+`, and header keys/values are non-empty, trimmed, without newlines and keys without `:`; body paths contain no newline. `show_url` prints the port only when it is not 80, and `parse_url` gives 80 when no port is written.)

- [ ] **Step 2: Failing test** `tests/target.bend` parses this string and prints each target as `METHOD URL|k=v,k=v|body`:
```
GET http://127.0.0.1:8080/a?b=c
X-A: 1
X-A: 2

# comment
POST http://localhost/x
@tests/golden/body.txt
PUT http://h:1/
```
expected:
```
#|GET http://127.0.0.1:8080/a?b=c|X-A=1,X-A=2|
#|POST http://localhost/x||@tests/golden/body.txt
#|PUT http://h:1/||
```
Then it prints the errors for `"get http://x/"` (`#|bad method: get`) and `"GET"` (`#|bad target: GET`). Check the latter against Go: with a single token, Go reports `bad target:`.

- [ ] **Step 3: Implement, prove, test, commit** — `git commit -m "bend: add URL and http-format target parsing"`

---

### Task 11: HTTP/1.1 (`lib/http.bend`)

**Files:**
- Create: `bend/lib/http.bend`, `bend/tests/http.bend`, `bend/tests/http_split.bend`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Http`):
  - `Http.request(+t: Tgt.Target, +u: Tgt.Url, +body: String, +seq: Nat, +name: String, keepalive: Bool) -> String` — `METHOD path HTTP/1.1\r\nHost: host[:port]\r\nUser-Agent: Go-http-client/1.1\r\n`, then the target headers in order; `Content-Length: n` when the body is non-empty or the method is POST/PUT/PATCH; `X-Vegeta-Attack` when the name is non-empty; `X-Vegeta-Seq: seq`; `Connection: close` when not keepalive; `\r\n`, body.
  - `type Resp is Data: Resp{code: U32, status: String, headers: List<&2, Res.Header>, body: String, body_len: Nat, keep: Bool}` — `status` is Go's `r.Status` (`"200 OK"`), `body` is truncated to max-body, `body_len` is the full length read, and `keep` says whether the connection may be reused (HTTP/1.1 without `Connection: close`).
  - `type Parse is Data` — the incremental state. `Http.start(max_body: Maybe<&2, Nat>, head: Bool) -> Parse` (`head` = request was HEAD: no body); `Http.feed(+p: Parse, chunk: String) -> Parse`; `Http.eof(+p: Parse) -> Parse` (peer closed); `Http.done(+p: Parse) -> Maybe<&2, Result<&2, &2, String, Resp & String>>` (`None` = need more input; `Some{Done{(resp, leftover)}}`; `Some{Fail{msg}}` = malformed). Body framing: `Content-Length`, `Transfer-Encoding: chunked` (with trailers skipped), or read-until-EOF; 1xx responses are skipped; 204/304/HEAD have no body.
  - `Http.render(+r: Resp) -> String` — canonical response with `Content-Length`, for laws/tests.

- [ ] **Step 1: Laws**
```python
# LAW: feeding a response in two pieces is feeding it whole
law http_feed_split:
  for +a: String
  for +b: String
  for +p: Http.Parse
  {Http.feed(Http.feed(p, a), b) == Http.feed(p, a ++ b) : Http.Parse}

# LAW: a rendered response parses back, whatever follows it
law http_render_parse:
  for +r: Http.Resp
  for +rest: String
  for -h: {Http.resp_ok(r) == True{} : Bool}
  {Http.done(Http.feed(Http.start(None{}, False{}), Http.render(r) ++ rest)) == Some{Done{(r, rest)}} : Maybe<&2, Result<&2, &2, String, Http.Resp & String>>}
```
`http_feed_split` is strong: it forces the parser to be a function of consumed bytes only. The simplest way to keep it true is to accumulate the input and re-derive on demand, but that costs O(n²). Do not do that. Instead design `Parse` as a byte-at-a-time state machine (`feed(p, c <> s) = feed(step(p, c), s)`), which makes the law a one-line induction. Bodies are appended through an accumulator list reversed at the end.

- [ ] **Step 2: Failing tests**
  - `tests/http.bend` renders the request for `GET http://127.0.0.1:8080/a?b=c` with header `X-A: 1`, seq 7, name `n`, and prints it with `\r` shown as `\\r`. Expected:
    `#|GET /a?b=c HTTP/1.1\r` / `#|Host: 127.0.0.1:8080\r` / `#|User-Agent: Go-http-client/1.1\r` / `#|X-A: 1\r` / `#|X-Vegeta-Attack: n\r` / `#|X-Vegeta-Seq: 7\r` / `#|\r`.
    It also parses fixed responses and prints `code|status|body|body_len|keep`:
    - Content-Length: `#|200|200 OK|ok|2|True`
    - chunked `5\r\nhello\r\n0\r\n\r\n`: `#|200|200 OK|hello|5|True`
    - `HTTP/1.1 500 Internal Server Error` with `Connection: close` and no length, closed: `#|500|500 Internal Server Error|boom|4|False`
    - a `100 Continue` before a 204: `#|204|204 No Content||0|True`
    - max-body 2 with an 8-byte body: `#|200|200 OK|ab|8|True`
  - `tests/http_split.bend` takes the chunked response above plus a pipelined second response and feeds it split at every index 0..len, printing `True` if every split gives the same `done` as the whole. Expected: `#|True`.

- [ ] **Step 3: Implement, prove, test, commit** — `git commit -m "bend: add HTTP/1.1 request rendering and incremental response parser"`

---

### Task 12: Sort and metrics (`lib/sort.bend`, `lib/metrics.bend`)

**Files:**
- Create: `bend/lib/sort.bend`, `bend/lib/metrics.bend`, `bend/tests/sort.bend`, `bend/tests/metrics.bend`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Sort`): `Sort.sort(xs: List<&2, Nat>) -> List<&2, Nat>` (bottom-up merge sort; use Bend's parallel `a b = f(x) g(y)` for the two halves in a top-down split so large reports use every core); `Sort.Sorted(xs) -> Type`; `Sort.count(x, xs) -> Nat`.
- Produces (alias `Met`):
```python
type Metrics is Data:
  Metrics{requests: Nat, success: Nat, codes: Map<Nat>, errors: List<&2, String>,
          lat_total: Big.Big, lats: List<&2, Nat>, lat_max: Nat, lat_min: Nat,
          bytes_in: Big.Big, bytes_out: Big.Big,
          earliest: Maybe<&2, Civil.Time>, latest: Maybe<&2, Civil.Time>, end: Maybe<&2, Civil.Time>,
          hist: Maybe<&2, List<&2, Nat>>}
```
  (`codes` is Base's string-keyed `Map` keyed by `Dec.show(code)`; check `bend base Map` for its exact type parameters and adapt.) `Met.new(buckets: Maybe<&2, List<&2, Nat>>) -> Metrics`; `Met.add(+m, +r: Res.Result) -> Metrics` (exactly Go `Metrics.Add`: success iff 200 ≤ code < 400; errors deduplicated in first-seen order; earliest/latest by timestamp; end = max(ts + latency)); `Met.pct(+sorted: List<&2, Nat>, n: Nat, q_num: Nat, q_den: Nat) -> Nat` (nearest rank: index ⌈q·n⌉−1, clamped to [0, n−1]; 0 when n = 0); `Met.hist_index(+buckets: List<&2, Nat>, lat: Nat) -> Nat` (Go `Histogram.Add`: the first i with b_i ≤ lat < b_{i+1}, else the last bucket).
- Produces `type Summary is Data` with the closed values the reporters need: requests, success, duration_ns, wait_ns, the `F64` rate, throughput, success ratio, bytes-in/out means, `Big` totals, latency mean/p50/p90/p95/p99/min/max as `Nat` ns, earliest/latest/end, codes, errors, histogram counts. Produced by `Met.close(+m: Metrics) -> Summary`, which mirrors Go `Metrics.Close` (zeros when requests = 0; rate and throughput only divided when duration > 0; `lat_mean = lat_total / requests` as `time.Duration(float64(total)/float64(n))`. Go truncates the float quotient toward zero, so compute `F64.div` and truncate, not integer division).

- [ ] **Step 1: Laws**
```python
law sort_sorted:
  for +xs: List<&2, Nat>
  Sort.Sorted(Sort.sort(xs))

law sort_perm:
  for +x: Nat
  for +xs: List<&2, Nat>
  {Sort.count(x, Sort.sort(xs)) == Sort.count(x, xs) : Nat}

# LAW: percentiles never decrease as the quantile grows
law pct_monotone:
  for +xs: List<&2, Nat>
  for +a: Nat
  for +b: Nat
  for +d: Nat
  for -h: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(Met.pct(Sort.sort(xs), List.length(&2, Nat, xs), a, 1n+d), Met.pct(Sort.sort(xs), List.length(&2, Nat, xs), b, 1n+d)) == True{} : Bool}

# LAW: a percentile of a non-empty sample is one of its values
law pct_member:
  for +x: Nat
  for +xs: List<&2, Nat>
  for +a: Nat
  for +d: Nat
  {Nat.is_gt(Sort.count(Met.pct(Sort.sort(x <> xs), 1n+List.length(&2, Nat, xs), a, 1n+d), x <> xs), 0n) == True{} : Bool}

# LAW: every added result lands in exactly one histogram bucket
law hist_total:
  for +bs: List<&2, Nat>
  for +rs: List<&2, Res.Result>
  {Met.hist_sum(Met.add_all(Met.new(Some{0n <> bs}), rs)) == List.length(&2, Res.Result, rs) : Nat}

law success_le_requests:
  for +rs: List<&2, Res.Result>
  {Nat.is_le(Met.success_of(Met.add_all(Met.new(None{}), rs)), List.length(&2, Res.Result, rs)) == True{} : Bool}

law requests_count:
  for +rs: List<&2, Res.Result>
  {Met.requests_of(Met.add_all(Met.new(None{}), rs)) == List.length(&2, Res.Result, rs) : Nat}
```
(`Met.add_all` folds `Met.add` over a list; `Met.hist_sum` sums the counts (0 when no histogram); `Met.success_of`/`Met.requests_of` are field getters. Export all four.)

- [ ] **Step 2: Failing tests** — `tests/sort.bend`: sorts `[5, 3, 9, 1, 3, 0]` and prints it with `List.show` → `#|[0, 1, 3, 3, 5, 9]` (run a one-line `List.show` program first and match its exact rendering). It also prints `Sort.sort` of 200000 descending numbers' first and last elements (`#|0`, `#|199999`) to catch O(n²). `tests/metrics.bend`: decodes `tests/golden/results.csv` (Task 9), adds all results with buckets `[0, 1ms, 10ms]`, closes, and prints requests, success, codes (`200:k 500:k`), errors (one per line), p50, max and histogram counts. Extend `gen-result-golden.go` (Task 9) to also write `bend/tests/golden/results.metrics` with exactly those lines, computed with Go's `Metrics` for everything except p50, which it computes as exact nearest rank over the six latencies; the test's `#|` lines are that file prefixed with `#|`.

- [ ] **Step 3: Implement, prove, test, commit** — `git commit -m "bend: add proven merge sort and metrics"`

---

### Task 13: Pacer and rate/flag parsing (`lib/pacer.bend`)

**Files:**
- Create: `bend/lib/pacer.bend`, `bend/tests/pacer.bend`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Pace`): `type Rate is Data: Rate{freq: Nat, per_ns: Nat}` (`freq = 0` or `per_ns = 0` means infinite); `Pace.parse_rate(s: String) -> Result<&2, &2, String, Rate>` (Go `rateFlag.Set`: `"infinity"` or `"0"` → 0/0; `"N"` → N per 1s; `"N/D"` with D a duration (`1s`, `500ms`) or a bare unit (`s`, `m`) → N per D); `Pace.next(+r: Rate, elapsed_ns: Nat, hits: Nat) -> Nat` (wait before the next hit, 0 if behind or infinite: port of `ConstantPacer.Pace` with `interval = per_ns / freq`, `delta = (hits+1)·interval`, answer `delta − elapsed` if positive); `Pace.expected(+r: Rate, elapsed_ns: Nat) -> Nat` (`freq · ⌊elapsed / per_ns⌋`).

- [ ] **Step 1: Laws**
```python
# LAW: a pacer never makes a hit wait when it is behind schedule
law pace_behind_no_wait:
  for +r: Pace.Rate
  for +e: Nat
  for +h: Nat
  for -hb: {Nat.is_lt(h, Pace.expected(r, e)) == True{} : Bool}
  {Pace.next(r, e, h) == 0n : Nat}

# LAW: waiting as told brings the clock to the hit's slot
law pace_slot:
  for +r: Pace.Rate
  for +e: Nat
  for +h: Nat
  for -hf: {Nat.is_gt(Pace.rate_freq(r), 0n) == True{} : Bool}
  for -hp: {Nat.is_gt(Pace.rate_per(r), 0n) == True{} : Bool}
  for -hn: {Nat.is_le(Pace.expected(r, e), h) == True{} : Bool}
  {Nat.is_ge(Nat.add(e, Pace.next(r, e, h)), Nat.mul(1n+h, Nat.div(Pace.rate_per(r), Pace.rate_freq(r)))) == True{} : Bool}
```

- [ ] **Step 2: Failing test** — prints `parse_rate` of `"50"`, `"50/1s"`, `"10/500ms"`, `"5/m"`, `"0"`, `"infinity"`, `"x"`, as `freq/per_ns` or `error: …` (take Go's error text for `"x"` from `rateFlag.Set` in `flags.go`). Then it prints `Pace.next(Rate{50, 1000000000}, e, h)` for `(e, h)` = `(0, 0)` → `20000000`, `(0, 1)` → `40000000`, `(1000000000, 10)` → `0`.

- [ ] **Step 3: Implement, prove, test, commit** — `git commit -m "bend: add constant pacer and rate parsing"`

---

### Task 14: Reporters (`lib/report.bend`)

**Files:**
- Create: `bend/lib/report.bend`, `bend/lib/tab.bend`, `bend/tests/report_text.bend`, `bend/tests/report_json.bend`, `bend/tests/report_hist.bend`, `bend/scripts/gen-report-golden.go`
- Modify: `bend/LAWS.bend`, `bend/PROOF.bend`

**Interfaces:**
- Produces (alias `Tab`): `Tab.render(minwidth: Nat, tabwidth: Nat, padding: Nat, padchar: Chr, text: String) -> String` — Go `text/tabwriter` with the flags Vegeta uses (`StripEscape`, no `AlignRight`): cells are `\t`-terminated; each column block of consecutive lines is padded to its max width + padding; a line's last cell (no trailing tab) is not a column.
- Produces (alias `Rep`): `Rep.text(+s: Met.Summary) -> String`, `Rep.json(+s: Met.Summary) -> String` (Go's JSON reporter: `json.NewEncoder(w).Encode(m)` of `Metrics`; key order and names from the struct tags in `lib/metrics.go`, e.g. `"latencies":{"total":…,"mean":…,"50th":…,"90th":…,"95th":…,"99th":…,"max":…,"min":…}`; read the tags, don't guess), `Rep.hist(+s: Met.Summary) -> String` (Go `NewHistogramReporter`: bucket bounds shown with `Dur.show`, last bucket `+Inf`; `ratio*75` `#`s truncated, `%.2f%%` via `F64.fixed`), `Rep.parse_type(s: String) -> Result<&2, &2, String, RType>` (`text`, `json`, `hist[0,1ms,10ms]`; the `hist` buckets parse with `Dur.parse`; error texts as Go's `report.go`).

- [ ] **Step 1: Golden generator** — `bend/scripts/gen-report-golden.go` reads each `bend/tests/golden/report-<case>.csv` (written by the same program from fixed synthetic results), runs Go's `Metrics` + `NewTextReporter`/`NewJSONReporter`/`NewHistogramReporter` (buckets `0,1ms,10ms,100ms`), and writes `report-<case>.{text,json,hist}`. Cases:
  - `empty`: 0 results
  - `single`: one 200
  - `mixed`: 100 results, codes 200/500/0 and 3 distinct errors, latencies 1..100 ms, timestamps 10 ms apart
  - `huge-sums`: 3 results with latency 200 h each and bytes_in 2^47 each, so sums pass 2^48
  - `two-zones`: results at +02:00 and Z

  For `mixed`, the Go program also prints exact nearest-rank percentiles into `report-mixed.pct`, so the test can check ours exactly while the text golden has Go's t-digest values.

- [ ] **Step 2: Laws**
```python
# LAW: the table renderer keeps every cell's text, in order
law tab_keeps_text:
  for +s: String
  {Tab.strip(Tab.render(0n, 8n, 2n, ' ', s)) == Tab.strip(s) : String}

# LAW: the histogram's counts add up to the number of requests
law hist_counts_total:
  for +s: Met.Summary
  for -h: {Met.summary_ok(s) == True{} : Bool}
  {Rep.hist_total(s) == Met.summary_requests(s) : Nat}
```
(`Tab.strip` deletes tabs, spaces and padding characters; export it and `Rep.hist_total`, `Met.summary_ok` (a summary produced by `Met.close`) and `Met.summary_requests`.)

- [ ] **Step 3: Failing tests** — each `report_*.bend` loads each case's CSV, summarizes, renders, and prints `Bool.show(String.eq(ours, golden))` per case, with the percentile values masked in both strings for `text`/`json`. Masking: replace the p50/p90/p95/p99 fields with `P`, using a helper in the test file that knows the line layout. It then prints our exact percentiles for `mixed` next to `report-mixed.pct`. Expected: all `#|True`.

- [ ] **Step 4: Implement, prove, test, commit** — `git commit -m "bend: add text, JSON and histogram reporters"`

---

### Task 15: The attack command (`attack.bend`)

**Files:**
- Create: `bend/attack.bend`, `bend/lib/flags.bend`, `bend/main.bend`, `bend/scripts/e2e.sh`, `bend/scripts/e2e-server.go`
- Test: `bend/scripts/e2e.sh` cases; `bend/tests/flags.bend`

**Interfaces:**
- Consumes: everything above.
- Produces: `bend/.build/vegeta` (built by `bend main.bend -o .build/vegeta`), CLI `vegeta attack [flags]`. Flags (Go names, defaults and semantics): `-rate` (50/1s), `-duration` (0 = forever), `-targets` (stdin), `-format` (http only; anything else → `unsupported format`), `-workers` (10), `-max-workers` (unbounded), `-timeout` (30s), `-header` (repeatable, `Key: Value`), `-body` (file), `-keepalive` (true), `-output` (stdout), `-name`, `-max-body` (-1), `-redirects` (10; -1 = don't follow but count 3xx as success). Plus one flag Go lacks: `-encoding csv|json` (csv). Unknown or unsupported Go flags (`-http2`, `-insecure`, …) print `flag not supported in the Bend port: -x` and exit 1.
- `Flags.parse(args: List<&2, String>) -> Result<&2, &2, String, Opts>` in `lib/flags.bend` (pure; `-k=v` and `-k v`; bool flags take `-k` or `-k=false`).

Engine (IO, `@unsafe` loops allowed here):
1. Read targets (stdin via `Stdin.read` until `""`, or file), parse all up front, read `@body` files and `-body`, resolve each distinct host once with `Dns.resolve` (Go's default `-dns-ttl 0` caches forever).
2. `began_wall <- Clock.wall()`, `began_mono <- Clock.mono_ns()`.
3. Channels: `ticks : Chan(Nat)` (room = workers), `results : Chan(Res.Result)` (room = 1024).
4. Spawn `workers` workers. A worker loops `Chan.recv(ticks)`: on `Some{seq}` it takes target `seq mod n` (round-robin like Go's static targeter) and does a hit; on `None` (ticks closed) it closes its socket and sends a `Done` marker. A worker holds `Maybe<Socket>` and reconnects when the previous response had `keep = False`, the send fails, or a recv fails with the connection reset (then the request is retried once, as Go's transport retries idempotent requests on a reused connection).
5. Hit: `t0_mono <- Clock.mono_ns()`; timestamp = `Civil.add_ns(began_wall, t0_mono − began_mono)`; send `Http.request`; recv with `TCP.poll(sock, 65536, remaining_ms)` feeding `Http.feed` until `Http.done` is `Some`, EOF (`Http.eof`), or the deadline passes (error `Get "URL": context deadline exceeded (Client.Timeout exceeded while awaiting headers)`); latency = `mono_now − t0_mono`; fill `Res.Result` exactly as Go `hit` does (error = status text when code ∉ [200, 400); `bytes_out` = body length; `bytes_in` = `body_len`; `headers = Some` on any response); follow redirects up to `-redirects` (301/302/303 → GET without body, 307/308 → same method and body; resolve relative `Location` against the URL).
6. Pacer (the main computation): `count = 0`; loop: `elapsed = mono − began_mono`; stop if `duration > 0 && elapsed > duration`; `wait = Pace.next(rate, elapsed, count)`; `Clock.sleep_ns(wait)` if > 0; if `wait = 0` and `elapsed − slot(count) > interval` and `workers < max_workers`, spawn one more worker; `Chan.send(ticks, count)`; `count += 1`. On stop: `Chan.close(ticks)`.
7. Writer: a computation receiving from `results`, encoding with `Res.to_csv` or `Res.to_json`, writing with `IO.write` (or `File.write` for `-output`), counting `Done` markers until it has one per spawned worker. It learns the final worker count from a message the pacer sends after closing ticks.
8. `SIGINT`: out of scope for v1 (the process is killed; the output may end mid-line). Say so in `bend/README.md`.

- [ ] **Step 1: Flags unit test (failing)** — `tests/flags.bend` parses `["-rate=100/1s", "-duration", "2s", "-header", "A: 1", "-header", "B: 2", "-keepalive=false", "-encoding", "json"]` and prints each field; also `["-http2"]` → `#|error: flag not supported in the Bend port: -http2`.

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

- [ ] **Step 4: Implement `lib/flags.bend`, `attack.bend`, `main.bend`** (`main` dispatches on the first arg: `attack`, `report`, `-version`; anything else prints Go's usage text trimmed to the two commands).

- [ ] **Step 5: Run** `sh bend/scripts/test.sh && sh bend/scripts/e2e.sh` — all pass.

- [ ] **Step 6: Commit** — `git commit -m "bend: add attack command"`

---

### Task 16: The report command (`report.bend`)

**Files:**
- Create: `bend/report.bend`
- Modify: `bend/main.bend`, `bend/scripts/e2e.sh`

**Interfaces:**
- CLI `vegeta report [flags] [files...]`: `-type` (text | json | `hist[...]`), `-buckets` (for hist, Go semantics), `-output` (stdout). With no files it reads stdin; `-every` → `flag not supported in the Bend port: -every`. Input format is detected per stream by `Res.decode`. A gob stream (first byte not `{` and not a digit) → error `gob input is not supported: convert with 'vegeta encode -to csv'`.
- Streams results: decode incrementally from `Stdin.read`/`File.read` chunks into `Met.add`, never holding the raw input. Latencies are kept in `Metrics.lats` for the sort.

- [ ] **Step 1: Differential cases in `e2e.sh` (failing)**:
  - `report-go-in`: `vegeta-go attack … | vegeta-go encode -to csv | bend report` equals `vegeta-go report` on the same results, percentile fields masked (same masking as Task 14, via `sed` on the fixed layout).
  - `report-json`: same with `-type=json`, compared with `jq -S 'del(.latencies["50th","90th","95th","99th"])'`.
  - `report-hist`: `-type='hist[0,1ms,10ms]'`, exact equality.
  - `report-goldens`: for each `tests/golden/report-<case>.csv`, `bend report` equals `report-<case>.text` masked. The `empty`, `single` and `huge-sums` cases cover the Review Focus lines.
  - `report-gob`: piping Go's default gob output prints the gob error and exits 1.
  - `report-multi`: two files as args aggregate like Go's.

- [ ] **Step 2: Implement, Step 3: run `test.sh` and `e2e.sh`, Step 4: commit** — `git commit -m "bend: add report command"`

---

### Task 17: Benchmarks, docs, final gate

**Files:**
- Create: `bend/scripts/bench.sh`
- Modify: `bend/README.md`

- [ ] **Step 1: Bench** — `bend/scripts/bench.sh` runs `-rate=0 -workers=50 -duration=5s` against `/ok` for Go and Bend (each with its own report), and `report` over a 1,000,000-result CSV for both; prints a table (req/s, p50, p99, report wall time).
- [ ] **Step 2: README** — install (`scripts/install-bend.sh`), build (`bend main.bend -o .build/vegeta`), usage, supported flags, the spec's out-of-scope list and known deviations (copy them), how laws/proofs are organized, the bench table from Step 1.
- [ ] **Step 3: Final gate** — `sh bend/scripts/test.sh && sh bend/scripts/e2e.sh && sh bend/scripts/bench.sh`; `grep -c '@unsafe' bend/lib/*.bend` prints 0 for every file; `bend PROOF.bend` prints `All terms check` with no TODOs.
- [ ] **Step 4: Commit** — `git commit -m "bend: add benchmarks and docs"`

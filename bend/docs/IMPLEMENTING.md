# Implementing and proving the Bend port

Read this before touching `lib/` or `proofs/`. Everything here was learned
the hard way on Bend 2.0.25; the examples compile.

## Ground rules

- `LAWS.bend` is the spec and is read-only. Never edit it, its helpers, or
  a stub's type signature (types and constructor shapes are part of the
  spec). If a law looks false or unprovable, stop and report it.
- `lib/X.bend` implements module X. `proofs/X.bend` proves X's laws; it
  imports `../LAWS.bend as L` and the lib modules it needs, and defines
  one `def L.<law>(args...)` per law (untyped parameters, one per `for`
  binder, in order). `PROOF.bend` imports every `proofs/*.bend`.
- Gate: `sh scripts/test.sh` (all tests, then `bend PROOF.bend`);
  `sh scripts/test.sh <pattern>` runs matching tests only.
- Toolchain: `export BEND_NO_TELEMETRY=1 PATH=<repo>/bend/.build/bendhome/bin:$PATH`
  (`scripts/install-bend.sh` installs it).

## Runtime rules (compiled code)

- Runtime `Nat` is a 48-bit machine word and its arithmetic is native
  (`Nat.div(10^12, 10n)` is instant). Anything that can pass 2^48 is a
  `Big`.
- Compiled code is strict: `pick(A, c, x, y)` evaluates both `x` and `y`.
  Never put a recursive call inside a `pick` branch in a loop. Loops use
  fuel plus a stop flag the function matches itself:

      def go(fuel: Nat, stop: Bool, +n: Nat, acc: String) -> String:
        match fuel:
          case 0n:
            acc
          case 1n+f:
            match stop:
              case True{}:
                acc
              case False{}:
                go(f, Nat.is_lt(n, 10n), Nat.div(n, 10n), SCon{digit(n), acc})

- A `match` may only inspect a parameter or a pattern-bound variable, not
  a computed value, and a `let` may not come before a `match` on a
  parameter. Give the value its own def (`read.of(ok: Bool, s)` matching
  `ok`, called as `read.of(all_digits(s), s)`).
- No mutual recursion; termination is checked left to right (put the
  shrinking argument first). No `@unsafe` in `lib/`.
- Destructuring a computed pair is a match too: use accessor defs taking
  the pair as a parameter.
- Bend 2.0.25 miscompiles `Bool.or(x, pick(Bool, <computed cond>, a, b))`
  (tests/compiler_canary.bend). In `lib/`, give such a `pick` a def of its
  own. Compiled unit tests and Go goldens are the last word on behavior.
- Base's `Nat.min`/`Nat.max` count down one at a time at runtime (two
  equal values near 2.5e14 overflow the stack). Compare instead:
  `pick(Nat, Nat.is_lt(a, b), a, b)`.
- Strings in `lib/` are bytes: one `Chr` per byte (0..255). Bend source
  literals are code points, so write non-ASCII bytes explicitly
  (`SCon{Chr{194}, SCon{Chr{181}, SNil{}}}` for "µ").
- Constructors of imported modules take the alias (`Big.Big{ls}`);
  constructor names must not clash with Base's (Done, Fail, Some, None,
  Nil, Con, Unit, ...).

## Checker rules (proofs)

- `%e : P` rewrites with `e : {a == b : T}`: the current goal must be `P`
  with `_` replaced by `b`; the new goal is `P` with `_` replaced by `a`.
  To go the other way use `Equal.sym(T, a, b, e)`.
- Law hypotheses are relevant (`for h:`) and usable in rewrites; an erased
  equation cannot be used.
- The checker does not unfold a def applied to an opaque value it would
  have to match on. Split the value first (`match c: case Chr{k}: {==}`;
  `match s: case SNil{} ... case SCon{c, rest} ...`), then `{==}`.
- A binder used twice in a proof (in a rewrite and a recursive call) must
  be reusable: `+acc` parameters, `SCon{+c, +rest}` patterns.
- Theory `Nat`s are unary. A proof must never make the checker compute a
  closed number above ~10^5 (it overflows or hangs, even for `x == x`).
  Keep big constants symbolic (`Nat.mul(k, 1000000000n)` with `k` a
  variable) or as `Big` limb literals, and prove arithmetic facts as
  symbolic lemmas (induction on a variable).
- Base has almost no lemmas. Shared ones go in `proofs/nat.bend`
  (arithmetic, div/mod) and `proofs/str.bend` (strings, lists). Look
  there before writing your own; add general ones there.
- Idioms from Bend's demos (`demos/proof_insertion_sort/PROOF.bend`,
  `demos/proof_numerics/PROOF.bend`): case analysis by `match`, the
  induction hypothesis is the self-call, a `.fin` helper takes a computed
  verdict as a parameter so it can be matched.
- Format laws (`hit_to_csv`, `dur_show`, `http_request`, `report_text`,
  ...) define the output text in LAWS.bend. Implement the lib function
  with the same structure as the LAWS helper; the proof is then an
  induction relating the two, like `all_same`/`value_go_same` in
  `proofs/dec.bend`.

## Checking behavior against Go

Every module with a byte format or a Go-defined behavior has a golden
test: a small Go program under `scripts/` writes `tests/golden/*`, and a
`tests/*.bend` compares. Run Go with the repo's module (`go run
./bend/scripts/gen-x.go` from the repo root).

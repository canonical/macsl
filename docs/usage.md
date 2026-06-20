# macsl — usage

## Build

```sh
eval $(opam env --switch=framac-coq8)   # Frama-C 32.1 + WP + Alt-Ergo/Z3
dune build
```

The plugin artifact is `_build/default/src/macsl.cmxs`.

## Running

macsl instruments the AST **in place**, as soon as it is computed, so any analysis that runs in the
same Frama-C invocation sees the generated assertions. The canonical command is simply:

```sh
frama-c file.c -macsl -wp -wp-rte
```

No `-then` / `-then-last` is required, and the input file may be in its usual position.

### Loading the plugin

If macsl is installed (via `dune install` / opam) it autoloads and `-macsl` is available directly.
When running from a build tree, load the `.cmxs`:

```sh
frama-c -load-module _build/default/src/macsl.cmxs -macsl -wp file.c
```

**Coexistence with an installed MetAcsl.** macsl reuses the shared ACSL builtins (`\prop`, `\written`,
…) if MetAcsl already declared them, and it registers only its own `happy` keyword (it does not squat
MetAcsl's `meta`). However, if *both* plugins try to *declare* those builtins in the wrong order you
get `already declared builtin \prop`. The robust way to run macsl by itself is to disable autoload and
load just what you need:

```sh
frama-c -no-autoload-plugins -load-plugin wp \
        -load-module _build/default/src/macsl.cmxs \
        -macsl -wp -wp-prover alt-ergo,z3 file.c
```

This is exactly what `tests/run.sh` does.

## The policy surface (Phase 0)

A HAPPY policy is a global ACSL annotation introduced by the `happy` keyword:

```c
/*@ happy \prop,
      \name(<string>),          // names the generated assertions
      \targets(<TS>),           // \ALL  |  {f, g, ...}
      \context(\writing),       // Phase 0: the writing context only
      P ;                       // an ACSL predicate; may mention \written
*/
```

- **`\written`** — inside `P`, the meta-variable `\written` denotes the address of the lvalue written
  at the current site (`&x` for `x = …;`). `\lhost_written` denotes the address of its base.
- **`\targets(\ALL)`** ranges over every defined function; **`\targets({f,g})`** over the named ones.
- The predicate is re-typed at each write site with `\written` bound to that site's lvalue, then
  emitted as `assert <name>: meta: P`.

Typical `P` is a separation (write-confinement) predicate:

```c
\separated(\written, &secret)          // no targeted function writes `secret`
\separated(\written, buf + (0 .. n-1)) // none writes into a buffer region
```

## Options

| Option | Effect |
|---|---|
| `-macsl` | enable HAPPY checking (in-place instrumentation) |
| `-macsl-list-targets` | report, per policy, how many sites it expanded over |
| `-macsl-number-assertions` | give each generated assert a unique numeric suffix |
| `-macsl-set p,...` | only process the named policies (default: all) |

## The non-vacuity discipline (read this)

A green WP run over a HAPPY policy means nothing unless the policy actually generated assertions and a
violating site is genuinely caught. Before trusting a result:

1. **Confirm instrumentation:** `frama-c file.c -macsl -print` must show `/*@ assert …: meta: … */`
   at the expected sites. macsl also **warns** (`zero-expansion`) when a policy matches no site —
   harden it to an error with `-macsl-warn-key zero-expansion=abort`.
2. **Run a negative control:** a deliberately-violating site's assert must be **unproved** by WP. See
   `tests/phase0/writing_neg.c` (the `secret = 42` write → `Proved goals: 4 / 5`).

This is the Gate-C non-vacuity rule applied to policies; it is what caught the original MetAcsl
misdiagnosis (see [design.md](design.md)).

## Limitations (Phase 0)

- Only `\context(\writing)`. `\reading`/`\calling`/invariants and the `\fguard`/`\tguard` guards are
  on the roadmap (`../happy-roadmap.md`).
- Temporal predicates over `\at(x, Before/After)` are not yet wired (no Before/After label
  machinery); Phase 0 targets separation/write-confinement predicates over `\written`.
- See `glossary/glossary.md` for terms.

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
      \context(<C>),            // \writing | \reading | \postcond | \precond
                                //   | \noninterference | \total | \guarded_by | \stable_check
      P ;                       // an ACSL predicate; may mention the context meta-variable
*/
```

- **`\context(\writing)`** (Phase 0, H-T) ranges over every **write** site; the meta-variable
  **`\written`** denotes the address of the written lvalue (`&x` for `x = …;`), `\lhost_written` its
  base.
- **`\context(\reading)`** (Phase 1, H-I1) ranges over every **read** site (each lvalue read inside an
  expression); the meta-variable **`\read`** denotes the address of the read lvalue, `\lhost_read` its
  base.
- **`\context(\postcond)`** (Phase 2, H-R) emits `P` as a **checked postcondition** (`check ensures`)
  on each target function — no per-site walk, no meta-variable. `P` is a whole predicate over globals
  and `\old(...)`; use it for function-level obligations (audit-log completeness, append-only). `Check`
  means WP must prove it but callers do not assume it.
- **`\context(\precond)`** (Phase 4, H-S) emits `P` as a **normal precondition** (`requires`) on each
  target (guarded) function. A normal `requires` is assumed by the body but **checked by WP at every
  call site** — so an unauthenticated caller fails *in the caller*. Use it for capability /
  check-before-use disciplines.
- **`\context(\noninterference)`** (Phase 5, H-I2) is the one **relational** (2-safety) property. Its
  tail is `\secret(p, ...)` (the secret parameters), *not* a predicate. macsl **synthesizes** a
  self-composition twin `f__selfcomp` that calls the target twice — public parameters shared, the
  secret ones distinct (`p_a`/`p_b`) — and asserts the two results are equal; WP discharges it from the
  target's functional contract.
- **`\targets(\ALL)`** ranges over every defined function; **`\targets({f,g})`** over the named ones;
  **`\targets(\diff(T1, T2))`** is set difference — e.g. `\diff(\ALL, {gate})` is "everything except
  `gate`" (used to exempt a privilege gate, H-E).
- For `\writing`/`\reading` the predicate is re-typed at each matching site (the meta-variable bound to
  that site) and emitted as `assert <name>: meta: P`; for `\postcond` it is emitted once per function
  as `check ensures <name>: meta: P`.

Typical `P` is a separation predicate (confinement):

```c
\separated(\written, &secret)          // write confinement: nothing WRITES `secret`
\separated(\written, buf + (0 .. n-1)) //   none writes into a buffer region
\separated(\read,    &secret)          // read confinement:  nothing READS `secret`  (H-I1)
```

For `\postcond` (H-R — audit-log completeness/immutability), supply a ghost log and write a
function-level obligation:

```c
//@ ghost int log_len = 0;
/*@ happy \prop, \name("audit"), \targets(\ALL), \context(\postcond),
      \old(disk) != disk ==> log_len > \old(log_len);   // every change is logged (completeness)
*/
/*@ happy \prop, \name("immut"), \targets(\ALL), \context(\postcond),
      \forall integer i; 0 <= i < \old(log_len) ==> logbuf[i] == \old(logbuf[i]);  // append-only
*/
```
macsl proves the program's logging *discipline*; that the log persists/ is signed on real storage stays
a trusted boundary for the risk study (roadmap GH1). The ghost log and the append code are yours;
macsl supplies the obligation that ties writes to log growth.

**Privilege monotonicity (H-E)** is the same `\postcond` mechanism plus a `\diff` exemption for the
gate — "no function except `sudo_gate` may end with higher privilege than it started":

```c
int proc_priv = 0;   // 0 = user, 1 = admin  (encode the lattice as ints, or add an axiomatic)
/*@ happy \prop, \name("noesc"),
      \targets(\diff(\ALL, {sudo_gate})),   // the gate is exempt; it may raise
      \context(\postcond),
      proc_priv <= \old(proc_priv);          // everyone else may only keep or lower privilege
*/
```
This catches the **confused deputy** — a non-gate function that raises privilege through *any* path
fails its monotonicity postcondition, in the function that took the shortcut.

**Check-before-use capabilities (H-S)** use `\precond`: a capability `session_ok`, granted only by a
trusted (declaration-only) `verify_token`, is required to call the guarded ops:

```c
//@ ghost int session_ok = 0;
/*@ assigns session_ok; ensures \result != 0 ==> session_ok == 1; */
int verify_token(int tok);                    // trusted: the identity check is NOT proved here

/*@ happy \prop, \name("authn"),
      \targets({sys_write, sys_unlink}),       // the guarded operations
      \context(\precond),
      session_ok == 1;
*/
```
WP then checks `session_ok == 1` at **every call site** of a guarded op: a path that reaches
`sys_write` without `verify_token` succeeding fails — in the caller. The identity check inside
`verify_token` is the trusted boundary the risk study carries (roadmap GH1); macsl proves only the
*discipline* around it. To additionally confine who may set `session_ok`, add an H-T policy
`\separated(\written, &session_ok)` over `\diff(\ALL, {verify_token})`.

**Noninterference (H-I2)** is the relational one — "the result does not depend on the secret":

```c
/*@ assigns \nothing; ensures \result == attempt; */
int check(int attempt, int stored);            // must carry a functional contract

/*@ happy \prop, \name("noleak"), \targets({check}),
      \context(\noninterference),
      \secret(stored);                          // `stored` is secret; other params + \result public
*/
```
macsl synthesizes `check__selfcomp(attempt, stored_a, stored_b)` (shared public input, distinct
secrets) with `assert ra == rb`, and WP proves/refutes it from `check`'s contract. A result that leaks
the secret (`ensures \result == attempt + stored`) makes the relational assert **red**.

> **Scope of H-I2 (honest).** The self-composition is *sequential* (two calls) and sound only because
> WP reasons through the target's **functional contract** — so the target **must carry an `ensures`**
> relating `\result` to its inputs. The observable is `\result` and the inputs are **parameters**:
> functions that communicate through globals or pointers (stateful noninterference, which needs store
> duplication) are **out of scope** — two sequential calls would share global state. `\declassify` is
> not yet implemented. Full relational verification (stateful, declassification) is future work; this
> covers the pure-result case (the `check_password`-style oracle).

> **What read confinement is and is NOT.** `\separated(\read, R)` proves no non-exempt code path
> *syntactically reads* region `R`. It is **not** noninterference — it says nothing about what an
> exempt reader does with the secret downstream. That stronger, relational property is **H-I2**
> (`happy-roadmap.md`), which needs self-composition; conflating the two would be a
> "coherent-and-wrong" claim.

## Concurrency (WS1 stage 1)

Two contexts begin to address GH4 (concurrency). They are **stage 1**: they establish a *local*
obligation at each shared access, **not** a full interleaving (rely-guarantee) argument. Read the bound
below before trusting any green result.

- **`\context(\guarded_by)`** (WS1) walks the target's **write sites** (the H-T walk) and injects, at
  each one, the *checked* assertion that a lock is held. You supply the obligation as the policy
  predicate, conventionally `\held(L)` (the macsl uninterpreted lock marker) or any user predicate
  `held(L)`:

  ```c
  //@ ghost int session_lock = 0;
  /*@ axiomatic Lock { predicate held(integer l) reads l; } */
  /*@ assigns session_lock; ensures held(session_lock); */   // trusted lock primitive
  void acquire_session(void);

  /*@ happy \prop, \name("session_guard"), \targets({touch_session}),
        \context(\guarded_by), held(session_lock);
  */
  ```
  WP must prove `held(session_lock)` at each write to the guarded state. A path that mutates the state
  without first acquiring the lock leaves the obligation **red, in the function that took the shortcut**
  — exactly like H-S. See `tests/phase7/race_session_{pos,neg}.c` (and `race_audit`, `race_priv`).

- **`\context(\stable_check)`** marks a check-then-act whose guard reads shared state: it injects, at
  the act's write site, the obligation that the guard value is **stable** to the act (conventionally
  `\stable(G)` / a user predicate `stable(G)`). This is the **marker that a real interleaving argument
  is OWED** — stage 1 does **not** discharge atomicity. See `tests/phase7/stable_check_{pos,neg}.c`.

`\held` and `\stable` are **uninterpreted** logic predicates — macsl declares them with no profile and
**no behavioural axiom** (the no-smuggled-axiom gate). The *establishing* hypothesis (a lock primitive
`ensures held(L)`, a snapshot primitive `ensures stable(G)`) is a **trusted declaration-only contract**,
the WS1 analog of `verify_token`: the rely-guarantee discharge of that assumption is **stage 2**.

> **CRITICAL bound — do not over-read a green `\guarded_by` suite.** Stage 1 establishes
> **lock-held-at-access ONLY**. It does **NOT** establish check-then-act **atomicity**, freedom from
> data races, or any interleaving property. A fully-green `\guarded_by` run is **not** "races handled":
> it says every guarded write is syntactically under its lock, nothing more. Consequently the
> **race-family crosswalk cell stays TRUSTED (never PROVED)** until **WS1 stage 2 (rely-guarantee)**
> lands. Treating a stage-1 green as race-safety is precisely the coherent-and-wrong this bound guards.

## Resource vocabulary (decision — Issue 4, settled)

`\fuel` is the **canonical step-budget spine**; `\cost` and `\resource` are its two **projections**, and
`\noninterference(\cost)` is the relational timing variant:

| Term | Meaning | Relation to `\fuel` |
|---|---|---|
| **`\fuel`** | step budget over WP-modelled loops (H-D bounded-work) | the spine |
| **`\cost`** | a **WP-discharged step bound from a supplied ranking** (declared ranking expression; closing VC proves it is never exceeded) | the *quantitative* projection of `\fuel` |
| **`\resource`** | allocations / recursion depth / handle counts **vs an explicit budget** | the *resource-pool* projection of `\fuel` |
| **`\noninterference(\cost)`** | equal public inputs ⇒ equal step count (a timing-channel 2-safety obligation) | the *relational timing* variant |

**Not implemented** (WS6 / Phase C — see `happy-roadmap.md` §4 and `ws-mechanisms.md` M-5/M-6); this
table only fixes the vocabulary so `usage.md` and `happy-roadmap.md` agree.

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

## Limitations (Phases 0–1)

- Contexts implemented: `\writing` (H-T), `\reading` (H-I1), `\postcond` (H-R/H-E), `\precond` (H-S),
  `\noninterference` (H-I2), `\total` (H-D), and `\guarded_by` / `\stable_check` (WS1 stage 1, see
  "Concurrency" above). `\calling`/invariants and the `\fguard`/`\tguard` guards are on the roadmap
  (`happy-roadmap.md`); `\fuel`/`\cost`/`\resource` are vocabulary-only (WS6, see above).
- **Read sites** = lvalues occurring inside expressions (rvalues, conditions, call args, return,
  and offset indices). A read of `R` through the *index* of a write target — e.g. `a[secret_i] = 0` —
  is covered (the index `i` is an expression); but address-taken reads (`&R`) are deliberately not
  counted (taking an address does not read the value).
- Temporal predicates over `\at(x, Before/After)` are not yet wired (no Before/After label
  machinery); macsl targets separation/confinement predicates over `\written` / `\read`.
- Read confinement is single-trace; true noninterference (H-I2) is future work.
- See `glossary/glossary.md` for terms.

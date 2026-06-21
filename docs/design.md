# macsl — design

## 1. Why macsl exists (the honest version)

macsl began as a fork to *fix* MetAcsl, which was believed to be a silent no-op on Frama-C 32.1: its
own test `monotony.c` appeared to generate no assertions and to prove vacuously. **Milestone M0 — run
the tool's own test — refuted that.** With the correct invocation MetAcsl works:

```sh
frama-c monotony.c -meta -then-last -wp      # file FIRST, -then-last
  [wp] Proved goals: 7 / 8                    # exactly the a=41 monotony violation unproved
```

The apparent "no-op" was two **invocation-order** mistakes, not a plugin bug:

1. `frama-c -meta -print monotony.c` — `-print` *without* `-then-last` prints the **original** project;
   MetAcsl builds the instrumented AST in a **copy** project (`generate` returns it, marked
   `~last:true`). So `-print` shows the raw `\meta::meta` annotation and looks empty.
2. `frama-c -meta -then-last -wp monotony.c` — the file is placed **after** `-then-last`, so it is
   consumed by the `-wp` stage; the `-meta` stage runs with **no input** → "0 properties" → vacuous.

So macsl is **not** "MetAcsl, fixed." Its reasons to exist are:

- **A footgun-free CLI** — the failure above is a real usability trap. macsl removes it by design (§2).
- **The rename HILARE → HAPPY** and the **STRIDE roadmap** (`happy-roadmap.md`).
- A small, self-contained codebase we control as the base for the STRIDE policy families.

## 2. The one design decision: instrument in place, after the AST is computed

MetAcsl builds the instrumented AST in a **separate project** and relies on `-then-last` to switch to
it before `-wp`/`-print`. That separate-project hand-off is the entire source of the footgun.

macsl instead:

- registers its pass with **`Ast.apply_after_computed`**, so it runs the moment the AST exists —
  *before* any analysis plugin's `-main` runs; and
- **mutates the current project in place** (`Visitor.frama_c_inplace` + `Annotations.add_code_annot`),
  adding only `assert` annotations — never a project copy, never a `set_current`.

Consequence: `frama-c file.c -macsl -wp` works in a single stage. macsl's hook fires when WP triggers
AST computation, the asserts land in the project WP is about to analyze, and WP discharges them. No
`-then`, no `-then-last`, no file-position sensitivity.

This is a pure **add-only** transformation (strip the generated asserts and you recover byte-identical
source) — the same faithfulness discipline used elsewhere in this project.

> We verified the ordering matters: an earlier version used `Boot.Main.extend`, and WP's `-main` ran
> *before* macsl's, so WP saw zero asserts (`No goal generated`). Moving to `apply_after_computed`
> fixed it. (Tests/`run.sh` would catch a regression: `neg/wp-catches` expects `4 / 5`.)

## 3. How a policy becomes assertions

1. **Parse** (`process_meta`/`process_property`). The `happy` global ACSL extension is registered with
   `Acsl_extension.register_global ~plugin:"macsl" "happy"`. Its typer reads
   `\prop, \name, \targets, \context(\writing), P`, and stores a `policy` whose `p_property` is a
   *closure* `kf -> substitution -> predicate` (delayed typing — the predicate is re-typed per site
   once `\written` is known). The meta-variables `\written`/`\read`/… are registered as logic
   **builtins** (idempotently — reused if MetAcsl already declared them) so `P` type-checks.
2. **Walk** — a `frama_c_inplace` visitor per target function, chosen by `\context`:
   - `\writing` (`writing_visitor`, H-T) matches write sites — `Set (lv,…)`, `Call (Some lv,…)`,
     `Local_init (vi,…)` — and binds `\written` to the written lvalue's address.
   - `\reading` (`reading_visitor`, H-I1) collects the lvalues *read* at each statement: an `in_exp`
     flag means `vlval` counts only lvals occurring inside expressions (not the write-target lval),
     `AddrOf`/`StartOf`/`SizeOf` are handled specially, results are deduped per statement
     (`Term_lval.Set`) and emitted in a `DoChildrenPost`. Binds `\read` to each read lvalue's address.
   Both bind via `Logic_utils.mk_logic_AddrOf`.
   - `\postcond` (H-R, H-E) does **not** walk sites: for each target function it types the whole policy
     predicate (`assoc = []`) in the post-state and injects it as a *checked* postcondition
     (`Logic_const.new_predicate ~kind:Check` + `Annotations.add_ensures kf [(Normal, ip)]`). `Check`
     means WP proves it but callers do not assume it. **H-E** (privilege monotonicity) is this context
     with a monotonicity predicate (`priv <= \old(priv)`) and the gate excluded from the target set.
   - `\precond` (H-S) injects `P` as a *normal* `requires` on each guarded function
     (`Annotations.add_requires kf [new_predicate P]`). A normal requires is assumed by the body but
     **checked by WP at every call site** — that automatic call-site obligation (no extra emission
     needed) is what catches an unauthenticated caller, in the caller.
   - `\noninterference` (H-I2) **synthesizes** a self-composition twin (`emit_selfcomp`): build a fresh
     `f__selfcomp` (`Cil.emptyFunction`) whose formals share the public params and split the
     `\secret(...)` params into `_a`/`_b`; body = two `Call`s to the target + `assert ra == rb`; then
     `Cfg.cfgFun`, `Globals.Functions.replace_by_definition`, append the `GFun` to the global list, and
     `Ast.mark_as_grown` (the add-a-function pattern from the kernel's `clone.ml`). WP analyzes the new
     function and discharges the relational assert from the target's functional contract. *(Note: in
     32.1 a `Call`'s callee is an `lhost`, not an `exp` — changed in Germanium.)*

   Targets form a small algebra resolved by `kfs_of_target`: `\ALL`, an explicit `{f,…}` set, and
   `\diff(T1,T2)` (set difference) — `\diff(\ALL,{gate})` is how H-E exempts the privilege gate.
3. **Emit** (`emit_at`). The closure is instantiated with that binding, trivially-true results are
   dropped, and the predicate is added as `AAssert ([], toplevel_predicate ~kind:Assert P)` under the
   `macsl` `Emitter`, named `<policy>: meta: …`.
4. **Discharge.** WP (run in the same invocation) turns each assert into a VC; Alt-Ergo/Z3 prove the
   satisfied sites and fail the violating ones.

## 4. Non-vacuity, built in

The whole point is that a green means something, so macsl makes vacuity loud:

- `-macsl-print` shows the instrumented AST (instrumentation must be *visible*).
- a policy that expands to **0** assertions raises the `zero-expansion` warning (promote to abort with
  `-macsl-warn-key zero-expansion=abort`).
- every test ships as a **prove/fail pair**: `writing_pos.c` (all green) and `writing_neg.c` (the
  violating write red). A green with no red negative control is inadmissible.

## 5. Module map

Single module, `src/macsl.ml`:

| Section | Responsibility |
|---|---|
| `Self`, options | `Plugin.Register`; `-macsl`, `-macsl-list-targets`, `-macsl-number-assertions`, `-macsl-set`; the `zero-expansion` warn category |
| types | `context` (Writing), `target`, `replaced_kind`, `policy` |
| builtins | idempotent `Logic_builtin.register` of the keywords |
| custom typer | `meta_type_predicate`/`meta_type_term` — substitute the meta-variables; `delay_prop` |
| parser | `process_property`/`process_meta`; `register_parsing` (the `happy` extension) |
| instrumentation | `instantiate` (per-site assert) + `emit_ensures` / `emit_requires` (per-function contract) + `emit_selfcomp` (synthesize a twin); `writing_visitor` (H-T), `reading_visitor` (H-I1), `\postcond` fold (H-R, H-E), `\precond` fold (H-S), `\noninterference` fold (H-I2); `kfs_of_target` (`\ALL`/set/`\diff`), `run_policy` (dispatches on `\context`) |
| entry | `Ast.apply_after_computed run` |

## 6. Deviations from `macsl-impl.md`

`macsl-impl.md` was written under the "MetAcsl is a no-op" premise. The implementation differs where M0
changed the facts:

- **No "fix the no-op."** The acceptance test is a *new* write-confinement property
  (`writing_neg.c` → `4/5`), not "make `monotony.c` go red" (MetAcsl already does that).
- **`apply_after_computed`, not `Boot.Main.extend`** — the impl plan's in-place idea was right; the
  concrete hook is the after-AST-computed one, which is what actually removes the footgun.
- **`happy` only, no `meta` alias** — so macsl coexists with an installed MetAcsl.
- Scope trimmed to `\writing` + separation predicates for Phase 0; the rest is `happy-roadmap.md`.

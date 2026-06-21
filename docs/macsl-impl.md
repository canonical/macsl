# `macsl` — implementation plan (Phase 0)

> **⚠ CORRECTED 2026-06-20 (milestone M0) — read `docs/design.md` §1 for the truth.**
> This plan was written believing MetAcsl was a *silent no-op* on 32.1. **It is not** — that was an
> invocation-order mistake (file after `-then-last`; `-print` without `-then-last`). MetAcsl works:
> `frama-c monotony.c -meta -then-last -wp` ⇒ `7/8`, the violating write red. So macsl's purpose is the
> **footgun-free in-place CLI** (+ the HAPPY rename + STRIDE), not "fix a no-op". Sections below that
> say "no-op" are superseded by `docs/design.md`; the in-place architecture they describe is still the
> implemented one (via `Ast.apply_after_computed`, not `Boot.Main.extend`).

Implements the spec `macsl.md` (kept in the parent `use-frama-c` working tree). This document lives in
the **`macsl/` git repo** and describes how to build the Phase-0 plugin: the MetAcsl invocation footgun
macsl removes, the in-place architecture, the module layout with grounded code skeletons, the build,
and the milestone/test plan.

**Platform:** Frama-C **32.1 (Germanium)**, OCaml 5.x. **Grounding:** read directly from the MetAcsl
0.10 source (`$OPAM/framac-coq8/.opam-switch/sources/frama-c-metacsl.0.10/`) and the 32.1 kernel odoc
(`$OPAM/framac-coq8/lib/frama-c/kernel/.../acsl_extension.mli`). Every API name below was checked
against that tree on 2026-06-20; re-confirm if the switch moves.

---

## 0. The acceptance test (as implemented)

> Originally stated as "make MetAcsl's `monotony.c` go red" — but M0 showed MetAcsl already does that.
> The real Phase-0 acceptance test is a **write-confinement** property checked **in one stage, no
> `-then-last`** (the footgun-free CLI):

```sh
frama-c file.c -macsl -print   # MUST show /*@ assert <name>: meta: \separated(...) */ at each write
frama-c file.c -macsl -wp      # a function writing the protected region -> that assert UNPROVED
```

Achieved: `tests/phase0/writing_neg.c` ⇒ `Proved goals 4/5` (the `secret = 42` write red),
`writing_pos.c` ⇒ `4/4`. See `docs/design.md` and `tests/run.sh` (6/6).

---

## 1. The MetAcsl invocation footgun macsl removes (was mis-filed as a "no-op")

> **M0 correction:** MetAcsl is *not* a no-op (see `docs/design.md` §1). The code below is real, but it
> is *why you must use `-then-last`*, not a fatal defect. macsl sidesteps the whole class by
> instrumenting in place.

`meta_run.ml`:

```ocaml
let generate flags =
  let prj = Project.current () in
  let new_prj = Project.create_by_copy ~last:true prj_name in
  Project.set_current new_prj;          (* (a) annotate the COPY *)
  ...
  Meta_annotate.annotate flags all_mp tables;   (* asserts go into new_prj *)
  ...
  Project.set_current prj;              (* (b) RESTORE the original project *)
  final_prj                            (* (c) return the annotated copy *)

let register () =
  if Enabled.get () then (
    Ast.compute ();
    ... ignore @@ generate flags ;     (* (d) DISCARD the returned annotated project *)
    Self.feedback "Successful translation";
    Enabled.set false )

let () = Boot.Main.extend register
```

The instrumented AST is built in `new_prj`, but step **(b)** restores the original project and step
**(d)** ignores the returned `new_prj`. After `-meta` runs, **the current project is the original,
un-instrumented one** — so a plain `-print`/`-wp` sees no asserts. The documented workaround is
`-meta -then-last -wp`, which relies on `-then-last` selecting the `~last:true` copy; on Frama-C 32.1
that hand-off also fails (the bug report observes `Will process 0 properties` + vacuous `4/4` even
*with* `-then-last`). The exact 32.0→32.1 mechanism by which `-then-last` stops selecting the copy is
the one thing still to pin down — **milestone M0** — but it does not change the design, because:

> **The fix is to never put the instrumented AST in a non-current project.** Phase-0 `macsl`
> instruments the **current project in place** and emits no copy. Then `-macsl -wp` works with no
> `-then-last`, and the entire fragile project-handoff class of bug is gone.

---

## 2. Decisive design decision — in-place instrumentation

MetAcsl copies the project because, in deduction mode, it injects ghost code and wants the original
preserved. **Phase-0 `macsl` does none of that:** it only *adds* `assert` annotations at existing
program points. That is a pure, **add-only** instrumentation — the same discipline as the squeeze
loop's faithfulness gate (strip the added ACSL and you get byte-identical source). So:

- **Run mode:** mutate the current project's AST in place via `Annotations.add_code_annot` / a
  `Visitor.frama_c_inplace` pass. No `Project.create_by_copy`, no `set_current`, no `-then-last`
  dependency.
- **Consequence:** `frama-c -macsl -wp file.c` instruments then proves in one project. `-macsl
  -then-last -wp` still works (the "last" project is just the current one) but is no longer required.
- **Tradeoff accepted:** the in-memory AST now carries the generated asserts (fine — we are checking,
  not emitting a pristine artifact; `-macsl-print` is how you inspect them). The original *source
  file* is never modified.
- **Deferred:** the copy/ghost-code path is only needed for deduction mode and 2-safety
  self-composition, both out of Phase 0 (spec §10). When those land (Phase 2+), reintroduce a copy
  **and install it as current** (the bug MetAcsl failed to do), or use `File.create_rebuilt_project_*`
  and switch to it explicitly.

---

## 3. Repository layout (`macsl/`)

```
macsl/
├── dune-project
├── macsl.opam                 # opam package metadata (frama-c 32.1 dep, pinned)
├── README.md
├── src/
│   ├── dune                   # the plugin library + (plugin ...) stanza
│   ├── macsl.ml               # entry point: Boot.Main.extend
│   ├── macsl_options.ml/.mli  # Plugin.Register + -macsl* options + warn categories
│   ├── macsl_parse.ml/.mli    # Acsl_extension registration + typer -> typed policy; gathered store
│   ├── macsl_types.ml         # the typed policy record + context/guard ADTs
│   ├── macsl_dispatch.ml/.mli # group policies by (context, target) for efficient annotation
│   ├── macsl_annotate.ml/.mli # THE CORE: per-context site matching, meta-var subst, guard, emit
│   ├── macsl_subst.ml/.mli    # meta-variable substitution (\written/\read/\called -> concrete term)
│   ├── macsl_run.ml/.mli      # pipeline: Ast.compute, annotate in place, list-targets, vacuity warn
│   └── macsl_utils.ml/.mli    # StrSet, helpers
└── tests/
    ├── dune                   # ptests wiring
    └── phase0/
        ├── monotony.c         # ported from MetAcsl; the smoking-gun regression
        ├── writing_pos.c  writing_neg.c
        ├── reading_pos.c  reading_neg.c
        ├── calling_pos.c  calling_neg.c
        ├── fguard.c  tguard.c  zero_targets.c
        └── oracle/            # expected outputs
```

Module names mirror MetAcsl (`meta_*` → `macsl_*`) so anyone who knows MetAcsl can navigate, and so a
later upstream-diff is legible. Phase 0 **drops** `meta_deduce` (Prolog), `meta_simplify` (optional),
and most of `meta_bindings` (ghost code) — see §10.

---

## 4. Toolchain & build

Build in a **separate opam switch** so the pinned proof toolchain (`framac-coq8`: frama-c 32.1 /
why3 1.8.2 / coq 8.20.1) is never disturbed. Installing/building a plugin against `frama-c.kernel`
does not perturb the pin (confirmed for MetAcsl itself), but isolate anyway.

`dune-project`:
```lisp
(lang dune 3.0)
(using dune_site 0.1)
(generate_opam_files true)
(package (name macsl) (synopsis "Working MetAcsl fork — the HAPPY policy framework")
 (depends (frama-c (= 32.1))))
```

`src/dune`:
```lisp
(library
 (name macsl)
 (public_name macsl.core)
 (flags (:standard -open Frama_c_kernel))   ; Cil_types/Plugin/Visitor/… unqualified
 (libraries frama-c.kernel)
 (optional))
(plugin (name macsl) (libraries macsl.core) (site (frama-c plugins)))
```

Build & smoke:
```sh
opam switch create macsl-dev 5.x ; eval $(opam env --switch=macsl-dev)
opam install frama-c.32.1
dune build
frama-c -macsl -print tests/phase0/monotony.c
```

---

## 5. Module skeletons (grounded against 32.1)

### 5.1 `macsl_options.ml` — registration, options, warn categories
Mirrors `meta_options.ml`. `-macsl*` replaces `-meta*`; keep `meta` as a hidden alias only if needed.
```ocaml
module Self = Plugin.Register (struct
  let name = "macsl"
  let shortname = "macsl"
  let help = "HAPPY policy checker — a working MetAcsl fork"
end)

module Enabled            = Self.False (struct let option_name="-macsl" let help="run macsl" end)
module Print_instrumented = Self.False (struct let option_name="-macsl-print"
                                          let help="print the AST with generated asserts" end)
module Number_assertions  = Self.False (struct let option_name="-macsl-number-assertions"
                                          let help="give each generated assert a unique id" end)
module List_targets       = Self.False (struct let option_name="-macsl-list-targets"
                                          let help="list each policy's expansion sites" end)
module Targets            = Self.String_set (struct let option_name="-macsl-set"
                                          let arg_name="p,..." let help="only these named policies" end)

(* a vacuous policy must SHOUT, not pass silently (spec §8) *)
let zero_expansion_wkey = Self.register_warn_category "zero-expansion"
let () = Self.set_warn_status zero_expansion_wkey Log.Wabort   (* -macsl-warn-key for override *)
```

### 5.2 `macsl_types.ml` — the typed policy
```ocaml
type context =
  | Writing | Reading | Calling
  | Strong_invariant | Weak_invariant

type guard =
  | Fguard of Kernel_function.t list * Cil_types.predicate   (* P must hold inside these fns *)
  | Tguard of Cil_types.predicate                            (* condition on the meta-variable *)

type target = All | Funcs of Kernel_function.t list

type policy = {
  name      : string;
  target    : target;
  context   : context;
  guards    : guard list;
  predicate : Cil_types.predicate;   (* refers to \written/\read/\called via logic builtins *)
  loc       : Cil_types.location;
}
```

### 5.3 `macsl_parse.ml` — ACSL extension registration + typer
MetAcsl registers exactly this way (`meta_parse.ml:476`); the typer signature is the kernel's
`extension_typer = typing_context -> location -> lexpr list -> acsl_extension_kind` (from
`acsl_extension.mli`). The typer parses the `\prop, \name(..), \targets(..), \context(..), P`
command, builds a `Macsl_types.policy`, **stashes it in projectified state**, and returns a trivial
`Ext_terms [..]` (the kernel only needs a valid extension kind back — the real payload is the stashed
policy, exactly as MetAcsl's `gathered_props` ref does).
```ocaml
(* \written / \read / \called must be known to the logic typer: register as builtins, like MetAcsl *)
let register_builtins () =
  List.iter Logic_builtin.register
    [ {bl_name="\\written"; bl_labels=[]; bl_params=[]; bl_profile=[]; bl_type=Some (Lvar "set")};
      (* \read, \called similarly; predicate builtins get bl_type=None *) ]

let process_happy (tc:typing_context) (loc:location) (l:lexpr list) : acsl_extension_kind =
  match l with
  | cmd :: rest ->
    (match cmd.lexpr_node with
     | PLvar "\\prop" | PLvar "\\policy" ->
       let p = parse_policy tc loc rest in          (* builds Macsl_types.policy *)
       Gathered.add p;                              (* State_builder.Ref/List_ref, dep Ast.self *)
       Ext_terms [Logic_const.tstring ~loc p.name]
     | _ -> tc.error loc "macsl: invalid command")
  | [] -> tc.error loc "macsl: missing command"

let register () =
  register_builtins ();
  Acsl_extension.register_global ~plugin:"macsl" "happy" process_happy true;
  Acsl_extension.register_global ~plugin:"macsl" "meta"  process_happy true   (* compat alias *)
```
`Gathered` is `State_builder.List_ref(...)` over `Macsl_types.policy` with `dependencies=[Ast.self]`
so the parsed policies are projectified and cleared if the AST is rebuilt.

### 5.4 `macsl_subst.ml` — bind the meta-variable
At each matched site the meta-variable in `predicate` is replaced by the concrete term: `\written` →
the written lval's address/term; `\read` → the read term; `\called` → the callee. Implement as a
`Cil.genericCilVisitor` over the predicate that rewrites the builtin application node to the concrete
`term`. (MetAcsl does this in its annotate/dispatch phase via the bindings machinery.)
```ocaml
val subst_written : Cil_types.term -> Cil_types.predicate -> Cil_types.predicate
val subst_read    : Cil_types.term -> Cil_types.predicate -> Cil_types.predicate
val subst_called  : Cil_types.term -> Cil_types.predicate -> Cil_types.predicate
```

### 5.5 `macsl_annotate.ml` — THE CORE (per-context matching + emit)
One `Visitor.frama_c_inplace` per dispatched (context, target) group. Emission mirrors
`meta_annotate.ml:136-140`: build an `AAssert` code annotation with `Logic_const.new_code_annotation`
and add it with `Annotations.add_code_annot emitter ~kf stmt annot`.
```ocaml
let emitter =
  Emitter.create "macsl" [Emitter.Code_annot] ~correctness:[] ~tuning:[]

let mk_assert ~kf ~stmt ~name (p:predicate) =
  let named = { p with pred_name = name :: p.pred_name } in
  let annot =
    Logic_const.(new_code_annotation (AAssert ([], toplevel_predicate named))) in
  Annotations.add_code_annot emitter ~kf stmt annot

class writing_visitor (pol:policy) ~kf = object(self)
  inherit Visitor.frama_c_inplace
  method! vstmt_aux s =
    (match s.skind with
     | Instr (Set (lv, _, loc) | Call (Some lv, _, _, loc)
              | Local_init (_, _, loc)) ->        (* a write site *)
       let written = Logic_utils.lval_to_term_lval ... |> Logic_const.taddrof ... in
       let p = Macsl_subst.subst_written written pol.predicate in
       let p = Macsl_guard.apply pol.guards ~kf p in   (* §6 *)
       mk_assert ~kf ~stmt:s ~name:pol.name p
     | _ -> ());
    Cil.DoChildren
end
```
- `\reading` → a `vexpr`/`vlval` override collecting each read lval at the current statement.
- `\calling` → match `Call (_, fexp, _, _)`; bind `\called` to the callee term.
- invariants → emit at function entry (`Kernel_function.find_first_stmt`) / each loop head.

Run a visitor only over the `target` functions (`Globals.Functions.iter` filtered, or directly the
`Funcs` list), counting emissions per policy for the vacuity check.

### 5.6 `macsl_run.ml` — the pipeline (in place, no copy)
```ocaml
let run () =
  if Macsl_options.Enabled.get () then begin
    Ast.compute ();
    let pols = Macsl_parse.Gathered.get () in
    let pols = filter_by_set pols (Macsl_options.Targets.get ()) in
    Self.feedback "Will process %d policies" (List.length pols);
    let groups = Macsl_dispatch.dispatch pols in
    List.iter (fun g ->
      let n = Macsl_annotate.annotate_group g in     (* returns #asserts emitted *)
      if n = 0 then
        Self.warning ~wkey:Macsl_options.zero_expansion_wkey
          "policy %s expanded to 0 assertions" (Macsl_dispatch.name g);
      if Macsl_options.List_targets.get () then Macsl_dispatch.print_targets g
    ) groups;
    if Macsl_options.Print_instrumented.get () then
      File.pretty_ast ();                            (* the instrumented current AST *)
    Self.feedback "Successful translation (%d policies)" (List.length pols)
    (* NOTE: no Project copy, no set_current, no -then-last needed. WP runs next on THIS project. *)
  end

let () = Boot.Main.extend run
```
`File.pretty_ast ()` (or `Printer.pp_file`) prints the **current**, now-instrumented AST, so the
generated asserts are visible. The `Successful translation` line is only emitted *after* real emission,
and a zero-expansion policy warns (or aborts) under the warn status.

---

## 6. Guard semantics (`macsl_guard.ml`)

- **`\fguard(F, P)`** — when emitting inside a function in set `F`, the obligation becomes `P`
  (the relaxed local rule) instead of the global predicate; outside `F`, the global predicate stands.
  Implementation: in the annotate visitor, if `kf ∈ F`, substitute the per-function predicate.
- **`\tguard(Q)`** — a condition on the meta-variable that *guards* the assertion: emit
  `Q ==> predicate` (canonical `calling` example: `\tguard(\called != uncalled)`). Implementation:
  `Logic_const.pimplies (q, p)` after meta-variable substitution (MetAcsl builds the same implication,
  cf. `meta_annotate.ml:347,466`).

Guards are what give a global policy *teeth without false alarms*: the trusted writer is excused, the
forbidden call is constrained, and every other site must still discharge the predicate.

---

## 7. Non-vacuity instrumentation (spec §8, built in)

| Mechanism | Where | Catches |
|---|---|---|
| `-macsl-print` shows generated `assert` | `macsl_run` `File.pretty_ast` | a policy that emitted nothing (instrumentation must be visible) |
| zero-expansion **warning→abort** | `macsl_run` per group | a policy whose `\targets` match nothing |
| `-macsl-list-targets` (count + sites) | `macsl_dispatch` | silent under-expansion |
| `-macsl-number-assertions` | `mk_assert` naming | identifying *which* obligation is the red one |
| **negative-control test** (mandatory) | `tests/phase0/*_neg.c` | "green with no teeth" |

A `Successful translation` + `Proved goals N/N` is admissible **only** after `-macsl-print` shows the
asserts *and* the matching `_neg.c` obligation is red. This is the Gate-C non-vacuity rule for policies.

---

## 8. Tests (ptests, `tests/phase0/`)

- **`monotony.c`** — ported verbatim from MetAcsl. Oracle: `-macsl -print` contains
  `assert …: meta: …` at the `a = 41` write; `-macsl -wp` reports it **Unknown**. (The regression that
  is vacuously green under MetAcsl today.)
- **`writing_{pos,neg}.c`** — isolation `\separated(\written, R)`: pos = no site writes `R` (all
  Valid); neg = one function writes into `R` (that assert red).
- **`reading_{pos,neg}.c`**, **`calling_{pos,neg}.c`** — analogous for `\read` / `\called`.
- **`fguard.c`** — trusted writer in `F` allowed (no alarm); untrusted writer flagged.
- **`tguard.c`** — `\tguard(\called != uncalled)`: only the guarded call constrained.
- **`zero_targets.c`** — a policy matching nothing ⇒ zero-expansion abort (oracle = the warning).

Harness: Frama-C **ptests** driven by `dune test`; oracles under `tests/phase0/oracle/`; update with
the ptests `-update` target. Each `run.config` header sets `OPT: -macsl -macsl-number-assertions
-then-last -wp -wp-prover alt-ergo`.

---

## 9. Implementation milestones

| M | Goal | Done when |
|---|---|---|
| **M0** | Run MetAcsl's own test before assuming it is broken | DONE: `monotony.c` works with `-then-last` (7/8) — the "no-op" was invocation order, not a bug (see `docs/design.md` §1) |
| **M1** | Plugin skeleton loads | `macsl_options` + `macsl.ml`; `frama-c -macsl` runs, prints "Will process 0 policies" |
| **M2** | Parse a policy | `macsl_parse` registers `happy`/`meta`; a `\writing` policy parses into `Gathered`; `-macsl-list-targets` shows its target set |
| **M3** | Emit in place (the fix) | `\writing` `\separated(\written,R)` produces an `assert` at each write; `-macsl-print` shows it; **`monotony.c` `-macsl -wp` goes RED** ← acceptance test |
| **M4** | All contexts + guards | `\reading`, `\calling`, `\fguard`, `\tguard`; pos/neg test pairs pass |
| **M5** | Vacuity hardening | zero-expansion abort; `-macsl-number-assertions`; list-targets counts |
| **M6** | CI green | full `tests/phase0` ptests suite green with oracles; README usage |

M3 is the milestone that maps to spec §11 items (2)+(3) — the point at which Tier 3 is genuinely
unblocked.

---

## 10. Explicitly deferred (Phase 0 out of scope)

- **Deduction mode** (`meta_deduce` / SWI-Prolog, `-macsl-set` deduce). WP-checked mode only.
- **Project-copy / ghost-code** path (`meta_bindings` ghost code, `Separate_annots`). Reintroduce —
  *and install the copy as current* — only when 2-safety self-composition needs it.
- **`\reading` confidentiality as true non-interference** (2-safety) — Phase 2+; Phase 0's `\reading`
  only checks single-trace access predicates (spec §5 boundary).
- **STRIDE breadth beyond Tampering/Elevation** (spec §7 Phase 1+).

---

## 11. Risks / open questions

- **M0 mechanism** — confirm whether 32.1's `-then-last` no longer selects `create_by_copy ~last:true`
  or whether `register`'s restore is the sole cause. (Does not block in-place design.)
- **`Acsl_extension` typer return** — `process_happy` must return a valid `acsl_extension_kind`;
  MetAcsl returns `Ext_terms [tstring name]`. Confirm nothing downstream in 32.1 requires the
  extension payload to *be* the property (we use the side-channel `Gathered` store, as MetAcsl does).
- **Meta-variable as a logic builtin** — `\written`/`\read`/`\called` must type-check inside `P`.
  MetAcsl registers them via `Logic_builtin.register`; confirm the `logic_info`/`builtin_logic_info`
  record shape on 32.1 (the most fiddly typing detail).
- **`toplevel_predicate` constructor** — 32.1 `AAssert` takes `string list * toplevel_predicate`;
  confirm `Logic_const.toplevel_predicate` (and `~kind` if needed) against the odoc.
- **Address-of for `\written`** — for scalar writes, `\written` should be `&lv` (an address/zone) so
  `\separated` types; confirm `Logic_const`/`Logic_utils` term-building for the lval→address term.
- **Upstream/licensing** — MetAcsl is LGPL-2.1; the fork inherits it. Decide attribution/diff posture.
```

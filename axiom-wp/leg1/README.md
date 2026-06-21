# Leg 1 (semantic Why3↔Coq) — `Memory.separated_trans`, `Memory.included_trans`

Leg 1 of the dual-TP (`../../docs/frama-c-dual-tp-spec.md` §4, §5.4a) anchors each Coq
realization lemma to **what Why3 means**, by proving — inside Coq, against the
Cohen–Johnson-Freyd denotational semantics — that the lemma is the denotation of its
Why3 formula (`L_Coq ⟺ formula_rep … ⟦Why3(L)⟧`).

**CLOSED for two `Memory` lemmas** (`Model.v`, both axiom-clean — `Print Assumptions` =
the why3-semantics framework's standard base only):
- `sep_trans_faithful` : `formula_rep … sep_trans_fmla = true ↔ sep_trans_prop`;
- `included_trans_faithful` : `formula_rep … inc_trans_fmla = true ↔ included_trans_prop`.

`included_trans` reuses the same model + helper lemmas as `separated_trans` (it has three
`included` predicate applications rather than one `included` + two `separated`). The build
path and ground-truth notes below are kept for the record; see the Status checklist.

## 1. Ground truth `Why3(L)` — extracted, and it matches both proofs
`why3-separated_trans.mlw` is the **verbatim** WP Why3 source
(`$(frama-c -print-share-path)/wp/why3/frama_c_wp/memaddr.mlw`, `lemma
separated_trans` @ line 107). By inspection the three statements are the **same
proposition** (variable renaming `lp,lq,lr ↔ a,b,c`):

| | `included` | `separated` | lemma |
|---|---|---|---|
| **Why3** (memaddr.mlw) | `lp>0 → (lq≥0 ∧ base p=base q ∧ off q≤off p ∧ off p+lp≤off q+lq)` | `lp≤0 ∨ lq≤0 ∨ base p≠base q ∨ off q+lq≤off p ∨ off p+lp≤off q` | `inc p lp q lq → sep q lq r lr → sep p lp r lr` |
| **Coq** (`../coqwp/Memory_hardened.v`) | identical | identical | identical |
| **Lean** (`../leanwp/Memory.lean`) | identical | identical | identical |

So the pilot's Coq+Lean twins are already faithful to the WP ground truth (an
eyeball confirmation today; leg 1 makes the Why3↔Coq half *mechanical*, leg 2 the
Coq↔Lean half). The `[ … ]` in the lemma is an **SMT trigger** — a prover hint,
semantically irrelevant; the denotation ignores it.

## 2. Fragment coverage (spec §5.8 gating check) — **PASS**
`Why3(separated_trans)` is first-order and lands inside the formalized fragment:
- **record type** `addr = { base:int; offset:int }` → a one-constructor ADT with
  field projections (the semantics supports ADTs + `match_rep`);
- **defined predicates** `included`/`separated` (definitional unfolding);
- **quantifiers** (`∀ p q r : addr, ∀ lp lq lr : int`), connectives
  (`→ ∨ ∧ ¬(=)`), and **`int`** arithmetic (`+ ≤ > =`);
- no higher-order, no exotic features; trigger ignored.

⇒ This lemma is **eligible** for leg-1 certification (no single-prover fallback
needed). Coverage must still be re-checked per lemma for the rest of Memory/Vset
and especially the `R`-based theories.

## 3. Build feasibility — FEASIBLE, heavy, and version-split (grounded)
The vendored notes (`/tmp …/docs/why3-semantics/`, mirrored from
`github.com/joscoh/why3-semantics`) are **three leaf files**; `formula_rep`
transitively needs the **full** project (`Syntax`, `Types`, `Interp`,
`FullInterp`, `Substitution`, `Typechecker`, …) — the `formula`/`term` inductive
itself lives in the un-vendored `Syntax.v`. Probed facts:
- the semantics targets **Rocq 9.x** (`Require Import Stdlib.…`, the post-8.21
  stdlib namespace) and the **Equations** plugin;
- `rocq-prover` **9.0.0–9.1.1** and **`coq-equations`** are installable in this
  opam universe; the upstream repo is reachable (pin a commit, e.g. current HEAD).

**Update — no version split (good news).** The upstream repo has a **`coq-8.20`
branch**: the semantics builds under **Coq 8.20.1** (Equations 1.3.1+8.20, MathComp
2.3.0, std++ 1.11.0, coq-ext-lib 0.13.0) — the *same* Coq as coqwp. So leg 1 does
NOT need a separate Rocq-9 dev; the re-stated Memory defs (or the coqwp ones) live
in one Coq world. `Types.v` uses `HB.instance` (Hierarchy Builder), so **MathComp
2.x is required** (1.x won't do — checked).

**RESOLVED (2026-06-21) via the Rocq-9.0 route — see `BUILD.md` and the Status checklist.**
The blocker below is the *Coq-8.20* diagnosis (kept for the record); leg 1 now builds on an
isolated Rocq-9.0 switch where rocq-elpi 3.4.0 builds cleanly. The remaining Coq-8.20 analysis:

**BLOCKED — coq-elpi cannot be added to the pinned Coq-8.20 switch.** Re-diagnosed
precisely (2026-06-21) in the `framac-coq8` switch itself (which is healthy: it
builds native `.cmxs`, and `coq-interval`'s native ML-plugin loads fine — so the
earlier "environmental, version-independent" note was imprecise). The real blocker
is a **two-way dependency trap** around the Coq-8.20 pin:

- With **Coq held at 8.20.1**, opam installs **rocq-elpi 3.2.0**, whose dune build
  **does not stage `elpi_plugin.cmxs`** into the install tree; then `theories/elpi.v`'s
  `Declare ML Module` makes `coqc` (native) fail with
  `System error: ".../rocq-elpi/elpi/elpi_plugin.cmxs: No such file or directory"`.
  This is a rocq-elpi-3.2.0-on-coq-core-8.20 **native-plugin staging bug**, *not* a
  missing OCaml/native capability (`supports_shared_libraries: true`; `.cmxs` builds;
  interval loads). The 3.2.0 package is the transitional Rocq-9-era one.
- The genuinely **Coq-8.20-targeted coq-elpi 2.x** (e.g. 2.5.2) *would* build, but
  installing it **downgrades `elpi` 3.4.2→2.0.7 + yojson/atd** and **recompiles
  `frama-c` 32.1 + `frama-c-metacsl`** — i.e. it perturbs the pinned coqwp/frama-c
  world. Not acceptable in this switch.
- The modern **coq-elpi 3.4.0** needs **Rocq 9.0.1**, upgrading Coq off 8.20 →
  breaks the entire 8.20-pinned coqwp + frama-c stack. Not acceptable.

Since MathComp 2.x → Hierarchy Builder → coq-elpi, this transitively blocks the
semantics, hence `formula_rep`, hence the leg-1 obligation. **Resolution path:**
build leg 1 in a **dedicated, isolated switch** (or the **Coq Platform** bundle,
which ships coq-elpi + MathComp 2.x prebuilt and coherent) — never in `framac-coq8`,
which must stay pinned for the coqwp/frama-c work. Then resume at §4–§5. Everything
*else* for leg 1 is grounded and ready.

## 4. The obligation, and a caveat
- Statement: `separated_trans_Coq ⟺ formula_rep γ pd pf vt vv ⟦sep_trans⟧ Hty`
  (or via `valid`/`satisfies` from `Logic.v`), with `included`/`separated`
  reflected as defined predicate symbols and `addr`/`int` interpreted per the
  theory.
- **`closed_satisfies_rep` does NOT apply here.** That collapse (validity →
  boolean `decide`) is for *closed integer VCs* (the SMT-escalated ACSL class).
  `separated_trans` is universally quantified over abstract `addr`/`int`, so prove
  the `⟺` against `formula_rep`-as-`Prop` by reasoning, not by evaluation
  (spec §5.4a, §10).

## 5. Status of the steps
1. Toolchain (Rocq-9.0 isolated switch `dualtp-leg1-r9`): **DONE** (`BUILD.md`).
2. why3-semantics vendored + built (`rocq-9.0` branch, pinned `d75ba4c`): **DONE**.
3. AST→`formula` bridges (`sep_trans_fmla`/`inc_trans_fmla`, `gamma_valid`, `*_typed`): **DONE**.
4. Bridge **round-trip check** (pretty-print the `formula` back through Why3, diff vs
   `why3-separated_trans.mlw`, spec §5.8): **optional hardening, not yet done**.
5. The §4 obligation `Coq(L) ⟺ formula_rep …`: **DONE** — `sep_trans_faithful` and
   `included_trans_faithful`, axiom-clean (`Print Assumptions` = the framework's standard base).
6. CI: the `leg1` job in `.github/workflows/axiom-wp.yml` builds `Model.vo` (so the proofs
   are gated) and guards against `Admitted`/`admit`/`Axiom`/`Abort`. With leg 2 (`dualtp/`)
   also passing, `Memory.separated_trans` and `Memory.included_trans` are **dual-TP certified**.

## Status
- [x] Ground-truth `Why3(L)` extracted; Why3≡Coq≡Lean confirmed by inspection.
- [x] Fragment coverage: **PASS** (in-fragment); MathComp 2.x required (`HB.instance`).
- [x] Toolchain: **coq-8.20 branch found** — semantics builds on Coq 8.20.1 (no
      Rocq-9 split). Coq + Equations + std++ + ext-lib install fine.
- [x] **Semantics built — blocker RESOLVED via the Rocq-9.0 route** (2026-06-21).
      Isolated switch `dualtp-leg1-r9` (rocq-elpi **3.4.0** / HB 1.10.2 / MathComp 2.5 /
      Equations / std++ / ext-lib build cleanly — the `.cmxs` failure was purely the
      transitional rocq-elpi 3.2.0-on-Coq-8.20). `proofs/core` 33/33 .vo incl.
      `Types`(HB), `Syntax`, `Denotational`/`formula_rep`. Build steps: `leg1/BUILD.md`.
      `framac-coq8` untouched. Used the `rocq-9.0` branch (Rocq 9 `Stdlib.*` namespace).
- [x] **§3 STARTED — `leg1/SeparatedTrans.v` compiles (exit 0).** Confirms the Why3
      denotational substrate is usable downstream; re-states the coqwp Memory defs in
      Rocq 9; **PROVES `separated_trans_Coq`** (the Coq side of the obligation); scaffolds
      `[[separated_trans]] : formula` against the real `Fquant`/`Fbinop`/`Fpred`/`Tfun`.
      `formula_rep` signature pinned: `gamma -> valid_context -> pi_dom -> pi_dom_full ->
      val_typevar -> pi_funpred -> val_vars -> forall f, formula_typed gamma f -> bool`.
- [x] **§5 step 3 DONE — `[[separated_trans]]` `formula` term built** (`leg1/SeparatedTrans.v`,
      `sep_trans_fmla : formula`, compiles exit 0). `addr` = `mk_ts "addr" nil`;
      `included`/`separated` = monomorphic `predsym`s (args `[addr;int;addr;int]`, wf = `eq_refl`);
      6× `Fquant Tforall` over `Fbinop Timplies` of `Fpred` applications. Type-checks as `formula`.
- [ ] §5 step 4 — bridge round-trip: pretty-print `sep_trans_fmla` back through Why3, diff vs
      `why3-separated_trans.mlw` (fail-closed).
- [x] §5 step 5 (foundations) — machine-checked, axiom-free (`leg1/SeparatedTrans.v`):
      `gamma` (abstract context), `gamma_valid : valid_context gamma` (decidable `check_context`),
      `sep_trans_typed : formula_typed gamma sep_trans_fmla` (decidable typechecker).
- [x] **§5 step 5 (the hard core) — the concrete model interpretation is BUILT and compiles**
      (`leg1/Model.v`, 155 lines, **axiom-free**, Rocq 9.0). This was the multi-session-flagged
      blocker; it is done:
      - `my_pd : pi_dom` — `dom_aux`: addr's sort -> Coq `addr` (int/real fixed to `Z`/`R` by the
        `domain` wrapper); `domain_ne` proved;
      - `my_pdf : pi_dom_full gamma my_pd` — `adts` vacuous (no ADTs; `mut_in_ctx` false by vm_compute);
      - `my_pf : pi_funpred gamma_valid my_pd my_pdf` — `constrs` vacuous; `funs` default-via-`domain_ne`;
        **`preds` REAL**: dispatches `predsym_eq_dec` on `included_ps`/`separated_ps`, casts the
        dependent `arg_list` (scast along the predsym eq + `sym_sigma_args _ srts = pred_srts` reduction
        lemmas), extracts the 4 values (`get4`, dom-casts addr-sort/int-sort domains to `addr`/`Z`),
        and applies `includedb`/`separatedb`;
      - boolean predicates `includedb`/`separatedb` + `includedb_iff`/`separatedb_iff` (reflect to the
        Coq `included`/`separated`).
- [x] **§5 step 5 (the equivalence) — CLOSED. `sep_trans_faithful` is a theorem in `Model.v`:**
      `formula_rep ... sep_trans_fmla = true <-> sep_trans_prop`, axiom-clean (no proof holes; the
      `Print Assumptions` footprint is exactly the framework's standard base — `eq_rect_eq`,
      `functional_extensionality`, `classic`, `constructive_indefinite_description`, `sig_forall_dec`).
      The genuine UIP/cast-cancellation (the framework's `sort`/`typesym` decidable equalities don't
      reduce under conversion, so `domain my_dom_aux addr_sort` is only propositionally `= addr` and
      `sym_sigma_args included_ps [] = pred_srts` holds via `sort_inj`) is discharged by the helper
      lemmas: `term_rep_tvar`/`argval`/`posval` push the three cast layers (`cast_set` from `get4` ⊕
      `term_rep`'s `dom_cast` ⊕ `get_arg_list_hnth`'s `dom_cast`) and cancel the eq_rect tower via
      `scast_scast`/`scast_eq_uip`/`dom_cast_*`/`UIP_dec`; `collapseA`/`collapseZ` land on `D2A`/`D2Z`;
      `my_preds_inc`/`_sep_qr`/`_sep_pr` evaluate `my_preds`; `includedb_iff`/`separatedb_iff` + `implb`
      and the `D2A`/`D2Z` bijections (`D2A_inv`/`D2Z_inv`) close the `<->`.

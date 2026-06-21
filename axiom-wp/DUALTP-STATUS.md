# Dual-TP status (Coq + Lean cross-validation)

Tracks the dual-prover certification of `axiom-wp`'s trust-bearing lemmas, per
`../docs/frama-c-dual-tp-spec.md`. A lemma is **dual-TP CERTIFIED** only when *all three*
hold: Coq verified, Lean verified, and the **3-way structural cross-check**
(`Why3 ≡ Coq ≡ Lean`) passes. Each side is gated by its own `check.sh`
(`coqwp/check.sh`, `leanwp/check.sh`) — **fail-closed**: a missing prover is a
non-zero `INFRA-MISSING`, never a PASS.

Layout (after the `coqwp → axiom-wp/{coqwp,leanwp}` split):

```
axiom-wp/
  coqwp/    — Coq side: vendored WP realizations + *_hardened.v + check.sh + AUDIT.md
  leanwp/   — Lean side: dual-TP twins + check.sh
  dualtp-registry.json   — qualname → {why3, coq, lean, status}
  DUALTP-STATUS.md       — this file
```

## Status

A lemma's `crosscheck` cell tracks the hybrid 3-way check: **leg 2** = syntactic
Coq↔Lean (`dualtp/`, built and CI-gated); **leg 1** = semantic Why3↔Coq (`leg1/`, the
pilot is reduced to one cast lemma). Full certification needs both legs.

| Family | Coq | Lean | 3-way crosscheck | Certified? |
|---|---|---|---|---|
| `Memory` (11 lemmas: separation/inclusion/eqmem/havoc/table + 3 addr↔Z bijection) | `Memory_hardened.v` | 8 `leanwp/Memory.lean` + 3 bijection `leanwp/realfloat/RealFloat.lean` (11/11) | leg 2 ✓ for `separated_trans`/`included_trans`/`separated_included` (`dualtp/`); **leg 1 ✓ for all three** (`leg1/Model.v::sep_trans_faithful`, `::included_trans_faithful`, `::sep_incl_faithful`) | `separated_trans`, `included_trans`, `separated_included` **CERTIFIED** (both legs); rest **partial** |
| `Vset` (11 lemmas) | `Vset_hardened.v` | `leanwp/Vset.lean` (11/11) | leg 2: out of FOL fragment (`dualtp` `OUT_OF_FRAGMENT`) | **partial** |
| `Cfloat` (32 lemmas) | `Cfloat_hardened.v` | `leanwp/realfloat/Cfloat.lean` (32/32) | leg 2: out of FOL fragment | **partial** |
| `ArcTrigo` (2) / `ExpLog` (1) | `*_hardened.v` | `leanwp/realfloat/RealFloat.lean` (3/3) | leg 2: out of FOL fragment | **partial** |
| `Trigonometry` (1: `Pi_double_precision_bounds`) | `Trigonometry_hardened.v` (CoqInterval) | `leanwp/realfloat/RealFloat.lean` (1/1, via `pi_gt_d20`/`pi_lt_d20`) | **leg 2 ✓** (`dualtp/`) | **partial** |

**Lean twins (status) — 58 of 58 done.** Every trust-bearing coqwp lemma now has a verified Lean twin.
Two gates, both fail-closed (Lean 4.31.0; no `sorry`; axioms ⊆ {propext, Classical.choice, Quot.sound}):
- `leanwp/check.sh` — the **standalone** core (no mathlib): `Memory.lean` (8) + `Vset.lean` (11).
- `leanwp/realfloat/check.sh` — the **mathlib** twins (lake project on mathlib `v4.31.0`):
  `RealFloat.lean` (3 `Memory` addr↔Z bijection + 2 `ArcTrigo` + 1 `ExpLog` + 1 π bound) + `Cfloat.lean`
  (32).

Statements are authored structurally identical to the Coq twins / WP's Why3 goals.

**`Pi_double_precision_bounds` — closed.** The Coq side discharges the 1-ulp-at-2⁻⁵¹ bracket on π with
CoqInterval. The Lean twin discharges the *same* bracket from mathlib's 20-digit bracket
`Real.pi_gt_d20` (`3.14159265358979323846 < π`) / `Real.pi_lt_d20` (`π < 3.14159265358979323847`): the
2⁻⁵¹ window is ~16 digits, well inside 20, so each endpoint reduces to a rational comparison closed by
`norm_num`. (An earlier note here claimed mathlib had no tight-enough π bound — that was wrong;
`Real.pi_gt_d20`/`pi_lt_d20` in `Mathlib.Analysis.Real.Pi.Bounds` supply it.)

**3-way cross-check — leg 2 BUILT (`dualtp/`).** The syntactic Coq↔Lean leg (spec §5.4b) now exists and
is CI-gated: a FOL canonicalizer (`dualtp/canonical.py`) unifying operator spellings, cross-prover
symbol/type aliases (`Reals.Rtrigo1.PI ≡ Real.pi`, `Z ≡ Int ≡ ℤ`, …) and bound-variable names
(de Bruijn) but **not** operand order; an adversarial corpus (`dualtp/corpus.py`, 21 positive + 21
negative, with a meta-check that a weakened canonicalizer turns it red — spec §5.7); and the per-lemma
`canon(Coq) == canon(Lean)` driver (`dualtp/crosscheck.py`). It passes for `Memory.separated_trans`,
`Memory.included_trans`, `Memory.separated_included`, and `Trigonometry.Pi_double_precision_bounds`.
Lemmas whose statement leaves the FOL fragment (Cfloat float predicates, Vset set-membership, the
record-constructor equality of `separated_1`, the transcendental applications) are honestly listed in
`dualtp/pairs.OUT_OF_FRAGMENT` — not silently passed; extending the canonicalizer to them is future work.

**Leg 1 (semantic Why3↔Coq, §5.4a) — CLOSED for three `Memory` lemmas.** `leg1/Model.v` now proves three
faithfulness theorems, all axiom-clean (no `Admitted`; `Print Assumptions` = the framework's standard
base only — `eq_rect_eq`, `functional_extensionality`, `classic`, `constructive_indefinite_description`,
`sig_forall_dec`; no custom/behavioural axioms):
- `sep_trans_faithful` : `formula_rep … sep_trans_fmla = true ↔ sep_trans_prop`;
- `included_trans_faithful` : `formula_rep … inc_trans_fmla = true ↔ included_trans_prop`;
- `sep_incl_faithful` : `formula_rep … sep_incl_fmla = true ↔ sep_incl_prop`.

With leg 2 also passing, `Memory.separated_trans`, `Memory.included_trans`, and
`Memory.separated_included` are **dual-TP CERTIFIED** (both legs). `separated_included` extended the model
with an interpreted integer `>` predicate (`gt_ps` in the context, `gtb`/`gtb_iff`), integer-literal
denotation (`term_rep_const`/`argval_const`/`posval_const`/`D2Z_id`) and `Ffalse`/`Fnot` handling — the
`trans` pair reused the substrate unchanged. The shared machinery
(`term_rep_tvar`/`argval`/`posval`/`collapseA`/`collapseZ`/`my_preds_*`/`D2A_inv`/`D2Z_inv`/`substi_*`) is
reusable; the remaining `Memory`/`Vset`/reals lemmas stay **partial** until their own obligations are
built (leg 2 already covers the FOL-fragment ones).

**Leg 1 (semantic Why3↔Coq anchoring, spec §5.4a) — substantial progress, see the Leg 1 section below.**
The stronger *semantic* check (Coq `separated_trans_Coq` ⟺ `formula_rep` of the Why3 AST, against the
joscoh denotational semantics) now has the why3-semantics built on Rocq 9.0, the `[[separated_trans]]`
formula term constructed, a complete concrete model interpretation (`leg1/Model.v`, axiom-free), and the
obligation **closed** as the theorem `sep_trans_faithful` (the UIP/cast-cancellation is fully discharged;
`Print Assumptions` = the framework's standard base only). Leg 1 is complete for the pilot lemma.

## Lean axiom bar — note (matches the PyCSL audit finding P1-1)
The verified Lean proof depends on `{propext, Classical.choice, Quot.sound}` — the **standard** Lean kernel
axiom set (what the `lean` skill's Quality Gate accepts). The spec's earlier "constructive" wording
(`⊆ {propext, Quot.sound}`) was aspirational; `Classical.choice` is standard and effectively unavoidable
(`by_cases`, `Int`), so `leanwp/check.sh` and `../docs/frama-c-dual-tp-spec.md §6` use the standard set and name it
honestly. This is exactly the code-vs-doc alignment the PyCSL audit flagged — applied here from day one.

## Leg 1 (semantic Why3↔Coq) — CLOSED for `separated_trans`, `included_trans`, `separated_included` (Rocq 9.0)

**Status 2026-06-21 (hand-off).** The coq-elpi blocker is RESOLVED via the **Rocq-9.0 route**: the
why3-semantics `rocq-9.0` branch builds on an isolated `dualtp-leg1-r9` switch (rocq-elpi **3.4.0** /
HB 1.10.2 / MathComp 2.5 / Equations / std++ / ext-lib — clean; the `.cmxs` failure was purely
transitional rocq-elpi 3.2.0-on-Coq-8.20). `proofs/core` 33/33 .vo (incl. `Types`[HB], `Syntax`,
`Denotational`/`formula_rep`), no errors. Build steps: `leg1/BUILD.md`; `framac-coq8` untouched.

**DONE (compiles, axiom-free — no `Admitted`/`admit`/`Axiom`/`Abort`):**
- `leg1/SeparatedTrans.v` (135 lines): substrate usable downstream; coqwp `Memory` defs re-stated in
  Rocq 9; **`separated_trans_Coq` PROVED**; `sep_trans_fmla : formula` built from the real Syntax
  constructors; **`gamma_valid : valid_context gamma`** + **`sep_trans_typed : formula_typed`**
  (both machine-checked by the framework's deciders).
- `leg1/Model.v` (188 lines): the **complete concrete model interpretation** — `my_pd` (`pi_dom`,
  addr-sort↦Coq `addr`), `my_pdf` (`pi_dom_full`, vacuous adts), **`my_pf` (`pi_funpred`) with the
  REAL `preds`** (dependent `arg_list` extraction → `includedb`/`separatedb`); boolean predicates +
  `includedb_iff`/`separatedb_iff`; `my_vt`/`my_vv`/`sep_trans_prop`; and **`allb`** which (verified)
  reduces the obligation `formula_rep … sep_trans_fmla = true ↔ sep_trans_prop` to the concrete goal
  `(∀ d..d4, implb (my_preds included_ps [] (pred_arg_list ..)) (implb ..)) ↔ sep_trans_prop`.

**CLOSED — `sep_trans_faithful` and `included_trans_faithful` (theorems).** The cast-cancellation is fully
discharged in `leg1/Model.v`; `included_trans` reuses the same machinery (it differs only in having three
`included` predicate applications instead of one `included` + two `separated`, so it rewrites with
`my_preds_inc`/`my_preds_inc_qr`/`my_preds_inc_pr` and reflects via `includedb_iff`). The chain:
`term_rep_tvar`/`argval`/`posval` compute the denotation of each `Tvar`
predicate argument through the dependent `dom_cast` layers (`get_arg_list_hnth` + `term_rep_irrel` +
`term_rep_equation_3`); `collapseA`/`collapseZ` reduce the `get4` eq_rect tower to the carrier
projections `D2A`/`D2Z` (via `scast_scast`/`scast_eq_uip`/`UIP_dec`); `my_preds_inc`/`_sep_qr`/`_sep_pr`
give the value of `my_preds` on the real argument lists; then `includedb_iff`/`separatedb_iff` + `implb`
close the equivalence and the `D2A`/`D2Z` bijections (`D2A_inv`/`D2Z_inv`) reindex `forall d:domain` as
`forall p:addr`.

**Axiom-base finding:** the framework's `Cast.UIP` is derived from Stdlib `Eqdep.Eq_rect_eq.eq_rect_eq`
(Streicher's K), so `formula_rep` itself rests on `eq_rect_eq`. `sep_trans_faithful` therefore carries
**no proof hole and no new axiom**: its `Print Assumptions` footprint is exactly the framework's standard
base (`eq_rect_eq`, `functional_extensionality`, `classic`, `constructive_indefinite_description`,
`sig_forall_dec`) — the allowed `A_coq` for leg 1.

It is a genuine **UIP/cast-cancellation** proof, NOT mere bookkeeping:
the framework's decidable equalities on `sort`/`typesym` (sig-types + proof-field records) don't reduce
under conversion, so `domain my_dom_aux addr_sort` is only *propositionally* `= addr` and
`sym_sigma_args included_ps [] = pred_srts` holds via `sort_inj`; the three cast layers
(`cast_set` ⊕ `term_rep`'s `dom_cast` ⊕ `get_arg_list_hnth`'s `dom_cast`) must cancel via
`UIP_dec` + `dom_cast_refl`/`dom_cast_eq`, then `term_rep (Tvar x) = dom_cast (var_to_dom vv' x)`
connects to the bound `d_i`, closing with `includedb_iff`/`separatedb_iff` + `implb`. Recipe is in
`Model.v` and `leg1/README.md`. `predsym_eq_dec included_ps included_ps` confirmed to reduce to
`left e` (so `my_preds` enters the `includedb` branch).

The original (now-historical) Coq-8.20 blocker writeup follows.


See `leg1/`. Grounded: the verbatim `Why3(separated_trans)` is extracted
(`leg1/why3-separated_trans.mlw`, from WP's `memaddr.mlw`), Why3≡Coq≡Lean confirmed
by inspection; **fragment coverage PASS**. Toolchain update: the semantics has a
**`coq-8.20` branch** — it builds on Coq 8.20.1 (no Rocq-9 split, contrary to the
first spike). Coq + Equations + std++ + ext-lib install fine.

**BLOCKER (re-diagnosed 2026-06-21, precisely):** building the semantics needs
MathComp 2.x (`Types.v` uses `HB.instance`) → Hierarchy Builder → **coq-elpi**, and
coq-elpi cannot be added to the pinned Coq-8.20 `framac-coq8` switch. It is a
**dependency trap around the pin**, NOT a missing native capability (the switch
builds `.cmxs` and loads `coq-interval`'s native ML plugin fine):
- Coq held at 8.20.1 ⇒ opam picks **rocq-elpi 3.2.0**, whose dune build **fails to
  stage `elpi_plugin.cmxs`** → `Declare ML Module` in `theories/elpi.v` errors
  `elpi_plugin.cmxs: No such file` (a rocq-elpi-3.2.0-on-coq-core-8.20 staging bug).
- coq-elpi **2.x** (true 8.20 line) ⇒ downgrades `elpi` 3.4.2→2.0.7 + yojson/atd and
  **recompiles frama-c 32.1 + frama-c-metacsl** (perturbs the pin).
- coq-elpi **3.4.0** ⇒ needs **Rocq 9.0.1**, upgrading Coq off 8.20 (breaks coqwp+frama-c).
So `formula_rep` is unbuildable *in this switch*; the obligation is **not started**.
Resolve in a **dedicated/isolated switch** or the **Coq Platform** (prebuilt
coq-elpi + MathComp 2.x); keep `framac-coq8` pinned. Resume at `leg1/README.md` §5.
No green is claimed.

## Next (per spec §7)
1. **Leg 1 — DONE for the pilot:** `sep_trans_faithful` closes the obligation in
   `leg1/Model.v` (axiom-clean). Optional hardening: the §5-step-4 bridge round-trip
   (print `sep_trans_fmla` back through Why3, diff vs `leg1/why3-separated_trans.mlw`).
2. **Leg 2 — DONE:** `dualtp/` Coq↔Lean cross-check + adversarial canonicalizer corpus
   (spec §5.7), CI-gated. Covers the FOL-fragment lemmas (incl. `separated_trans`).
3. `Memory.separated_trans` is **CERTIFIED** (both legs pass). ✓
4. Extend: leg-1 obligations for the rest of `Memory`/`Vset`/reals (each needs its own
   model interpretation), and grow the leg-2 fragment to the float/set statements.

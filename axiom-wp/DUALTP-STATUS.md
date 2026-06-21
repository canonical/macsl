# Dual-TP status (Coq + Lean cross-validation)

Tracks the dual-prover certification of `axiom-wp`'s trust-bearing lemmas, per
`../frama-c-dual-tp-spec.md`. A lemma is **dual-TP CERTIFIED** only when *all three*
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

| Family | Coq | Lean | 3-way crosscheck | Certified? |
|---|---|---|---|---|
| `Memory` (11 lemmas: separation/inclusion/eqmem/havoc/table + 3 addr↔Z bijection) | ✅ `Memory_hardened.v` | ✅ 8 `leanwp/Memory.lean` + 3 bijection `leanwp/realfloat/RealFloat.lean` (11/11) | ⛔ tooling not built | **partial** |
| `Vset` (11 lemmas) | ✅ `Vset_hardened.v` | ✅ `leanwp/Vset.lean` (11/11) | ⛔ tooling not built | **partial** |
| `Cfloat` (32 lemmas) | ✅ `Cfloat_hardened.v` | ✅ `leanwp/realfloat/Cfloat.lean` (32/32) | ⛔ tooling not built | **partial** |
| `ArcTrigo` (2) / `ExpLog` (1) | ✅ `*_hardened.v` | ✅ `leanwp/realfloat/RealFloat.lean` (3/3) | ⛔ tooling not built | **partial** |
| `Trigonometry` (1: `Pi_double_precision_bounds`) | ✅ `Trigonometry_hardened.v` (CoqInterval) | ⛔ **deferred** — mathlib has no tight-enough π bound | ⛔ tooling not built | pending |

**Lean twins (status) — 57 of 58 done.** Every trust-bearing coqwp lemma now has a verified Lean twin
**except `Pi_double_precision_bounds`**. Two gates, both fail-closed (Lean 4.31.0; no `sorry`; axioms ⊆
{propext, Classical.choice, Quot.sound}):
- `leanwp/check.sh` — the **standalone** core (no mathlib): `Memory.lean` (8) + `Vset.lean` (11).
- `leanwp/realfloat/check.sh` — the **mathlib** twins (lake project on mathlib `v4.31.0`):
  `RealFloat.lean` (3 `Memory` addr↔Z bijection + 2 `ArcTrigo` + 1 `ExpLog`) + `Cfloat.lean` (32).

Statements are authored structurally identical to the Coq twins / WP's Why3 goals.

**The one holdout — `Pi_double_precision_bounds`.** Deferred honestly, not faked. The Coq side discharges
it with **CoqInterval** (a 1-ulp-at-2⁻⁵¹, ~16-digit bracket on π). mathlib's standard π bounds
(`Real.pi_gt_3141592` / `Real.pi_lt_3141593`) are only ~6 digits — *looser* than the bracket's endpoints,
so they cannot prove it, and mathlib ships no `interval`-style reflective π tactic to close the gap cheaply.
Same lemma that needed the extra CoqInterval dependency on the Coq side; the Lean twin waits on an
equivalent tight-π facility.

What is **still not mechanical** for any twin is the 3-way structural equality check (`dualtp/`, spec §5.4)
proving `Why3 ≡ Coq ≡ Lean` — so each is **partial**, not certified, until that tool exists.

**Leg 1 (semantic Why3↔Coq anchoring, spec §5.4a) — substantial progress, see the Leg 1 section below.**
The stronger *semantic* check (Coq `separated_trans_Coq` ⟺ `formula_rep` of the Why3 AST, against the
joscoh denotational semantics) now has the why3-semantics built on Rocq 9.0, the `[[separated_trans]]`
formula term constructed, a complete concrete model interpretation (`leg1/Model.v`, axiom-free), and the
obligation reduced to **one open UIP/cast-cancellation lemma** (handed off for an interactive session).
Not certified until that lemma closes; do not report leg 1 as complete.

## Lean axiom bar — note (matches the PyCSL audit finding P1-1)
The verified Lean proof depends on `{propext, Classical.choice, Quot.sound}` — the **standard** Lean kernel
axiom set (what the `lean` skill's Quality Gate accepts). The spec's earlier "constructive" wording
(`⊆ {propext, Quot.sound}`) was aspirational; `Classical.choice` is standard and effectively unavoidable
(`by_cases`, `Int`), so `leanwp/check.sh` and `frama-c-dual-tp-spec.md §6` use the standard set and name it
honestly. This is exactly the code-vs-doc alignment the PyCSL audit flagged — applied here from day one.

## Leg 1 (semantic Why3↔Coq) — model BUILT (Rocq 9.0); obligation reduced to one cast lemma (HAND-OFF)

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

**OPEN — one lemma, handed off for an interactive Coq session.** Compute
`my_preds included_ps [] (pred_arg_list .. [Tvar a;..] (term_rep .. vv')) = includedb (vv' a) ..`
(and the `separated` analogue). It is a genuine **UIP/cast-cancellation** proof, NOT mere bookkeeping:
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
1. **Leg 1 (semantics built; formula term + model done):** finish the one open
   **UIP/cast-cancellation lemma** (`my_preds … = includedb/separatedb …`) in an
   interactive Coq session to close `sep_trans_faithful` in `leg1/Model.v`; then add
   the §5-step-4 bridge round-trip (print `sep_trans_fmla` back through Why3, diff vs
   `leg1/why3-separated_trans.mlw`). Recipe: `leg1/Model.v` / `leg1/README.md`.
2. **Leg 2:** build the `dualtp/` Coq↔Lean cross-check (extract Coq `Check` + Lean
   `#check` → shared IR → canonical `==`), **with its adversarial canonicalizer
   corpus** (spec §5.7) from the start.
3. Flip `Memory.separated_trans` to **certified** once both legs pass in CI.
4. Add Lean twins for the rest of `Memory.v` (10 lemmas), then `Vset.v`, then the
   `R`-based theories.

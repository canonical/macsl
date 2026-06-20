# Specification: dual Rocq/Coq + Lean proof cross-validation for Frama-C/WP

**Status:** specification (not yet implemented).
**Goal:** bring PyCSL's dual-prover axiom-plumbing rigor to the Frama-C/WP trust root — every
trust-bearing lemma that a WP green rests on must carry a **paired Coq + Lean proof of the same formula**,
mechanically cross-checked against the Why3 source (a semantic Coq↔Why3 leg + a syntactic Coq↔Lean leg), each side using only allow-listed kernel axioms.
**Builds on:** the `coqwp/` hardening already in this repo (Memory/Vset/Cfloat/ArcTrigo/ExpLog lemmas
re-proved in Coq, `axiom-wp/coqwp/check.sh`, `axiom-wp/coqwp/AUDIT.md`) and the Coq-escalation discipline in
`config/skills/frama-c/references/coq-escalation.md` + `coqwp-trust-root.md`.
**Reference design:** PyCSL's `proof2why3` 3-way cross-check. **The PyCSL audit
(`pycsl-audit-dual-tp.md`) lists gaps in that implementation; this spec bakes the fixes in from day one.**

---

## 1. Why two provers (the property we are buying)

A `-wp-prover coq` green is sound only modulo (a) Coq's kernel, (b) WP's Why3→Coq realization (`coqwp` —
itself the TCB, with admitted lemmas we hardened this session), and (c) the claim that the proved formula
is the one WP actually emits. A second, independent prover (Lean 4) cross-validates **(b) and (c)** far more
than (a): the highest-probability error is not a kernel bug but a wrong/over-strong **statement** or a
faithfulness slip between the Why3 goal and its rendering. An independent Lean encoding of the *same* Why3
formula, proved independently and checked structurally-equal, catches those. (Kernel-soundness defense is a
real but second-order bonus.) This is exactly the PyCSL thesis, and the natural next step beyond the
single-prover `coqwp` hardening.

**Trust property (per lemma `L`) — a HYBRID: a *semantic* Why3↔Coq leg + a *syntactic* Coq↔Lean leg:**

> 1. **`Coq(L) ⟺ ⟦Why3(L)⟧`** — proved *inside Coq* against the Why3 **denotational semantics**
>    (`formula_rep`/`valid`; §5.4a), not a string match; **and**
> 2. **`canon(Coq(L)) == canon(Lean(L))`** — structural equality over the shared first-order IR (§5.4b); **and**
> 3. **`axioms(Coq L) ⊆ A_coq`** and **`axioms(Lean L) ⊆ A_lean`** (§6); **and**
> 4. both proofs compile under their pinned kernels with no `Admitted`/`sorry`.

Leg 1 anchors the Coq statement to what Why3 *means*; leg 2 carries that anchor to the independent Lean
kernel. Composed, `Lean(L)` is the same proposition as `⟦Why3(L)⟧`, proved by two kernels. `Why3(L)` is
the formula WP actually uses; `Coq(L)`/`Lean(L)` are the proved theorem statements; `A_coq`/`A_lean` are
the published axiom allow-lists (§6).

> **Why hybrid, not a uniform 3-way canonicalizer (the original v1 of this spec).** The Why3 semantics
> (Cohen & Johnson-Freyd, POPL 2024 — `joscoh/why3-semantics`, the POPL'24 artifact; vendor under `axiom-wp/why3-semantics/` at impl time)
> is a *Coq* development, so it can ground the Why3↔Coq leg in a **published mechanized semantics** rather
> than a bespoke canonicalizer — strictly stronger. It cannot reach Lean (no Lean port), so the Coq↔Lean
> leg stays syntactic, with the canonicalizer's job *narrowed* to "same first-order proposition across two
> prover syntaxes." This moves the bulk of the trust onto a peer-reviewed artifact and shrinks the
> canonicalizer TCB.

---

## 2. Mapping PyCSL → Frama-C

| PyCSL | Frama-C/WP analogue |
|---|---|
| `_AXIOM_REGISTRY[qn]` (Why3 formula SMT assumes) | the WP-emitted **Why3 goal** for lemma `L` (printable Why3 task), or the `(* Why3 goal *)` statement in a `coqwp` `.v` |
| `#@ proof rocq\|lean <qn>` citation | a registry entry binding `L` → its `{coq,lean}` proof files (and, for ACSL lemmas, the C/ACSL site + `-wp-prop` selector) |
| `*.proofs/{rocq,lean}/*.{v,lean}` | `proofs/{coq,lean}/*.{v,lean}` next to the unit (or under `coqwp/` for realization lemmas) |
| `audit_proof.py` (attribution) | name-presence + axiom-cleanliness audit (extend `axiom-wp/coqwp/check.sh`) |
| `proof2why3/crosscheck_ir.py` (syntactic 3-way) | **new** `dualtp`: *semantic* Why3↔Coq (§5.4a) + *syntactic* Coq↔Lean (§5.4b) |
| (no PyCSL analogue) | the **Why3 denotational semantics** (`formula_rep`/`valid`, Cohen–Johnson-Freyd POPL'24) — grounds leg 1 |
| `proof_axiom_allowlist.py` | `A_coq` / `A_lean` (§6) |
| `sync-axiom-registry` | regenerate the registry statements **from** the cross-checked IR |

---

## 3. Two classes of trust-bearing lemma in scope

1. **`coqwp` realization lemmas** — the TCB of `-wp-prover coq`. These are the `(* Why3 goal *)` lemmas in
   `Memory.v`/`Vset.v`/`Cfloat.v`/`ArcTrigo.v`/`ExpLog.v` we proved in Coq this session
   (`coqwp/*_hardened.v`). Each gets a **Lean twin** stating the same Why3 goal and a hybrid cross-check (§4).
   These are the highest-value targets: every coq green inherits them.
2. **SMT-escalated ACSL lemmas** — a named ACSL `lemma` (gcd-style) that SMT cannot discharge, proved via
   `-wp-interactive update -wp-prover coq`. Each gets a Lean twin + cross-check. The Why3 statement is the
   WP-emitted goal for that lemma.

Out of scope (by design, document as such): the ~52 opaque-definition `Admitted`s and 3 `WhyType` axioms
in `coqwp` (abstract/uninterpreted symbols, not facts — see `axiom-wp/coqwp/AUDIT.md`); contract→Why3 encoding;
function-VC proofs (escalate a *named lemma*, never the postcondition VC — see `coq-escalation.md §3`).

---

## 4. The Frama-C-specific challenge, and the resolution

**Why3 ships a Coq driver but no production Lean driver.** So unlike PyCSL (where both `.v` and `.lean` are
hand-written against a Why3 registry), here the **Coq statement is produced by WP's trusted driver** (the
same driver that produces the goals SMT solves), and **the Lean statement is hand-written**. That asymmetry
must not become a hole: the Lean twin is only trustworthy because the cross-check proves it equals the
authoritative Why3 formula.

**The hybrid resolution — two legs, composed:**

- **Leg 1 — Why3↔Coq, SEMANTIC (`Coq(L) ⟺ ⟦Why3(L)⟧`).** Reflect the WP-emitted Why3 goal into the
  Cohen–Johnson-Freyd deep embedding (`formula` / `term`) and prove, *inside Coq*, that the realization
  lemma `Coq(L)` is equivalent to the goal's denotation (`formula_rep`) / its validity (`valid`). This
  grounds faithfulness in a **published mechanized semantics**, not a syntactic task-string match — so the
  Coq↔Why3 anchor is no longer a canonicalizer TCB. For **closed integer VCs** (the SMT-escalated ACSL
  class), `closed_satisfies_rep` collapses `valid` to a boolean evaluation — a finite `decide`, the
  strongest form. For the **quantified realization lemmas** (`separated_trans`, …, over abstract addr/map/
  real sorts) there is no such collapse: prove the `⟺` against `formula_rep`-as-`Prop` by reasoning.
- **Leg 2 — Coq↔Lean, SYNTACTIC (`canon(Coq(L)) == canon(Lean(L))`).** Extract both prover statements
  (`Check` / `#check`), canonicalize to the shared IR (§5.4b), require structural equality. The Lean kernel
  independently re-proves the *same proposition*, defending against a Coq-kernel bug and a mis-stated Coq
  theorem. The canonicalizer's job is now only "same FOL proposition across two prover syntaxes" — far
  narrower than "matches the Why3 source."

Composed: `Lean(L) ≡(syntactic) Coq(L) ⟺(semantic) ⟦Why3(L)⟧`. **Eligibility & honesty rules:** if `Why3(L)`
falls outside the formalized fragment, or the AST→`formula` bridge cannot represent it (§5.8), leg 1 is
unavailable — record the lemma as a single-prover (`coqwp`-hardened) result, **never** silently drop to a
Lean≡Coq-only check and call it dual-TP. The fragment-coverage and bridge trust items are §5.8.

---

## 5. Components to build

### 5.1 Registry (`axiom-wp/dualtp-registry.{json,py}`)
One entry per certified lemma:
```
{ "qualname": "Memory.separated_trans",
  "trust_class": "coqwp-realization" | "acsl-escalation",
  "why3":  { "source": "task-print|coqwp-goal", "locator": "…" },
  "coq":   "axiom-wp/coqwp/Memory_hardened.v",
  "lean":  "axiom-wp/leanwp/Memory.lean",
  "acsl_site": null | { "file": "…/foo.c", "prop": "lemma_name", "wp_fct": "…" } }
```
The registry **statements are derivable** from the cross-checked IR (a `sync` mode), so the human authors
proofs, not formulas — removing hand-transcription as a correlated-failure source (PyCSL `sync-axiom-registry`).

### 5.2 Proof layout
- realization lemmas: `axiom-wp/coqwp/<Theory>_hardened.v` (exists) + `axiom-wp/leanwp/<Theory>.lean` (new).
- escalation lemmas: `<unit>.proofs/{coq,lean}/<Lemma>.{v,lean}` next to the C unit.

### 5.3 Statement extraction (`dualtp/extract.py`)
- **Why3 → `formula` (the bridge, leg 1):** reflect the WP-emitted Why3 goal (`frama-c -wp -wp-out DIR …`
  / task printer) into the semantics' deep-embedded `formula`/`term` AST. This bridge is trust-bearing —
  see §5.8.
- **Coq (leg 2):** SerAPI (`sertop`) or `coqc` companion `Check L`. (Coq 8.20.1, the `framac-coq8` switch.)
- **Lean (leg 2):** `lake env lean` with appended `#check L`. (Lean 4, pinned version.)
- **Empty extraction is a hard error, never "trivially equal"** (PyCSL P0-2).

### 5.4a Semantic leg — Why3↔Coq (`dualtp/semantic/`, in Coq)
For each lemma, build a Coq obligation `Coq(L) ⟺ ⟦Why3(L)⟧` and discharge it with the vendored
Cohen–Johnson-Freyd semantics:
- closed integer VC → `valid` collapses to `formula_rep … = true` via `closed_satisfies_rep`; close by
  `decide`/`reflexivity` (finite case analysis).
- quantified realization lemma → unfold `formula_rep` to a `Prop` and prove the `⟺` by reasoning.
This obligation is itself a Coq proof and so is gated by `axiom-wp/coqwp/check.sh` (axiom-clean, no
`Admitted`). It **replaces** any syntactic Why3-task↔Coq match — there is no canonicalizer on this leg.

### 5.4b Syntactic leg — Coq↔Lean (`dualtp/canonical.py`, `dualtp/crosscheck.py`)
Shared first-order IR (quantifiers, connectives, arithmetic, uninterpreted symbols, sorts) for the **two
prover statements only**. `canonicalize` must normalize: bound-variable names (de Bruijn / consistent
α-renaming), binder grouping (`∀x y` ≡ `∀x, ∀y`), AC flattening where semantically valid, `0<=k<16` vs
`0<=k ∧ k<16`, integer-literal forms, notation vs raw; then require `canon(Coq) == canon(Lean)`. **The
canonicalizer is a TCB for this leg only** (narrower than v1's three-way canonicalizer) — adversarially
tested per §5.7.

### 5.5 Axiom-cleanliness (`dualtp/axioms.py`)
Run `Print Assumptions L` (Coq) and `#print axioms L` (Lean); parse; check `⊆ A_coq` / `A_lean` (§6).

### 5.6 CI from day one, fail-closed (PyCSL P0-1, P0-2)
A `.github/workflows/dualtp.yml` (mirror the existing `axiom-wp.yml`) installs **both** pinned toolchains and
runs `make dualtp-verify` on every push/PR touching `axiom-wp/**`, `**/*.proofs/**`, `dualtp/**`, or the
registry. The gate must distinguish **PASS / FAIL / INFRA-MISSING**, and `INFRA-MISSING` (either prover or
the Why3 printer absent, or an empty extraction) is **non-zero**. Print the exact Coq/Lean/Frama-C/Why3
versions used. A missing prover must never read as PASS.

### 5.7 Canonicalizer adversarial test set from day one (PyCSL P0-3)
Ship, with the canonicalizer, a corpus of **≥20 negative pairs** (almost-equal but distinct: swapped
quantifier order, `<` vs `≤`, `16` vs `15`, dropped hypothesis, transposed args, `∀`/`∃` flipped, extra
conjunct) that MUST canonicalize **unequal**, and **≥20 positive pairs** (same proposition, different
surface syntax / different prover) that MUST canonicalize equal; plus round-trip + idempotence checks. A
deliberately-weakened canonicalizer must turn this suite red. This is the highest-value foundational task
for **leg 2** — the Coq↔Lean check is only as sound as this. (Leg 1 has no canonicalizer; its soundness
rests on the published semantics + the §5.8 bridge instead.)

### 5.8 Leg-1 trust items: fragment coverage + the AST→`formula` bridge
Leg 1 moves the Why3↔Coq trust off a canonicalizer and onto two new, explicit items — scrutinize them like
the proofs:
- **Fragment coverage.** The semantics formalizes a Why3 *fragment* (typed terms/formulas, quantifiers,
  pattern matching, rec/inductive defs; theory symbols like int/map/real enter as uninterpreted
  funsyms/predsyms + axioms). Before certifying a lemma, **check its Why3 goal lies inside that fragment**;
  anything outside (an unsupported builtin/notation/feature) makes leg 1 unavailable → single-prover
  fallback, documented (§4 honesty rule). Maintain a checked list of supported constructs and assert each
  goal against it (fail-closed: unknown construct ⇒ not certified, never silently accepted).
- **The bridge (`Why3 task → formula`).** Reflecting WP's emitted Why3 AST into the deep-embedded `formula`
  is trust-bearing: a wrong reflection could make `⟦Why3(L)⟧` mean something other than the goal WP solved.
  Mitigations: (a) drive the reflection from WP's own Why3 task output (not a re-parse of pretty-printed
  text); (b) a **round-trip / differential check** — pretty-print the reflected `formula` back through
  Why3 and diff against the original task (à la PyCSL's registry emit round-trip), and/or evaluate both on
  sample interpretations; (c) pin Frama-C/Why3 versions and the semantics commit; smoke-test the bridge on
  a known goal in CI (empty/garbled reflection ⇒ fail-closed). The bridge + semantics commit are now part
  of the TCB — but a peer-reviewed semantics + a checkable reflection is a far better TCB than a bespoke
  three-way canonicalizer.

---

## 6. Axiom allow-lists (code == docs, decided up front — PyCSL P1-1)
State the allowed set **once**, in `dualtp/axioms.py`, and cite it verbatim in every doc. Recommended,
matching the rigor already achieved in `coqwp/` (and being honest about Coq's `R`):
- **`A_coq`**: `Closed under the global context` (preferred); else `⊆ { functional_extensionality[_dep],
  propositional_extensionality }`; and for `Reals`-based lemmas additionally `ClassicalDedekindReals.sig_forall_dec`
  (Coq's `R` is axiomatized — see `axiom-wp/coqwp/Cfloat_hardened.v`). **No `classic`/choice unless explicitly
  justified per lemma.**
- **`A_lean`**: `⊆ { propext, Classical.choice, Quot.sound }` — the **standard** Lean kernel axiom set
  (what the `lean` skill's Quality Gate accepts and what `axiom-wp/leanwp/check.sh` enforces).
  **Empirically confirmed by the pilot:** `Memory.separated_trans` depends on all three (`Classical.choice`
  arrives via `by_cases`/`Int`), so a stricter `{ propext, Quot.sound }` bar is *aspirational and
  per-lemma*, not the default. This is precisely the code-vs-doc gap the PyCSL audit flagged (P1-1): name
  the bar you actually enforce, not a prettier one. A genuinely choice-free proof may tighten its own entry.
Every certified lemma's registry entry records the exact axioms each side used, so the trust class is
auditable per lemma, not just in aggregate.

---

## 7. Phasing
1. **Pilot — `Memory.separated_trans`** (1 lemma). The Lean twin and both `check.sh` gates **already exist
   and pass** (this session; see `axiom-wp/DUALTP-STATUS.md`). Remaining for full certification: leg 1
   (vendor the semantics, build the AST→`formula` bridge for this goal, discharge `Coq(L) ⟺ ⟦Why3(L)⟧`)
   and leg 2 (`extract`/`canonical`/`crosscheck` minimal + the adversarial corpus skeleton), wired into CI
   fail-closed. End-to-end **hybrid** green on one lemma before scaling. (Mirror the coqwp pilot discipline.)
2. **`Memory.v`** — the remaining 10 hardened lemmas (highest value: separation algebra under every proof).
3. **`Vset.v`** (11), then **`Cfloat.v`** (32) / `ArcTrigo` / `ExpLog` — note these are `R`-based, so
   `A_coq` includes `sig_forall_dec`; design the Lean twins to land in `A_lean` (Lean's reals differ —
   decide whether to model over `ℝ` or an abstract ordered field; document the modelling choice as part of
   the statement, exactly as `axiom-wp/coqwp/Cfloat_hardened.v` clamps to `[-max,max]`).
4. **SMT-escalated ACSL lemmas** (gcd-style), per unit, via the escalation workflow + Lean twin.
Each phase: registry entries + Lean twins + hybrid (leg-1 + leg-2) green in CI + axioms recorded. Track in a
`axiom-wp/DUALTP-STATUS.md` like `AUDIT.md`.

## 8. Gate semantics & acceptance criteria (per lemma and aggregate)
A lemma is **dual-TP certified** iff, in CI on pinned toolchains:
- [ ] Coq `.v` compiles, no `Admitted`; `Print Assumptions L ⊆ A_coq`.
- [ ] Lean `.lean` compiles, no `sorry`; `#print axioms L ⊆ A_lean`.
- [ ] **Leg 1 (semantic):** `Coq(L) ⟺ ⟦Why3(L)⟧` is a discharged, axiom-clean Coq obligation; the Why3
  goal is inside the formalized fragment and the AST→`formula` bridge round-trips (§5.4a, §5.8).
- [ ] **Leg 2 (syntactic):** `canon(Coq(L)) == canon(Lean(L))` (neither side skipped).
- [ ] Registry entry present; its statement matches the cross-checked IR (`sync` is a fixpoint).
- [ ] The lemma is **load-bearing**: removing the Coq side reddens a real WP goal (the `coq-escalation.md`
  "each lemma load-bearing" gate) — a dead certified lemma is a smell.
Aggregate gate (`make dualtp-verify`): every registry lemma certified; **INFRA-MISSING ⇒ non-zero**; the
canonicalizer adversarial corpus green.

## 9. Toolchain
- Coq **8.20.1** on the `framac-coq8` opam switch (Coq before Why3; see `axiom-wp/coqwp/AUDIT.md` / `axiom-wp.yml`).
- Frama-C **32.1** / Why3 **1.8.2** (the task printer for `Why3(L)`).
- **Lean 4** (pinned `lean-toolchain`; the pilot uses **4.31.0**), core only where possible (avoid Mathlib
  to keep `A_lean` tight); use the `lean` skill for proof authoring and `#print axioms` discipline.
- SerAPI (`sertop`) for robust Coq statement extraction (leg 2).
- **Why3 denotational semantics** — Cohen & Johnson-Freyd, POPL 2024, `github.com/joscoh/why3-semantics`
  (vendor under `axiom-wp/why3-semantics/`; key defs — `formula_rep`/`Denotational.v`, `satisfies`/`valid`/
  `closed_satisfies_rep`/`Logic.v`). Pin the commit; it is part of leg-1's TCB.

## 10. Risks specific to Frama-C (state them, don't paper over)
- **No Why3→Lean driver** → Lean is hand-written; the hybrid handles it (leg 1 semantically anchors Coq to
  Why3; leg 2 carries it to Lean syntactically — §4). If leg 1 is unavailable for a lemma, demote to
  single-prover; never fake dual-TP with a Lean≡Coq-only check.
- **Leg-1 TCB = the semantics + the bridge + fragment coverage (§5.8).** The trust that used to sit on a
  three-way canonicalizer now sits on (a) the published Cohen–Johnson-Freyd semantics (pinned commit),
  (b) the WP-AST→`formula` reflection (round-tripped, fail-closed), and (c) a checked fragment list. A
  net win, but these must be guarded as hard as the proofs — an unchecked construct or a wrong reflection
  is a silent hole.
- **Leg-2 canonicalizer as TCB** (§5.4b/§5.7): now scoped to "same FOL proposition across two prover
  syntaxes" — narrower than v1, but still must pass the adversarial corpus or leg 2's rigor is only apparent.
- **`R`-based theories** (`Cfloat`): Coq's `R` and Lean's `ℝ` are different axiomatizations; the *statement*
  must be modelled identically on both sides (or over a shared abstract structure) or leg 2 will —
  correctly — reject them. Treat the modelling choice as part of the certified statement. (Leg 1 likewise
  needs the real theory inside the formalized fragment, or it falls back to single-prover.)
- **`closed_satisfies_rep` is for closed integer VCs only** — the strong `decide` collapse applies to the
  SMT-escalated ACSL class, *not* the quantified realization lemmas (those use `formula_rep`-as-`Prop`
  reasoning). Don't assume the evaluation shortcut everywhere.
- **Version drift** in prover output formats / Why3 task shape → fail-closed + pinned-version smoke test
  (PyCSL P2-2); pin the Frama-C, Why3, Coq, Lean, *and* semantics-commit versions together.

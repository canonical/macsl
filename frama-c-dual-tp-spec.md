# Specification: dual Rocq/Coq + Lean proof cross-validation for Frama-C/WP

**Status:** specification (not yet implemented).
**Goal:** bring PyCSL's dual-prover axiom-plumbing rigor to the Frama-C/WP trust root — every
trust-bearing lemma that a WP green rests on must carry a **paired Coq + Lean proof of the same formula**,
mechanically cross-checked 3-way against the Why3 source, each side using only allow-listed kernel axioms.
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

**Trust property (the one mechanical predicate we must enforce per lemma `L`):**

> `canon(Why3(L)) == canon(Coq(L)) == canon(Lean(L))`  **and**  `axioms(Coq L) ⊆ A_coq`  **and**
> `axioms(Lean L) ⊆ A_lean`  **and** both proofs compile under their pinned kernels with no `Admitted`/`sorry`.

Where `Why3(L)` is the formula WP actually uses, `Coq(L)`/`Lean(L)` are the proved theorem statements, and
`A_coq`/`A_lean` are the published axiom allow-lists (§6).

---

## 2. Mapping PyCSL → Frama-C

| PyCSL | Frama-C/WP analogue |
|---|---|
| `_AXIOM_REGISTRY[qn]` (Why3 formula SMT assumes) | the WP-emitted **Why3 goal** for lemma `L` (printable Why3 task), or the `(* Why3 goal *)` statement in a `coqwp` `.v` |
| `#@ proof rocq\|lean <qn>` citation | a registry entry binding `L` → its `{coq,lean}` proof files (and, for ACSL lemmas, the C/ACSL site + `-wp-prop` selector) |
| `*.proofs/{rocq,lean}/*.{v,lean}` | `proofs/{coq,lean}/*.{v,lean}` next to the unit (or under `coqwp/` for realization lemmas) |
| `audit_proof.py` (attribution) | name-presence + axiom-cleanliness audit (extend `axiom-wp/coqwp/check.sh`) |
| `proof2why3/crosscheck_ir.py` (3-way) | **new** `dualtp` cross-check tool (this spec, §5) |
| `proof_axiom_allowlist.py` | `A_coq` / `A_lean` (§6) |
| `sync-axiom-registry` | regenerate the registry statements **from** the cross-checked IR |

---

## 3. Two classes of trust-bearing lemma in scope

1. **`coqwp` realization lemmas** — the TCB of `-wp-prover coq`. These are the `(* Why3 goal *)` lemmas in
   `Memory.v`/`Vset.v`/`Cfloat.v`/`ArcTrigo.v`/`ExpLog.v` we proved in Coq this session
   (`coqwp/*_hardened.v`). Each gets a **Lean twin** stating the same Why3 goal and a 3-way cross-check.
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

**Three anchors, three-way check (do not drop to two):**
- **`Why3(L)`** — extract the WP-emitted Why3 task formula directly (e.g. `frama-c -wp -wp-out DIR …`
  writes the `.why`/`.mlw` tasks; or `why3 prove --print-theory`/task printer). This is the independent
  ground truth — it does **not** go through the Coq driver, so it can catch a driver bug.
- **`Coq(L)`** — `coqc`/SerAPI `Check L` on the `coqwp`/escalation `.v`.
- **`Lean(L)`** — `lake env lean` `#check L` on the hand-written `.lean`.

Canonicalize all three to a shared first-order IR and require structural equality. The Coq↔Why3 agreement
re-confirms the driver; the Lean↔Why3 agreement is the independent cross-encoding. **If extracting a clean
`Why3(L)` is infeasible for some `L`, that lemma is NOT eligible for dual-TP certification — record it as a
single-prover (`coqwp`-hardened) result instead. Never silently fall back to a 2-way Coq≡Lean check and
call it 3-way.**

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
- Coq: SerAPI (`sertop`) or `coqc` companion `Check`. (Coq 8.20.1, the `framac-coq8` switch.)
- Lean: `lake env lean` with appended `#check`. (Lean 4, pinned version.)
- Why3: WP task printer / `-wp-out`. Pin the Frama-C + Why3 versions.
- **Empty extraction is a hard error, never "trivially equal"** (PyCSL P0-2).

### 5.4 Canonical IR + 3-way equality (`dualtp/canonical.py`, `dualtp/crosscheck.py`)
Shared first-order IR (quantifiers, connectives, arithmetic, uninterpreted symbols, sorts). `canonicalize`
must normalize: bound-variable names (de Bruijn or consistent α-renaming), binder grouping
(`∀x y` ≡ `∀x, ∀y`), associative/commutative flattening where semantically valid, `0<=k<16` vs
`0<=k ∧ k<16`, integer-literal forms, and notation vs raw. **The canonicalizer is the new TCB** — see 5.7.

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
deliberately-weakened canonicalizer must turn this suite red. This is the highest-value foundational task —
the 3-way check is only as sound as this.

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
1. **Pilot — `Memory.separated_trans`** (1 lemma): write the Lean twin, build `extract`/`canonical`/
   `crosscheck` minimally, wire CI + the adversarial corpus skeleton. End-to-end 3-way green on one lemma
   *with CI and fail-closed semantics* before scaling. (Mirror the coqwp pilot discipline.)
2. **`Memory.v`** — the remaining 10 hardened lemmas (highest value: separation algebra under every proof).
3. **`Vset.v`** (11), then **`Cfloat.v`** (32) / `ArcTrigo` / `ExpLog` — note these are `R`-based, so
   `A_coq` includes `sig_forall_dec`; design the Lean twins to land in `A_lean` (Lean's reals differ —
   decide whether to model over `ℝ` or an abstract ordered field; document the modelling choice as part of
   the statement, exactly as `axiom-wp/coqwp/Cfloat_hardened.v` clamps to `[-max,max]`).
4. **SMT-escalated ACSL lemmas** (gcd-style), per unit, via the escalation workflow + Lean twin.
Each phase: registry entries + Lean twins + 3-way green in CI + axioms recorded. Track in a
`axiom-wp/DUALTP-STATUS.md` like `AUDIT.md`.

## 8. Gate semantics & acceptance criteria (per lemma and aggregate)
A lemma is **dual-TP certified** iff, in CI on pinned toolchains:
- [ ] Coq `.v` compiles, no `Admitted`; `Print Assumptions L ⊆ A_coq`.
- [ ] Lean `.lean` compiles, no `sorry`; `#print axioms L ⊆ A_lean`.
- [ ] `canon(Why3(L)) == canon(Coq(L)) == canon(Lean(L))` (3-way, none skipped).
- [ ] Registry entry present; its statement matches the cross-checked IR (`sync` is a fixpoint).
- [ ] The lemma is **load-bearing**: removing the Coq side reddens a real WP goal (the `coq-escalation.md`
  "each lemma load-bearing" gate) — a dead certified lemma is a smell.
Aggregate gate (`make dualtp-verify`): every registry lemma certified; **INFRA-MISSING ⇒ non-zero**; the
canonicalizer adversarial corpus green.

## 9. Toolchain
- Coq **8.20.1** on the `framac-coq8` opam switch (Coq before Why3; see `axiom-wp/coqwp/AUDIT.md` / `axiom-wp.yml`).
- Frama-C **32.1** / Why3 **1.8.2** (the task printer for `Why3(L)`).
- **Lean 4** (pinned `lean-toolchain`), core only where possible (avoid Mathlib to keep `A_lean` tight);
  use the `lean` skill for proof authoring and `#print axioms` discipline.
- SerAPI (`sertop`) for robust Coq statement extraction.

## 10. Risks specific to Frama-C (state them, don't paper over)
- **No Why3→Lean driver** → Lean is hand-written; the 3-way check is what makes it trustworthy (§4). If
  `Why3(L)` can't be cleanly extracted, demote to single-prover, don't fake 3-way.
- **`R`-based theories** (`Cfloat`): Coq's `R` and Lean's `ℝ` are different axiomatizations; the *statement*
  must be modelled identically on both sides (or over a shared abstract structure) or the 3-way check will —
  correctly — reject them. Treat the modelling choice as part of the certified statement.
- **Canonicalizer as TCB** (§5.7): the manual trust assumption moves into the IR layer; it must be
  adversarially tested or the whole scheme's rigor is only apparent.
- **Version drift** in prover output formats → fail-closed + pinned-version smoke test (PyCSL P2-2).

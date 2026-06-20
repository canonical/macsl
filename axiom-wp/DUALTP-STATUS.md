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

| Lemma | Coq | Lean | 3-way crosscheck | Certified? |
|---|---|---|---|---|
| `Memory.separated_trans` | ✅ Closed-under-global-context | ✅ `{propext, Classical.choice, Quot.sound}` | ⛔ tooling not built | **partial** (both proofs hold; 3-way pending) |

**Pilot note (Phase 1).** `Memory.separated_trans` is the spec's pilot. Both proofs are written and
**independently verified** (Coq via `coqwp/check.sh`; Lean 4.31.0 via `leanwp/check.sh`), and the two
statements were authored to be structurally identical to WP's Why3 goal. What is **not yet mechanical** is
the 3-way structural equality check (`dualtp/`, spec §5.4) that would prove `Why3 ≡ Coq ≡ Lean` rather than
relying on human eyeballing. Until that tool exists and gates, this lemma is **partial**, not certified —
do not report it as fully dual-TP.

## Lean axiom bar — note (matches the PyCSL audit finding P1-1)
The verified Lean proof depends on `{propext, Classical.choice, Quot.sound}` — the **standard** Lean kernel
axiom set (what the `lean` skill's Quality Gate accepts). The spec's earlier "constructive" wording
(`⊆ {propext, Quot.sound}`) was aspirational; `Classical.choice` is standard and effectively unavoidable
(`by_cases`, `Int`), so `leanwp/check.sh` and `frama-c-dual-tp-spec.md §6` use the standard set and name it
honestly. This is exactly the code-vs-doc alignment the PyCSL audit flagged — applied here from day one.

## Next (per spec §7)
1. Build the `dualtp/` 3-way cross-check (extract Coq `Check` + Lean `#check` + Why3 task → shared IR →
   canonicalize → structural `==`), **with its adversarial canonicalizer corpus** (spec §5.7) from the start.
2. Flip `Memory.separated_trans` to **certified** once the 3-way passes in CI.
3. Add Lean twins for the rest of `Memory.v` (10 lemmas), then `Vset.v`, then the `R`-based theories.

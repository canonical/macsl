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

## Leg 1 (semantic Why3↔Coq) — spike DONE, build BLOCKED on coq-elpi
See `leg1/`. Grounded: the verbatim `Why3(separated_trans)` is extracted
(`leg1/why3-separated_trans.mlw`, from WP's `memaddr.mlw`), Why3≡Coq≡Lean confirmed
by inspection; **fragment coverage PASS**. Toolchain update: the semantics has a
**`coq-8.20` branch** — it builds on Coq 8.20.1 (no Rocq-9 split, contrary to the
first spike). Coq + Equations + std++ + ext-lib install fine.

**BLOCKER (this session):** building the semantics needs MathComp 2.x (`Types.v`
uses `HB.instance`) → Hierarchy Builder → **coq-elpi**, and coq-elpi **fails to
build in this environment** — identically across 2.3.0 / 2.5.2 / rocq-elpi 3.2.0:
`elpi_plugin.cmxs: No such file` (environmental, version-independent; `ocamlopt`
works). So `formula_rep` is unbuildable here and the obligation is **not started**.
Resolve on a Coq-Platform / prebuilt-coq-elpi environment, then resume at
`leg1/README.md` §5. No green is claimed.

## Next (per spec §7)
1. **Leg 1:** execute `leg1/README.md` §5 — vendor+build the full semantics under
   Rocq 9, write `⟦separated_trans⟧` + the bridge round-trip, prove the obligation.
2. **Leg 2:** build the `dualtp/` Coq↔Lean cross-check (extract Coq `Check` + Lean
   `#check` → shared IR → canonical `==`), **with its adversarial canonicalizer
   corpus** (spec §5.7) from the start.
3. Flip `Memory.separated_trans` to **certified** once both legs pass in CI.
4. Add Lean twins for the rest of `Memory.v` (10 lemmas), then `Vset.v`, then the
   `R`-based theories.

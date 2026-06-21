# dualtp — the `Why3 ≡ Coq ≡ Lean` cross-check

This is the hybrid 3-way cross-check of `../../docs/frama-c-dual-tp-spec.md` §5.4. A trust-bearing
coqwp lemma `L` is **dual-TP certified** when both legs hold:

1. **Leg 1 — semantic Why3 ↔ Coq** (`../leg1/`): a Coq proof, against the joscoh
   `why3-semantics` denotational model, that the coqwp lemma is the denotation of the
   Why3 goal (`separated_trans_Coq ⟺ formula_rep … ⟦Why3(L)⟧`). No canonicalizer is on this
   leg; its soundness rests on the published semantics + the §5.8 bridge. Status: the pilot
   (`Memory.separated_trans`) is reduced to one mechanical cast-cancellation lemma — see
   `../leg1/`.

2. **Leg 2 — syntactic Coq ↔ Lean** (this directory): extract each lemma's first-order
   statement from Coq and from Lean, canonicalize both to a shared FOL IR, and require
   structural equality. The canonicalizer is the TCB of *this leg only* (§5.4b) and is
   adversarially tested (§5.7).

## Files
- `canonical.py` — the shared FOL IR + canonicalizer. Unifies operator spellings
  (`-> ≡ →`, `/\ ≡ ∧`, `<= ≡ ≤`, `<> ≡ ≠ ≡ ~(=)`, `~ ≡ ¬ ≡ not`), cross-prover symbol/type
  aliases (`Reals.Rtrigo1.PI ≡ Real.pi`, `Z ≡ Int ≡ ℤ`, `R ≡ ℝ`, `addr ≡ Addr`), and
  bound-variable names (de Bruijn). It does **not** reorder operands of any operator, so
  swapped-operand / dropped-conjunct / off-by-one mutations stay distinct.
- `corpus.py` — the adversarial corpus (§5.7): ≥20 positive pairs (same proposition,
  different surface/prover → MUST canon equal) and ≥20 negative pairs (almost-equal but
  distinct → MUST canon unequal), including pilot mutations.
- `test_canonical.py` — runs the corpus fail-closed, checks the ≥20/≥20 floor, checks canon
  determinism, and a **meta-check**: a deliberately weakened canonicalizer must turn the
  corpus red (proving it discriminates).
- `pairs.py` — the actual Coq/Lean statement pairs cross-checked, transcribed from
  `../coqwp/*_hardened.v` and `../leanwp/**/*.lean`, plus `OUT_OF_FRAGMENT` (lemmas whose
  statement leaves the FOL fragment — honest scope, §5.8).
- `crosscheck.py` — the leg-2 driver: `canon(Coq) == canon(Lean)` per lemma, fail-closed.
- `check.sh` — runs both, fail-closed.

## Run
```sh
bash axiom-wp/dualtp/check.sh
```

## Current leg-2 coverage
Cross-checked Coq ≡ Lean: `Memory.separated_trans`, `Memory.included_trans`,
`Memory.separated_included`, `Trigonometry.Pi_double_precision_bounds`. The remaining
families' statements leave the FOL fragment (float predicates, set-membership over a
function model, record-constructor equality) and are listed in `pairs.OUT_OF_FRAGMENT`;
extending the canonicalizer to them is future work, not a silent pass.

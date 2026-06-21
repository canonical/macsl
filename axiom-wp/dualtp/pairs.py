#!/usr/bin/env python3
"""
dualtp/pairs.py — the actual Coq/Lean statement pairs cross-checked by leg 2
(../../docs/frama-c-dual-tp-spec.md §5.4b). Each entry is the first-order proposition of a
trust-bearing coqwp lemma, transcribed faithfully from:
  - Coq : axiom-wp/coqwp/*_hardened.v   (the `Lemma <name> : <stmt>.`)
  - Lean: axiom-wp/leanwp/**/*.lean      (the `theorem <name> … : <concl>` ,
          curried hypotheses read as an implication chain)

The cross-check (crosscheck.py) requires canon(coq) == canon(lean) for each.

FRAGMENT COVERAGE (§5.8). The leg-2 canonicalizer covers the first-order fragment
(quantifiers, connectives, (dis)equality, order, integer/real arithmetic,
uninterpreted predicate/relation symbols). Lemmas whose *statement* leaves that
fragment — Cfloat's float-classification predicates, Vset's set-membership over a
function model, Memory.separated_1's record-constructor equality — are listed in
OUT_OF_FRAGMENT with the reason; they are honestly NOT yet leg-2 cross-checked
(extending the canonicalizer to them is future work, not a silent pass).
"""

PAIRS = {
    # --- Memory (the pilot family) ---
    "Memory.separated_trans": {
        "coq": "forall p q r : addr, forall a b c : Z, "
               "included p a q b -> separated q b r c -> separated p a r c",
        "lean": "∀ p q r : Addr, ∀ a b c : Int, "
                "included p a q b → separated q b r c → separated p a r c",
    },
    "Memory.included_trans": {
        "coq": "forall p q r : addr, forall a b c : Z, "
               "included p a q b -> included q b r c -> included p a r c",
        "lean": "∀ p q r : Addr, ∀ a b c : Int, "
                "included p a q b → included q b r c → included p a r c",
    },
    "Memory.separated_included": {
        "coq": "forall p q : addr, forall a b : Z, "
               "0 < a -> 0 < b -> separated p a q b -> ~ included p a q b",
        "lean": "∀ p q : Addr, ∀ a b : Int, "
                "0 < a → 0 < b → separated p a q b → ¬ included p a q b",
    },
    # --- Trigonometry: the π double-precision bracket (denominator 2^51) ---
    "Trigonometry.Pi_double_precision_bounds": {
        "coq": "7074237752028440 / 2251799813685248 < Reals.Rtrigo1.PI /\\ "
               "Reals.Rtrigo1.PI < 7074237752028441 / 2251799813685248",
        "lean": "7074237752028440 / 2251799813685248 < Real.pi ∧ "
                "Real.pi < 7074237752028441 / 2251799813685248",
    },
}

# lemmas whose statement is outside the current leg-2 FOL fragment (honest scope)
OUT_OF_FRAGMENT = {
    "Memory.separated_1": "record-constructor equality (Addr.mk b i = Addr.mk b' j)",
    "Vset.*": "set membership over a function model (member s x = s x : Bool)",
    "Cfloat.*": "float classification predicates (is_finite / of_f32 / clamp)",
    "ArcTrigo.*": "transcendental application on a closed interval",
    "ExpLog.*": "transcendental application (Real.exp)",
}

#!/usr/bin/env python3
"""
dualtp/corpus.py — the canonicalizer adversarial corpus (../../docs/frama-c-dual-tp-spec.md §5.7).

POSITIVE pairs: same first-order proposition, different surface syntax or different
prover (Coq vs Lean spelling). MUST canonicalize EQUAL.

NEGATIVE pairs: almost-equal but genuinely distinct propositions (swapped operand of
a non-commutative op, off-by-one constant, dropped conjunct, wrong connective,
wrong relation, …). MUST canonicalize UNEQUAL.

A deliberately-weakened canonicalizer must turn this suite red (see test_canonical.py).
"""

# (coq-ish surface, lean-ish surface)  -- must be EQUAL after canon
POSITIVE = [
    # implication spelling Coq -> vs Lean →
    ("forall x : Z, x = x -> x = x", "∀ x : Int, x = x → x = x"),
    # type alias Z ≡ Int ≡ ℤ
    ("forall n : Z, n + 0 = n", "∀ n : ℤ, n + 0 = n"),
    # <= vs ≤
    ("forall a b : Z, a <= b -> a <= b", "∀ a b : Int, a ≤ b → a ≤ b"),
    # >= vs ≥
    ("forall a b : Z, a >= b -> a >= b", "∀ a b : Int, a ≥ b → a ≥ b"),
    # disequality: <>  vs  ≠  vs  ~ (a = b)
    ("forall a b : Z, a <> b", "∀ a b : Int, a ≠ b"),
    ("forall a b : Z, ~ (a = b)", "∀ a b : Int, a ≠ b"),
    # negation spelling ~ vs ¬ vs not
    ("forall p : Prop, ~ p \\/ p", "∀ p : Prop, ¬ p ∨ p"),
    ("forall p : Prop, not p \\/ p", "∀ p : Prop, ¬ p ∨ p"),
    # conj / disj spelling
    ("forall a b : Z, a = a /\\ b = b", "∀ a b : Int, a = a ∧ b = b"),
    ("forall a b : Z, a = a \\/ b = b", "∀ a b : Int, a = a ∨ b = b"),
    # iff spelling
    ("forall p q : Prop, p <-> q", "∀ p q : Prop, p ↔ q"),
    # bound-variable renaming is irrelevant (de Bruijn)
    ("forall x : Z, x = x", "∀ y : Int, y = y"),
    ("forall a b : Z, a + b = b + a", "∀ x y : Int, x + y = y + x"),
    # the real cross-prover constant: Reals.Rtrigo1.PI ≡ Real.pi
    ("3 < Reals.Rtrigo1.PI", "3 < Real.pi"),
    ("Reals.Rtrigo1.PI < 4", "Real.pi < 4"),
    # multi-binder grouping ≡ nested binders
    ("forall a b : Z, a = b", "∀ a : Int, ∀ b : Int, a = b"),
    # application surface  f(a,b) ≡ f a b
    ("forall p q : addr, included p q", "∀ p q : Addr, included p q"),
    # nested implication right-assoc, with conj
    ("forall a b : Z, a = b /\\ b = a -> a = a",
     "∀ a b : Int, a = b ∧ b = a → a = a"),
    # the pi double-precision bracket (Coq /\ pair vs Lean ∧), same rationals
    ("7074237752028440 / 2251799813685248 < Reals.Rtrigo1.PI /\\ "
     "Reals.Rtrigo1.PI < 7074237752028441 / 2251799813685248",
     "7074237752028440 / 2251799813685248 < Real.pi ∧ "
     "Real.pi < 7074237752028441 / 2251799813685248"),
    # decimal normalization: 3.14 ≡ 3.140
    ("3.14 < Reals.Rtrigo1.PI", "3.140 < Real.pi"),
    # the separated_trans pilot (Coq vs Lean), variable renaming + spellings
    ("forall p q r : addr, forall lp lq lr : Z, "
     "included p lp q lq -> separated q lq r lr -> separated p lp r lr",
     "∀ a b c : Addr, ∀ la lb lc : Int, "
     "included a la b lb → separated b lb c lc → separated a la c lc"),
]

# (stmt A, stmt B)  -- must be UNEQUAL after canon
NEGATIVE = [
    # swapped operands of implication (non-commutative)
    ("forall a b : Prop, a -> b", "forall a b : Prop, b -> a"),
    # swapped operands of subtraction
    ("forall a b : Z, a - b = 0", "forall a b : Z, b - a = 0"),
    # swapped operands of <
    ("forall a b : Z, a < b", "forall a b : Z, b < a"),
    # off-by-one constant
    ("3.141592 < Reals.Rtrigo1.PI", "3.141593 < Reals.Rtrigo1.PI"),
    ("7074237752028440 / 2251799813685248 < Reals.Rtrigo1.PI",
     "7074237752028441 / 2251799813685248 < Reals.Rtrigo1.PI"),
    # dropped conjunct
    ("forall a b : Z, a = a /\\ b = b", "forall a b : Z, a = a"),
    # wrong connective:  /\  vs  \/
    ("forall a b : Prop, a /\\ b", "forall a b : Prop, a \\/ b"),
    # wrong relation:  <  vs  <=
    ("forall a b : Z, a < b", "forall a b : Z, a <= b"),
    # negation dropped
    ("forall a : Prop, ~ a", "forall a : Prop, a"),
    # different predicate
    ("forall p q : addr, included p q", "forall p q : addr, separated p q"),
    # arg order in a predicate application (non-commutative)
    ("forall p q : addr, included p q", "forall p q : addr, included q p"),
    # iff vs imp
    ("forall p q : Prop, p <-> q", "forall p q : Prop, p -> q"),
    # = vs <>
    ("forall a b : Z, a = b", "forall a b : Z, a <> b"),
    # extra quantifier
    ("forall a : Z, a = a", "forall a b : Z, a = a"),
    # different bound type (Z vs R are NOT aliased to each other)
    ("forall a : Z, a = a", "forall a : R, a = a"),
    # constant vs variable
    ("forall a : Z, a = 0", "forall a : Z, a = 1"),
    # swapped implication antecedent/consequent in a 3-chain (pilot mutation)
    ("forall p q r : addr, forall lp lq lr : Z, "
     "included p lp q lq -> separated q lq r lr -> separated p lp r lr",
     "forall p q r : addr, forall lp lq lr : Z, "
     "separated q lq r lr -> included p lp q lq -> separated p lp r lr"),
    # wrong conclusion in the pilot (separated p lp r lr  ->  separated p lp q lq)
    ("forall p q r : addr, forall lp lq lr : Z, "
     "included p lp q lq -> separated q lq r lr -> separated p lp r lr",
     "forall p q r : addr, forall lp lq lr : Z, "
     "included p lp q lq -> separated q lq r lr -> separated p lp q lq"),
    # addition vs multiplication
    ("forall a b : Z, a + b = 0", "forall a b : Z, a * b = 0"),
    # off-by-one in a bound variable index usage (a vs b in conclusion)
    ("forall a b : Z, a = b -> a = a", "forall a b : Z, a = b -> b = b"),
    # le vs ge
    ("forall a b : Z, a <= b", "forall a b : Z, a >= b"),
]

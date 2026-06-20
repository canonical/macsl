/-
  Memory.lean — Lean 4 twin of WP's coqwp `Memory` realization lemmas.
  Pilot for the dual Coq+Lean cross-validation (see ../../frama-c-dual-tp-spec.md).

  VERIFIED: Lean 4.31.0, `lean Memory.lean` exit 0, and
  `#print axioms separated_trans` = [propext, Classical.choice, Quot.sound]
  — the standard Lean kernel-axiom set (no `sorry`, no custom axiom). The Coq
  twin (../coqwp/Memory_hardened.v `separated_trans`) is "Closed under the
  global context". Both sides of the pilot now hold.

  The statement is structurally identical to the Coq twin and to WP's Why3 goal
  — that equality is what the 3-way cross-check (../../frama-c-dual-tp-spec.md
  §5.4) will enforce once the `dualtp` tooling is built (still TODO; see
  ../DUALTP-STATUS.md). Definitions mirror Memory_hardened.v verbatim
  (Coq `Z` ↦ Lean `Int`).
-/

namespace Frama.Memory

/-- Address = (base, offset), mirroring Coq `Inductive addr := mk_addr : Z -> Z -> addr`. -/
structure Addr where
  base : Int
  offset : Int

/-- `included p a q b` — the `[p, p+a)` block sits inside `[q, q+b)` (when `a>0`).
    Verbatim image of Memory_hardened.v `included`. -/
def included (p : Addr) (a : Int) (q : Addr) (b : Int) : Prop :=
  0 < a →
    0 ≤ b ∧ p.base = q.base ∧ q.offset ≤ p.offset ∧ p.offset + a ≤ q.offset + b

/-- `separated p a q b` — the blocks `[p,p+a)` and `[q,q+b)` do not overlap.
    Verbatim image of Memory_hardened.v `separated`. -/
def separated (p : Addr) (a : Int) (q : Addr) (b : Int) : Prop :=
  a ≤ 0 ∨ b ≤ 0 ∨ p.base ≠ q.base ∨
    q.offset + b ≤ p.offset ∨ p.offset + a ≤ q.offset

/-- Why3 goal (coqwp `Memory.separated_trans`): inclusion composes with
    separation.  Same statement as Memory_hardened.v `separated_trans`. -/
theorem separated_trans
    (p q r : Addr) (a b c : Int)
    (hinc : included p a q b) (hsep : separated q b r c) :
    separated p a r c := by
  unfold included separated at *
  by_cases ha : 0 < a
  · -- a > 0: discharge `included`; omega closes the disjunctive goal from the
    -- inclusion conjunction + the separation disjunction (handles ∧/∨/=/≠ on Int).
    have hh := hinc ha
    omega
  · -- a ≤ 0: separation holds by its first disjunct.
    omega

-- Axiom audit (the reverify gate will read this line):
#print axioms separated_trans

end Frama.Memory

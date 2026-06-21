/-
  RealFloat.lean — mathlib-dependent Lean twins of coqwp lemmas:
  the addr↔Z bijection (Memory), ArcTrigo, ExpLog. (Cfloat below; the π bound is
  tracked separately — mathlib lacks a tight enough Real.pi bound.)
  Axioms must stay within {propext, Classical.choice, Quot.sound} (mathlib's set).
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Logic.Denumerable

namespace Frama.RealFloat
open Real

/-- ExpLog: exp is positive (coqwp `ExpLog.exp_pos`). -/
theorem exp_pos (x : ℝ) : 0 < Real.exp x := Real.exp_pos x

/-- ArcTrigo: `sin (asin x) = x` on `[-1,1]` (coqwp `ArcTrigo.Sin_asin`). -/
theorem Sin_asin (x : ℝ) (h : -1 ≤ x ∧ x ≤ 1) : Real.sin (Real.arcsin x) = x :=
  Real.sin_arcsin h.1 h.2

/-- ArcTrigo: `cos (acos x) = x` on `[-1,1]` (coqwp `ArcTrigo.Cos_acos`). -/
theorem Cos_acos (x : ℝ) (h : -1 ≤ x ∧ x ≤ 1) : Real.cos (Real.arccos x) = x :=
  Real.cos_arccos h.1 h.2

/-- Memory addr↔Z bijection, realized via `Denumerable` (witness; coqwp used Cantor).
    Offset by `e (0,0)` so that `int_of_addr null = 0`. -/
structure Addr where
  base : Int
  offset : Int

noncomputable def e : (ℤ × ℤ) ≃ ℤ := (Denumerable.eqv (ℤ × ℤ)).trans (Denumerable.eqv ℤ).symm
noncomputable def int_of_addr (p : Addr) : ℤ := e (p.base, p.offset) - e (0, 0)
noncomputable def addr_of_int (z : ℤ) : Addr := let q := e.symm (z + e (0, 0)); ⟨q.1, q.2⟩
def null : Addr := ⟨0, 0⟩

theorem int_of_addr_bijection (z : ℤ) : int_of_addr (addr_of_int z) = z := by
  unfold int_of_addr addr_of_int
  simp [Equiv.apply_symm_apply]

theorem addr_of_int_bijection (p : Addr) : addr_of_int (int_of_addr p) = p := by
  unfold int_of_addr addr_of_int
  simp [Equiv.symm_apply_apply]

theorem addr_of_null : int_of_addr null = 0 := by
  unfold int_of_addr null; simp

#print axioms exp_pos
#print axioms Sin_asin
#print axioms Cos_acos
#print axioms int_of_addr_bijection
#print axioms addr_of_int_bijection
#print axioms addr_of_null

end Frama.RealFloat

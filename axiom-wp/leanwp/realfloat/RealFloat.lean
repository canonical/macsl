/-
  RealFloat.lean — mathlib-dependent Lean twins of coqwp lemmas:
  the addr↔Z bijection (Memory), ArcTrigo, ExpLog, and the π bound (Trigonometry).
  Axioms must stay within {propext, Classical.choice, Quot.sound} (mathlib's set).
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds
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

/-- Trigonometry: the 1-ulp-at-2⁻⁵¹ bracket on π (coqwp `Trigonometry.Pi_double_precision_bounds`,
    proved on the Coq side with CoqInterval). Discharged here from mathlib's 20-digit bracket
    `Real.pi_gt_d20` / `Real.pi_lt_d20`; the 2⁻⁵¹ window is ~16 digits, well inside it. The two
    endpoints reduce to rational comparisons (`norm_num`). Denominator 2251799813685248 = 2⁵¹. -/
theorem Pi_double_precision_bounds :
    (7074237752028440 / 2251799813685248 : ℝ) < Real.pi ∧
    Real.pi < (7074237752028441 / 2251799813685248 : ℝ) := by
  refine ⟨?_, ?_⟩
  · calc (7074237752028440 / 2251799813685248 : ℝ)
          ≤ 3.14159265358979323846 := by norm_num
        _ < Real.pi := Real.pi_gt_d20
  · calc Real.pi
          < 3.14159265358979323847 := Real.pi_lt_d20
        _ ≤ (7074237752028441 / 2251799813685248 : ℝ) := by norm_num

#print axioms exp_pos
#print axioms Sin_asin
#print axioms Cos_acos
#print axioms int_of_addr_bijection
#print axioms addr_of_int_bijection
#print axioms addr_of_null
#print axioms Pi_double_precision_bounds

end Frama.RealFloat

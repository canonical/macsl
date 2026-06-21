/-
  Cfloat.lean — Lean twins of coqwp Cfloat_hardened.v's 32 lemmas.
  Float model = ℝ with `clamp` into [-max,max] (verbatim image of Cfloat_hardened.v).
  Axioms must stay within {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
namespace Frama.Cfloat
open scoped Classical
noncomputable section

def max32 : ℝ := 340282346600000016151267322115014000640
def max64 : ℝ := 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368

theorem max32_ge1 : 1 ≤ max32 := by unfold max32; norm_num
theorem max64_ge1 : 1 ≤ max64 := by unfold max64; norm_num

def clamp (m x : ℝ) : ℝ := min (max x (-m)) m

theorem clamp_in (m x : ℝ) (h : 1 ≤ m) : -m ≤ clamp m x ∧ clamp m x ≤ m := by
  unfold clamp
  refine ⟨?_, min_le_right _ _⟩
  rw [le_min_iff]
  exact ⟨le_max_right _ _, by linarith⟩

theorem clamp_id (m x : ℝ) (h : -m ≤ x ∧ x ≤ m) : clamp m x = x := by
  unfold clamp
  rw [max_eq_left h.1, min_eq_left h.2]

-- model
abbrev f32 := ℝ
abbrev f64 := ℝ
def of_f32 (f : f32) : ℝ := f
def of_f64 (d : f64) : ℝ := d
def to_f32 (x : ℝ) : f32 := clamp max32 x
def to_f64 (x : ℝ) : f64 := clamp max64 x

inductive rounding_mode | Up | Down | ToZero | NearestTiesToAway | NearestTiesToEven
def round_float (_ : rounding_mode) (x : ℝ) : f32 := to_f32 x
def round_double (_ : rounding_mode) (x : ℝ) : f64 := to_f64 x

inductive float_kind | Finite | NaN | Inf_pos | Inf_neg
deriving DecidableEq

def classify_f32 (f : f32) : float_kind :=
  if -max32 ≤ f then (if f ≤ max32 then float_kind.Finite else float_kind.Inf_pos) else float_kind.Inf_neg
def classify_f64 (d : f64) : float_kind :=
  if -max64 ≤ d then (if d ≤ max64 then float_kind.Finite else float_kind.Inf_pos) else float_kind.Inf_neg
def is_finite_f32 (f : f32) : Prop := classify_f32 f = float_kind.Finite
def is_finite_f64 (d : f64) : Prop := classify_f64 d = float_kind.Finite

def eq_f32b (x y : f32) : Bool := decide (of_f32 x = of_f32 y)
def eq_f64b (x y : f64) : Bool := decide (of_f64 x = of_f64 y)
def ne_f32b (x y : f32) : Bool := !(eq_f32b x y)
def ne_f64b (x y : f64) : Bool := !(eq_f64b x y)
def le_f32b (x y : f32) : Bool := decide (of_f32 x ≤ of_f32 y)
def le_f64b (x y : f64) : Bool := decide (of_f64 x ≤ of_f64 y)
def lt_f32b (x y : f32) : Bool := decide (of_f32 x < of_f32 y)
def lt_f64b (x y : f64) : Bool := decide (of_f64 x < of_f64 y)
def eq_f32 (x y : f32) : Prop := eq_f32b x y = true
def eq_f64 (x y : f64) : Prop := eq_f64b x y = true
def ne_f32 (x y : f32) : Prop := ne_f32b x y = true
def ne_f64 (x y : f64) : Prop := ne_f64b x y = true
def le_f32 (x y : f32) : Prop := le_f32b x y = true
def le_f64 (x y : f64) : Prop := le_f64b x y = true
def lt_f32 (x y : f32) : Prop := lt_f32b x y = true
def lt_f64 (x y : f64) : Prop := lt_f64b x y = true

def neg_f32 (x : f32) : f32 := -x
def neg_f64 (x : f64) : f64 := -x
def add_f32 (x y : f32) : f32 := to_f32 (of_f32 x + of_f32 y)
def add_f64 (x y : f64) : f64 := to_f64 (of_f64 x + of_f64 y)
def mul_f32 (x y : f32) : f32 := to_f32 (of_f32 x * of_f32 y)
def mul_f64 (x y : f64) : f64 := to_f64 (of_f64 x * of_f64 y)
def div_f32 (x y : f32) : f32 := to_f32 (of_f32 x / of_f32 y)
def div_f64 (x y : f64) : f64 := to_f64 (of_f64 x / of_f64 y)
def sqrt_f32 (x : f32) : f32 := to_f32 (Real.sqrt (of_f32 x))
def sqrt_f64 (x : f64) : f64 := to_f64 (Real.sqrt (of_f64 x))

theorem finite32_iff (f : f32) : is_finite_f32 f ↔ -max32 ≤ of_f32 f ∧ of_f32 f ≤ max32 := by
  unfold is_finite_f32 classify_f32 of_f32
  by_cases h1 : -max32 ≤ f <;> by_cases h2 : f ≤ max32 <;> simp [h1, h2]
theorem finite64_iff (d : f64) : is_finite_f64 d ↔ -max64 ≤ of_f64 d ∧ of_f64 d ≤ max64 := by
  unfold is_finite_f64 classify_f64 of_f64
  by_cases h1 : -max64 ≤ d <;> by_cases h2 : d ≤ max64 <;> simp [h1, h2]

theorem to_f32_zero : of_f32 (to_f32 0) = 0 := by
  unfold of_f32 to_f32; rw [clamp_id]; exact ⟨by linarith [max32_ge1], by linarith [max32_ge1]⟩
theorem to_f32_one : of_f32 (to_f32 1) = 1 := by
  unfold of_f32 to_f32; rw [clamp_id]; exact ⟨by linarith [max32_ge1], by linarith [max32_ge1]⟩
theorem to_f64_zero : of_f64 (to_f64 0) = 0 := by
  unfold of_f64 to_f64; rw [clamp_id]; exact ⟨by linarith [max64_ge1], by linarith [max64_ge1]⟩
theorem to_f64_one : of_f64 (to_f64 1) = 1 := by
  unfold of_f64 to_f64; rw [clamp_id]; exact ⟨by linarith [max64_ge1], by linarith [max64_ge1]⟩

theorem float_32 (x : ℝ) : to_f32 x = round_float rounding_mode.NearestTiesToEven x := rfl
theorem float_64 (x : ℝ) : to_f64 x = round_double rounding_mode.NearestTiesToEven x := rfl

theorem is_finite_to_float_32 (x : ℝ) : is_finite_f32 (to_f32 x) := by
  rw [finite32_iff]; unfold of_f32 to_f32; exact clamp_in _ _ max32_ge1
theorem is_finite_to_float_64 (x : ℝ) : is_finite_f64 (to_f64 x) := by
  rw [finite64_iff]; unfold of_f64 to_f64; exact clamp_in _ _ max64_ge1

theorem to_float_is_finite_32 (f : f32) (h : is_finite_f32 f) : to_f32 (of_f32 f) = f := by
  rw [finite32_iff] at h; unfold to_f32 of_f32 at *; exact clamp_id _ _ h
theorem to_float_is_finite_64 (d : f64) (h : is_finite_f64 d) : to_f64 (of_f64 d) = d := by
  rw [finite64_iff] at h; unfold to_f64 of_f64 at *; exact clamp_id _ _ h

theorem finite_small_f32 (x : ℝ) (_ : -max64 ≤ x ∧ x ≤ max32) : is_finite_f32 (to_f32 x) :=
  is_finite_to_float_32 x
theorem finite_small_f64 (x : ℝ) (_ : -max64 ≤ x ∧ x ≤ max64) : is_finite_f64 (to_f64 x) :=
  is_finite_to_float_64 x

theorem finite_range_f32 (f : f32) : is_finite_f32 f ↔ (-max32 ≤ of_f32 f ∧ of_f32 f ≤ max32) :=
  finite32_iff f
theorem finite_range_f64 (d : f64) : is_finite_f64 d ↔ (-max64 ≤ of_f64 d ∧ of_f64 d ≤ max64) :=
  finite64_iff d

theorem eq_finite_f32 (x y : f32) (_ : is_finite_f32 x) (_ : is_finite_f32 y) :
    eq_f32 x y ↔ of_f32 x = of_f32 y := by simp [eq_f32, eq_f32b]
theorem eq_finite_f64 (x y : f64) (_ : is_finite_f64 x) (_ : is_finite_f64 y) :
    eq_f64 x y ↔ of_f64 x = of_f64 y := by simp [eq_f64, eq_f64b]
theorem ne_finite_f32 (x y : f32) (_ : is_finite_f32 x) (_ : is_finite_f32 y) :
    ne_f32 x y ↔ ¬ (of_f32 x = of_f32 y) := by
  simp [ne_f32, ne_f32b, eq_f32b]
theorem ne_finite_f64 (x y : f64) (_ : is_finite_f64 x) (_ : is_finite_f64 y) :
    ne_f64 x y ↔ ¬ (of_f64 x = of_f64 y) := by
  simp [ne_f64, ne_f64b, eq_f64b]
theorem le_finite_f32 (x y : f32) (_ : is_finite_f32 x) (_ : is_finite_f32 y) :
    le_f32 x y ↔ of_f32 x ≤ of_f32 y := by simp [le_f32, le_f32b]
theorem le_finite_f64 (x y : f64) (_ : is_finite_f64 x) (_ : is_finite_f64 y) :
    le_f64 x y ↔ of_f64 x ≤ of_f64 y := by simp [le_f64, le_f64b]
theorem lt_finite_f32 (x y : f32) (_ : is_finite_f32 x) (_ : is_finite_f32 y) :
    lt_f32 x y ↔ of_f32 x < of_f32 y := by simp [lt_f32, lt_f32b]
theorem lt_finite_f64 (x y : f64) (_ : is_finite_f64 x) (_ : is_finite_f64 y) :
    lt_f64 x y ↔ of_f64 x < of_f64 y := by simp [lt_f64, lt_f64b]

theorem neg_finite_f32 (x : f32) (_ : is_finite_f32 x) : of_f32 (neg_f32 x) = - of_f32 x := rfl
theorem neg_finite_f64 (x : f64) (_ : is_finite_f64 x) : of_f64 (neg_f64 x) = - of_f64 x := rfl
theorem add_finite_f32 (x y : f32) (_ : is_finite_f32 x) (_ : is_finite_f32 y) :
    add_f32 x y = to_f32 (of_f32 x + of_f32 y) := rfl
theorem add_finite_f64 (x y : f64) (_ : is_finite_f64 x) (_ : is_finite_f64 y) :
    add_f64 x y = to_f64 (of_f64 x + of_f64 y) := rfl
theorem mul_finite_f32 (x y : f32) (_ : is_finite_f32 x) (_ : is_finite_f32 y) :
    mul_f32 x y = to_f32 (of_f32 x * of_f32 y) := rfl
theorem mul_finite_f64 (x y : f64) (_ : is_finite_f64 x) (_ : is_finite_f64 y) :
    mul_f64 x y = to_f64 (of_f64 x * of_f64 y) := rfl
theorem div_finite_f32 (x y : f32) (_ : is_finite_f32 x) (_ : is_finite_f32 y) :
    div_f32 x y = to_f32 (of_f32 x / of_f32 y) := rfl
theorem div_finite_f64 (x y : f64) (_ : is_finite_f64 x) (_ : is_finite_f64 y) :
    div_f64 x y = to_f64 (of_f64 x / of_f64 y) := rfl
theorem sqrt_finite_f32 (x : f32) (_ : is_finite_f32 x) :
    sqrt_f32 x = to_f32 (Real.sqrt (of_f32 x)) := rfl
theorem sqrt_finite_f64 (x : f64) (_ : is_finite_f64 x) :
    sqrt_f64 x = to_f64 (Real.sqrt (of_f64 x)) := rfl

#print axioms to_f32_zero
#print axioms is_finite_to_float_32
#print axioms to_float_is_finite_64
#print axioms eq_finite_f32
#print axioms le_finite_f64
#print axioms add_finite_f32
#print axioms sqrt_finite_f64

end
end Frama.Cfloat

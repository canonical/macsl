/-
  Vset.lean — Lean 4 twin of WP's coqwp `Vset` realization lemmas.
  Set realized as its characteristic function (Coq `set a := a -> bool`),
  mirroring axiom-wp/coqwp/Vset_hardened.v verbatim (Coq `Z` ↦ Lean `Int`).
  All `#print axioms` lines must stay within {propext, Classical.choice, Quot.sound}.
-/
namespace Frama.Vset

def VSet (a : Type) := a → Bool
def member {a : Type} (x : a) (s : VSet a) : Prop := s x = true
def member_bool {a : Type} (x : a) (s : VSet a) : Bool := s x
def empty {a : Type} : VSet a := fun _ => false
def singleton {a : Type} [DecidableEq a] (y : a) : VSet a := fun z => decide (z = y)
def union {a : Type} (s1 s2 : VSet a) : VSet a := fun z => s1 z || s2 z
def inter {a : Type} (s1 s2 : VSet a) : VSet a := fun z => s1 z && s2 z
def range (a b : Int) : VSet Int := fun x => decide (a ≤ x) && decide (x ≤ b)
def range_sup (a : Int) : VSet Int := fun x => decide (a ≤ x)
def range_inf (b : Int) : VSet Int := fun x => decide (x ≤ b)
def range_all : VSet Int := fun _ => true

theorem member_bool1 {a : Type} (x : a) (s : VSet a) :
    (member x s → member_bool x s = true) ∧ (¬ member x s → member_bool x s = false) := by
  unfold member member_bool
  refine ⟨fun h => h, fun h => ?_⟩
  cases hx : s x with
  | true => exact absurd hx h
  | false => rfl

theorem member_empty {a : Type} (x : a) : ¬ member x (empty : VSet a) := by
  unfold member empty; simp

theorem member_singleton {a : Type} [DecidableEq a] (x y : a) :
    member x (singleton y) ↔ x = y := by
  unfold member singleton; simp

theorem member_union {a : Type} (x : a) (s1 s2 : VSet a) :
    member x (union s1 s2) ↔ (member x s1 ∨ member x s2) := by
  unfold member union; simp [Bool.or_eq_true]

theorem member_inter {a : Type} (x : a) (s1 s2 : VSet a) :
    member x (inter s1 s2) ↔ (member x s1 ∧ member x s2) := by
  unfold member inter; simp [Bool.and_eq_true]

theorem union_empty {a : Type} (s : VSet a) :
    union s (empty : VSet a) = s ∧ union (empty : VSet a) s = s := by
  refine ⟨?_, ?_⟩ <;> (funext x; unfold union empty; simp)

theorem inter_empty {a : Type} (s : VSet a) :
    inter s (empty : VSet a) = (empty : VSet a) ∧
    inter (empty : VSet a) s = (empty : VSet a) := by
  refine ⟨?_, ?_⟩ <;> (funext x; unfold inter empty; simp)

theorem member_range (x a b : Int) :
    member x (range a b) ↔ (a ≤ x ∧ x ≤ b) := by
  unfold member range; simp [Bool.and_eq_true]

theorem member_range_sup (x a : Int) : member x (range_sup a) ↔ a ≤ x := by
  unfold member range_sup; simp

theorem member_range_inf (x b : Int) : member x (range_inf b) ↔ x ≤ b := by
  unfold member range_inf; simp

theorem member_range_all (x : Int) : member x range_all := by
  unfold member range_all; rfl

#print axioms member_bool1
#print axioms member_empty
#print axioms member_singleton
#print axioms member_union
#print axioms member_inter
#print axioms union_empty
#print axioms inter_empty
#print axioms member_range
#print axioms member_range_sup
#print axioms member_range_inf
#print axioms member_range_all

end Frama.Vset

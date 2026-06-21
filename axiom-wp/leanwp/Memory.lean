/-
  Memory.lean — Lean 4 twin of WP's coqwp `Memory` realization lemmas.
  Pilot for the dual Coq+Lean cross-validation (see ../../docs/frama-c-dual-tp-spec.md).

  VERIFIED: Lean 4.31.0, `lean Memory.lean` exit 0, and
  `#print axioms separated_trans` = [propext, Classical.choice, Quot.sound]
  — the standard Lean kernel-axiom set (no `sorry`, no custom axiom). The Coq
  twin (../coqwp/Memory_hardened.v `separated_trans`) is "Closed under the
  global context". Both sides of the pilot now hold.

  The statement is structurally identical to the Coq twin and to WP's Why3 goal
  — that equality is what the 3-way cross-check (../../docs/frama-c-dual-tp-spec.md
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

/-- helper: inclusion is transitive (coqwp `included_trans`). -/
theorem included_trans (p q r : Addr) (a b c : Int)
    (h1 : included p a q b) (h2 : included q b r c) : included p a r c := by
  unfold included at *
  intro ha
  obtain ⟨hb0, hbe, ho1, ho2⟩ := h1 ha
  have hbpos : 0 < b := by omega
  obtain ⟨hc0, hbe2, ho3, ho4⟩ := h2 hbpos
  omega

theorem separated_1 (p q : Addr) (a b i j : Int)
    (hsep : separated p a q b)
    (hi : p.offset ≤ i ∧ i < p.offset + a)
    (hj : q.offset ≤ j ∧ j < q.offset + b) :
    ¬ (Addr.mk p.base i = Addr.mk q.base j) := by
  unfold separated at hsep
  intro h
  injection h with hb hij
  omega

theorem separated_included (p q : Addr) (a b : Int)
    (ha : 0 < a) (hb : 0 < b) (hsep : separated p a q b) : ¬ included p a q b := by
  unfold separated at hsep
  unfold included
  intro hinc
  obtain ⟨hb0, hbe, h1, h2⟩ := hinc ha
  omega

/-- farray modelled by its access function (as Memory_hardened.v: `Map.map a b := a -> b`). -/
def eqmem {α : Type} (m1 m2 : Addr → α) (p : Addr) (a1 : Int) : Prop :=
  ∀ q : Addr, included q 1 p a1 → m1 q = m2 q

theorem eqmem_included {α : Type} (m1 m2 : Addr → α) (p q : Addr) (a1 b : Int)
    (hpq : included p a1 q b) (heq : eqmem m1 m2 q b) : eqmem m1 m2 p a1 := by
  intro r hr
  exact heq r (included_trans r p q 1 a1 b hr hpq)

theorem eqmem_sym {α : Type} (m1 m2 : Addr → α) (p : Addr) (a1 : Int)
    (h : eqmem m1 m2 p a1) : eqmem m2 m1 p a1 := by
  intro q hq; exact (h q hq).symm

instance instDecSeparated (p : Addr) (a : Int) (q : Addr) (b : Int) :
    Decidable (separated p a q b) := by unfold separated; infer_instance

/-- `havoc` realized with the decidable `separated` (mirrors Memory_hardened.v). -/
def havoc {α : Type} (m0 m1 : Addr → α) (p : Addr) (n : Int) : Addr → α :=
  fun q => if separated q 1 p n then m1 q else m0 q

theorem havoc_access {α : Type} (m0 m1 : Addr → α) (q p : Addr) (a1 : Int) :
    (separated q 1 p a1 → havoc m0 m1 p a1 q = m1 q) ∧
    (¬ separated q 1 p a1 → havoc m0 m1 p a1 q = m0 q) := by
  unfold havoc
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [if_pos h]
  · rw [if_neg h]

/-- `table_to_offset` realized as identity (mirrors Memory_hardened.v). -/
abbrev Table := Unit
def table_to_offset (_ : Table) (o : Int) : Int := o

theorem table_to_offset_zero (t : Table) : table_to_offset t 0 = 0 := rfl

theorem table_to_offset_monotonic (t : Table) (i j : Int)
    (h : i ≤ j) : table_to_offset t i ≤ table_to_offset t j := h

#print axioms separated_1
#print axioms separated_included
#print axioms included_trans
#print axioms eqmem_included
#print axioms eqmem_sym
#print axioms havoc_access
#print axioms table_to_offset_zero
#print axioms table_to_offset_monotonic

end Frama.Memory

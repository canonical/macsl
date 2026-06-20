(**************************************************************************)
(*  Vset_hardened.v -- Coq 8.20 proofs of the 11 lemmas that the shipped   *)
(*  coqwp/Vset.v leaves Admitted (all marked Why3 goal).                    *)
(*                                                                          *)
(*  coqwp is source-only and does NOT build under Coq 8.20 (it uses omega), *)
(*  so this file is self-contained: it RESTATES the Vset lemmas verbatim    *)
(*  and realizes the (all-abstract) set symbols with a sound witness model  *)
(*    set a := a -> bool      (a decidable membership characteristic fn)    *)
(*  using WhyType decidable equality for singleton. Proving each lemma for   *)
(*  this model shows Vset admitted axioms are consistent/satisfiable.        *)
(*                                                                          *)
(*  Axiom status (Print Assumptions): 9 lemmas are Closed under the global   *)
(*  context; the two SET-EQUALITY lemmas (union_empty, inter_empty) rely on  *)
(*  functional_extensionality -- a standard Coq axiom, and exactly what the  *)
(*  Qedlib realization itself assumes (Hypothesis extensionality). AUDIT.md. *)
(*                                                                          *)
(*  Build: see coqwp/check.sh                                                *)
(**************************************************************************)

Require Import BuiltIn.
From Coq Require Import ZArith Lia Bool.
From Coq Require Import Logic.FunctionalExtensionality.
Open Scope Z_scope.

(* ---- sound witness model: a set is a decidable characteristic function -- *)
Definition set (a:Type) : Type := a -> bool.

Definition member {a:Type} {a_WT:WhyType a} (x:a) (s:set a) : Prop := s x = true.
Definition member_bool {a:Type} {a_WT:WhyType a} (x:a) (s:set a) : bool := s x.
Definition empty {a:Type} {a_WT:WhyType a} : set a := fun _ => false.
Definition singleton {a:Type} {a_WT:WhyType a} (y:a) : set a :=
  fun x => if why_decidable_eq x y then true else false.
Definition union {a:Type} {a_WT:WhyType a} (s1 s2:set a) : set a :=
  fun x => orb (s1 x) (s2 x).
Definition inter {a:Type} {a_WT:WhyType a} (s1 s2:set a) : set a :=
  fun x => andb (s1 x) (s2 x).
Definition range (a b:Z) : set Z := fun x => andb (Z.leb a x) (Z.leb x b).
Definition range_sup (a:Z) : set Z := fun x => Z.leb a x.
Definition range_inf (b:Z) : set Z := fun x => Z.leb x b.
Definition range_all : set Z := fun _ => true.

(* ---- the 11 lemmas -------------------------------------------------- *)

(* Why3 goal *)
Lemma member_bool1 {a:Type} {a_WT:WhyType a} :
  forall (x:a) (s:set a),
  ((member x s) -> ((member_bool x s) = true)) /\
  (~ (member x s) -> ((member_bool x s) = false)).
Proof.
  intros x s. unfold member, member_bool. split; intro H.
  - exact H.
  - destruct (s x); [ exfalso; apply H; reflexivity | reflexivity ].
Qed.

(* Why3 goal *)
Lemma member_empty {a:Type} {a_WT:WhyType a} :
  forall (x:a), ~ (member x (empty : set a)).
Proof. intros x. unfold member, empty. discriminate. Qed.

(* Why3 goal *)
Lemma member_singleton {a:Type} {a_WT:WhyType a} :
  forall (x:a) (y:a), (member x (singleton y)) <-> (x = y).
Proof.
  intros x y. unfold member, singleton.
  destruct (why_decidable_eq x y) as [E|E]; split; intro H;
    solve [ exact E | reflexivity | discriminate H | contradiction (E H) ].
Qed.

(* Why3 goal *)
Lemma member_union {a:Type} {a_WT:WhyType a} :
  forall (x:a) (a1 b:set a),
  (member x (union a1 b)) <-> ((member x a1) \/ (member x b)).
Proof. intros x a1 b. unfold member, union. apply orb_true_iff. Qed.

(* Why3 goal *)
Lemma member_inter {a:Type} {a_WT:WhyType a} :
  forall (x:a) (a1 b:set a),
  (member x (inter a1 b)) <-> ((member x a1) /\ (member x b)).
Proof. intros x a1 b. unfold member, inter. apply andb_true_iff. Qed.

(* Why3 goal *)
Lemma union_empty {a:Type} {a_WT:WhyType a} :
  forall (a1:set a),
  ((union a1 (empty : set a)) = a1) /\ ((union (empty : set a) a1) = a1).
Proof.
  intros a1. split; apply functional_extensionality; intro x; unfold union, empty.
  - apply orb_false_r.
  - apply orb_false_l.
Qed.

(* Why3 goal *)
Lemma inter_empty {a:Type} {a_WT:WhyType a} :
  forall (a1:set a),
  ((inter a1 (empty : set a)) = (empty : set a)) /\
  ((inter (empty : set a) a1) = (empty : set a)).
Proof.
  intros a1. split; apply functional_extensionality; intro x; unfold inter, empty.
  - apply andb_false_r.
  - apply andb_false_l.
Qed.

(* Why3 goal *)
Lemma member_range :
  forall (x a b:Z), (member x (range a b)) <-> ((a <= x)%Z /\ (x <= b)%Z).
Proof.
  intros x a b. unfold member, range.
  rewrite andb_true_iff, !Z.leb_le. reflexivity.
Qed.

(* Why3 goal *)
Lemma member_range_sup :
  forall (x a:Z), (member x (range_sup a)) <-> (a <= x)%Z.
Proof. intros x a. unfold member, range_sup. apply Z.leb_le. Qed.

(* Why3 goal *)
Lemma member_range_inf :
  forall (x b:Z), (member x (range_inf b)) <-> (x <= b)%Z.
Proof. intros x b. unfold member, range_inf. apply Z.leb_le. Qed.

(* Why3 goal *)
Lemma member_range_all : forall (x:Z), member x range_all.
Proof. intros x. unfold member, range_all. reflexivity. Qed.

(**************************************************************************)
(*  Memory_hardened.v — Coq 8.20 proofs of the 11 lemmas that Frama-C's   *)
(*  shipped coqwp/Memory.v leaves `Admitted` (all marked `(* Why3 goal *)`).*)
(*                                                                          *)
(*  Why a separate file: Frama-C 32.1's coqwp is source-only and does NOT   *)
(*  build under Coq 8.20 (it uses `omega`, removed in 8.12). This file is    *)
(*  self-contained — it re-states the relevant definitions VERBATIM from     *)
(*  coqwp/Memory.v, realizes the abstract symbols soundly, and proves every  *)
(*  one of the 11 lemmas with `lia` (the omega replacement). It compiles     *)
(*  clean and `Print Assumptions` shows no axioms/admits (see AUDIT.md).     *)
(*                                                                          *)
(*  Build: coqc -R "$(why3 --print-libdir)/coq" Why3 Memory_hardened.v       *)
(**************************************************************************)

Require Import ZArith Lia.
Require Import BuiltIn.
Require map.Map.
From Coq Require Import Cantor.
Open Scope Z_scope.

(* ---- definitions, verbatim from coqwp/Memory.v ---------------------- *)
Inductive addr := mk_addr : Z -> Z -> addr.
Definition offset (v:addr) : Z := match v with mk_addr _ o => o end.
Definition base   (v:addr) : Z := match v with mk_addr b _ => b end.
Definition null : addr := mk_addr 0 0.
Definition shift (p:addr) (k:Z) : addr := mk_addr (base p) (offset p + k).

Definition included (p:addr) (a:Z) (q:addr) (b:Z) : Prop :=
  0 < a ->
  0 <= b /\ base p = base q /\ offset q <= offset p /\ offset p + a <= offset q + b.

Definition separated (p:addr) (a:Z) (q:addr) (b:Z) : Prop :=
  a <= 0 \/ b <= 0 \/ base p <> base q \/
  offset q + b <= offset p \/ offset p + a <= offset q.

(* farray is modelled by its access function (Why3 `map.Map.map a b := a -> b`,
   Qedlib `.[ ]` = access); the record's whytype metadata is irrelevant to
   these lemmas. *)
Definition farray (A B:Type) := Map.map A B.
Definition select {A B:Type} (m:farray A B) (k:A) : B := m k.
Notation "a .[ k ]" := (select a k) (at level 60).

Definition eqmem {a:Type} {a_WT:WhyType a}
  (m1 m2:farray addr a) (p:addr) (a1:Z) : Prop :=
  forall q:addr, included q 1 p a1 -> m1.[q] = m2.[q].

(* ---- 1-3 : separation algebra (pure, no realization) ---------------- *)

(* Why3 goal *)
Lemma separated_1 :
  forall (p q:addr) (a b i j:Z),
  separated p a q b ->
  (offset p <= i /\ i < offset p + a) ->
  (offset q <= j /\ j < offset q + b) ->
  ~ (mk_addr (base p) i = mk_addr (base q) j).
Proof.
  intros p q a b i j Hsep [Hi1 Hi2] [Hj1 Hj2] Heq.
  injection Heq; intros Hij Hb.
  unfold separated in Hsep.
  destruct Hsep as [H|[H|[H|[H|H]]]]; lia.
Qed.

(* Why3 goal *)
Lemma separated_included :
  forall (p q:addr) (a b:Z), 0 < a -> 0 < b ->
  separated p a q b -> ~ included p a q b.
Proof.
  intros p q a b Ha Hb Hsep Hinc.
  unfold separated in Hsep. unfold included in Hinc.
  destruct (Hinc Ha) as (Hb0 & Hbe & H1 & H2).
  destruct Hsep as [H|[H|[H|[H|H]]]]; lia.
Qed.

(* Why3 goal *)
Lemma separated_trans :
  forall (p q r:addr) (a b c:Z),
  included p a q b -> separated q b r c -> separated p a r c.
Proof.
  intros p q r a b c Hinc Hsep.
  unfold separated in *. unfold included in Hinc.
  destruct (Z_le_gt_dec a 0) as [Ha|Ha]; [left; lia|].
  destruct (Hinc ltac:(lia)) as (Hb0 & Hbe & H1 & H2).
  destruct Hsep as [H|[H|[H|[H|H]]]].
  - exfalso; lia.
  - right; left; lia.
  - right; right; left. rewrite Hbe; exact H.
  - right; right; right; left; lia.
  - right; right; right; right; lia.
Qed.

(* ---- helper (also Admitted-as-Qed in coqwp) ------------------------- *)
Lemma included_trans :
  forall (p q r:addr) (a b c:Z),
  included p a q b -> included q b r c -> included p a r c.
Proof.
  intros p q r a b c H1 H2 Ha.
  destruct (H1 Ha) as (Hb0 & Hbe & Ho1 & Ho2).
  assert (Hbpos : 0 < b) by lia.
  destruct (H2 Hbpos) as (Hc0 & Hbe2 & Ho3 & Ho4).
  repeat split; lia.
Qed.

(* ---- 4-5 : eqmem ---------------------------------------------------- *)

(* Why3 goal *)
Lemma eqmem_included {a:Type} {a_WT:WhyType a} :
  forall (m1 m2:farray addr a) (p q:addr) (a1 b:Z),
  included p a1 q b -> eqmem m1 m2 q b -> eqmem m1 m2 p a1.
Proof.
  intros m1 m2 p q a1 b Hpq Heq r Hr.
  apply Heq. eapply included_trans; eauto.
Qed.

(* Why3 goal *)
Lemma eqmem_sym {a:Type} {a_WT:WhyType a} :
  forall (m1 m2:farray addr a) (p:addr) (a1:Z),
  eqmem m1 m2 p a1 -> eqmem m2 m1 p a1.
Proof.
  intros m1 m2 p a1 H q Hq. symmetry. apply H; exact Hq.
Qed.

(* ---- 6 : havoc (realize `havoc` with a decidable `separated`) -------- *)
Definition separated_dec (p:addr) (a:Z) (q:addr) (b:Z) :
  {separated p a q b} + {~ separated p a q b}.
Proof.
  unfold separated.
  destruct (Z_le_dec a 0); [left; tauto|].
  destruct (Z_le_dec b 0); [left; tauto|].
  destruct (Z.eq_dec (base p) (base q)); [|left; tauto].
  destruct (Z_le_dec (offset q + b) (offset p)); [left; tauto|].
  destruct (Z_le_dec (offset p + a) (offset q)); [left; tauto|].
  right; tauto.
Defined.

Definition havoc {a:Type} {a_WT:WhyType a}
  (m0 m1:farray addr a) (p:addr) (n:Z) : farray addr a :=
  fun q => if separated_dec q 1 p n then m1 q else m0 q.

(* Why3 goal *)
Lemma havoc_access {a:Type} {a_WT:WhyType a} :
  forall (m0 m1:farray addr a) (q p:addr) (a1:Z),
  (separated q 1 p a1 -> (havoc m0 m1 p a1) q = m1.[q]) /\
  (~ separated q 1 p a1 -> (havoc m0 m1 p a1) q = m0.[q]).
Proof.
  intros m0 m1 q p a1. unfold havoc, select.
  destruct (separated_dec q 1 p a1) as [s|s]; split; intro H;
    solve [reflexivity | contradiction].
Qed.

(* ---- 7 : table (realize `table_to_offset` as identity) -------------- *)
Definition table : Type := unit.
Definition table_to_offset (t:table) (o:Z) : Z := o.
Definition table_of_base (b:Z) : table := tt.

(* Why3 goal *)
Lemma table_to_offset_zero : forall (t:table), table_to_offset t 0 = 0.
Proof. reflexivity. Qed.

(* Why3 goal *)
Lemma table_to_offset_monotonic :
  forall (t:table) (i j:Z), i <= j -> table_to_offset t i <= table_to_offset t j.
Proof. intros t i j H. unfold table_to_offset. exact H. Qed.

(* ---- 8-10 : addr <-> Z bijection (realize int_of_addr/addr_of_int) -- *)
(* A bijection Z <-> nat (0<->0), then Cantor for nat <-> nat*nat. *)
Definition z2n (z:Z) : nat :=
  match z with
  | Z0     => 0
  | Zpos p => (2 * Pos.to_nat p)%nat
  | Zneg p => (2 * Pos.to_nat p - 1)%nat
  end.
Definition n2z (n:nat) : Z :=
  if Nat.even n then Z.of_nat (Nat.div2 n)
  else Z.opp (Z.of_nat (Nat.div2 (S n))).

Lemma n2z_z2n : forall z, n2z (z2n z) = z.
Proof.
  intro z. destruct z as [|p|p]; unfold z2n.
  - reflexivity.
  - assert (Ev : Nat.even (2 * Pos.to_nat p) = true)
      by (rewrite Nat.even_mul; reflexivity).
    unfold n2z. rewrite Ev. rewrite Nat.div2_double. apply positive_nat_Z.
  - assert (Hk : (1 <= Pos.to_nat p)%nat) by apply Pos2Nat.is_pos.
    replace (2 * Pos.to_nat p - 1)%nat with (S (2 * (Pos.to_nat p - 1)))%nat by lia.
    assert (Ev : Nat.even (S (2 * (Pos.to_nat p - 1))) = false)
      by (rewrite Nat.even_succ, Nat.odd_mul; reflexivity).
    unfold n2z. rewrite Ev.
    replace (S (S (2 * (Pos.to_nat p - 1))))%nat with (2 * Pos.to_nat p)%nat by lia.
    rewrite Nat.div2_double. rewrite positive_nat_Z. reflexivity.
Qed.

Lemma z2n_n2z : forall n, z2n (n2z n) = n.
Proof.
  intro n. unfold n2z.
  destruct (Nat.even n) eqn:E.
  - apply Nat.even_spec in E. destruct E as [m Hm]. subst n.
    rewrite Nat.div2_double.
    destruct m as [|m'].
    + reflexivity.
    + change (Z.of_nat (S m')) with (Z.pos (Pos.of_succ_nat m')).
      unfold z2n. rewrite SuccNat2Pos.id_succ. lia.
  - assert (Ho : Nat.Odd n)
      by (apply Nat.odd_spec; rewrite <- Nat.negb_even, E; reflexivity).
    destruct Ho as [m Hm]. subst n.
    replace (S (2 * m + 1))%nat with (2 * (m + 1))%nat by lia.
    rewrite Nat.div2_double.
    replace (m + 1)%nat with (S m) by lia.
    change (Z.of_nat (S m)) with (Z.pos (Pos.of_succ_nat m)).
    change (- Z.pos (Pos.of_succ_nat m)) with (Z.neg (Pos.of_succ_nat m)).
    unfold z2n. rewrite SuccNat2Pos.id_succ. lia.
Qed.

Lemma z2n_0 : z2n 0 = 0%nat. Proof. reflexivity. Qed.
Lemma n2z_0 : n2z 0 = 0. Proof. reflexivity. Qed.

Definition int_of_addr (p:addr) : Z :=
  n2z (Cantor.to_nat (z2n (base p), z2n (offset p))).
Definition addr_of_int (i:Z) : addr :=
  let (a, b) := Cantor.of_nat (z2n i) in mk_addr (n2z a) (n2z b).

(* Why3 goal *)
Lemma int_of_addr_bijection : forall (a:Z), int_of_addr (addr_of_int a) = a.
Proof.
  intro a. unfold addr_of_int.
  destruct (Cantor.of_nat (z2n a)) as [x y] eqn:E.
  unfold int_of_addr. simpl base; simpl offset.
  rewrite !z2n_n2z.
  replace (x, y) with (Cantor.of_nat (z2n a)) by (rewrite E; reflexivity).
  rewrite Cantor.cancel_to_of. apply n2z_z2n.
Qed.

(* Why3 goal *)
Lemma addr_of_int_bijection : forall (p:addr), addr_of_int (int_of_addr p) = p.
Proof.
  intro p. unfold int_of_addr, addr_of_int.
  rewrite z2n_n2z. rewrite Cantor.cancel_of_to.
  rewrite !n2z_z2n. destruct p; reflexivity.
Qed.

(* Why3 goal *)
Lemma addr_of_null : int_of_addr null = 0.
Proof.
  unfold int_of_addr, null. simpl base; simpl offset.
  rewrite z2n_0. change (Cantor.to_nat (0,0)%nat) with 0%nat. apply n2z_0.
Qed.

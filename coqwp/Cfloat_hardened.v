(**************************************************************************)
(*  Cfloat_hardened.v -- Coq 8.20 proofs of the 32 lemmas that the shipped *)
(*  coqwp/Cfloat.v leaves Admitted (all marked Why3 goal).                  *)
(*                                                                          *)
(*  coqwp is source-only and does NOT build under Coq 8.20 (omega), so this *)
(*  file is self-contained: it RESTATES the Cfloat lemmas verbatim and       *)
(*  realizes the (all-abstract) float symbols with a SOUND WITNESS model:    *)
(*    f32 := f64 := R ;  of_f := identity ;  to_f := clamp into [-max,max] ; *)
(*    ops := to_f (real op) ; comparisons via Rle_dec/Rlt_dec/Req_EM_T ;     *)
(*    classify Finite iff in finite range.                                   *)
(*  Proving each lemma for this model shows Cfloat's admitted axioms are     *)
(*  consistent/satisfiable.                                                  *)
(*                                                                          *)
(*  Axiom status: Coq's R is itself axiomatized, so these lemmas are NOT     *)
(*  Closed under the global context -- they depend ONLY on Coq's standard    *)
(*  Reals / classical axiomatization (Rdefinitions, Raxioms, classical      *)
(*  decidability used by Rle_dec/Req_EM_T). There are NO admits and NO       *)
(*  custom axioms. check.sh enforces: no admit, and every axiom is from a    *)
(*  standard Coq namespace. See AUDIT.md.                                    *)
(*                                                                          *)
(*  Build: see coqwp/check.sh                                                *)
(**************************************************************************)

Require Import BuiltIn.
From Coq Require Import Reals Lra Lia.
Open Scope R_scope.

(* finite ranges (single + double maxima, verbatim from Cfloat.v) *)
Definition max32 : R := 340282346600000016151267322115014000640%R.
Definition max64 : R :=
  179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368%R.

Lemma max32_ge1 : 1 <= max32. Proof. unfold max32. lra. Qed.
Lemma max64_ge1 : 1 <= max64. Proof. unfold max64. lra. Qed.

(* clamp x into [-m, m] *)
Definition clamp (m x : R) : R := Rmin (Rmax x (-m)) m.

Ltac clamptac := unfold clamp, Rmin, Rmax in *; repeat destruct (Rle_dec _ _); lra.

Lemma clamp_in : forall m x, 1 <= m -> -m <= clamp m x <= m. Proof. intros; clamptac. Qed.
Lemma clamp_id : forall m x, -m <= x <= m -> clamp m x = x. Proof. intros; clamptac. Qed.

(* ---- the model -------------------------------------------------------- *)
Definition f32 : Type := R.
Definition f64 : Type := R.
Definition of_f32 (f:f32) : R := f.
Definition of_f64 (d:f64) : R := d.
Definition to_f32 (x:R) : f32 := clamp max32 x.
Definition to_f64 (x:R) : f64 := clamp max64 x.

Inductive rounding_mode :=
  | Up | Down | ToZero | NearestTiesToAway | NearestTiesToEven.
Definition round_float  (m:rounding_mode) (x:R) : f32 := to_f32 x.
Definition round_double (m:rounding_mode) (x:R) : f64 := to_f64 x.

Inductive float_kind := Finite | NaN | Inf_pos | Inf_neg.
Definition classify_f32 (f:f32) : float_kind :=
  if Rle_dec (-max32) f then (if Rle_dec f max32 then Finite else Inf_pos) else Inf_neg.
Definition classify_f64 (d:f64) : float_kind :=
  if Rle_dec (-max64) d then (if Rle_dec d max64 then Finite else Inf_pos) else Inf_neg.

Definition is_finite_f32 (f:f32): Prop := classify_f32 f = Finite.
Definition is_finite_f64 (d:f64): Prop := classify_f64 d = Finite.

Definition eq_f32b (x y:f32) : bool := if Req_EM_T (of_f32 x) (of_f32 y) then true else false.
Definition eq_f64b (x y:f64) : bool := if Req_EM_T (of_f64 x) (of_f64 y) then true else false.
Definition ne_f32b (x y:f32) : bool := negb (eq_f32b x y).
Definition ne_f64b (x y:f64) : bool := negb (eq_f64b x y).
Definition le_f32b (x y:f32) : bool := if Rle_dec (of_f32 x) (of_f32 y) then true else false.
Definition le_f64b (x y:f64) : bool := if Rle_dec (of_f64 x) (of_f64 y) then true else false.
Definition lt_f32b (x y:f32) : bool := if Rlt_dec (of_f32 x) (of_f32 y) then true else false.
Definition lt_f64b (x y:f64) : bool := if Rlt_dec (of_f64 x) (of_f64 y) then true else false.
Definition eq_f32 (x y:f32):Prop := eq_f32b x y = true.
Definition eq_f64 (x y:f64):Prop := eq_f64b x y = true.
Definition ne_f32 (x y:f32):Prop := ne_f32b x y = true.
Definition ne_f64 (x y:f64):Prop := ne_f64b x y = true.
Definition le_f32 (x y:f32):Prop := le_f32b x y = true.
Definition le_f64 (x y:f64):Prop := le_f64b x y = true.
Definition lt_f32 (x y:f32):Prop := lt_f32b x y = true.
Definition lt_f64 (x y:f64):Prop := lt_f64b x y = true.

Definition neg_f32 (x:f32):f32 := Ropp x.
Definition neg_f64 (x:f64):f64 := Ropp x.
Definition add_f32 (x y:f32):f32 := to_f32 (of_f32 x + of_f32 y).
Definition add_f64 (x y:f64):f64 := to_f64 (of_f64 x + of_f64 y).
Definition mul_f32 (x y:f32):f32 := to_f32 (of_f32 x * of_f32 y).
Definition mul_f64 (x y:f64):f64 := to_f64 (of_f64 x * of_f64 y).
Definition div_f32 (x y:f32):f32 := to_f32 (of_f32 x / of_f32 y).
Definition div_f64 (x y:f64):f64 := to_f64 (of_f64 x / of_f64 y).
Definition sqrt_f32 (x:f32):f32 := to_f32 (sqrt (of_f32 x)).
Definition sqrt_f64 (x:f64):f64 := to_f64 (sqrt (of_f64 x)).
Definition model_f32 (f:f32):R := of_f32 f.
Definition model_f64 (f:f64):R := of_f64 f.

(* helper: classify reflects the finite range *)
Lemma finite32_iff : forall f, is_finite_f32 f <-> -max32 <= of_f32 f <= max32.
Proof.
  intro f. unfold is_finite_f32, classify_f32, of_f32.
  destruct (Rle_dec (-max32) f); destruct (Rle_dec f max32);
    split; intro H; try (split; lra); try discriminate; try lra.
Qed.
Lemma finite64_iff : forall d, is_finite_f64 d <-> -max64 <= of_f64 d <= max64.
Proof.
  intro d. unfold is_finite_f64, classify_f64, of_f64.
  destruct (Rle_dec (-max64) d); destruct (Rle_dec d max64);
    split; intro H; try (split; lra); try discriminate; try lra.
Qed.

(* ---- the 32 lemmas --------------------------------------------------- *)

Lemma to_f32_zero : of_f32 (to_f32 0) = 0.
Proof. unfold of_f32, to_f32. apply clamp_id. generalize max32_ge1; lra. Qed.
Lemma to_f32_one : of_f32 (to_f32 1) = 1.
Proof. unfold of_f32, to_f32. apply clamp_id. generalize max32_ge1; lra. Qed.
Lemma to_f64_zero : of_f64 (to_f64 0) = 0.
Proof. unfold of_f64, to_f64. apply clamp_id. generalize max64_ge1; lra. Qed.
Lemma to_f64_one : of_f64 (to_f64 1) = 1.
Proof. unfold of_f64, to_f64. apply clamp_id. generalize max64_ge1; lra. Qed.

Lemma float_32 : forall x, to_f32 x = round_float NearestTiesToEven x.
Proof. reflexivity. Qed.
Lemma float_64 : forall x, to_f64 x = round_double NearestTiesToEven x.
Proof. reflexivity. Qed.

Lemma is_finite_to_float_32 : forall x, is_finite_f32 (to_f32 x).
Proof. intro x. apply finite32_iff. unfold of_f32, to_f32. apply clamp_in, max32_ge1. Qed.
Lemma is_finite_to_float_64 : forall x, is_finite_f64 (to_f64 x).
Proof. intro x. apply finite64_iff. unfold of_f64, to_f64. apply clamp_in, max64_ge1. Qed.

Lemma to_float_is_finite_32 : forall f, is_finite_f32 f -> to_f32 (of_f32 f) = f.
Proof. intros f H. apply finite32_iff in H. unfold to_f32, of_f32 in *. apply clamp_id; lra. Qed.
Lemma to_float_is_finite_64 : forall d, is_finite_f64 d -> to_f64 (of_f64 d) = d.
Proof. intros d H. apply finite64_iff in H. unfold to_f64, of_f64 in *. apply clamp_id; lra. Qed.

Lemma finite_small_f32 : forall x,
  (-max64 <= x /\ x <= max32) -> is_finite_f32 (to_f32 x).
Proof. intros x _. apply is_finite_to_float_32. Qed.
Lemma finite_small_f64 : forall x,
  (-max64 <= x /\ x <= max64) -> is_finite_f64 (to_f64 x).
Proof. intros x _. apply is_finite_to_float_64. Qed.

Lemma finite_range_f32 : forall f,
  is_finite_f32 f <-> (-max32 <= of_f32 f /\ of_f32 f <= max32).
Proof. intro f. rewrite finite32_iff. tauto. Qed.
Lemma finite_range_f64 : forall d,
  is_finite_f64 d <-> (-max64 <= of_f64 d /\ of_f64 d <= max64).
Proof. intro d. rewrite finite64_iff. tauto. Qed.

Ltac cmp_eq := unfold eq_f32, eq_f64, eq_f32b, eq_f64b, of_f32, of_f64;
  match goal with |- context[Req_EM_T ?a ?b] => destruct (Req_EM_T a b) end;
  split; intro; solve [assumption | reflexivity | discriminate | contradiction].
Ltac cmp_ne := unfold ne_f32, ne_f64, ne_f32b, ne_f64b, eq_f32b, eq_f64b, of_f32, of_f64;
  match goal with |- context[Req_EM_T ?a ?b] => destruct (Req_EM_T a b) end;
  simpl negb; split; intro; solve [assumption | reflexivity | discriminate | contradiction].
Ltac cmp_le := unfold le_f32, le_f64, le_f32b, le_f64b, of_f32, of_f64;
  match goal with |- context[Rle_dec ?a ?b] => destruct (Rle_dec a b) end;
  split; intro; solve [assumption | reflexivity | discriminate | contradiction].
Ltac cmp_lt := unfold lt_f32, lt_f64, lt_f32b, lt_f64b, of_f32, of_f64;
  match goal with |- context[Rlt_dec ?a ?b] => destruct (Rlt_dec a b) end;
  split; intro; solve [assumption | reflexivity | discriminate | contradiction].

Lemma eq_finite_f32 : forall x y, is_finite_f32 x -> is_finite_f32 y ->
  (eq_f32 x y <-> of_f32 x = of_f32 y).
Proof. intros x y _ _. cmp_eq. Qed.
Lemma eq_finite_f64 : forall x y, is_finite_f64 x -> is_finite_f64 y ->
  (eq_f64 x y <-> of_f64 x = of_f64 y).
Proof. intros x y _ _. cmp_eq. Qed.
Lemma ne_finite_f32 : forall x y, is_finite_f32 x -> is_finite_f32 y ->
  (ne_f32 x y <-> ~ (of_f32 x = of_f32 y)).
Proof. intros x y _ _. cmp_ne. Qed.
Lemma ne_finite_f64 : forall x y, is_finite_f64 x -> is_finite_f64 y ->
  (ne_f64 x y <-> ~ (of_f64 x = of_f64 y)).
Proof. intros x y _ _. cmp_ne. Qed.
Lemma le_finite_f32 : forall x y, is_finite_f32 x -> is_finite_f32 y ->
  (le_f32 x y <-> of_f32 x <= of_f32 y).
Proof. intros x y _ _. cmp_le. Qed.
Lemma le_finite_f64 : forall x y, is_finite_f64 x -> is_finite_f64 y ->
  (le_f64 x y <-> of_f64 x <= of_f64 y).
Proof. intros x y _ _. cmp_le. Qed.
Lemma lt_finite_f32 : forall x y, is_finite_f32 x -> is_finite_f32 y ->
  (lt_f32 x y <-> of_f32 x < of_f32 y).
Proof. intros x y _ _. cmp_lt. Qed.
Lemma lt_finite_f64 : forall x y, is_finite_f64 x -> is_finite_f64 y ->
  (lt_f64 x y <-> of_f64 x < of_f64 y).
Proof. intros x y _ _. cmp_lt. Qed.

Lemma neg_finite_f32 : forall x, is_finite_f32 x -> of_f32 (neg_f32 x) = - of_f32 x.
Proof. intros x _. reflexivity. Qed.
Lemma neg_finite_f64 : forall x, is_finite_f64 x -> of_f64 (neg_f64 x) = - of_f64 x.
Proof. intros x _. reflexivity. Qed.

Lemma add_finite_f32 : forall x y, is_finite_f32 x -> is_finite_f32 y ->
  add_f32 x y = to_f32 (of_f32 x + of_f32 y).
Proof. reflexivity. Qed.
Lemma add_finite_f64 : forall x y, is_finite_f64 x -> is_finite_f64 y ->
  add_f64 x y = to_f64 (of_f64 x + of_f64 y).
Proof. reflexivity. Qed.
Lemma mul_finite_f32 : forall x y, is_finite_f32 x -> is_finite_f32 y ->
  mul_f32 x y = to_f32 (of_f32 x * of_f32 y).
Proof. reflexivity. Qed.
Lemma mul_finite_f64 : forall x y, is_finite_f64 x -> is_finite_f64 y ->
  mul_f64 x y = to_f64 (of_f64 x * of_f64 y).
Proof. reflexivity. Qed.
Lemma div_finite_f32 : forall x y, is_finite_f32 x -> is_finite_f32 y ->
  div_f32 x y = to_f32 (of_f32 x / of_f32 y).
Proof. reflexivity. Qed.
Lemma div_finite_f64 : forall x y, is_finite_f64 x -> is_finite_f64 y ->
  div_f64 x y = to_f64 (of_f64 x / of_f64 y).
Proof. reflexivity. Qed.
Lemma sqrt_finite_f32 : forall x, is_finite_f32 x ->
  sqrt_f32 x = to_f32 (sqrt (of_f32 x)).
Proof. reflexivity. Qed.
Lemma sqrt_finite_f64 : forall x, is_finite_f64 x ->
  sqrt_f64 x = to_f64 (sqrt (of_f64 x)).
Proof. reflexivity. Qed.

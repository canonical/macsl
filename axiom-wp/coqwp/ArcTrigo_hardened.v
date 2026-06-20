(**************************************************************************)
(*  ArcTrigo_hardened.v -- Coq 8.20 proofs of the 2 lemmas that the shipped *)
(*  coqwp/ArcTrigo.v leaves Admitted (both marked Why3 goal).               *)
(*                                                                          *)
(*  coqwp is source-only and does NOT build under Coq 8.20 (omega), so this *)
(*  file is self-contained. Unlike the other hardened files this is a       *)
(*  GENUINE realization, not a witness: asin/acos are realized as Coq's own  *)
(*  Ratan.asin / Ratan.acos, so the two lemmas are exactly the stdlib facts  *)
(*  sin_asin / cos_acos -- the admitted ArcTrigo axioms are simply TRUE.     *)
(*                                                                          *)
(*  Axiom status: Coq's R is itself axiomatized, so (like Cfloat) these are  *)
(*  not Closed under the global context; they depend ONLY on Coq's standard  *)
(*  Reals axioms (sig_forall_dec, functional_extensionality). No admits, no  *)
(*  custom axioms. See AUDIT.md / check.sh.                                  *)
(*                                                                          *)
(*  Build: see coqwp/check.sh                                                *)
(**************************************************************************)

Require Import BuiltIn.
From Coq Require Import Reals Lra.
Open Scope R_scope.

(* genuine realization: Coq's own inverse trig functions *)
Definition asin : R -> R := Reals.Ratan.asin.
Definition acos : R -> R := Reals.Ratan.acos.

(* Why3 goal *)
Lemma Sin_asin :
  forall (x:R), ((-1)%R <= x /\ x <= 1%R) -> sin (asin x) = x.
Proof. intros x [H1 H2]. unfold asin. apply sin_asin. lra. Qed.

(* Why3 goal *)
Lemma Cos_acos :
  forall (x:R), ((-1)%R <= x /\ x <= 1%R) -> cos (acos x) = x.
Proof. intros x [H1 H2]. unfold acos. apply cos_acos. lra. Qed.

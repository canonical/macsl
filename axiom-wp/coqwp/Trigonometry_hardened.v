(**************************************************************************)
(*  Trigonometry_hardened.v -- Coq 8.20 proof of the 1 lemma that the       *)
(*  shipped coqwp/real/Trigonometry.v leaves Admitted (marked Why3 goal):   *)
(*  Pi_double_precision_bounds.                                             *)
(*                                                                          *)
(*  The shipped realization stubbed this out (to avoid a CoqInterval        *)
(*  dependency) -- it is a 1-ulp-at-2^-51 bracket on PI, infeasible to      *)
(*  prove from the Coq Reals stdlib alone. This twin discharges it with     *)
(*  CoqInterval verified interval arithmetic. The original real version is  *)
(*  also patched to use the same proof (Qed, no stub).                      *)
(*                                                                          *)
(*  GENUINE result: PI is Coq own Reals.Rtrigo1.PI; the bounds are simply   *)
(*  TRUE. Self-contained. Axiom footprint is all STANDARD Coq foundations,  *)
(*  no custom or behavioural axioms: classical logic (Classical_Prop and    *)
(*  ClassicalDedekindReals sig_forall_dec/sig_not_dec), functional          *)
(*  extensionality, and Coq native 63-bit integer primitives (PrimInt63 /   *)
(*  Uint63) used by CoqInterval reflective computation.                     *)
(*  See AUDIT.md / check.sh.                                                *)
(*                                                                          *)
(*  Build: needs coq-interval in the switch; see coqwp/check.sh.            *)
(**************************************************************************)

From Coq Require Import Reals.
From Coq Require Import Reals.Rtrigo1.
From Interval Require Import Tactic.
Open Scope R_scope.

(* Why3 goal *)
Lemma Pi_double_precision_bounds :
  ((7074237752028440 / 2251799813685248)%R < Reals.Rtrigo1.PI)%R /\
  (Reals.Rtrigo1.PI < (7074237752028441 / 2251799813685248)%R)%R.
Proof.
  split; interval with (i_prec 70).
Qed.

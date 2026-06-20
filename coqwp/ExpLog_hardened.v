(**************************************************************************)
(*  ExpLog_hardened.v -- Coq 8.20 proof of the 1 lemma that the shipped     *)
(*  coqwp/ExpLog.v leaves Admitted (marked Why3 goal).                      *)
(*                                                                          *)
(*  coqwp is source-only and does NOT build under Coq 8.20 (omega), so this *)
(*  file is self-contained. This is a GENUINE result: exp is Coq's own       *)
(*  Rtrigo_def.exp, and exp_pos is exactly the stdlib lemma of the same name *)
(*  -- the admitted ExpLog axiom is simply TRUE.                             *)
(*                                                                          *)
(*  Axiom status: Coq's R is itself axiomatized, so (like Cfloat) this is    *)
(*  not Closed under the global context; it depends ONLY on Coq's standard   *)
(*  Reals axioms (sig_forall_dec, functional_extensionality). No admits, no  *)
(*  custom axioms. See AUDIT.md / check.sh.                                  *)
(*                                                                          *)
(*  Build: see coqwp/check.sh                                                *)
(**************************************************************************)

Require Import BuiltIn.
From Coq Require Import Reals.
Open Scope R_scope.

(* Why3 goal *)
Lemma exp_pos : forall (x:R), 0%R < exp x.
Proof. exact exp_pos. Qed.

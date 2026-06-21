(* ===================================================================== *)
(*  Leg 1 (Rocq 9.0) -- pilot lemma: Memory.separated_trans               *)
(*                                                                         *)
(*  Goal (dual-TP spec 5.4a): anchor the coqwp realization lemma to what    *)
(*  Why3 *means*, by proving, against the Cohen / Johnson-Freyd            *)
(*  denotational semantics (joscoh/why3-semantics, rocq-9.0 branch):       *)
(*                                                                         *)
(*     separated_trans_Coq  <->  formula_rep ... [[ Why3(separated_trans) ]]*)
(*                                                                         *)
(*  STEP 1 (this file): construct [[separated_trans]] : formula and the     *)
(*  Coq side of the obligation. Substrate confirmed usable; coqwp Memory     *)
(*  defs re-stated in Rocq 9; separated_trans_Coq PROVED; the Why3 AST term  *)
(*  built against the real Syntax constructors and type-checked as a formula.*)
(* ===================================================================== *)

From Stdlib Require Import ZArith Lia.
From Proofs Require Import core.Types.
From Proofs Require Import core.Syntax.
From Proofs Require Import core.Denotational.

(* ---- (a) substrate usable downstream: the Why3 AST + denotation are in scope ---- *)
Check term.
Check formula.
Check @formula_rep.

(* ---- (b) coqwp Memory defs, re-stated VERBATIM in this Rocq-9 Coq world ---- *)
(*     (from macsl/axiom-wp/coqwp/Memory_hardened.v lines 22-34)                *)
Open Scope Z_scope.
Inductive addr := mk_addr : Z -> Z -> addr.
Definition offset (v:addr) : Z := match v with mk_addr _ o => o end.
Definition base   (v:addr) : Z := match v with mk_addr b _ => b end.

Definition included (p:addr) (a:Z) (q:addr) (b:Z) : Prop :=
  0 < a ->
  0 <= b /\ base p = base q /\ offset q <= offset p /\ offset p + a <= offset q + b.

Definition separated (p:addr) (a:Z) (q:addr) (b:Z) : Prop :=
  a <= 0 \/ b <= 0 \/ base p <> base q \/
  offset q + b <= offset p \/ offset p + a <= offset q.

(* ---- (c) the Coq side of the obligation: separated_trans, exactly as coqwp ---- *)
Lemma separated_trans_Coq :
  forall (p q r:addr) (lp lq lr:Z),
  included p lp q lq -> separated q lq r lr -> separated p lp r lr.
Proof.
  intros p q r lp lq lr Hinc Hsep.
  unfold included, separated in *.
  destruct (Z_le_gt_dec lp 0) as [Hlp | Hlp].
  - left; exact Hlp.
  - assert (Hlp' : 0 < lp) by lia.
    specialize (Hinc Hlp'); destruct Hinc as (Hlq & Hbase & Hoff1 & Hoff2).
    destruct Hsep as [H | [H | [H | [H | H]]]].
    + left; lia.
    + right; left; exact H.
    + right; right; left; rewrite Hbase; exact H.
    + right; right; right; left; lia.
    + right; right; right; right; lia.
Qed.

(* ===================================================================== *)
(*  STEP 1 -- the Why3 AST  [[separated_trans]] : formula                  *)
(* ===================================================================== *)
Local Open Scope string_scope.

(* The 'addr' type as a monomorphic 0-ary type symbol (its ADT structure is
   irrelevant to the lemma *statement*; only its name/arity matter here). *)
Definition addr_ts : typesym := mk_ts "addr" nil.
Definition addr_ty : vty     := vty_cons addr_ts nil.

(* The two defined predicates, as uninterpreted predicate symbols of the
   statement: included, separated : addr -> int -> addr -> int -> Prop.
   Monomorphic (s_params = []), so the well-formedness proofs are eq_refl. *)
Definition pred_args : list vty := [addr_ty; vty_int; addr_ty; vty_int].
Definition included_ps : predsym :=
  Build_predsym (Build_fpsym "included" nil pred_args eq_refl eq_refl).
Definition separated_ps : predsym :=
  Build_predsym (Build_fpsym "separated" nil pred_args eq_refl eq_refl).

(* The six bound variables (vsymbol = string * vty). *)
Definition p_vs  : vsymbol := ("p",  addr_ty).
Definition q_vs  : vsymbol := ("q",  addr_ty).
Definition r_vs  : vsymbol := ("r",  addr_ty).
Definition lp_vs : vsymbol := ("lp", vty_int).
Definition lq_vs : vsymbol := ("lq", vty_int).
Definition lr_vs : vsymbol := ("lr", vty_int).

(* Predicate applications (no type-args: the symbols are monomorphic). *)
Definition app_inc (x lx y ly : vsymbol) : formula :=
  Fpred included_ps nil [Tvar x; Tvar lx; Tvar y; Tvar ly].
Definition app_sep (x lx y ly : vsymbol) : formula :=
  Fpred separated_ps nil [Tvar x; Tvar lx; Tvar y; Tvar ly].

(* Body:  included(p,lp,q,lq) -> separated(q,lq,r,lr) -> separated(p,lp,r,lr) *)
Definition sep_trans_body : formula :=
  Fbinop Timplies (app_inc p_vs lp_vs q_vs lq_vs)
    (Fbinop Timplies (app_sep q_vs lq_vs r_vs lr_vs)
                     (app_sep p_vs lp_vs r_vs lr_vs)).

(* Closed formula:  forall p q r : addr, forall lp lq lr : int, <body> *)
Definition sep_trans_fmla : formula :=
  Fquant Tforall p_vs  (Fquant Tforall q_vs  (Fquant Tforall r_vs
  (Fquant Tforall lp_vs (Fquant Tforall lq_vs (Fquant Tforall lr_vs
     sep_trans_body))))).

(* It type-checks as a formula (the AST is well-formed). *)
Check sep_trans_fmla : formula.

(* NEXT (§5 steps 4-5): the bridge round-trip vs why3-separated_trans.mlw, the
   context gamma (addr ADT + included/separated defs), and the obligation
   separated_trans_Coq <-> formula_rep ... sep_trans_fmla, Print-Assumptions-clean. *)

(* ===================================================================== *)
(*  STEP 5 -- the obligation: model foundations (machine-checked)          *)
(* ===================================================================== *)
From Proofs Require Import core.Context.
From Proofs Require Import core.Typechecker.

(* (i) The Why3 context: addr as an ABSTRACT type, included/separated as
   ABSTRACT predicate symbols. (In the lemma *statement* these are the
   interpreted symbols of the obligation; their Coq meaning is supplied by
   the interpretation pi_funpred, below.) *)
Definition gamma : context :=
  [abs_pred separated_ps; abs_pred included_ps; abs_type addr_ts].

(* (ii) valid_context, discharged by the framework's decidable checker
   (no axioms -- pure computation via check_context_correct). *)
Lemma gamma_valid : valid_context gamma.
Proof. apply (elimT (check_context_correct gamma)). vm_compute; reflexivity. Qed.

(* (iii) sep_trans_fmla is well-typed in gamma, by the decidable typechecker. *)
Lemma sep_trans_typed : formula_typed gamma sep_trans_fmla.
Proof.
  apply (elimT (typecheck_formula_correct gamma sep_trans_fmla)).
  vm_compute; reflexivity.
Qed.

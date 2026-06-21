(* Leg 1 -- the concrete model interpretation for the separated_trans obligation. *)
From Stdlib Require Import ZArith.
From Proofs Require Import core.Types core.Syntax core.Context core.Interp
                           core.Domain core.Denotational core.IndTypes.
Require Import Leg1.SeparatedTrans.
Set Bullet Behavior "Strict Subproofs".
Open Scope Z_scope.

(* addr's sort; the domain interpretation: addr_sort -> Coq addr, else unit
   (the `domain` wrapper hardcodes int->Z, real->R regardless of dom_aux). *)
Definition addr_sort : sort := typesym_to_sort addr_ts nil.
Definition my_dom_aux (s: sort) : Set :=
  if sort_eq_dec s addr_sort then addr else unit.

Lemma my_dom_ne : forall s, domain_nonempty (domain my_dom_aux) s.
Proof.
  intros s. apply DE. unfold domain.
  destruct (sort_to_ty s).
  - exact 0%Z.
  - exact 0%R.
  - unfold my_dom_aux; destruct (sort_eq_dec s addr_sort);
      [ exact (mk_addr 0 0) | exact tt ].
  - unfold my_dom_aux; destruct (sort_eq_dec s addr_sort);
      [ exact (mk_addr 0 0) | exact tt ].
Defined.

Definition my_pd : pi_dom := Build_pi_dom my_dom_aux my_dom_ne.

Definition my_pdf : pi_dom_full gamma my_pd.
Proof.
  refine (Build_pi_dom_full gamma my_pd (fun m srts a m_in Hin => _)).
  exfalso. unfold mut_in_ctx in m_in. vm_compute in m_in. discriminate.
Defined.

(* funs: default value via non-emptiness (no funsyms are used by the formula). *)
Definition my_funs (f:funsym) (srts:list sort)
  (args: arg_list (domain my_dom_aux) (sym_sigma_args f srts))
  : domain my_dom_aux (funsym_sigma_ret f srts) :=
  match my_dom_ne (funsym_sigma_ret f srts) with DE x => x end.

(* preds: the real interpretation. included_ps/separated_ps are monomorphic with
   no type vars, so sym_sigma_args _ srts reduces to [addr_sort;s_int;addr_sort;s_int]
   for ANY srts; domain my_dom_aux addr_sort reduces to addr, domain _ s_int to Z. *)
Definition pred_srts : list sort := [addr_sort; s_int; addr_sort; s_int].

Definition includedb (p:addr) (a:Z) (q:addr) (b:Z) : bool :=
  implb (0 <? a)
    (((0 <=? b) && (base p =? base q)) &&
     ((offset q <=? offset p) && (offset p + a <=? offset q + b))).

Definition separatedb (p:addr) (a:Z) (q:addr) (b:Z) : bool :=
  (((a <=? 0) || (b <=? 0)) || negb (base p =? base q)) ||
  ((offset q + b <=? offset p) || (offset p + a <=? offset q)).

Definition cast_set {A B : Set} (H : A = B) (x : A) : B :=
  match H in (_ = B0) return B0 with eq_refl => x end.

Lemma dom_addr_eq : domain my_dom_aux addr_sort = addr.
Proof.
  unfold domain.
  replace (sort_to_ty addr_sort) with (vty_cons addr_ts nil) by reflexivity.
  unfold my_dom_aux. destruct (sort_eq_dec addr_sort addr_sort) as [e|e];
    [ reflexivity | now exfalso; apply e ].
Qed.

Lemma dom_int_eq : domain my_dom_aux s_int = Z.
Proof. reflexivity. Qed.

Definition dom_to_addr (d : domain my_dom_aux addr_sort) : addr := cast_set dom_addr_eq d.
Definition dom_to_Z    (d : domain my_dom_aux s_int)     : Z    := cast_set dom_int_eq d.

Definition get4 (args : arg_list (domain my_dom_aux) pred_srts) : addr * Z * addr * Z :=
  (dom_to_addr (hlist_hd args),
   dom_to_Z    (hlist_hd (hlist_tl args)),
   dom_to_addr (hlist_hd (hlist_tl (hlist_tl args))),
   dom_to_Z    (hlist_hd (hlist_tl (hlist_tl (hlist_tl args))))).

Lemma sym_args_inc (srts:list sort) : sym_sigma_args included_ps srts = pred_srts.
Proof.
  unfold sym_sigma_args, ty_subst_list_s, pred_srts. cbn.
  repeat (f_equal; try (apply sort_inj; reflexivity)).
Qed.
Lemma sym_args_sep (srts:list sort) : sym_sigma_args separated_ps srts = pred_srts.
Proof.
  unfold sym_sigma_args, ty_subst_list_s, pred_srts. cbn.
  repeat (f_equal; try (apply sort_inj; reflexivity)).
Qed.

Definition my_preds (p:predsym) (srts:list sort)
  (args: arg_list (domain my_dom_aux) (sym_sigma_args p srts)) : bool :=
  match predsym_eq_dec p included_ps with
  | left Heq =>
      let args' : arg_list (domain my_dom_aux) (sym_sigma_args included_ps srts) :=
        scast (f_equal (fun pp : predsym => arg_list (domain my_dom_aux) (sym_sigma_args pp srts)) Heq) args in
      let args2 : arg_list (domain my_dom_aux) pred_srts :=
        scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc srts)) args' in
      let '(a0, a1, a2, a3) := get4 args2 in includedb a0 a1 a2 a3
  | right _ =>
      match predsym_eq_dec p separated_ps with
      | left Heq =>
          let args' : arg_list (domain my_dom_aux) (sym_sigma_args separated_ps srts) :=
            scast (f_equal (fun pp : predsym => arg_list (domain my_dom_aux) (sym_sigma_args pp srts)) Heq) args in
          let args2 : arg_list (domain my_dom_aux) pred_srts :=
            scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep srts)) args' in
          let '(a0, a1, a2, a3) := get4 args2 in separatedb a0 a1 a2 a3
      | right _ => false
      end
  end.

Definition my_pf : pi_funpred gamma_valid my_pd my_pdf.
Proof.
  refine (Build_pi_funpred gamma_valid my_pd my_pdf my_funs my_preds (fun m a c Hm Ha Hc srts Hlens args => _)).
  exfalso. unfold mut_in_ctx in Hm. vm_compute in Hm. discriminate.
Defined.

(* ---- boolean versions of the Coq predicates + their reflections ---- *)
Lemma includedb_iff p a q b : included p a q b <-> includedb p a q b = true.
Proof.
  unfold included, includedb.
  rewrite implb_true_iff, Z.ltb_lt, !andb_true_iff,
          !Z.leb_le, Z.eqb_eq.
  split; intros H; [ intros Ha | intros Ha ]; specialize (H Ha); tauto.
Qed.

Lemma separatedb_iff p a q b : separated p a q b <-> separatedb p a q b = true.
Proof.
  unfold separated, separatedb.
  rewrite !orb_true_iff, negb_true_iff, !Z.leb_le.
  destruct (Z.eqb_spec (base p) (base q)); split; intros H;
    repeat (destruct H as [H|H]); try tauto; try lia.
Qed.

(* ===================================================================== *)
(*  The obligation -- components built; statement reduced to a concrete    *)
(*  goal by simpl_rep_full (finishing is a dom_cast-cancellation grind).    *)
(* ===================================================================== *)
Definition my_vt : val_typevar := fun _ => s_int.
Definition my_vv : val_vars my_pd my_vt :=
  fun x => match my_dom_ne (v_subst my_vt (snd x)) with DE d => d end.

(* The Coq proposition the Why3 formula must denote (= separated_trans_Coq's type). *)
Definition sep_trans_prop : Prop :=
  forall (p q r:addr) (lp lq lr:Z),
    included p lp q lq -> separated q lq r lr -> separated p lp r lr.

(* OBLIGATION (leg1 README §4):
     formula_rep ... sep_trans_fmla = true  <->  sep_trans_prop
   `unfold sep_trans_fmla, sep_trans_body; simpl_rep_full` reduces the LHS to
     all_dec (forall d:addr, ... all_dec (forall d4:Z,
       implb (my_preds included_ps [] (pred_arg_list ... [Tvar p;Tvar lp;Tvar q;Tvar lq] (term_rep ...)))
             (implb (my_preds separated_ps [] ...) (my_preds separated_ps [] ...)))).
   Remaining: strip the 6 all_dec (simpl_all_dec), compute my_preds (predsym_eq_dec
   reduces to `left`; the scasts cancel via dom_cast_twice), show term_rep of each
   Tvar = the bound d_i (substi_mult_nth' + var_to_dom), then close with
   includedb_iff / separatedb_iff and implb semantics. *)

(* ---- obligation, partially mechanized (axiom-free) ---- *)
Require Import Stdlib.Setoids.Setoid.

(* Strips formula_rep's all_dec (= true) to its proposition. *)
Lemma allb (P:Prop) : proj_sumbool _ _ (all_dec P) = true <-> P.
Proof.
  destruct (all_dec P) as [p|np]; simpl; split; intro H.
  - exact p.
  - reflexivity.
  - discriminate H.
  - exfalso; exact (np H).
Qed.

(* REDUCTION (verified to compile):
     unfold sep_trans_fmla, sep_trans_body; simpl_rep_full;
     rewrite allb; repeat setoid_rewrite allb.
   turns the obligation
     formula_rep ... sep_trans_fmla = true  <->  sep_trans_prop
   into the concrete goal
     (forall (d d0 d1 : domain my_dom_aux (v_subst my_vt addr_ty))
             (d2 d3 d4 : domain my_dom_aux (v_subst my_vt vty_int)),
        implb (my_preds included_ps [] (pred_arg_list ... [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs]
                  (term_rep ... (substi ... my_vv p_vs d ... lr_vs d4))))
              (implb (my_preds separated_ps [] (pred_arg_list ... [Tvar q_vs;...]))
                     (my_preds separated_ps [] (pred_arg_list ... [Tvar p_vs;...]))))
     <-> sep_trans_prop.
   REMAINING (one cast-cancellation lemma, mechanical, no axioms): prove
     my_preds included_ps [] (pred_arg_list .. [Tvar a;Tvar b;Tvar c;Tvar e] (term_rep .. vv'))
       = includedb (vv' a) (vv' b) (vv' c) (vv' e)   (modulo cast_set/dom_cast,
   merged via dom_cast_compose + dom_cast_refl; term_rep(Tvar x) = dom_cast (var_to_dom vv' x)
   and get_arg_list_hnth give hnth i = dom_cast (term_rep ..)); ditto separated;
   then close with includedb_iff / separatedb_iff and implb semantics. *)

(* Leg 1 -- the concrete model interpretation for the separated_trans obligation. *)
From Stdlib Require Import ZArith.
From Proofs Require Import core.Types core.Syntax core.Context core.Interp
                           core.Domain core.Denotational core.IndTypes core.Typechecker.
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

(* gt : int -> int -> Prop, interpreted as Z `>` (a > b := b < a). *)
Definition gt_srts : list sort := [s_int; s_int].
Definition gtb (a b : Z) : bool := b <? a.
Definition get2 (args : arg_list (domain my_dom_aux) gt_srts) : Z * Z :=
  (dom_to_Z (hlist_hd args), dom_to_Z (hlist_hd (hlist_tl args))).
Lemma sym_args_gt (srts:list sort) : sym_sigma_args gt_ps srts = gt_srts.
Proof.
  unfold sym_sigma_args, ty_subst_list_s, gt_srts. cbn.
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
      | right _ =>
          match predsym_eq_dec p gt_ps with
          | left Heq =>
              let args' : arg_list (domain my_dom_aux) (sym_sigma_args gt_ps srts) :=
                scast (f_equal (fun pp : predsym => arg_list (domain my_dom_aux) (sym_sigma_args pp srts)) Heq) args in
              let args2 : arg_list (domain my_dom_aux) gt_srts :=
                scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_gt srts)) args' in
              let '(a0, a1) := get2 args2 in gtb a0 a1
          | right _ => false
          end
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

Lemma gtb_iff a b : a > b <-> gtb a b = true.
Proof. unfold gtb. rewrite Z.ltb_lt. lia. Qed.

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

(* REDUCTION + CLOSURE (now a theorem -- see `sep_trans_faithful` at the end).
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
   The cast-cancellation is discharged by the helper lemmas below
   (term_rep_tvar / argval / posval compute the denotation of each Tvar predicate
   argument through the dependent dom_cast layers; collapseA/collapseZ reduce the
   get4 cast tower to the carrier projections D2A/D2Z; my_preds_inc/_sep_* give the
   value of my_preds on the real argument lists). The outer `forall d:domain` is
   reindexed as `forall p:addr` via the D2A/D2Z bijections (D2A_inv/D2Z_inv), and
   includedb_iff/separatedb_iff + implb close the equivalence.

   AXIOM BASE (finding): the why3-semantics framework's Cast.UIP is derived from Stdlib's
   Eqdep.Eq_rect_eq.eq_rect_eq (Streicher's K), so `formula_rep` itself rests on eq_rect_eq.
   So `sep_trans_faithful` carries NO proof hole and introduces NO new axiom; its
   Print-Assumptions footprint is exactly the framework's standard base (eq_rect_eq /
   functional_extensionality / classic / constructive_indefinite_description /
   sig_forall_dec) -- the allowed A_coq for leg 1. *)

(* ===== projection casts + helper lemmas for the faithfulness obligation ===== *)
Definition Hva : v_subst my_vt addr_ty = addr_sort := ltac:(apply sort_inj; reflexivity).
Definition Hvi : v_subst my_vt vty_int = s_int := ltac:(apply sort_inj; reflexivity).
Definition D2A (d : domain my_dom_aux (v_subst my_vt addr_ty)) : addr :=
  cast_set dom_addr_eq (dom_cast my_dom_aux Hva d).
Definition D2Z (d : domain my_dom_aux (v_subst my_vt vty_int)) : Z :=
  dom_cast my_dom_aux Hvi d.

Lemma cast_set_scast {A B:Set} (H:A=B) x : cast_set H x = scast H x.
Proof. destruct H; reflexivity. Qed.

Lemma term_rep_tvar (vv: val_vars my_pd my_vt) (t:term) (x:vsymbol) (ty:vty)
  (Ht : term_has_type gamma t ty) (Hx : t = Tvar x) :
  exists (E : v_subst my_vt (snd x) = v_subst my_vt ty),
    term_rep gamma_valid my_pd my_pdf my_vt my_pf vv t ty Ht = dom_cast (dom_aux my_pd) E (vv x).
Proof. subst t. eexists. rewrite term_rep_equation_3. cbv zeta. unfold var_to_dom. reflexivity. Qed.

Lemma argval (P:predsym) (Hsp : s_params P = []) (vv: val_vars my_pd my_vt) (ts: list term)
  (Hval : formula_typed gamma (Fpred P [] ts)) (i:nat) (x:vsymbol)
  (Hi : (i < Datatypes.length (s_args P))%nat) (Hnth : nth i ts tm_d = Tvar x) :
  exists (E : v_subst my_vt (snd x) = nth i (sym_sigma_args P []) s_int),
    hnth i (pred_arg_list my_pd my_vt P [] ts
              (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval) s_int (dom_int my_pd)
    = dom_cast (dom_aux my_pd) E (vv x).
Proof.
  unfold pred_arg_list.
  pose (Heq := arg_list_hnth_eq P (eq_sym (f_equal (map vty_var) Hsp)) Hi my_vt).
  pose (Hty := arg_list_hnth_ty (proj1' (pred_val_inv Hval))
                                (proj2' (proj2' (pred_val_inv Hval))) Hi).
  destruct (term_rep_tvar vv (nth i ts tm_d) x _ Hty Hnth) as [E' HE'].
  exists (eq_trans E' Heq). etransitivity.
  { apply (get_arg_list_hnth my_pd my_vt P [] ts
      (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv)
      (@term_rep_irrel gamma gamma_valid my_pd my_pdf my_pf my_vt vv)
      (s_params_Nodup P) (proj1' (pred_val_inv Hval))
      (proj1' (proj2' (pred_val_inv Hval))) (proj2' (proj2' (pred_val_inv Hval)))
      i Hi Heq Hty). }
  rewrite HE'. rewrite dom_cast_compose. reflexivity.
Qed.

Lemma posval (P:predsym) (Hsp : s_params P = []) (vv: val_vars my_pd my_vt) (ts: list term)
  (Hval : formula_typed gamma (Fpred P [] ts)) (i:nat) (x:vsymbol)
  (Hi : (i < Datatypes.length (s_args P))%nat) (Hnth : nth i ts tm_d = Tvar x)
  {L : list sort} (HP : sym_sigma_args P [] = L) :
  exists (E : v_subst my_vt (snd x) = nth i L s_int),
    hnth i (cast_arg_list HP (pred_arg_list my_pd my_vt P [] ts
              (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)) s_int (dom_int my_pd)
    = dom_cast (dom_aux my_pd) E (vv x).
Proof.
  destruct (argval P Hsp vv ts Hval i x Hi Hnth) as [E0 HE0].
  exists (eq_trans E0 (cast_nth_eq HP i s_int)).
  rewrite hnth_cast_arg_list.
  transitivity (scast (f_equal (domain (dom_aux my_pd)) (cast_nth_eq HP i s_int))
                  (dom_cast (dom_aux my_pd) E0 (vv x))).
  { f_equal. exact HE0. }
  unfold dom_cast. rewrite scast_scast. apply scast_eq_uip.
Qed.

Lemma collapseA (E : v_subst my_vt addr_ty = addr_sort)
  (y : domain my_dom_aux (v_subst my_vt addr_ty)) :
  cast_set dom_addr_eq (dom_cast (dom_aux my_pd) E y) = D2A y.
Proof. unfold D2A. f_equal. unfold dom_cast. apply scast_eq_uip. Qed.

Lemma collapseZ (E : v_subst my_vt vty_int = s_int)
  (y : domain my_dom_aux (v_subst my_vt vty_int)) :
  cast_set dom_int_eq (dom_cast (dom_aux my_pd) E y) = D2Z y.
Proof.
  unfold D2Z. rewrite cast_set_scast. unfold dom_cast. rewrite scast_scast.
  apply scast_eq_uip.
Qed.

Lemma my_preds_inc (vv: val_vars my_pd my_vt)
  (Hval : formula_typed gamma (Fpred included_ps []
            [Tvar p_vs; Tvar lp_vs; Tvar q_vs; Tvar lq_vs])) :
  my_preds included_ps [] (pred_arg_list my_pd my_vt included_ps []
     [Tvar p_vs; Tvar lp_vs; Tvar q_vs; Tvar lq_vs]
     (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)
  = includedb (D2A (vv p_vs)) (D2Z (vv lp_vs)) (D2A (vv q_vs)) (D2Z (vv lq_vs)).
Proof.
  unfold my_preds.
  destruct (predsym_eq_dec included_ps included_ps) as [Heqp|Hne]; [|exfalso; now apply Hne].
  rewrite (UIP_dec predsym_eq_dec Heqp eq_refl). simpl.
  set (ARGS := pred_arg_list my_pd my_vt included_ps []
        [Tvar p_vs; Tvar lp_vs; Tvar q_vs; Tvar lq_vs]
        (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval).
  unfold get4.
  destruct (posval included_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs] Hval 0 p_vs  ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E0 H0].
  destruct (posval included_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs] Hval 1 lp_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E1 H1].
  destruct (posval included_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs] Hval 2 q_vs  ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E2 H2].
  destruct (posval included_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs] Hval 3 lq_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E3 H3].
  fold ARGS in H0, H1, H2, H3.
  change (hlist_hd (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS))
    with (hnth 0 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS)))
    with (hnth 1 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS))))
    with (hnth 2 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS)))))
    with (hnth 3 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  rewrite H0, H1, H2, H3. unfold dom_to_addr, dom_to_Z.
  f_equal; [ apply collapseA | apply collapseZ | apply collapseA | apply collapseZ ].
Qed.

Lemma my_preds_sep_qr (vv: val_vars my_pd my_vt)
  (Hval : formula_typed gamma (Fpred separated_ps [] [Tvar q_vs; Tvar lq_vs; Tvar r_vs; Tvar lr_vs])) :
  my_preds separated_ps [] (pred_arg_list my_pd my_vt separated_ps []
     [Tvar q_vs; Tvar lq_vs; Tvar r_vs; Tvar lr_vs]
     (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)
  = separatedb (D2A (vv q_vs)) (D2Z (vv lq_vs)) (D2A (vv r_vs)) (D2Z (vv lr_vs)).
Proof.
  unfold my_preds.
  destruct (predsym_eq_dec separated_ps included_ps) as [Hbad|_]; [exfalso; inversion Hbad|].
  destruct (predsym_eq_dec separated_ps separated_ps) as [Heqp|Hne]; [|exfalso; now apply Hne].
  rewrite (UIP_dec predsym_eq_dec Heqp eq_refl). simpl.
  set (ARGS := pred_arg_list my_pd my_vt separated_ps []
        [Tvar q_vs; Tvar lq_vs; Tvar r_vs; Tvar lr_vs]
        (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval).
  unfold get4.
  destruct (posval separated_ps eq_refl vv [Tvar q_vs;Tvar lq_vs;Tvar r_vs;Tvar lr_vs] Hval 0 q_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E0 H0].
  destruct (posval separated_ps eq_refl vv [Tvar q_vs;Tvar lq_vs;Tvar r_vs;Tvar lr_vs] Hval 1 lq_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E1 H1].
  destruct (posval separated_ps eq_refl vv [Tvar q_vs;Tvar lq_vs;Tvar r_vs;Tvar lr_vs] Hval 2 r_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E2 H2].
  destruct (posval separated_ps eq_refl vv [Tvar q_vs;Tvar lq_vs;Tvar r_vs;Tvar lr_vs] Hval 3 lr_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E3 H3].
  fold ARGS in H0, H1, H2, H3.
  change (hlist_hd (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS))
    with (hnth 0 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS)))
    with (hnth 1 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS))))
    with (hnth 2 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS)))))
    with (hnth 3 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  rewrite H0, H1, H2, H3. unfold dom_to_addr, dom_to_Z.
  f_equal; [ apply collapseA | apply collapseZ | apply collapseA | apply collapseZ ].
Qed.

Lemma my_preds_sep_pr (vv: val_vars my_pd my_vt)
  (Hval : formula_typed gamma (Fpred separated_ps [] [Tvar p_vs; Tvar lp_vs; Tvar r_vs; Tvar lr_vs])) :
  my_preds separated_ps [] (pred_arg_list my_pd my_vt separated_ps []
     [Tvar p_vs; Tvar lp_vs; Tvar r_vs; Tvar lr_vs]
     (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)
  = separatedb (D2A (vv p_vs)) (D2Z (vv lp_vs)) (D2A (vv r_vs)) (D2Z (vv lr_vs)).
Proof.
  unfold my_preds.
  destruct (predsym_eq_dec separated_ps included_ps) as [Hbad|_]; [exfalso; inversion Hbad|].
  destruct (predsym_eq_dec separated_ps separated_ps) as [Heqp|Hne]; [|exfalso; now apply Hne].
  rewrite (UIP_dec predsym_eq_dec Heqp eq_refl). simpl.
  set (ARGS := pred_arg_list my_pd my_vt separated_ps []
        [Tvar p_vs; Tvar lp_vs; Tvar r_vs; Tvar lr_vs]
        (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval).
  unfold get4.
  destruct (posval separated_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar r_vs;Tvar lr_vs] Hval 0 p_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E0 H0].
  destruct (posval separated_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar r_vs;Tvar lr_vs] Hval 1 lp_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E1 H1].
  destruct (posval separated_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar r_vs;Tvar lr_vs] Hval 2 r_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E2 H2].
  destruct (posval separated_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar r_vs;Tvar lr_vs] Hval 3 lr_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E3 H3].
  fold ARGS in H0, H1, H2, H3.
  change (hlist_hd (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS))
    with (hnth 0 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS)))
    with (hnth 1 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS))))
    with (hnth 2 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS)))))
    with (hnth 3 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  rewrite H0, H1, H2, H3. unfold dom_to_addr, dom_to_Z.
  f_equal; [ apply collapseA | apply collapseZ | apply collapseA | apply collapseZ ].
Qed.

(* ===================================================================== *)
(*  Leg-1 obligation CLOSED (§5.4a): the coqwp lemma IS what Why3 means.   *)
(*  Helper lemmas (all axiom-free modulo the framework's standard base):   *)
(*   term_rep_tvar/argval/posval  -- compute the denotation of a Tvar      *)
(*     predicate-argument list through the dependent dom_cast layers;       *)
(*   collapseA/collapseZ          -- the get4 cast tower = the carrier      *)
(*     projections D2A/D2Z;                                                 *)
(*   my_preds_inc/_sep_qr/_sep_pr -- my_preds on the actual argument lists  *)
(*     = includedb/separatedb of the projected values;                     *)
(*   D2A_inv/D2Z_inv              -- D2A/D2Z are bijections (A2D/Z2D);      *)
(*   substi_eq/substi_neq         -- the six bound-variable lookups;        *)
(*  then includedb_iff/separatedb_iff + implb close the equivalence and the *)
(*  D2A/D2Z bijection reindexes forall-over-domain as forall-over-addr.     *)
(* ===================================================================== *)
Definition A2D (a:addr) : domain my_dom_aux (v_subst my_vt addr_ty) :=
  dom_cast my_dom_aux (eq_sym Hva) (cast_set (eq_sym dom_addr_eq) a).
Definition Z2D (z:Z) : domain my_dom_aux (v_subst my_vt vty_int) :=
  dom_cast my_dom_aux (eq_sym Hvi) z.
Lemma D2A_inv (a:addr) : D2A (A2D a) = a.
Proof. unfold D2A, A2D. rewrite dom_cast_twice. rewrite !cast_set_scast.
  rewrite scast_scast. apply scast_refl_uip. Qed.
Lemma D2Z_inv (z:Z) : D2Z (Z2D z) = z.
Proof. unfold D2Z, Z2D. rewrite dom_cast_twice. reflexivity. Qed.

Lemma substi_eq (vv:val_vars my_pd my_vt) (x:vsymbol) (y:domain my_dom_aux (v_subst my_vt (snd x))) :
  substi my_pd my_vt vv x y x = y.
Proof. unfold substi. destruct (vsymbol_eq_dec x x) as [e|n]; [|exfalso; now apply n].
  rewrite (UIP_dec vsymbol_eq_dec e eq_refl). reflexivity. Qed.
Lemma substi_neq (vv:val_vars my_pd my_vt) (x z:vsymbol) (y:domain my_dom_aux (v_subst my_vt (snd x))) :
  z <> x -> substi my_pd my_vt vv x y z = vv z.
Proof. intro H. unfold substi. destruct (vsymbol_eq_dec z x) as [e|n]; [exfalso; now apply H|reflexivity]. Qed.

Ltac slook := repeat (rewrite substi_eq || (rewrite substi_neq by (intro Hc; inversion Hc))).
Ltac slookin H := repeat (rewrite substi_eq in H || (rewrite substi_neq in H by (intro Hc; inversion Hc))).

Theorem sep_trans_faithful :
  @formula_rep gamma gamma_valid my_pd my_pdf my_vt my_pf my_vv
    sep_trans_fmla sep_trans_typed = true
  <-> sep_trans_prop.
Proof.
  unfold sep_trans_fmla, sep_trans_body. simpl_rep_full.
  rewrite allb; repeat setoid_rewrite allb.
  unfold sep_trans_prop. split.
  - intros H p q r lp lq lr Hinc Hsep.
    specialize (H (A2D p) (A2D q) (A2D r) (Z2D lp) (Z2D lq) (Z2D lr)).
    rewrite my_preds_inc, my_preds_sep_qr, my_preds_sep_pr in H.
    slookin H. rewrite !D2A_inv, !D2Z_inv in H. unfold is_true in H.
    rewrite includedb_iff in Hinc. rewrite separatedb_iff in Hsep.
    rewrite Hinc in H. simpl in H. rewrite Hsep in H. simpl in H.
    apply separatedb_iff. exact H.
  - intros H d d0 d1 d2 d3 d4.
    rewrite my_preds_inc, my_preds_sep_qr, my_preds_sep_pr. slook. unfold is_true.
    destruct (includedb (D2A d) (D2Z d2) (D2A d0) (D2Z d3)) eqn:Eic; simpl; [|reflexivity].
    destruct (separatedb (D2A d0) (D2Z d3) (D2A d1) (D2Z d4)) eqn:Esq; simpl; [|reflexivity].
    rewrite <- separatedb_iff.
    apply (H (D2A d) (D2A d0) (D2A d1) (D2Z d2) (D2Z d3) (D2Z d4)).
    + rewrite <- includedb_iff in Eic. exact Eic.
    + rewrite <- separatedb_iff in Esq. exact Esq.
Qed.

Lemma my_preds_inc_qr (vv: val_vars my_pd my_vt)
  (Hval : formula_typed gamma (Fpred included_ps [] [Tvar q_vs; Tvar lq_vs; Tvar r_vs; Tvar lr_vs])) :
  my_preds included_ps [] (pred_arg_list my_pd my_vt included_ps []
     [Tvar q_vs; Tvar lq_vs; Tvar r_vs; Tvar lr_vs]
     (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)
  = includedb (D2A (vv q_vs)) (D2Z (vv lq_vs)) (D2A (vv r_vs)) (D2Z (vv lr_vs)).
Proof.
  unfold my_preds.
  destruct (predsym_eq_dec included_ps included_ps) as [Heqp|Hne]; [|exfalso; now apply Hne].
  rewrite (UIP_dec predsym_eq_dec Heqp eq_refl). simpl.
  set (ARGS := pred_arg_list my_pd my_vt included_ps []
        [Tvar q_vs; Tvar lq_vs; Tvar r_vs; Tvar lr_vs]
        (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval).
  unfold get4.
  destruct (posval included_ps eq_refl vv [Tvar q_vs;Tvar lq_vs;Tvar r_vs;Tvar lr_vs] Hval 0 q_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E0 H0].
  destruct (posval included_ps eq_refl vv [Tvar q_vs;Tvar lq_vs;Tvar r_vs;Tvar lr_vs] Hval 1 lq_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E1 H1].
  destruct (posval included_ps eq_refl vv [Tvar q_vs;Tvar lq_vs;Tvar r_vs;Tvar lr_vs] Hval 2 r_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E2 H2].
  destruct (posval included_ps eq_refl vv [Tvar q_vs;Tvar lq_vs;Tvar r_vs;Tvar lr_vs] Hval 3 lr_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E3 H3].
  fold ARGS in H0, H1, H2, H3.
  change (hlist_hd (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS))
    with (hnth 0 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS)))
    with (hnth 1 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS))))
    with (hnth 2 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS)))))
    with (hnth 3 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  rewrite H0, H1, H2, H3. unfold dom_to_addr, dom_to_Z.
  f_equal; [ apply collapseA | apply collapseZ | apply collapseA | apply collapseZ ].
Qed.

Lemma my_preds_inc_pr (vv: val_vars my_pd my_vt)
  (Hval : formula_typed gamma (Fpred included_ps [] [Tvar p_vs; Tvar lp_vs; Tvar r_vs; Tvar lr_vs])) :
  my_preds included_ps [] (pred_arg_list my_pd my_vt included_ps []
     [Tvar p_vs; Tvar lp_vs; Tvar r_vs; Tvar lr_vs]
     (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)
  = includedb (D2A (vv p_vs)) (D2Z (vv lp_vs)) (D2A (vv r_vs)) (D2Z (vv lr_vs)).
Proof.
  unfold my_preds.
  destruct (predsym_eq_dec included_ps included_ps) as [Heqp|Hne]; [|exfalso; now apply Hne].
  rewrite (UIP_dec predsym_eq_dec Heqp eq_refl). simpl.
  set (ARGS := pred_arg_list my_pd my_vt included_ps []
        [Tvar p_vs; Tvar lp_vs; Tvar r_vs; Tvar lr_vs]
        (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval).
  unfold get4.
  destruct (posval included_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar r_vs;Tvar lr_vs] Hval 0 p_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E0 H0].
  destruct (posval included_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar r_vs;Tvar lr_vs] Hval 1 lp_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E1 H1].
  destruct (posval included_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar r_vs;Tvar lr_vs] Hval 2 r_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E2 H2].
  destruct (posval included_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar r_vs;Tvar lr_vs] Hval 3 lr_vs ltac:(cbn;lia) eq_refl (sym_args_inc [])) as [E3 H3].
  fold ARGS in H0, H1, H2, H3.
  change (hlist_hd (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS))
    with (hnth 0 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS)))
    with (hnth 1 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS))))
    with (hnth 2 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_inc [])) ARGS)))))
    with (hnth 3 (cast_arg_list (sym_args_inc []) ARGS) s_int (dom_int my_pd)).
  rewrite H0, H1, H2, H3. unfold dom_to_addr, dom_to_Z.
  f_equal; [ apply collapseA | apply collapseZ | apply collapseA | apply collapseZ ].
Qed.

(* ===================================================================== *)
(*  Leg 1 for Memory.included_trans (same model; three included preds).    *)
(* ===================================================================== *)
Definition inc_trans_body : formula :=
  Fbinop Timplies (app_inc p_vs lp_vs q_vs lq_vs)
    (Fbinop Timplies (app_inc q_vs lq_vs r_vs lr_vs)
                     (app_inc p_vs lp_vs r_vs lr_vs)).
Definition inc_trans_fmla : formula :=
  Fquant Tforall p_vs (Fquant Tforall q_vs (Fquant Tforall r_vs
  (Fquant Tforall lp_vs (Fquant Tforall lq_vs (Fquant Tforall lr_vs inc_trans_body))))).
Lemma inc_trans_typed : formula_typed gamma inc_trans_fmla.
Proof.
  apply (elimT (typecheck_formula_correct gamma inc_trans_fmla)).
  vm_compute; reflexivity.
Qed.

Definition included_trans_prop : Prop :=
  forall (p q r:addr) (lp lq lr:Z),
    included p lp q lq -> included q lq r lr -> included p lp r lr.

Theorem included_trans_faithful :
  @formula_rep gamma gamma_valid my_pd my_pdf my_vt my_pf my_vv
    inc_trans_fmla inc_trans_typed = true
  <-> included_trans_prop.
Proof.
  unfold inc_trans_fmla, inc_trans_body. simpl_rep_full.
  rewrite allb; repeat setoid_rewrite allb.
  unfold included_trans_prop. split.
  - intros H p q r lp lq lr H1 H2.
    specialize (H (A2D p) (A2D q) (A2D r) (Z2D lp) (Z2D lq) (Z2D lr)).
    rewrite my_preds_inc, my_preds_inc_qr, my_preds_inc_pr in H.
    slookin H. rewrite !D2A_inv, !D2Z_inv in H. unfold is_true in H.
    rewrite includedb_iff in H1. rewrite includedb_iff in H2.
    rewrite H1 in H. simpl in H. rewrite H2 in H. simpl in H.
    apply includedb_iff. exact H.
  - intros H d d0 d1 d2 d3 d4.
    rewrite my_preds_inc, my_preds_inc_qr, my_preds_inc_pr. slook. unfold is_true.
    destruct (includedb (D2A d) (D2Z d2) (D2A d0) (D2Z d3)) eqn:E1; simpl; [|reflexivity].
    destruct (includedb (D2A d0) (D2Z d3) (D2A d1) (D2Z d4)) eqn:E2; simpl; [|reflexivity].
    rewrite <- includedb_iff.
    apply (H (D2A d) (D2A d0) (D2A d1) (D2Z d2) (D2Z d3) (D2Z d4)).
    + rewrite <- includedb_iff in E1. exact E1.
    + rewrite <- includedb_iff in E2. exact E2.
Qed.

(* ===================================================================== *)
(*  Leg 1 for Memory.separated_included (adds: gt predicate + int const).  *)
(* ===================================================================== *)

(* denotation of an integer literal: term_rep (Tconst (ConstInt z)) = z (cast). *)
Lemma term_rep_const (vv: val_vars my_pd my_vt) (t:term) (z:Z) (ty:vty)
  (Ht : term_has_type gamma t ty) (Hx : t = Tconst (ConstInt z)) :
  exists (E : v_subst my_vt vty_int = v_subst my_vt ty),
    term_rep gamma_valid my_pd my_pdf my_vt my_pf vv t ty Ht = dom_cast (dom_aux my_pd) E z.
Proof. subst t. eexists. rewrite term_rep_equation_1. cbv zeta. unfold cast_dom_vty. reflexivity. Qed.

Lemma argval_const (P:predsym) (Hsp : s_params P = []) (vv: val_vars my_pd my_vt) (ts: list term)
  (Hval : formula_typed gamma (Fpred P [] ts)) (i:nat) (z:Z)
  (Hi : (i < Datatypes.length (s_args P))%nat) (Hnth : nth i ts tm_d = Tconst (ConstInt z)) :
  exists (E : v_subst my_vt vty_int = nth i (sym_sigma_args P []) s_int),
    hnth i (pred_arg_list my_pd my_vt P [] ts
              (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval) s_int (dom_int my_pd)
    = dom_cast (dom_aux my_pd) E z.
Proof.
  unfold pred_arg_list.
  pose (Heq := arg_list_hnth_eq P (eq_sym (f_equal (map vty_var) Hsp)) Hi my_vt).
  pose (Hty := arg_list_hnth_ty (proj1' (pred_val_inv Hval))
                                (proj2' (proj2' (pred_val_inv Hval))) Hi).
  destruct (term_rep_const vv (nth i ts tm_d) z _ Hty Hnth) as [E' HE'].
  exists (eq_trans E' Heq). etransitivity.
  { apply (get_arg_list_hnth my_pd my_vt P [] ts
      (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv)
      (@term_rep_irrel gamma gamma_valid my_pd my_pdf my_pf my_vt vv)
      (s_params_Nodup P) (proj1' (pred_val_inv Hval))
      (proj1' (proj2' (pred_val_inv Hval))) (proj2' (proj2' (pred_val_inv Hval)))
      i Hi Heq Hty). }
  rewrite HE'. rewrite dom_cast_compose. reflexivity.
Qed.

Lemma posval_const (P:predsym) (Hsp : s_params P = []) (vv: val_vars my_pd my_vt) (ts: list term)
  (Hval : formula_typed gamma (Fpred P [] ts)) (i:nat) (z:Z)
  (Hi : (i < Datatypes.length (s_args P))%nat) (Hnth : nth i ts tm_d = Tconst (ConstInt z))
  {L : list sort} (HP : sym_sigma_args P [] = L) :
  exists (E : v_subst my_vt vty_int = nth i L s_int),
    hnth i (cast_arg_list HP (pred_arg_list my_pd my_vt P [] ts
              (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)) s_int (dom_int my_pd)
    = dom_cast (dom_aux my_pd) E z.
Proof.
  destruct (argval_const P Hsp vv ts Hval i z Hi Hnth) as [E0 HE0].
  exists (eq_trans E0 (cast_nth_eq HP i s_int)).
  rewrite hnth_cast_arg_list.
  transitivity (scast (f_equal (domain (dom_aux my_pd)) (cast_nth_eq HP i s_int))
                  (dom_cast (dom_aux my_pd) E0 z)).
  { f_equal. exact HE0. }
  unfold dom_cast. rewrite scast_scast. apply scast_eq_uip.
Qed.

(* D2Z is the identity on Z (domain my_dom_aux (v_subst my_vt vty_int) = Z definitionally). *)
Lemma D2Z_id (z:Z) : D2Z z = z.
Proof.
  unfold D2Z, dom_cast. generalize (f_equal (domain my_dom_aux) Hvi); intro H.
  assert (H = eq_refl) as -> by apply Cast.UIP. reflexivity.
Qed.

(* my_preds on gt applied to [Tvar x; Tconst z] = gtb (D2Z (vv x)) z, for the two
   concrete int variables used by separated_included (snd _ = vty_int definitionally). *)
Lemma my_preds_gt_lp (vv: val_vars my_pd my_vt) (z:Z)
  (Hval : formula_typed gamma (Fpred gt_ps [] [Tvar lp_vs; Tconst (ConstInt z)])) :
  my_preds gt_ps [] (pred_arg_list my_pd my_vt gt_ps []
     [Tvar lp_vs; Tconst (ConstInt z)]
     (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)
  = gtb (D2Z (vv lp_vs)) z.
Proof.
  unfold my_preds.
  destruct (predsym_eq_dec gt_ps included_ps) as [Hb|_]; [exfalso; inversion Hb|].
  destruct (predsym_eq_dec gt_ps separated_ps) as [Hb|_]; [exfalso; inversion Hb|].
  destruct (predsym_eq_dec gt_ps gt_ps) as [Heqp|Hne]; [|exfalso; now apply Hne].
  rewrite (UIP_dec predsym_eq_dec Heqp eq_refl). simpl.
  set (ARGS := pred_arg_list my_pd my_vt gt_ps [] [Tvar lp_vs; Tconst (ConstInt z)]
        (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval).
  unfold get2.
  destruct (posval gt_ps eq_refl vv [Tvar lp_vs; Tconst (ConstInt z)] Hval 0 lp_vs ltac:(cbn;lia) eq_refl (sym_args_gt [])) as [E0 H0].
  destruct (posval_const gt_ps eq_refl vv [Tvar lp_vs; Tconst (ConstInt z)] Hval 1 z ltac:(cbn;lia) eq_refl (sym_args_gt [])) as [E1 H1].
  fold ARGS in H0, H1.
  change (hlist_hd (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_gt [])) ARGS))
    with (hnth 0 (cast_arg_list (sym_args_gt []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_gt [])) ARGS)))
    with (hnth 1 (cast_arg_list (sym_args_gt []) ARGS) s_int (dom_int my_pd)).
  rewrite H0, H1. unfold dom_to_Z.
  f_equal.
  - apply collapseZ.
  - transitivity (D2Z z); [ apply collapseZ | apply D2Z_id ].
Qed.

Lemma my_preds_gt_lq (vv: val_vars my_pd my_vt) (z:Z)
  (Hval : formula_typed gamma (Fpred gt_ps [] [Tvar lq_vs; Tconst (ConstInt z)])) :
  my_preds gt_ps [] (pred_arg_list my_pd my_vt gt_ps []
     [Tvar lq_vs; Tconst (ConstInt z)]
     (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)
  = gtb (D2Z (vv lq_vs)) z.
Proof.
  unfold my_preds.
  destruct (predsym_eq_dec gt_ps included_ps) as [Hb|_]; [exfalso; inversion Hb|].
  destruct (predsym_eq_dec gt_ps separated_ps) as [Hb|_]; [exfalso; inversion Hb|].
  destruct (predsym_eq_dec gt_ps gt_ps) as [Heqp|Hne]; [|exfalso; now apply Hne].
  rewrite (UIP_dec predsym_eq_dec Heqp eq_refl). simpl.
  set (ARGS := pred_arg_list my_pd my_vt gt_ps [] [Tvar lq_vs; Tconst (ConstInt z)]
        (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval).
  unfold get2.
  destruct (posval gt_ps eq_refl vv [Tvar lq_vs; Tconst (ConstInt z)] Hval 0 lq_vs ltac:(cbn;lia) eq_refl (sym_args_gt [])) as [E0 H0].
  destruct (posval_const gt_ps eq_refl vv [Tvar lq_vs; Tconst (ConstInt z)] Hval 1 z ltac:(cbn;lia) eq_refl (sym_args_gt [])) as [E1 H1].
  fold ARGS in H0, H1.
  change (hlist_hd (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_gt [])) ARGS))
    with (hnth 0 (cast_arg_list (sym_args_gt []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_gt [])) ARGS)))
    with (hnth 1 (cast_arg_list (sym_args_gt []) ARGS) s_int (dom_int my_pd)).
  rewrite H0, H1. unfold dom_to_Z.
  f_equal.
  - apply collapseZ.
  - transitivity (D2Z z); [ apply collapseZ | apply D2Z_id ].
Qed.

(* separated on the [p,lp,q,lq] list (companion to my_preds_sep_qr / _pr). *)
Lemma my_preds_sep_pq (vv: val_vars my_pd my_vt)
  (Hval : formula_typed gamma (Fpred separated_ps [] [Tvar p_vs; Tvar lp_vs; Tvar q_vs; Tvar lq_vs])) :
  my_preds separated_ps [] (pred_arg_list my_pd my_vt separated_ps []
     [Tvar p_vs; Tvar lp_vs; Tvar q_vs; Tvar lq_vs]
     (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval)
  = separatedb (D2A (vv p_vs)) (D2Z (vv lp_vs)) (D2A (vv q_vs)) (D2Z (vv lq_vs)).
Proof.
  unfold my_preds.
  destruct (predsym_eq_dec separated_ps included_ps) as [Hbad|_]; [exfalso; inversion Hbad|].
  destruct (predsym_eq_dec separated_ps separated_ps) as [Heqp|Hne]; [|exfalso; now apply Hne].
  rewrite (UIP_dec predsym_eq_dec Heqp eq_refl). simpl.
  set (ARGS := pred_arg_list my_pd my_vt separated_ps []
        [Tvar p_vs; Tvar lp_vs; Tvar q_vs; Tvar lq_vs]
        (term_rep gamma_valid my_pd my_pdf my_vt my_pf vv) Hval).
  unfold get4.
  destruct (posval separated_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs] Hval 0 p_vs  ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E0 H0].
  destruct (posval separated_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs] Hval 1 lp_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E1 H1].
  destruct (posval separated_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs] Hval 2 q_vs  ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E2 H2].
  destruct (posval separated_ps eq_refl vv [Tvar p_vs;Tvar lp_vs;Tvar q_vs;Tvar lq_vs] Hval 3 lq_vs ltac:(cbn;lia) eq_refl (sym_args_sep [])) as [E3 H3].
  fold ARGS in H0, H1, H2, H3.
  change (hlist_hd (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS))
    with (hnth 0 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS)))
    with (hnth 1 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS))))
    with (hnth 2 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  change (hlist_hd (hlist_tl (hlist_tl (hlist_tl (scast (f_equal (arg_list (domain my_dom_aux)) (sym_args_sep [])) ARGS)))))
    with (hnth 3 (cast_arg_list (sym_args_sep []) ARGS) s_int (dom_int my_pd)).
  rewrite H0, H1, H2, H3. unfold dom_to_addr, dom_to_Z.
  f_equal; [ apply collapseA | apply collapseZ | apply collapseA | apply collapseZ ].
Qed.

Definition sep_incl_prop : Prop :=
  forall (p q:addr) (lp lq:Z),
    lp > 0 -> lq > 0 -> separated p lp q lq -> included p lp q lq -> False.

Theorem sep_incl_faithful :
  @formula_rep gamma gamma_valid my_pd my_pdf my_vt my_pf my_vv
    sep_incl_fmla sep_incl_typed = true
  <-> sep_incl_prop.
Proof.
  unfold sep_incl_fmla, sep_incl_body, app_gt, app_sep, app_inc. simpl_rep_full.
  rewrite allb; repeat setoid_rewrite allb.
  unfold sep_incl_prop. split.
  - intros H p q lp lq Hlp Hlq Hsep Hinc.
    specialize (H (A2D p) (A2D q) (Z2D lp) (Z2D lq)).
    rewrite my_preds_gt_lp, my_preds_gt_lq, my_preds_sep_pq, my_preds_inc in H.
    slookin H. rewrite !D2A_inv, !D2Z_inv in H. unfold is_true in H.
    rewrite gtb_iff in Hlp. rewrite gtb_iff in Hlq.
    rewrite separatedb_iff in Hsep. rewrite includedb_iff in Hinc.
    rewrite Hlp in H. simpl in H. rewrite Hlq in H. simpl in H.
    rewrite Hsep in H. simpl in H. rewrite Hinc in H. simpl in H. discriminate H.
  - intros H d d0 d1 d2.
    rewrite my_preds_gt_lp, my_preds_gt_lq, my_preds_sep_pq, my_preds_inc. slook. unfold is_true.
    destruct (gtb (D2Z d1) 0) eqn:G1; simpl; [|reflexivity].
    destruct (gtb (D2Z d2) 0) eqn:G2; simpl; [|reflexivity].
    destruct (separatedb (D2A d) (D2Z d1) (D2A d0) (D2Z d2)) eqn:S; simpl; [|reflexivity].
    destruct (includedb (D2A d) (D2Z d1) (D2A d0) (D2Z d2)) eqn:I; simpl; [|reflexivity].
    exfalso. apply (H (D2A d) (D2A d0) (D2Z d1) (D2Z d2)).
    + apply gtb_iff. exact G1.
    + apply gtb_iff. exact G2.
    + apply separatedb_iff. exact S.
    + apply includedb_iff. exact I.
Qed.

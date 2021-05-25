Require Import Reals.

Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_solve.
Require Import List.

Require Import RL.Archimedean.pol_continuous.
Require Import RL.Archimedean.Lim_seq_US.
Require Import RL.Archimedean.R_complements.
Require Import RL.Archimedean.lambda_prop_one.

Require Import RL.hmr.term.
Require Import RL.hmr.hseq.
Require Import RL.hmr.p_hseq.
Require Import RL.hmr.apply_logical_rule.
Require Import RL.hmr.lambda_prop_tools.
Require Import RL.hmr.hmr.
Require Import RL.hmr.semantic.
Require Import RL.hmr.can_elim.
Require Import RL.hmr.completeness.
Require Import RL.hmr.soundness.

Require Import RL.Utilities.riesz_logic_List_more.
Require Import RL.Utilities.riesz_logic_Nat_more.
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.polynomials.

Require Import Lra.
Require Import Lia.

Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rcomplements.
Local Open Scope R_scope.

(** * Modal free case *)
(** ** Lemma 4 with the additional information that t_i = 1 . *)
(** Useful when dealing with sequences, to ensure that t_{i,n} = 1 for all elements of the sequence *)
Definition p_def_lambda_prop_atomic_one_fixed i G val := 
  { L &
    prod (length L = length G)
         ((i < length L)%nat *
          (nth i L 0 = 1) *
          (Forall_inf (fun x => prod (0 <= x) (x <= 1)) L) *
          (forall n, eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_var n (mul_p_hseq_new_var G)) = 0) *
          (0 <= eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_one (mul_p_hseq_new_var G))))}.

(** Proof that if a parametrized hypersequent satisfies the lambda property for a sequence of valuations, then there is subsequence that satisfies the lambda property, and where t_i = 1 for each insance of the lambda property for the valuations (with the same i each time) *)
Lemma p_lambda_prop_atomic_one_seq_fixed: forall G (un : nat -> val_UniformSpace),
    (forall n, p_def_lambda_prop_atomic_one G (un n)) ->
    {' (v , i) : _ & prod (is_subseq v un)
                            (forall n, p_def_lambda_prop_atomic_one_fixed i G (v n))}.
Proof.
  intros G un H.
  destruct (IPP_eq_1 (fun n i => (nth i (projT1 (H n)) 0)) (length G)) as [[v i] [Hsubseq [Him Hipp]]].
  { intros n.
    remember (H n).
    destruct p as [L [Hlen [[[Hex Hall] Hsum] Hone]]].
    destruct (Exists_inf_nth Hex) as [[i r] Hlen' HP].
    split with i.
    split.
    - clear - Hlen Hlen'; rewrite <- Hlen.
      lia.
    - simpl.
      rewrite nth_indep with _ _ _ _ 0 in HP; try lia.
      rewrite HP; simpl; reflexivity. }
  destruct Hsubseq as [phi Hsubseq].
  split with (fun n => un (phi n), i).
  split.
  { split with phi.
    destruct Hsubseq; split; auto. }
  intros n.
  specialize (Hipp n).
  remember (H (phi n)).
  destruct p as [L [Hlen [[[Hex Hall] Hsum] Hone]]].
  split with L; repeat split; try assumption.
  - rewrite Hlen.
    apply Him.
  - destruct Hsubseq as [Hsubseq Heqn].
    rewrite Heqn in Hipp.
    rewrite <- Heqp in Hipp.
    apply Hipp.
Qed.

(** Lemma ??? - "continuity" of the lambda property *)
Lemma p_lambda_prop_atomic_one_lim : forall G (un : nat -> val_UniformSpace) (ul : val_UniformSpace),
    is_lim_seq un ul ->
    (forall n, p_def_lambda_prop_atomic_one G (un n)) ->
    p_def_lambda_prop_atomic_one G ul.
Proof.
  enough (forall G i (un : nat -> val_UniformSpace) (ul : val_UniformSpace),
             is_lim_seq un ul ->
             (forall n, p_def_lambda_prop_atomic_one_fixed i G (un n)) ->
             p_def_lambda_prop_atomic_one G ul).
  { intros.
    apply p_lambda_prop_atomic_one_seq_fixed in X0 as [[phi i] [Hsubseq Hipp]].
    refine (X G i phi ul _ Hipp).
    apply is_lim_seq_subseq with un; assumption. }
  intros G i un ul Hlim Hlp.
  destruct (seq_compact_Rn (length G) 0 1 (fun n => (projT1 (Hlp n)))) as [[v Hul] Hcs].
  - intros k.
    destruct (Hlp k) as [L [Hlen H']]; simpl.
    apply Hlen.
  - intros k j Hlt.
    destruct (Hlp k) as [L [Hlen [[[H' Hborned] Hsum] Hone]]].
    simpl.
    apply Forall_inf_forall with _ _ _ (nth j L 0) in Hborned.
    2:{ apply nth_In_inf.
        rewrite Hlen.
        apply Hlt. }
    apply Hborned.
  - destruct Hcs as [Hsubseq [Hlenul Hlimul]].
    split with Hul.
    repeat split.
    + apply Hlenul.
    + apply exists_Exists_inf with (nth i Hul 0).
      { destruct (Hlp 0%nat) as [L [Hlen [[[H' Hborned] Hsum] Hone]]].
        apply nth_In_inf.
        rewrite Hlenul.
        rewrite <- Hlen.
        apply H'. }
      specialize (Hlimul i).
      assert (i < length G)%nat as Hi.
      { destruct (Hlp 0%nat) as [L [Hlen [[[H' Hborned] Hsum] Hone]]].
        rewrite <- Hlen.
        apply H'. }
      specialize (Hlimul Hi).
      apply is_lim_seq_ext with _ (fun _ : nat => 1) _ in Hlimul.
      2:{ intros n.
          destruct Hsubseq as [phi Hsubseq].
          destruct Hsubseq as [Hsup Heqn].
          rewrite Heqn.
          destruct (Hlp (phi n)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]].
          simpl. 
          apply H'. }
      apply is_lim_seq_unique with (fun _ : nat => 1).
      * intros x y H.
        apply Req_lt_aux.
        intros eps.
        specialize (H eps).
        apply ball_sym in H.
        apply H.
      * apply Hlimul.
      * apply is_lim_seq_const. 
    + apply forall_Forall_inf.
      intros r Hin.
      apply (In_inf_nth _ _ 0) in Hin as [j Hltj Heq].
      symmetry in Heq; subst.
      split.
      * apply is_lim_seq_lb with (fun i0 : nat => nth j (v i0) 0).
        -- apply Hlimul.
           lia.
        -- intros n.
           destruct Hsubseq as [phi [Hsub Heqn]].
           rewrite Heqn.
           destruct (Hlp (phi n)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]].
           simpl.
           apply Forall_inf_forall with _ _ _ (nth j L 0) in Hborned.
           2:{ apply nth_In_inf.
               lia. }
           destruct Hborned; lra.
      * apply is_lim_seq_ub with (fun i0 : nat => nth j (v i0) 0).
        -- apply Hlimul.
           lia.
        -- intros n.
           destruct Hsubseq as [phi [Hsub Heqn]].
           rewrite Heqn.
           destruct (Hlp (phi n)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]].
           simpl.
           apply Forall_inf_forall with _ _ _ (nth j L 0) in Hborned.
           2:{ apply nth_In_inf.
               lia. }
           destruct Hborned; lra.
    + intros n.
      destruct Hsubseq as [phi [Hsubseq Heqn]].
      apply (@is_lim_seq_unique R_UniformSpace) with (fun i => eval_Poly (val_add_vec (un (phi i)) (S (max_var_weight_p_hseq G)) (projT1 (Hlp (phi i)))) (p_sum_weight_var n (mul_p_hseq_new_var G))).
      * intros x y Heps.
        symmetry; apply Req_lt_aux.
        apply Heps.
      * apply Poly_lim.
        unfold val_add_vec.
        apply is_lim_seq_ext with (fun n0 => upd_val_vec (un (phi n0)) (seq (S (max_var_weight_p_hseq G)) (length Hul)) (projT1 (Hlp (phi n0)))).
        { intros i0.
          destruct (Hlp (phi i0)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]]; simpl in *.
          replace (length Hul) with (length L) by lia; reflexivity. }
        apply upd_val_vec_lim with (length Hul).
        -- intros i0.
           destruct (Hlp (phi i0)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]]; simpl; lia.
        -- rewrite seq_length; reflexivity.
        -- reflexivity.
        -- apply is_lim_seq_subseq with un; try assumption.
           split with phi.
           split; auto.
        -- rewrite Hlenul.
           intros i0 Hlen.
           eapply is_lim_seq_ext; [ | apply Hlimul; try assumption].
           intros n0; simpl; rewrite Heqn; reflexivity.
      * apply is_lim_seq_ext with (fun _ => 0).
        -- intros i0; symmetry.
           destruct (Hlp (phi i0)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]]; simpl.
           apply Hsum.
        -- apply is_lim_seq_const.
    + destruct Hsubseq as [phi [Hsubseq Heqn]].
      apply is_lim_seq_lb with (fun i => eval_Poly (val_add_vec (un (phi i)) (S (max_var_weight_p_hseq G)) (projT1 (Hlp (phi i)))) (p_sum_weight_one (mul_p_hseq_new_var G))).
      * apply Poly_lim.
        unfold val_add_vec.
        apply is_lim_seq_ext with (fun n0 => upd_val_vec (un (phi n0)) (seq (S (max_var_weight_p_hseq G)) (length Hul)) (projT1 (Hlp (phi n0)))).
        { intros i0.
          destruct (Hlp (phi i0)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]]; simpl in *.
          replace (length Hul) with (length L) by lia; reflexivity. }
        apply upd_val_vec_lim with (length Hul).
        -- intros i0.
           destruct (Hlp (phi i0)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]]; simpl; lia.
        -- rewrite seq_length; reflexivity.
        -- reflexivity.
        -- apply is_lim_seq_subseq with un; try assumption.
           split with phi; split; auto.
        -- rewrite Hlenul.
           intros i0 Hlen.
           eapply is_lim_seq_ext; [ | apply Hlimul; try assumption].
           intros n0; simpl; rewrite Heqn; reflexivity.
      * intros i0.
        destruct (Hlp (phi i0)) as [L [Hlen [[[H' Hborned] Hsum] Hone]]]; simpl.
        apply Hone.
Qed.        

(** Lemma ??? - application of the previous lemma *)
Lemma HMR_atomic_lim : forall G (val_n : nat -> val_UniformSpace) (val_l : val_UniformSpace),
    p_hseq_is_basic G ->
    max_diamond_p_hseq G = 0%nat ->
    is_lim_seq val_n val_l ->
    (forall n, HMR_T_M (map (eval_p_sequent (val_n n)) G)) ->
    HMR_T_M (map (eval_p_sequent val_l) G).
Proof.
  intros.
  apply lambda_prop_atomic_inv.
  - apply p_hseq_basic_hseq_basic; apply X.
  - assert (H' := max_diamond_eval_p_hseq val_l G).
    lia.
  - apply def_lambda_prop_atomic_one_implies_reg.
    apply def_lambda_prop_atomic_one_p_implies_reg.
    apply (p_lambda_prop_atomic_one_lim G val_n); try assumption.
    intros n.
    specialize (X0 n).
    apply def_lambda_prop_atomic_one_reg_implies_p.
    apply def_lambda_prop_atomic_reg_implies_one.
    apply lambda_prop_atomic.
    + apply p_hseq_basic_hseq_basic; apply X.
    + assert (H' := max_diamond_eval_p_hseq (val_n n) G).
      lia.
    + apply X0.
Qed.

(** Lemma ???? *)
Lemma HMR_no_diamond_lim : forall G (val_n : nat -> val_UniformSpace) (val_l : val_UniformSpace),
    (forall n, p_hseq_well_defined (val_n n) G) ->
    max_diamond_p_hseq G = 0%nat ->
    is_lim_seq val_n val_l ->
    (forall n, HMR_T_M (map (eval_p_sequent (val_n n)) G)) ->
    HMR_T_M (map (eval_p_sequent val_l) G).
Proof.
  intros G; remember (HMR_complexity_p_hseq G).
  revert G Heqp.
  apply (lt_nat2_wf_rect p); clear p.
  intros n Hinn G Heqn val_n val_l Hwd_n Hnd Hlim Hpi_n.
  destruct n as [a b].
  destruct a.
  - apply HMR_atomic_lim with val_n; try assumption.
    apply p_hseq_is_basic_complexity_0_inv.
    rewrite <- Heqn; reflexivity.
  - remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G)).
    destruct s.
    + specialize (Hinn (HMR_complexity_p_hseq p)).
      apply p_hseq_put_non_basic_fst_HMR.
      { intros H.
        apply p_hseq_is_basic_complexity_0 in H.
        rewrite <- Heqn in H.
        inversion H. }
      apply apply_logical_rule_on_p_hypersequent_inl_HMR_inv with p.
      * rewrite Heqs; reflexivity.
      * apply p_hseq_put_non_basic_fst_well_defined.
        { rewrite <- Heqn.
          simpl; lia. }
        apply p_hseq_well_defined_lim with val_n; try assumption.
      * apply Hinn with val_n.
        -- rewrite Heqn.
           symmetry in Heqs.
           assert (modal_complexity_p_hseq p <3 modal_complexity_p_hseq G).
           { apply apply_logical_rule_on_p_hypersequent_correct_inl with a; try assumption.
             simpl.
             rewrite <- Heqn; reflexivity. }
           unfold modal_complexity_p_hseq in H.
           inversion H; subst.
           ++ rewrite Hnd in H1; inversion H1.
           ++ rewrite surjective_pairing.
              rewrite (surjective_pairing (HMR_complexity_p_hseq p)).
              apply fst_lt2; assumption.
           ++ rewrite surjective_pairing.
              rewrite (surjective_pairing (HMR_complexity_p_hseq p)).
              rewrite H5.
              apply snd_lt2; assumption.
        -- reflexivity.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inl_well_defined with (p_hseq_put_non_basic_fst G); [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_basic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
           apply Hwd_n.
        -- assert (modal_complexity_p_hseq p <3 modal_complexity_p_hseq G).
           { apply apply_logical_rule_on_p_hypersequent_correct_inl with a; [ | rewrite Heqs; reflexivity ].
             simpl.
             rewrite <- Heqn; reflexivity. }
           unfold modal_complexity_p_hseq in H.
           inversion H; subst; lia.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inl_HMR with (p_hseq_put_non_basic_fst G); try assumption.
           ++ apply p_hseq_put_non_basic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
              apply Hwd_n.
           ++ apply p_hseq_put_non_basic_fst_HMR_inv.
              { intros H; apply p_hseq_is_basic_complexity_0 in H.
                rewrite <- Heqn in H; inversion H. }
              apply Hpi_n.
    + destruct p as [G1 G2].
      apply p_hseq_put_non_basic_fst_HMR.
      { intros H.
        apply p_hseq_is_basic_complexity_0 in H.
        rewrite <- Heqn in H.
        inversion H. }
      apply apply_logical_rule_on_p_hypersequent_inr_HMR_inv with G1 G2.
      * rewrite Heqs; reflexivity.
      * apply p_hseq_put_non_basic_fst_well_defined.
        { rewrite <- Heqn.
          simpl; lia. }
        apply p_hseq_well_defined_lim with val_n; try assumption.
      * apply Hinn with (HMR_complexity_p_hseq G1) val_n.
        -- rewrite Heqn.
           symmetry in Heqs.
           assert (modal_complexity_p_hseq G1 <3 modal_complexity_p_hseq G).
           { apply apply_logical_rule_on_p_hypersequent_correct_inr_l with G2 a; try assumption.
             simpl.
             rewrite <- Heqn; reflexivity. }
           unfold modal_complexity_p_hseq in H.
           inversion H; subst.
           ++ rewrite Hnd in H1; inversion H1.
           ++ rewrite surjective_pairing.
              rewrite (surjective_pairing (HMR_complexity_p_hseq G1)).
              apply fst_lt2; assumption.
           ++ rewrite surjective_pairing.
              rewrite (surjective_pairing (HMR_complexity_p_hseq G1)).
              rewrite H5.
              apply snd_lt2; assumption.
        -- reflexivity.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inr_l_well_defined with (p_hseq_put_non_basic_fst G) G2; [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_basic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
           apply Hwd_n.
        -- assert (modal_complexity_p_hseq G1 <3 modal_complexity_p_hseq G).
           { apply apply_logical_rule_on_p_hypersequent_correct_inr_l with G2 a; [ | rewrite Heqs; reflexivity ].
             simpl.
             rewrite <- Heqn; reflexivity. }
           unfold modal_complexity_p_hseq in H.
           inversion H; subst; lia.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inr_l_HMR with (p_hseq_put_non_basic_fst G) G2; try assumption.
           ++ apply p_hseq_put_non_basic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
              apply Hwd_n.
           ++ apply p_hseq_put_non_basic_fst_HMR_inv.
              { intros H; apply p_hseq_is_basic_complexity_0 in H.
                rewrite <- Heqn in H; inversion H. }
              apply Hpi_n.
      * apply Hinn with (HMR_complexity_p_hseq G2) val_n.
        -- rewrite Heqn.
           symmetry in Heqs.
           assert (modal_complexity_p_hseq G2 <3 modal_complexity_p_hseq G).
           { apply apply_logical_rule_on_p_hypersequent_correct_inr_r with G1 a; try assumption.
             simpl.
             rewrite <- Heqn; reflexivity. }
           unfold modal_complexity_p_hseq in H.
           inversion H; subst.
           ++ rewrite Hnd in H1; inversion H1.
           ++ rewrite surjective_pairing.
              rewrite (surjective_pairing (HMR_complexity_p_hseq G2)).
              apply fst_lt2; assumption.
           ++ rewrite surjective_pairing.
              rewrite (surjective_pairing (HMR_complexity_p_hseq G2)).
              rewrite H5.
              apply snd_lt2; assumption.
        -- reflexivity.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inr_r_well_defined with (p_hseq_put_non_basic_fst G) G1; [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_basic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
           apply Hwd_n.
        -- assert (modal_complexity_p_hseq G2 <3 modal_complexity_p_hseq G).
           { apply apply_logical_rule_on_p_hypersequent_correct_inr_r with G1 a; [ | rewrite Heqs; reflexivity ].
             simpl.
             rewrite <- Heqn; reflexivity. }
           unfold modal_complexity_p_hseq in H.
           inversion H; subst; lia.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inr_r_HMR with (p_hseq_put_non_basic_fst G) G1; try assumption.
           ++ apply p_hseq_put_non_basic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
              apply Hwd_n.
           ++ apply p_hseq_put_non_basic_fst_HMR_inv.
              { intros H; apply p_hseq_is_basic_complexity_0 in H.
                rewrite <- Heqn in H; inversion H. }
              apply Hpi_n.
Qed.

(** Instance of the previous lemma for the Archimedean property *)
Lemma HMR_no_diamond_archimedean : forall A B,
    max_diamond_term A = 0%nat ->
    max_diamond_term B = 0%nat ->
    (forall n, HMR_T_M (((inv_pos (INRpos n), B) :: (One, -S A) :: nil) :: nil)) ->
    HMR_T_M (((One, -S A) :: nil) :: nil).
Proof.
  intros A B HndA HndB Hpi_n.
  replace (((One, -S A) :: nil) :: nil) with
      (map (eval_p_sequent (fun (_ : nat) => 0)) (((Poly_var 0%nat, B) :: (Poly_cst 1, -S A) :: nil) :: nil)).
  2:{ simpl.
      case (R_order_dec 0); intros H0; try (exfalso; apply R_blt_lt in H0; lra).
      case (R_order_dec 1); intros H1; try (exfalso; try apply R_blt_lt in H1; lra).
      repeat f_equal.
      apply Rpos_eq; reflexivity. }
  apply HMR_no_diamond_lim with (fun n => (fun (_ : nat) => /INR (S n))).
  - intros n.
    apply Forall_inf_cons; [ | apply Forall_inf_nil].
    apply Forall_inf_cons; [ | apply Forall_inf_cons; [ | apply Forall_inf_nil ]].
    + simpl.
      change (match n with
              | 0%nat => 1
              | S _ => INR n + 1
              end) with (INR (S n)).
      apply Rlt_le.
      apply Rinv_0_lt_compat.
      apply INR_S_n_pos.
    + simpl; lra.
  - simpl.
    rewrite <- max_diamond_minus; lia.
  - apply lim_def_fun_eps.
    intros eps.
    destruct (archimed_cor1 eps) as [N [Heps HN]].
    { destruct eps; assumption. }
    split with N.
    intros n Hle _.
    rewrite Rminus_0_r.
    rewrite Rabs_pos_eq.
    2:{ apply Rlt_le.
        apply Rinv_0_lt_compat.
        apply INR_S_n_pos. }
    apply Rlt_trans with (/ INR N); try assumption.
    apply Rinv_lt_contravar.
    + rewrite <- mult_INR.
      apply lt_0_INR.
      nia.
    + apply lt_INR.
      lia.
  - intros n.
    replace ((map (eval_p_sequent (fun _ : nat => / INR (S n)))
                  (((Poly_var 0, B) :: (Poly_cst 1, -S A) :: nil) :: nil)))
      with (((inv_pos (INRpos n), B) :: (One, -S A) :: nil) :: nil).
    2:{ simpl.
        change (match n with
                | 0%nat => 1
                | S _ => INR n + 1
                end) with (INR (S n)).
        assert (0 < / INR (S n)).
        { apply Rinv_0_lt_compat; apply INR_S_n_pos. }
        case (R_order_dec (/ INR (S n))); intros Hsn; try (exfalso; try apply R_blt_lt in Hsn; lra).
        case (R_order_dec 1); intros H1; try (exfalso; try apply R_blt_lt in H1; lra).
        do 3 f_equal; [ | f_equal]; now apply Rpos_eq. }
    apply Hpi_n.
Qed.

(** * Modal case *)
(** Definition of the lambda property with fixed i such that t_i = 1 *)
Definition p_def_lambda_prop_one_fixed i G val := 
  { L &
    prod (length L = length G)
         ((i < length L)%nat *
          (nth i L 0 = 1) *
          (Forall_inf (fun x => prod (0 <= x) (x <= 1)) L) *
          (forall n, eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_var n (mul_p_hseq_new_var G)) = 0) *
          (0 <= eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_one (mul_p_hseq_new_var G))) *
          (HMR_T_M ( concat (map (eval_p_sequent (val_add_vec val (S (max_var_weight_p_hseq G)) L)) (only_diamond_p_hseq (mul_p_hseq_new_var G))) :: nil)))}.

(** Proof that if a parametrized hypersequent satisfies the lambda property for a sequence of valuations, then there is subsequence that satisfies the lambda property, and where t_i = 1 for each insance of the lambda property for the valuations *)
Lemma p_lambda_prop_one_seq_fixed: forall G (un : nat -> val_UniformSpace),
    (forall n, p_def_lambda_prop_one G (un n)) ->
    {' (v , i) : _ & prod (is_subseq v un)
                            (forall n, p_def_lambda_prop_one_fixed i G (v n))}.
Proof.
  intros G un H.
  destruct (IPP_eq_1 (fun n i => (nth i (projT1 (H n)) 0)) (length G)) as [[v i] [Hsubseq [Him Hipp]]].
  { intros n.
    remember (H n).
    destruct p as [L [Hlen [[[[Hex Hall] Hsum] Hone] Hstep]]].
    destruct (Exists_inf_nth Hex) as [[i r] Hlen' HP].
    split with i.
    split.
    - clear - Hlen Hlen'; rewrite <- Hlen.
      lia.
    - simpl.
      rewrite nth_indep with _ _ _ _ 0 in HP; try lia.
      rewrite HP; simpl; reflexivity. }
  destruct Hsubseq as [phi [Hsubseq Heqn]].
  split with (fun n => un (phi n), i).
  split.
  { split with phi.
    repeat split; auto. }
  intros n.
  specialize (Hipp n).
  remember (H (phi n)).
  rewrite Heqn in Hipp; rewrite <- Heqp in Hipp.
  destruct p as [L [Hlen [[[[Hex Hall] Hsum] Hone] Hstep]]].
  split with L; repeat split; try assumption.
  rewrite Hlen.
  apply Him.
Qed.

(** Lemma ??? *)
Lemma p_lambda_prop_one_lim : forall G (un : nat -> val_UniformSpace) (ul : val_UniformSpace) (acc : Acc lt_nat4 (modal_complexity_p_hseq G , 0%nat)) i,
    (forall n, p_hseq_well_defined (un n) G) ->
    is_lim_seq un ul ->
    (forall n, p_def_lambda_prop_one_fixed i G (un n)) ->
    p_def_lambda_prop_one G ul
with HMR_lim : forall G (val_n : nat -> val_UniformSpace) (val_l : val_UniformSpace) (acc : Acc lt_nat4 (modal_complexity_p_hseq G , 1%nat)),
    (forall n, p_hseq_well_defined (val_n n) G) ->
    is_lim_seq val_n val_l ->
    (forall n, HMR_T_M (map (eval_p_sequent (val_n n)) G)) ->
    HMR_T_M (map (eval_p_sequent val_l) G).
Proof.
  (* p_lambda_prop_one_lim *)
  intros G un ul acc i Hwd Hlim Hlp.
  destruct acc as [acc].
  remember (max_diamond_p_hseq G) as nb_diam.
  destruct nb_diam.
  { destruct (p_lambda_prop_atomic_one_lim G un ul Hlim) as [L [Hlen [[[H' Hborned] Hsum] Hone]]].
    - intros n.
      destruct (Hlp n) as [L [Hlen [[[[[Hlti Heqi] Hall] Hborned] Hsum] Hone]]].
      + split with L; repeat split; try assumption.
        apply nth_Exists_inf with i 0; try assumption.
      + split with L.
        repeat split; try assumption.
        replace L with (map oRpos_to_R (map R_to_oRpos L)).
        2:{ clear - Hborned.
            induction L; simpl; try reflexivity.
            inversion Hborned; subst.
            destruct H0 as [H0 _].
            specialize (IHL X).
            rewrite IHL; f_equal.
            unfold R_to_oRpos.
            case (R_order_dec a); intros e; subst; try reflexivity;
              exfalso; apply R_blt_lt in e; nra. }
        rewrite concat_with_coeff_mul_p_hseq_new_var_only_diamond.
        2:{ rewrite map_length; lia. }
        destruct (concat_with_coeff_mul_only_diamond_no_diamond (map (eval_p_sequent ul) G) (map R_to_oRpos L)) as [[r s] [Hperm Heqrs]].
        { assert (H'' :=max_diamond_eval_p_hseq ul G).
          lia. }
        eapply hmrr_ex_seq; [ symmetry; apply Hperm | ].
        rewrite <- (app_nil_r (hseq.vec r HMR_one)).
        apply hmrr_one; [ | apply hmrr_INIT].
        rewrite <- sum_weight_one_mul_p_hseq_new_var in Hone; try nra; try lia.
        apply Forall_inf_arrow with (fun x => prod (0 <= x) (x <= 1)); try assumption.
        intros a [H _]; apply H. }
  destruct (seq_compact_Rn (length G) 0 1 (fun n => (projT1 (Hlp n)))) as [[v Hul] Hcs].
  - intros k.
    destruct (Hlp k) as [L [Hlen H']]; simpl.
    apply Hlen.
  - intros k j Hlt.
    destruct (Hlp k) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]].
    simpl.
    apply Forall_inf_forall with _ _ _ (nth j L 0) in Hborned.
    2:{ apply nth_In_inf.
        rewrite Hlen.
        apply Hlt. }
    apply Hborned.
  - destruct Hcs as [Hsubseq [Hlenul Hlimul]].
    destruct Hsubseq as [phi [Hsubseq Heqn]].
    split with Hul.
    repeat split.
    + apply Hlenul.
    + apply exists_Exists_inf with (nth i Hul 0).
      { destruct (Hlp 0%nat) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]].
        apply nth_In_inf.
        rewrite Hlenul.
        rewrite <- Hlen.
        apply H'. }
      specialize (Hlimul i).
      assert (i < length G)%nat as Hi.
      { destruct (Hlp 0%nat) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]].
        rewrite <- Hlen.
        apply H'. }
      specialize (Hlimul Hi).
      apply is_lim_seq_ext with _ (fun _ : nat => 1) _ in Hlimul.
      2:{ intros n.
          rewrite Heqn.
          destruct (Hlp (phi n)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]].
          simpl.
          apply H'. }
      apply is_lim_seq_unique with (fun _ : nat => 1).
      * intros x y H'.
        apply Req_lt_aux.
        intros eps.
        specialize (H' eps).
        apply ball_sym in H'.
        apply H'.
      * apply Hlimul.
      * apply is_lim_seq_const. 
    + apply forall_Forall_inf.
      intros r Hin.
      apply (In_inf_nth _ _ 0) in Hin as [j Hltj Heq].
      symmetry in Heq; subst.
      split.
      * apply is_lim_seq_lb with (fun i0 : nat => nth j (v i0) 0).
        -- apply Hlimul.
           lia.
        -- intros n.
           rewrite Heqn.
           destruct (Hlp (phi n)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]].
           simpl.
           apply Forall_inf_forall with _ _ _ (nth j L 0) in Hborned.
           2:{ apply nth_In_inf.
               lia. }
           destruct Hborned; lra.
      * apply is_lim_seq_ub with (fun i0 : nat => nth j (v i0) 0).
        -- apply Hlimul.
           lia.
        -- intros n.
           rewrite Heqn.
           destruct (Hlp (phi n)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]].
           simpl.
           apply Forall_inf_forall with _ _ _ (nth j L 0) in Hborned.
           2:{ apply nth_In_inf.
               lia. }
           destruct Hborned; lra.
    + intros n.
      apply (@is_lim_seq_unique R_UniformSpace) with (fun i => eval_Poly (val_add_vec (un (phi i)) (S (max_var_weight_p_hseq G)) (projT1 (Hlp (phi i)))) (p_sum_weight_var n (mul_p_hseq_new_var G))).
      * intros x y Heps.
        symmetry; apply Req_lt_aux.
        apply Heps.
      * apply Poly_lim.
        unfold val_add_vec.
        apply is_lim_seq_ext with (fun n0 => upd_val_vec (un (phi n0)) (seq (S (max_var_weight_p_hseq G)) (length Hul)) (projT1 (Hlp (phi n0)))).
        { intros i0.
          destruct (Hlp (phi i0)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl in *.
          replace (length Hul) with (length L) by lia; reflexivity. }
        apply upd_val_vec_lim with (length Hul).
        -- intros i0.
           destruct (Hlp (phi i0)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl; lia.
        -- rewrite seq_length; reflexivity.
        -- reflexivity.
        -- apply is_lim_seq_subseq with un; try assumption.
           split with phi.
           split; auto.
        -- rewrite Hlenul.
           intros i0 Hlen.
           eapply is_lim_seq_ext; [ | apply Hlimul; try assumption].
           intros n0; simpl; rewrite Heqn; reflexivity.
      * apply is_lim_seq_ext with (fun _ => 0).
        -- intros i0; symmetry.
           destruct (Hlp (phi i0)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl.
           apply Hsum.
        -- apply is_lim_seq_const.
    + apply is_lim_seq_lb with (fun i => eval_Poly (val_add_vec (un (phi i)) (S (max_var_weight_p_hseq G)) (projT1 (Hlp (phi i)))) (p_sum_weight_one (mul_p_hseq_new_var G))).
      * apply Poly_lim.
        unfold val_add_vec.
        apply is_lim_seq_ext with (fun n0 => upd_val_vec (un (phi n0)) (seq (S (max_var_weight_p_hseq G)) (length Hul)) (projT1 (Hlp (phi n0)))).
        { intros i0.
          destruct (Hlp (phi i0)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl in *.
          replace (length Hul) with (length L) by lia; reflexivity. }
        apply upd_val_vec_lim with (length Hul).
        -- intros i0.
           destruct (Hlp (phi i0)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl; lia.
        -- rewrite seq_length; reflexivity.
        -- reflexivity.
        -- apply is_lim_seq_subseq with un; try assumption.
           split with phi; split; auto.
        -- rewrite Hlenul.
           intros i0 Hlen.
           eapply is_lim_seq_ext; [ | apply Hlimul; try assumption].
           intros n0; simpl; rewrite Heqn; reflexivity.
      * intros i0.
        destruct (Hlp (phi i0)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl.
        apply Hone.
    + rewrite concat_eval_p_sequent.
      specialize (HMR_lim (concat (only_diamond_p_hseq (mul_p_hseq_new_var G)) :: nil)).
      apply HMR_lim with (fun n => val_add_vec (un (phi n)) (S (max_var_weight_p_hseq G)) (projT1 (Hlp (phi n)))).
      * apply acc.
        apply fst_lt4; simpl.
        rewrite Nat.max_0_r.
        rewrite <- Heqnb_diam.
        apply max_diamond_p_seq_concat.
        rewrite Heqnb_diam.
        rewrite max_diamond_p_hseq_mul_new_var.
        apply Forall_inf_max_diamond_only_diamond_p_hseq.
        rewrite <- max_diamond_p_hseq_mul_new_var.
        lia.
      * intros n.
        apply Forall_inf_cons; [ | apply Forall_inf_nil].
        apply well_defined_concat.
        apply well_defined_only_diamond_p_hseq.
        destruct (Hlp (phi n)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl.
        apply well_defined_mul_new_var; try lia.
        -- apply Hwd.
        -- apply Forall_inf_arrow with (fun x => prod (0 <= x) (x <= 1)); try assumption.
           intros a [Ha _]; apply Ha.
      * unfold val_add_vec.
        apply is_lim_seq_ext with (fun n0 => upd_val_vec (un (phi n0)) (seq (S (max_var_weight_p_hseq G)) (length Hul)) (projT1 (Hlp (phi n0)))).
        { intros i0.
          destruct (Hlp (phi i0)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl in *.
          replace (length Hul) with (length L) by lia; reflexivity. }
        apply upd_val_vec_lim with (length Hul).
        -- intros i0.
           destruct (Hlp (phi i0)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl; lia.
        -- rewrite seq_length; reflexivity.
        -- reflexivity.
        -- apply is_lim_seq_subseq with un; try assumption.
           split with phi; split; auto.
        -- rewrite Hlenul.
           intros i0 Hlen.
           eapply is_lim_seq_ext; [ | apply Hlimul; try assumption].
           intros n0; simpl; rewrite Heqn; reflexivity.
      * intros n.
        destruct (Hlp (phi n)) as [L [Hlen [[[[H' Hborned] Hsum] Hone] Hstep]]]; simpl in *.
        rewrite concat_eval_p_sequent in Hstep.
        apply Hstep.
(* HMR_lim *)
  intros G; remember (modal_complexity_p_hseq G).
  intros val_n val_l acc Hwd_n Hlim Hpi_n.
  destruct acc as [acc].
  destruct p as [[a b] c].
  destruct a.
  { apply HMR_no_diamond_lim with val_n; try assumption.
    unfold modal_complexity_p_hseq in Heqp.
    inversion Heqp; lia. }
  destruct b.
  - apply lambda_prop_inv.
    { apply p_hseq_basic_hseq_basic.
      unfold modal_complexity_p_hseq in Heqp.
      inversion Heqp.
      apply p_hseq_is_basic_complexity_0_inv; lia. }
    apply def_lambda_prop_one_implies_reg.
    apply def_lambda_prop_one_p_implies_reg.
    destruct (p_lambda_prop_one_seq_fixed G val_n) as [[v i] [Hsubseq H]].
    { intros n.
      apply def_lambda_prop_one_reg_implies_p.
      apply def_lambda_prop_reg_implies_one.
      apply lambda_prop.
      { apply p_hseq_basic_hseq_basic.
        unfold modal_complexity_p_hseq in Heqp.
        inversion Heqp.
        apply p_hseq_is_basic_complexity_0_inv; lia. }
      apply Hpi_n. }
    destruct Hsubseq as [phi [Hsubseq Heqn]].
    refine (p_lambda_prop_one_lim G (fun n => val_n (phi n)) val_l _ i _ _ _).
    + apply acc.
      rewrite Heqp.
      apply lt_nat4_last.
      lia.
    + intros n; apply Hwd_n.
    + apply is_lim_seq_subseq with val_n; try assumption.
      split with phi; split; auto.
    + intros n; specialize (H n); rewrite Heqn in H; apply H.
  - remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G)).
    destruct s.
    + apply p_hseq_put_non_basic_fst_HMR.
      { intros H.
        apply p_hseq_is_basic_complexity_0 in H.
        unfold modal_complexity_p_hseq in Heqp.
        inversion Heqp.
        lia. }
      apply apply_logical_rule_on_p_hypersequent_inl_HMR_inv with p.
      * rewrite Heqs; reflexivity.
      * apply p_hseq_put_non_basic_fst_well_defined.
        { unfold modal_complexity_p_hseq in Heqp.
          inversion Heqp.
          lia. }
        apply p_hseq_well_defined_lim with val_n; try assumption.
      * apply HMR_lim with val_n.
        -- apply acc.
           apply lt_nat3_to_lt_nat4.
           rewrite Heqp.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_correct_inl with b; try assumption.
           rewrite <- Heqp; reflexivity.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inl_well_defined with (p_hseq_put_non_basic_fst G); [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_basic_fst_well_defined.
           { unfold modal_complexity_p_hseq in Heqp.
             inversion Heqp.
             lia. }
           apply Hwd_n.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inl_HMR with (p_hseq_put_non_basic_fst G); try assumption.
           ++ apply p_hseq_put_non_basic_fst_well_defined.
              { unfold modal_complexity_p_hseq in Heqp.
                inversion Heqp.
                lia. }
              apply Hwd_n.
           ++ apply p_hseq_put_non_basic_fst_HMR_inv.
              { intros H; apply p_hseq_is_basic_complexity_0 in H.
                unfold modal_complexity_p_hseq in Heqp.
                inversion Heqp.
                lia. }
              apply Hpi_n.
    + destruct p as [G1 G2].
      apply p_hseq_put_non_basic_fst_HMR.
      { intros H.
        apply p_hseq_is_basic_complexity_0 in H.
        unfold modal_complexity_p_hseq in Heqp.
        inversion Heqp.
        lia. }
      apply apply_logical_rule_on_p_hypersequent_inr_HMR_inv with G1 G2.
      * rewrite Heqs; reflexivity.
      * apply p_hseq_put_non_basic_fst_well_defined.
        { unfold modal_complexity_p_hseq in Heqp.
          inversion Heqp.
          lia. }
        apply p_hseq_well_defined_lim with val_n; try assumption.
      * apply HMR_lim with val_n.
        -- apply acc.
           apply lt_nat3_to_lt_nat4.
           rewrite Heqp.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_correct_inr_l with G2 b; try assumption.
           simpl.
           unfold modal_complexity_p_hseq in Heqp.
           inversion Heqp.
           lia.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inr_l_well_defined with (p_hseq_put_non_basic_fst G) G2; [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_basic_fst_well_defined.
           { unfold modal_complexity_p_hseq in Heqp.
             inversion Heqp.
             lia. }
           apply Hwd_n.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inr_l_HMR with (p_hseq_put_non_basic_fst G) G2; try assumption.
           ++ apply p_hseq_put_non_basic_fst_well_defined.
              { unfold modal_complexity_p_hseq in Heqp.
                inversion Heqp.
                lia. }
              apply Hwd_n.
           ++ apply p_hseq_put_non_basic_fst_HMR_inv.
              { intros H; apply p_hseq_is_basic_complexity_0 in H.
                unfold modal_complexity_p_hseq in Heqp.
                inversion Heqp.
                lia. }
              apply Hpi_n.
      * apply HMR_lim with val_n.
        -- apply acc.
           apply lt_nat3_to_lt_nat4.
           rewrite Heqp.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_correct_inr_r with G1 b; try assumption.
           simpl.
           unfold modal_complexity_p_hseq in Heqp.
           inversion Heqp.
           lia.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inr_r_well_defined with (p_hseq_put_non_basic_fst G) G1; [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_basic_fst_well_defined.
           { unfold modal_complexity_p_hseq in Heqp.
             inversion Heqp.
             lia. }
           apply Hwd_n.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inr_r_HMR with (p_hseq_put_non_basic_fst G) G1; try assumption.
           ++ apply p_hseq_put_non_basic_fst_well_defined.
              { unfold modal_complexity_p_hseq in Heqp.
                inversion Heqp.
                lia. }
              apply Hwd_n.
           ++ apply p_hseq_put_non_basic_fst_HMR_inv.
              { intros H; apply p_hseq_is_basic_complexity_0 in H.
                unfold modal_complexity_p_hseq in Heqp.
                inversion Heqp.
                lia. }
              apply Hpi_n.
Qed.

(** Instance of the previous lemma for the Archimedean property *)
Lemma HMR_archimedean : forall A B,
    (forall n, HMR_T_M (((inv_pos (INRpos n), B) :: (One, -S A) :: nil) :: nil)) ->
    HMR_T_M (((One, -S A) :: nil) :: nil).
Proof.
  intros A B Hpi_n.
  replace (((One, -S A) :: nil) :: nil) with
      (map (eval_p_sequent (fun (_ : nat) => 0)) (((Poly_var 0%nat, B) :: (Poly_cst 1, -S A) :: nil) :: nil)).
  2:{ simpl.
      case (R_order_dec 0); intros H0; try (exfalso; apply R_blt_lt in H0; lra).
      case (R_order_dec 1); intros H1; try (exfalso; try apply R_blt_lt in H1; lra).
      repeat f_equal.
      apply Rpos_eq; reflexivity. }
  apply HMR_lim with (fun n => (fun (_ : nat) => /INR (S n))).
  - apply wf_lt_nat4.
  - intros n.
    apply Forall_inf_cons; [ | apply Forall_inf_nil].
    apply Forall_inf_cons; [ | apply Forall_inf_cons; [ | apply Forall_inf_nil ]].
    + simpl.
      change (match n with
              | 0%nat => 1
              | S _ => INR n + 1
              end) with (INR (S n)).
      apply Rlt_le.
      apply Rinv_0_lt_compat.
      apply INR_S_n_pos.
    + simpl; lra.
  - apply lim_def_fun_eps.
    intros eps.
    destruct (archimed_cor1 eps) as [N [Heps HN]].
    { destruct eps; assumption. }
    split with N.
    intros n Hle _.
    rewrite Rminus_0_r.
    rewrite Rabs_pos_eq.
    2:{ apply Rlt_le.
        apply Rinv_0_lt_compat.
        apply INR_S_n_pos. }
    apply Rlt_trans with (/ INR N); try assumption.
    apply Rinv_lt_contravar.
    + rewrite <- mult_INR.
      apply lt_0_INR.
      nia.
    + apply lt_INR.
      lia.
  - intros n.
    replace ((map (eval_p_sequent (fun _ : nat => / INR (S n)))
                  (((Poly_var 0, B) :: (Poly_cst 1, -S A) :: nil) :: nil)))
      with (((inv_pos (INRpos n), B) :: (One, -S A) :: nil) :: nil).
    2:{ simpl.
        change (match n with
                | 0%nat => 1
                | S _ => INR n + 1
                end) with (INR (S n)).
        assert (0 < / INR (S n)).
        { apply Rinv_0_lt_compat; apply INR_S_n_pos. }
        case (R_order_dec (/ INR (S n))); intros Hsn; try (exfalso; try apply R_blt_lt in Hsn; lra).
        case (R_order_dec 1); intros H1; try (exfalso; try apply R_blt_lt in H1; lra).
        do 3 f_equal; [ | f_equal]; now apply Rpos_eq. }
    apply Hpi_n.
Qed.

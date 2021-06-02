Require Import Reals.

Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_solve.
Require Import List.

Require Import RL.hr_archimedean.lambda_prop_one.

Require Import RL.hr.term.
Require Import RL.hr.hseq.
Require Import RL.hr.p_hseq.
Require Import RL.hr.apply_logical_rule.
Require Import RL.hr.lambda_prop_tools.
Require Import RL.hr.hr.
Require Import RL.hr.semantic.
Require Import RL.hr.can_elim.
Require Import RL.hr.completeness.
Require Import RL.hr.soundness.

Require Import RL.Utilities.riesz_logic_List_more.
Require Import RL.Utilities.riesz_logic_Nat_more.
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.polynomials.
Require Import RL.Utilities.pol_continuous.
Require Import RL.Utilities.Lim_seq_US.
Require Import RL.Utilities.R_complements.

Require Import Lra.
Require Import Lia.

Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rcomplements.
Local Open Scope R_scope.

(** ** Theorem 6 with the additional information that t_i = 1 . *)
(** Useful when dealing with sequences, to ensure that t_{i,n} = 1 for all elements of the sequence *)
(** In this section, atomic is used in the sense that the only terms are (co)variables and (co)ones *)
Definition p_def_lambda_prop_one_fixed i G val := 
  { L &
    prod (length L = length G)
         ((i < length L)%nat *
          (nth i L 0 = 1) *
          (Forall_inf (fun x => prod (0 <= x) (x <= 1)) L) *
          (forall n, eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_var n (mul_p_hseq_new_var G)) = 0))}.

(** Proof that if a parametrized hypersequent satisfies the lambda property for a sequence of valuations, then there is subsequence that satisfies the lambda property, and where t_i = 1 for each insance of the lambda property for the valuations *)
Lemma p_lambda_prop_one_seq_fixed: forall G (un : nat -> val_UniformSpace),
    (forall n, p_def_lambda_prop_one G (un n)) ->
    {' (phi , i) : _ & prod (subseq_support phi)
                            (forall n, p_def_lambda_prop_one_fixed i G (un (phi n)))}.
Proof.
  intros G un H.
  destruct (IPP_eq_1 (fun n i => (nth i (projT1 (H n)) 0)) (length G)) as [[phi i] [Hsubseq [Him Hipp]]].
  { intros n.
    remember (H n).
    destruct p as [L [Hlen [[Hex Hall] Hsum]]].
    destruct (Exists_inf_nth Hex) as [[i r] Hlen' HP].
    split with i.
    split.
    - clear - Hlen Hlen'; rewrite <- Hlen.
      lia.
    - simpl.
      rewrite nth_indep with _ _ _ _ 0 in HP; try lia.
      rewrite HP; simpl; reflexivity. }
  split with (phi, i).
  split; try assumption.
  intros n.
  specialize (Hipp n).
  remember (H (phi n)).
  destruct p as [L [Hlen [[Hex Hall] Hsum]]].
  split with L; repeat split; try assumption.
  rewrite Hlen.
  apply Him.
Qed.

(** "continuity" of the lambda property - used in the next lemma *)
Lemma p_lambda_prop_one_lim : forall G (un : nat -> val_UniformSpace) (ul : val_UniformSpace),
    is_lim_seq un ul ->
    (forall n, p_def_lambda_prop_one G (un n)) ->
    p_def_lambda_prop_one G ul.
Proof.
  enough (forall G i (un : nat -> val_UniformSpace) (ul : val_UniformSpace),
             is_lim_seq un ul ->
             (forall n, p_def_lambda_prop_one_fixed i G (un n)) ->
             p_def_lambda_prop_one G ul).
  { intros.
    apply p_lambda_prop_one_seq_fixed in X0 as [[phi i] [Hsubseq Hipp]].
    refine (X G i (fun n => un (phi n)) ul _ Hipp).
    apply is_lim_seq_subseq with un; try assumption.
    split with phi; split; auto. }
  intros G i un ul Hlim Hlp.
  destruct (seq_compact_Rn (length G) 0 1 (fun n => (projT1 (Hlp n)))) as [[phi Hul] Hcs].
  - intros k.
    destruct (Hlp k) as [L [Hlen H']]; simpl.
    apply Hlen.
  - intros k j Hlt.
    destruct (Hlp k) as [L [Hlen [[H' Hborned] Hsum]]].
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
      { destruct (Hlp 0%nat) as [L [Hlen [[H' Hborned] Hsum]]].
        apply nth_In_inf.
        rewrite Hlenul.
        rewrite <- Hlen.
        apply H'. }
      specialize (Hlimul i).
      assert (i < length G)%nat as Hi.
      { destruct (Hlp 0%nat) as [L [Hlen [[H' Hborned] Hsum]]].
        rewrite <- Hlen.
        apply H'. }
      specialize (Hlimul Hi).
      apply is_lim_seq_ext with _ (fun _ : nat => 1) _ in Hlimul.
      2:{ intros n.
          destruct (Hlp (phi n)) as [L [Hlen [[H' Hborned] Hsum]]].
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
      * apply is_lim_seq_lb with (fun i0 : nat => nth j (projT1 (Hlp (phi i0))) 0).
        -- apply Hlimul.
           lia.
        -- intros n.
           destruct (Hlp (phi n)) as [L [Hlen [[H' Hborned] Hsum]]].
           simpl.
           apply Forall_inf_forall with _ _ _ (nth j L 0) in Hborned.
           2:{ apply nth_In_inf.
               lia. }
           destruct Hborned; lra.
      * apply is_lim_seq_ub with (fun i0 : nat => nth j (projT1 (Hlp (phi i0))) 0).
        -- apply Hlimul.
           lia.
        -- intros n.
           destruct (Hlp (phi n)) as [L [Hlen [[H' Hborned] Hsum]]].
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
          destruct (Hlp (phi i0)) as [L [Hlen [[H' Hborned] Hsum]]]; simpl in *.
          replace (length Hul) with (length L) by lia; reflexivity. }
        apply upd_val_vec_lim with (length Hul).
        -- intros i0.
           destruct (Hlp (phi i0)) as [L [Hlen [[H' Hborned] Hsum]]]; simpl; lia.
        -- rewrite seq_length; reflexivity.
        -- reflexivity.
        -- apply is_lim_seq_subseq with un; try assumption.
           split with phi.
           split; auto.
        -- rewrite Hlenul.
           intros i0 Hlen.
           eapply is_lim_seq_ext; [ | apply Hlimul; try assumption].
           reflexivity.
      * apply is_lim_seq_ext with (fun _ => 0).
        -- intros i0; symmetry.
           destruct (Hlp (phi i0)) as [L [Hlen [[H' Hborned] Hsum]]]; simpl.
           apply Hsum.
        -- apply is_lim_seq_const.
Qed.        

(** Lemma 4 *)
Lemma HR_atomic_lim : forall G (val_n : nat -> val_UniformSpace) (val_l : val_UniformSpace),
    p_hseq_is_atomic G ->
    is_lim_seq val_n val_l ->
    (forall n, HR_T_M (map (eval_p_sequent (val_n n)) G)) ->
    HR_T_M (map (eval_p_sequent val_l) G).
Proof.
  intros.
  apply lambda_prop_inv.
  - apply p_hseq_atomic_hseq_atomic; apply X.
  - apply def_lambda_prop_one_implies_reg.
    apply def_lambda_prop_one_p_implies_reg.
    apply (p_lambda_prop_one_lim G val_n); try assumption.
    intros n.
    specialize (X0 n).
    apply def_lambda_prop_one_reg_implies_p.
    apply def_lambda_prop_reg_implies_one.
    apply lambda_prop.
    + apply p_hseq_atomic_hseq_atomic; apply X.
    + apply X0.
Qed.

(** Theorem 8 *)
Lemma HR_lim : forall G (val_n : nat -> val_UniformSpace) (val_l : val_UniformSpace),
    (forall n, p_hseq_well_defined (val_n n) G) ->
    is_lim_seq val_n val_l ->
    (forall n, HR_T_M (map (eval_p_sequent (val_n n)) G)) ->
    HR_T_M (map (eval_p_sequent val_l) G).
Proof.
  intros G; remember (HR_outer_complexity_p_hseq G).
  revert G Heqp.
  apply (lt_nat2_wf_rect p); clear p.
  intros n Hinn G Heqn val_n val_l Hwd_n Hlim Hpi_n.
  destruct n as [a b].
  destruct a.
  - apply HR_atomic_lim with val_n; try assumption.
    apply p_hseq_is_atomic_outer_complexity_0_inv.
    rewrite <- Heqn; reflexivity.
  - remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_atomic_fst G)).
    destruct s.
    + specialize (Hinn (HR_outer_complexity_p_hseq p)).
      apply p_hseq_put_non_atomic_fst_HR.
      { intros H.
        apply p_hseq_is_atomic_outer_complexity_0 in H.
        rewrite <- Heqn in H.
        inversion H. }
      apply apply_logical_rule_on_p_hypersequent_inl_HR_inv with p.
      * rewrite Heqs; reflexivity.
      * apply p_hseq_put_non_atomic_fst_well_defined.
        { rewrite <- Heqn.
          simpl; lia. }
        apply p_hseq_well_defined_lim with val_n; try assumption.
      * apply Hinn with val_n.
        -- rewrite Heqn.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_correct_inl with a; try assumption.
           simpl.
           rewrite <- Heqn; reflexivity.
        -- reflexivity.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inl_well_defined with (p_hseq_put_non_atomic_fst G); [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_atomic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
           apply Hwd_n.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inl_HR with (p_hseq_put_non_atomic_fst G); try assumption.
           ++ apply p_hseq_put_non_atomic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
              apply Hwd_n.
           ++ apply p_hseq_put_non_atomic_fst_HR_inv.
              { intros H; apply p_hseq_is_atomic_outer_complexity_0 in H.
                rewrite <- Heqn in H; inversion H. }
              apply Hpi_n.
    + destruct p as [G1 G2].
      apply p_hseq_put_non_atomic_fst_HR.
      { intros H.
        apply p_hseq_is_atomic_outer_complexity_0 in H.
        rewrite <- Heqn in H.
        inversion H. }
      apply apply_logical_rule_on_p_hypersequent_inr_HR_inv with G1 G2.
      * rewrite Heqs; reflexivity.
      * apply p_hseq_put_non_atomic_fst_well_defined.
        { rewrite <- Heqn.
          simpl; lia. }
        apply p_hseq_well_defined_lim with val_n; try assumption.
      * apply Hinn with (HR_outer_complexity_p_hseq G1) val_n.
        -- rewrite Heqn.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_correct_inr_l with G2 a; try assumption.
           simpl.
           rewrite <- Heqn; reflexivity.
        -- reflexivity.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inr_l_well_defined with (p_hseq_put_non_atomic_fst G) G2; [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_atomic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
           apply Hwd_n.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inr_l_HR with (p_hseq_put_non_atomic_fst G) G2; try assumption.
           ++ apply p_hseq_put_non_atomic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
              apply Hwd_n.
           ++ apply p_hseq_put_non_atomic_fst_HR_inv.
              { intros H; apply p_hseq_is_atomic_outer_complexity_0 in H.
                rewrite <- Heqn in H; inversion H. }
              apply Hpi_n.
      * apply Hinn with (HR_outer_complexity_p_hseq G2) val_n.
        -- rewrite Heqn.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_correct_inr_r with G1 a; try assumption.
           simpl.
           rewrite <- Heqn; reflexivity.
        -- reflexivity.
        -- intros n.
           apply apply_logical_rule_on_p_hypersequent_inr_r_well_defined with (p_hseq_put_non_atomic_fst G) G1; [rewrite Heqs; reflexivity | ].
           apply p_hseq_put_non_atomic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
           apply Hwd_n.
        -- apply Hlim.
        -- intros n.
           symmetry in Heqs.
           apply apply_logical_rule_on_p_hypersequent_inr_r_HR with (p_hseq_put_non_atomic_fst G) G1; try assumption.
           ++ apply p_hseq_put_non_atomic_fst_well_defined; [ rewrite <- Heqn; simpl; lia | ].
              apply Hwd_n.
           ++ apply p_hseq_put_non_atomic_fst_HR_inv.
              { intros H; apply p_hseq_is_atomic_outer_complexity_0 in H.
                rewrite <- Heqn in H; inversion H. }
              apply Hpi_n.
Qed.

(** Instance of the previous lemma for the Archimedean property *)
Lemma HR_archimedean : forall A B,
    (forall n, HR_T_M (((inv_pos (INRpos n), B) :: (One, -S A) :: nil) :: nil)) ->
    HR_T_M (((One, -S A) :: nil) :: nil).
Proof.
  intros A B Hpi_n.
  replace (((One, -S A) :: nil) :: nil) with
      (map (eval_p_sequent (fun (_ : nat) => 0)) (((Poly_var 0%nat, B) :: (Poly_cst 1, -S A) :: nil) :: nil)).
  2:{ simpl.
      case (R_order_dec 0); intros H0; try (exfalso; apply R_blt_lt in H0; lra).
      case (R_order_dec 1); intros H1; try (exfalso; try apply R_blt_lt in H1; lra).
      repeat f_equal.
      apply Rpos_eq; reflexivity. }
  apply HR_lim with (fun n => (fun (_ : nat) => /INR (S n))).
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

(** Corollary 1 for free modal Riesz spaces *)
Lemma FreeRS_archimedean : forall A B,
    (forall n, (INRpos n) *S A <== B) ->
    A <== RS_zero.
Proof.
  intros A B H.
  apply leq_cong_l with (-S (-S A)); [auto with MGA_solver | ].
  apply leq_cong_r with (-S RS_zero); [ auto | ].
  apply minus_reverse_leq.
  apply leq_cong_r with (interpretation.sem_hseq (((One, -S A) :: nil) :: nil)).
  { simpl.
    etransitivity ; [ | symmetry; apply neutral_plus].
    symmetry.
    auto. }
  eapply hr_sound.
  apply HR_archimedean with B.
  intros n.
  apply hrr_can_elim.
  eapply HR_le_frag; [ | apply hr_complete].
  - repeat split; auto.
  - intros H'; inversion H'.
  - unfold interpretation.sem_hseq.
    unfold interpretation.sem_seq.
    eapply leq_cong_r; [ apply plus_right; apply neutral_plus | ].
    eapply leq_cong_r; [ apply plus_right; apply mul_minus | ].
    apply leq_minus_right.
    apply leq_cong_l with (One *S A); [ etransitivity; [ apply commu_plus | ]; apply neutral_plus | ].
    replace One with (time_pos (inv_pos (INRpos n)) (INRpos n)).
    2:{ apply Rpos_eq; simpl.
        apply Rinv_l.
        intros H'.
        change (match n with
                | 0%nat => 1
                | S _ => INR n + 1
                end) with (INR (S n)) in H'.
        assert (H'' := INR_S_n_pos n).
        lra. }
    eapply leq_cong_l ; [ symmetry; apply mul_assoc | ].
    apply mul_leq.
    apply H.
Qed.

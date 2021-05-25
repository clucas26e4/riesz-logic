(** * Implementation of Section 4.8 *)
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.polynomials.
Require Import RL.Utilities.riesz_logic_Nat_more.
Require Import riesz_logic_List_more.
Require Import RL.hmr.hmr.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.p_hseq.
Require Import RL.hmr.lambda_prop_tools.
Require Import RL.hmr.invertibility.
Require Import RL.hmr.can_elim.
Require Import RL.hmr.M_elim.
Require Import RL.hmr.tech_lemmas.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import Program.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Import EqNotations.

Local Open Scope R_scope.

(** ** Lambda property *)
Lemma hmrr_fuse :
  forall G T A r1 r2,
    HMR_T_M (((r1, A) :: (r2 , A) :: T) :: G) ->
    HMR_T_M (((plus_pos r1 r2, A) :: T) :: G).
Proof.
  intros G T A r1 r2 pi.
  apply hmrr_can_elim.
  unfold HMR_full.
  change hmr_frag_full with (hmr_frag_add_CAN hmr_frag_full).
  apply hmrr_can_fuse.
  apply HMR_le_frag with hmr_frag_T_M; try assumption.
  repeat split.
Qed.

Lemma hmrr_unfuse :
  forall G T A r1 r2,
    HMR_T_M (((plus_pos r1 r2, A) :: T) :: G) ->
    HMR_T_M (((r1, A) :: (r2 , A) :: T) :: G).
Proof.
  intros G T A r1 r2 pi.
  apply hmrr_can_elim.
  unfold HMR_full.
  change hmr_frag_full with (hmr_frag_add_CAN hmr_frag_full).
  apply hmrr_can_unfuse.
  apply HMR_le_frag with hmr_frag_T_M; try assumption.
  repeat split.
Qed.

Lemma hmrr_unfuse_gen :
  forall G T D r1 r2,
    HMR_T_M ((hseq.seq_mul (plus_pos r1 r2) D ++ T) :: G) ->
    HMR_T_M ((hseq.seq_mul r1 D ++ hseq.seq_mul r2 D ++ T) :: G).
Proof.
  intros G T D r1 r2.
  revert T; induction D; intros T pi; try assumption.
  - destruct a as [a A]; simpl in *.
    apply hmrr_ex_seq with ((time_pos r1 a, A) :: (time_pos r2 a, A) :: hseq.seq_mul r1 D ++ hseq.seq_mul r2 D ++ T); [ Permutation_Type_solve | ].
    apply hmrr_unfuse.
    replace (plus_pos (time_pos r1 a) (time_pos r2 a)) with (time_pos (plus_pos r1 r2) a) by (destruct r1; destruct r2; destruct a; apply Rpos_eq; simpl; nra).
    apply hmrr_ex_seq with (hseq.seq_mul r1 D ++ hseq.seq_mul r2 D ++ (time_pos (plus_pos r1 r2) a, A) :: T) ; [ Permutation_Type_solve | ].
    apply IHD.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
Qed.

Lemma hmrr_fuse_gen :
  forall G T D r1 r2,
    HMR_T_M ((hseq.seq_mul r1 D ++ hseq.seq_mul r2 D ++ T) :: G) ->
    HMR_T_M ((hseq.seq_mul (plus_pos r1 r2) D ++ T) :: G).
Proof.
  intros G T D r1 r2.
  revert T; induction D; intros T pi; try assumption.
  - destruct a as [a A]; simpl in *.
    replace (time_pos (plus_pos r1 r2) a) with (plus_pos (time_pos r1 a) (time_pos r2 a)) by (destruct r1; destruct r2; destruct a; apply Rpos_eq; simpl; nra).
    apply hmrr_fuse.
    apply hmrr_ex_seq with (hseq.seq_mul (plus_pos r1 r2) D ++ (time_pos r1 a, A) :: (time_pos r2 a, A) :: T) ; [ Permutation_Type_solve | ].
    apply IHD.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
Qed.

(* begin hide *)
Lemma concat_with_coeff_mul_oadd_Rpos_list_fuse : forall G T H L1 L2,
    length L1 = length L2 ->
    HMR_T_M ((concat_with_coeff_mul G L1 ++ concat_with_coeff_mul G L2 ++ T) :: H) ->
    HMR_T_M ((concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ T) :: H).
Proof.
  intros G T H L1; revert G T H; induction L1; intros G T H L2 Hlen pi; [ destruct L2; inversion Hlen; destruct G; apply pi | ].
  destruct L2; inversion Hlen.
  destruct G; [ apply pi | ].
  destruct a; destruct o; simpl in *.
  - rewrite<- app_assoc; apply hmrr_fuse_gen.
    apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (hseq.seq_mul r s ++ hseq.seq_mul r0 s ++ T)) ; [ Permutation_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (hseq.seq_mul r s ++ T)) ; [ Permutation_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (hseq.seq_mul r s ++ T)) ; [ Permutation_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    Permutation_Type_solve.
  - apply IHL1; try assumption.
Qed.
(* end hide *)

Lemma lambda_prop :
  forall G,
    hseq_is_basic G ->
    HMR_T_M G ->
    { L &
      prod (length L = length G)
           ((Exists_inf (fun x => x <> None) L) *
            (forall n, sum_weight_var_with_coeff n G L = 0) *
            (0 <= sum_weight_one_with_coeff G L) *
            (HMR_T_M ((concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))}.
Proof.
  intros G Ha pi.
  induction pi.
  - split with ((Some One) :: nil).
    repeat split; try reflexivity.
    + apply Exists_inf_cons_hd.
      intros H; inversion H.
    + intros n.
      simpl; nra.
    + simpl; nra.
    + apply hmrr_INIT.
  - inversion Ha; subst.
    destruct (IHpi X0) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with (None :: L).
    repeat split; auto.
    simpl; rewrite Hlen; reflexivity.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons ;[ | apply Forall_inf_cons]; try assumption. }
    destruct L; [ | destruct L]; try now inversion Hlen.
    split with ((oadd_Rpos o o0) :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_inf_cons_hd.
        destruct o; [ | exfalso; apply H0; reflexivity].
        destruct o0; intros H; inversion H.
      * inversion X1; subst; auto.
        apply Exists_inf_cons_hd.
        destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intro H; inversion H.
    + intros n.
      specialize (Hsum n).
      destruct o; destruct o0; try destruct r; try destruct r0; simpl; simpl in Hsum; nra.
    + destruct o; destruct o0; try destruct r; try destruct r0; simpl; simpl in Hone; nra.
    + destruct o; destruct o0; simpl; simpl in Hind; try assumption.
      apply hmrr_fuse_gen.
      apply Hind.
  - inversion Ha; inversion X0; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons; try assumption.
      apply seq_basic_app; assumption. }
    destruct L; try now inversion Hlen.
    split with (o :: o :: L).
    repeat split; auto.
    + simpl in *; rewrite Hlen; reflexivity.
    + intro n.
      specialize (Hsum n).
      destruct o; auto.
      simpl in *.
      rewrite sum_weight_var_seq_app in Hsum.
      nra.
    + destruct o; auto.
      simpl in *.
      rewrite sum_weight_one_seq_app in Hone.
      nra.
    + destruct o; try assumption.
      simpl in *.
      rewrite only_diamond_seq_app in Hind.
      rewrite hseq.seq_mul_app in Hind.
      rewrite app_assoc; apply Hind.
  - inversion Ha; subst.
    destruct IHpi1 as [L1 [Hlen1 [[[Hex1 Hsum1] Hone1] Hind1]]].
    { apply Forall_inf_cons ; [ apply seq_basic_app_inv_l with T2 | ]; try assumption. }
    destruct L1; try now inversion Hlen1.
    destruct o.
    2:{ split with (None :: L1).
        repeat split; auto. }
    destruct IHpi2 as [L2 [Hlen2 [[[Hex2 Hsum2] Hone2] Hind2]]].
    { apply Forall_inf_cons ; [ apply seq_basic_app_inv_r with T1 | ]; try assumption. }
    destruct L2; try now inversion Hlen2.
    destruct o.
    2:{ split with (None :: L2).
        repeat split; auto. }
    split with ((Some (time_pos r r0)) :: oadd_Rpos_list (map (mul_Rpos_oRpos r0) L1) (map (mul_Rpos_oRpos r) L2)).
    repeat split; auto.
    + simpl in Hlen1, Hlen2; simpl.
      rewrite oadd_Rpos_list_length ; [ rewrite map_length; assumption | ].
      rewrite 2 map_length.
      lia.
    + apply Exists_inf_cons_hd.
      intros H; inversion H.
    + intros n; specialize (Hsum1 n); specialize (Hsum2 n); simpl in Hsum1, Hsum2.
      simpl.
      rewrite sum_weight_var_seq_app.
      rewrite sum_weight_var_with_coeff_oadd_Rpos_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      rewrite 2 sum_weight_var_with_coeff_omul_Rpos_list.
      destruct r; destruct r0; simpl in *; nra.
    + simpl; simpl in Hone1, Hone2.
      rewrite sum_weight_one_seq_app.
      rewrite sum_weight_one_with_coeff_oadd_Rpos_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      rewrite 2 sum_weight_one_with_coeff_omul_Rpos_list.
      destruct r as [r Hr]; destruct r0 as [r0 Hr0]; simpl in *.
      clear - Hr Hr0 Hone1 Hone2.
      apply R_blt_lt in Hr; apply R_blt_lt in Hr0.
      nra.
    + simpl in Hind1, Hind2 |- *.
      rewrite only_diamond_seq_app; rewrite hseq.seq_mul_app.
      rewrite <- (seq_mul_twice (only_diamond_seq T2)).
      replace (time_pos r r0) with (time_pos r0 r) by (destruct r0; destruct r; apply Rpos_eq; simpl; nra).
      rewrite <- seq_mul_twice.
      apply hmrr_ex_seq with ((concat_with_coeff_mul (only_diamond_hseq G) (oadd_Rpos_list (map (mul_Rpos_oRpos r0) L1) (map (mul_Rpos_oRpos r) L2))) ++ (hseq.seq_mul r0 (hseq.seq_mul r (only_diamond_seq T1)) ++ hseq.seq_mul r (hseq.seq_mul r0 (only_diamond_seq T2)))) ; [ Permutation_Type_solve | ].
      apply concat_with_coeff_mul_oadd_Rpos_list_fuse ; [ simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia | ].
      rewrite 2 concat_with_coeff_mul_omul_Rpos_list.
      apply hmrr_ex_seq with (hseq.seq_mul r (hseq.seq_mul r0 (only_diamond_seq T2) ++ (concat_with_coeff_mul (only_diamond_hseq G) L2)) ++ hseq.seq_mul r0 (hseq.seq_mul r (only_diamond_seq T1) ++ (concat_with_coeff_mul (only_diamond_hseq G) L1))) ; [ rewrite ? hseq.seq_mul_app; Permutation_Type_solve | ].
      apply hmrr_M; [ reflexivity | | ];
        eapply hmrr_T; try reflexivity;
          rewrite hseq.seq_mul_twice; rewrite inv_pos_l; rewrite hseq.seq_mul_One; assumption.      
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons; try assumption.
      apply seq_basic_mul; apply X. }
    destruct L; try now inversion Hlen.
    destruct o.
    2:{ split with (None :: L).
        repeat split; auto. }
    split with (Some (time_pos r0 r) :: L).
    repeat split; auto.
    + apply Exists_inf_cons_hd; intros H; inversion H.
    + destruct r; destruct r0; simpl in *; intros n; specialize (Hsum n);rewrite sum_weight_var_seq_mul in Hsum; simpl in *.
      nra.
    + destruct r; destruct r0; simpl in *; rewrite sum_weight_one_seq_mul in Hone.
      simpl in *; nra.
    + simpl in *.
      rewrite<- hseq.seq_mul_twice; rewrite only_diamond_seq_mul.
      apply Hind.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_inf_cons; try assumption.
      eapply seq_basic_app_inv_r; eapply seq_basic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    + intros n0; specialize (Hsum n0).
      destruct L; try now inversion Hlen.
      simpl; rewrite ? sum_weight_seq_app.
      case (term.V_eq n0 n); intros H.
      * subst.
        rewrite ? sum_weight_var_seq_app.
        rewrite sum_weight_var_seq_vec_covar_eq;rewrite sum_weight_var_seq_vec_var_eq.
        simpl in Hsum.
        destruct o; nra.
      * rewrite ? sum_weight_var_seq_app.
        rewrite ? sum_weight_var_seq_vec_neq; try (intros H'; inversion H'; contradiction).
        destruct o; simpl in Hsum; auto.
        nra.
    + destruct L; try now inversion Hlen.
      simpl in *; rewrite ? sum_weight_seq_app.
      simpl in *; rewrite ? sum_weight_one_seq_app.
      destruct o; auto.
      rewrite ? sum_weight_one_seq_vec_neq; try now (intros H; inversion H).
      nra.
    + unfold only_diamond_hseq; fold only_diamond_hseq.
      rewrite 2 only_diamond_seq_app.
      rewrite only_diamond_seq_vec_var; rewrite only_diamond_seq_vec_covar.
      apply Hind.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_inf_cons ; [ | apply Forall_inf_cons ]; assumption. }
    destruct L ; [ | destruct L]; try now inversion Hlen.
    split with (oadd_Rpos o o0 :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_inf_cons_hd.
        destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intros H; inversion H.
      * inversion X; subst; auto.
        apply Exists_inf_cons_hd; 
          destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intros H; inversion H.
    + intros n.
      simpl.
      specialize (Hsum n).
      destruct o; destruct o0; try destruct r; try destruct r0; simpl in *; nra.
    + destruct o; destruct o0; try destruct r; try destruct r0; simpl in *; nra.
    + destruct o; destruct o0; try apply Hind.
      simpl in *.
      apply hmrr_fuse_gen; apply Hind.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi1 Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_inf_cons; try assumption.
      eapply seq_basic_app_inv_r; eapply seq_basic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    + intros n; specialize (Hsum n).
      destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite ? sum_weight_var_seq_app.
      rewrite ? sum_weight_var_seq_vec_neq; try (intros H; now inversion H).
      nra.
    + destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite ? sum_weight_one_seq_app.
      rewrite ? sum_weight_one_seq_vec_one_eq; rewrite ? sum_weight_one_seq_vec_coone_eq.
      apply (Rmult_le_compat_l (projT1 r1)) in r0.
      2:{ destruct r1 as [r1 Hr1]; simpl.
          clear - Hr1; apply R_blt_lt in Hr1.
          nra. }
      nra.
    + destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite 2 only_diamond_seq_app; rewrite 2 hseq.seq_mul_app.
      rewrite only_diamond_seq_vec_one; rewrite only_diamond_seq_vec_coone.
      rewrite 2 hseq.seq_mul_vec_mul_vec.
      rewrite<- ? app_assoc.
      apply hmrr_one; try assumption.
      rewrite 2 hseq.mul_vec_sum_vec.
      clear - r0.
      destruct r1 as [r1 Hr1]; simpl; apply R_blt_lt in Hr1; nra.
  - split with (Some One :: nil).
    repeat split; auto.
    + apply Exists_inf_cons_hd; intros H; inversion H.
    + intros n.
      simpl.
      rewrite ? sum_weight_var_seq_app.
      rewrite ? sum_weight_var_seq_vec_neq; try (intros H; now inversion H).
      rewrite sum_weight_var_seq_seq_diamond; nra.
    + simpl.
      rewrite ? sum_weight_one_seq_app.
      rewrite sum_weight_one_seq_vec_one_eq; rewrite sum_weight_one_seq_vec_coone_eq.
      rewrite sum_weight_one_seq_seq_diamond; nra.
    + simpl.
      rewrite hseq.seq_mul_One.
      rewrite ? only_diamond_seq_app.
      rewrite only_diamond_seq_vec_coone; rewrite only_diamond_seq_vec_one; rewrite only_diamond_seq_only_diamond.
      rewrite app_nil_r; apply pi.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_inf_cons; try assumption.
      apply seq_basic_perm with T2; [ Permutation_Type_solve | apply X]. }
    split with L.
    destruct L; try now inversion Hlen.
    repeat split; auto.
    + intro n; specialize (Hsum n).
      destruct o; simpl in *; auto.
      rewrite <- (sum_weight_var_seq_perm _ _ _ p); apply Hsum.
    + destruct o; simpl in *; auto.
      rewrite <- (sum_weight_one_seq_perm _ _ p); apply Hone.
    + destruct o; simpl in *; auto.
      eapply hmrr_ex_seq; [ | apply Hind].
      apply Permutation_Type_app; try reflexivity.
      apply hseq.seq_mul_perm.
      apply only_diamond_seq_perm.
      apply p.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply hseq_basic_perm with H; try assumption.
      symmetry; apply p. }
    destruct (sum_weight_var_with_coeff_perm_r G H L p Hlen) as [L' [Hperm' [[Hsum' Hone'] Hperm'']]].
    split with L'.
    repeat split.
    + apply Permutation_Type_length in p.
      apply Permutation_Type_length in Hperm'.
      etransitivity ; [ | apply p].
      etransitivity ; [ | apply Hlen].
      symmetry; apply Hperm'.
    + apply Exists_inf_Permutation_Type with L; assumption.
    + intros n.
      rewrite <- (Hsum' n); apply Hsum.
    + rewrite <- Hone'; apply Hone.
    + eapply hmrr_ex_seq ; [ | apply Hind].
      apply Hperm''.
  - inversion f.
Qed.

Lemma lambda_prop_inv :
  forall G,
    hseq_is_basic G ->
    { L &
      prod (length L = length G)
           ((Exists_inf (fun x => x <> None) L) *
            (forall n, sum_weight_var_with_coeff n G L = 0) *
            (0 <= sum_weight_one_with_coeff G L) *
            (HMR_T_M ((concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))} ->
    HMR_T_M G.
Proof.
  enough (forall G H,
             hseq_is_basic G ->
             hseq_is_basic H ->
             { L &
               prod (length L = length G)
                    ((Exists_inf (fun x => x <> None) L) *
                     (forall n, sum_weight_var n H + sum_weight_var_with_coeff n G L = 0) *
                     (0 <= sum_weight_one H + sum_weight_one_with_coeff G L) *
                     (HMR_T_M ((flat_map only_diamond_seq H ++ concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))} + HMR_T_M H ->
             HMR_T_M (H ++  G)).
  { intros G Hat [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    change G with (nil ++ G).
    refine (X G nil Hat _ _).
    - apply Forall_inf_nil.
    - left.
      split with L.
      repeat split; auto.
      + intros n; simpl; specialize (Hsum n); nra.
      + simpl; nra. }
  intros G.
  remember (length G) as n.
  revert G Heqn.
  induction n; intros G Heqn H HatG HatH [[L [Hlen [[[Hex Hsum] Hone] Hind]]] | pi].
  - destruct L; inversion Hlen; inversion Hex.
  - destruct G; inversion Heqn; rewrite app_nil_r; apply pi.
  - destruct (Exists_inf_split _ _ _ Hex) as [[[r La] Lb] [Hp HeqL]].
    assert (Permutation_Type L (r :: La ++ Lb)) as Hperm by (rewrite HeqL ; Permutation_Type_solve).
    destruct (sum_weight_var_with_coeff_perm_l G _ _ Hperm) as [G' [HpermG [[Hsum' Hone'] Hpc]]].
    { lia. }
    destruct G' as [ | T G'].
    { symmetry in HpermG; apply Permutation_Type_nil in HpermG.
      subst; inversion Heqn. }
    apply hmrr_ex_hseq with (T :: H ++ G') ; [ Permutation_Type_solve | ].
    destruct r ; [ | exfalso; apply Hp; reflexivity].
    apply hmrr_T with r; try reflexivity.
    change (hseq.seq_mul r T :: H ++ G')
      with
        ((hseq.seq_mul r T :: H) ++ G').
    assert (hseq_is_basic (T :: G')) as HatG'.
    { apply Forall_inf_Permutation_Type with G; try assumption. }
    apply IHn.
    + apply Permutation_Type_length in HpermG.
      rewrite HpermG in Heqn; simpl in Heqn; inversion Heqn; auto.
    + inversion HatG'; auto.
    + apply Forall_inf_cons; auto.
      apply seq_basic_mul; now inversion HatG'.
    + destruct (Forall_inf_Exists_inf_dec (fun x : option Rpos => x = None)) with (La ++ Lb).
      { intros x.
        destruct x ; [ right; intros H'; inversion H' | left; reflexivity]. }
      * right.
        apply basic_proof_all_eq.
        -- apply seq_basic_mul.
           apply hseq_basic_perm with _ (T :: G') in HatG; try assumption.
           inversion HatG; assumption.
        -- apply HatH.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite (sum_weight_var_with_coeff_all_0 _ (La ++ Lb)) in Hsum'; try assumption.
           rewrite sum_weight_var_seq_mul; simpl.
           nra.
        -- simpl in *.
           rewrite (sum_weight_one_with_coeff_all_0 _ (La ++ Lb)) in Hone'; try assumption.
           rewrite sum_weight_one_seq_mul; simpl.
           nra.
        -- eapply hmrr_ex_seq ; [ | apply Hind].
           rewrite HeqL.
           simpl.
           etransitivity ; [ apply Permutation_Type_app_swap | ].
           apply Permutation_Type_app; [ | reflexivity].
           rewrite concat_with_coeff_mul_only_diamond.
           apply only_diamond_seq_perm.
           rewrite HeqL in Hpc; etransitivity ; [ apply Hpc | ].
           simpl.
           rewrite concat_with_coeff_mul_all_0; try assumption.
           rewrite app_nil_r; reflexivity.
      * left; split with (La ++ Lb).
        repeat split.
        -- rewrite HeqL in Hlen.
           rewrite ? app_length.
           rewrite ? app_length in Hlen; simpl in Hlen.
           lia.
        -- apply e.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite sum_weight_var_seq_mul; simpl.
           nra.
        -- simpl in *.
           rewrite sum_weight_one_seq_mul; simpl.
           nra.
        -- eapply hmrr_ex_seq ; [ | apply Hind].
           rewrite HeqL.
           simpl.
           etransitivity ; [ | apply Permutation_Type_app_swap ].
           etransitivity ; [ apply Permutation_Type_app_swap | ].
           rewrite app_assoc.
           apply Permutation_Type_app; [ | reflexivity].
           rewrite 2 concat_with_coeff_mul_only_diamond.
           rewrite <- only_diamond_seq_app.
           apply only_diamond_seq_perm.
           rewrite HeqL in Hpc; etransitivity ; [ apply Hpc | ].
           simpl.
           apply Permutation_Type_app_swap.
  - eapply hmrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply hmrr_W_gen.
    apply pi.
Qed.

(** ** Decidablity *)
(* begin hide *)
(* Preliminary work necessary for the decidability result *)

(* get a real number x and convert |x| to oRpos *)
Definition R_to_oRpos x :=
  match R_order_dec x with
              | R_is_gt H => Some (existT (fun x => 0 <? x = true) x H)
              | R_is_lt H => Some (existT (fun x => 0 <? x = true) (- x) H)
              | R_is_null _ => None
  end.

Definition eval_to_oRpos val f := R_to_oRpos (eval_Poly val f).

Definition oRpos_to_R (o : option Rpos) :=
  match o with
  | None => 0
  | Some r => projT1 r
  end.

Lemma R_to_oRpos_oRpos_to_R :
  forall o,
    R_to_oRpos (oRpos_to_R o) = o.
Proof.
  destruct o; unfold R_to_oRpos; simpl;
    [ | case (R_order_dec 0); intros e; simpl; try reflexivity; exfalso; apply R_blt_lt in e; lra].
  destruct r as [r Hr]; simpl.
  case (R_order_dec r); intros e;
    try (replace e with Hr by (apply Eqdep_dec.UIP_dec; apply Bool.bool_dec); reflexivity);
    exfalso; apply R_blt_lt in Hr; try apply R_blt_lt in e; lra.
Qed.

Lemma oRpos_to_R_to_Rpos : forall r (Hr : 0 <? projT1 r = true),
    existT _ (oRpos_to_R (Some r)) Hr = r.
Proof.
  intros [r Hr] H.
  apply Rpos_eq; reflexivity.
Qed.

Lemma map_oRpos_to_R_all_pos:
  forall L val i, Forall_inf (fun x => 0 <= eval_Poly (upd_val_vec val (seq i (length L)) (map oRpos_to_R L)) x) (map Poly_var (seq i (length L))).
Proof.
  induction L; intros val i; [ apply Forall_inf_nil | ].
  simpl.
  apply Forall_inf_cons; [ | apply IHL].
  rewrite eval_Poly_upd_val_vec_not_in.
  2:{ apply not_In_inf_seq; lia. }
  rewrite upd_val_eq.
  clear.
  destruct a; simpl; try (destruct r as [r Hr]; simpl; apply R_blt_lt in Hr); lra.
Qed.

Lemma eval_to_oRpos_eq :
  forall val vr k,
    map (eval_to_oRpos (upd_val_vec val (seq k (length vr)) vr)) (map Poly_var (seq k (length vr))) = map R_to_oRpos vr.
Proof.
  intros val vr; revert val; induction vr; intros val k; auto.
  simpl.
  rewrite (IHvr _ (S k)).
  unfold eval_to_oRpos.
  rewrite eval_Poly_upd_val_vec_not_in.
  2:{ apply not_In_inf_seq; lia. }
  unfold upd_val.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Fixpoint p_sum_weight_var_with_coeff n G L :=
  match G, L with
  | _, nil => Poly_cst 0
  | nil, _ => Poly_cst 0
  | T :: G , r :: L => (r *R sum_weight_var_p_seq n T) +R p_sum_weight_var_with_coeff n G L
  end.
(*
Lemma p_sum_weight_var_with_coeff_lt_max_var : forall n G L val,
    (max_var_p_hseq G < n)%nat ->
    eval_Poly val (p_sum_weight_var_with_coeff n G L) = 0.
Proof.
  intros n; induction G; intros L val Hlt; destruct L; auto.
  simpl in *.
  simpl; try rewrite sum_weight_var_p_seq_lt_max_var; try lia;
    rewrite IHG; try lia;
      lra.
Qed. *)

Lemma p_sum_weight_var_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    p_sum_weight_var_with_coeff n (G1 ++ G2) L = p_sum_weight_var_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma p_sum_weight_var_with_coeff_app2 : forall val n G1 G2 L1 L2,
    (length L1 = length G1) ->
    eval_Poly val (p_sum_weight_var_with_coeff n (G1 ++ G2) (L1 ++ L2)) = eval_Poly val (p_sum_weight_var_with_coeff n G1 L1 +R p_sum_weight_var_with_coeff n G2 L2).
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  lra.
Qed.

Lemma p_sum_weight_var_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    p_sum_weight_var_with_coeff n G (L1 ++ L2) = p_sum_weight_var_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint p_sum_weight_one_with_coeff G L :=
  match G, L with
  | _, nil => Poly_cst 0
  | nil, _ => Poly_cst 0
  | T :: G , r :: L => (r *R sum_weight_one_p_seq T) +R p_sum_weight_one_with_coeff G L
  end.

Lemma p_sum_weight_one_with_coeff_app1 : forall G1 G2 L,
    (length L <= length G1)%nat ->
    p_sum_weight_one_with_coeff (G1 ++ G2) L = p_sum_weight_one_with_coeff G1 L.
Proof.
  induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma p_sum_weight_one_with_coeff_app2 : forall val G1 G2 L1 L2,
    (length L1 = length G1) ->
    eval_Poly val (p_sum_weight_one_with_coeff (G1 ++ G2) (L1 ++ L2)) = eval_Poly val (p_sum_weight_one_with_coeff G1 L1 +R p_sum_weight_one_with_coeff G2 L2).
Proof.
  induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  lra.
Qed.

Lemma p_sum_weight_one_with_coeff_app3 : forall G L1 L2,
    (length G <= length L1)%nat ->
    p_sum_weight_one_with_coeff G (L1 ++ L2) = p_sum_weight_one_with_coeff G L1.
Proof.
  induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Lemma eval_to_oRpos_to_R_eq : forall L val i,
    Forall_inf (fun x => 0 <= eval_Poly (upd_val_vec val (seq i (length L)) (map oRpos_to_R L)) x) (map Poly_var (seq i (length L))) ->
    map (eval_to_oRpos (upd_val_vec val (seq i (length L)) (map oRpos_to_R L))) (map Poly_var (seq i (length L))) = L.
Proof.
  induction L; intros val i Hall.
  - reflexivity.
  - inversion Hall; subst.
    simpl.
    rewrite IHL; auto.
    unfold eval_to_oRpos.
    rewrite eval_Poly_upd_val_vec_not_in.
    2:{ apply not_In_inf_seq; lia. }
    clear - H0.
    simpl in H0.
    rewrite upd_val_vec_not_in in H0.
    2:{ apply not_In_inf_seq; lia. }
    rewrite upd_val_eq in H0 |-*.
    case_eq (R_order_dec (oRpos_to_R a));
      intros e He;
      [ | exfalso; clear - H0 e; apply R_blt_lt in e | ]; try lra.
    + destruct a;
        simpl in H0;
        [ | exfalso; clear - e; apply R_blt_lt in e; simpl in e; lra].
      rewrite R_to_oRpos_oRpos_to_R; reflexivity.
    + rewrite R_to_oRpos_oRpos_to_R; reflexivity.
Qed.

Fixpoint p_concat_with_coeff_mul G L :=
  match G, L with
  | _, nil => nil
  | nil, _ => nil
  | T :: G , r :: L => seq_mul r T ++ p_concat_with_coeff_mul G L
  end.

Lemma p_concat_with_coeff_mul_only_diamond : forall G L,
    p_concat_with_coeff_mul (only_diamond_p_hseq G) L = only_diamond_p_seq (p_concat_with_coeff_mul G L).
Proof.
  induction G; intros L; destruct L; auto.
  simpl; rewrite IHG; auto.
  rewrite only_diamond_p_seq_app.
  rewrite only_diamond_p_seq_mul; reflexivity.
Qed.

Lemma eval_Poly_eval_p_sequent : forall val n T,
    eval_Poly val (sum_weight_var_p_seq n T) = sum_weight_var_seq n (eval_p_sequent val T).
Proof.
  intros val n; induction T; simpl; try lra.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros e He; simpl;
    destruct A; simpl; try case (term.V_eq n v); simpl; try rewrite IHT; try lra.
Qed.

Lemma eval_Poly_eval_p_hseq : forall val n G L,
    Forall_inf (fun x => 0 <= eval_Poly val x) L ->
    eval_Poly val (p_sum_weight_var_with_coeff n G L) = sum_weight_var_with_coeff n (map (eval_p_sequent val) G) (map (eval_to_oRpos val) L).
Proof.
  intros val n; induction G; intros L Hall; destruct Hall; simpl; try reflexivity.
  specialize (IHG l Hall).
  unfold eval_to_oRpos; unfold R_to_oRpos.
  sem_is_pos_decomp val x; intros e' He'; simpl ; [ | exfalso; clear - r e'; apply R_blt_lt in e' |  ]; try lra.
  - rewrite IHG; rewrite eval_Poly_eval_p_sequent.
    unfold eval_to_oRpos; unfold R_to_oRpos.
    lra.
  - rewrite e'.
    unfold eval_to_oRpos in IHG; unfold R_to_oRpos in IHG.
    lra.
Qed.

Lemma eval_Poly_eval_p_sequent_one : forall val T,
    eval_Poly val (sum_weight_one_p_seq T) = sum_weight_one_seq (eval_p_sequent val T).
Proof.
  intros val; induction T; simpl; try reflexivity.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros e He; simpl;
    destruct A;  simpl; try rewrite IHT; try lra.
Qed.

Lemma eval_Poly_eval_p_hseq_one : forall val G L,
    Forall_inf (fun x => 0 <= eval_Poly val x) L ->
    eval_Poly val (p_sum_weight_one_with_coeff G L) = sum_weight_one_with_coeff (map (eval_p_sequent val) G) (map (eval_to_oRpos val) L).
Proof.
  intros val; induction G; intros L Hall; destruct Hall; simpl; try reflexivity.
  specialize (IHG l Hall).
  unfold eval_to_oRpos; unfold R_to_oRpos.
  sem_is_pos_decomp val x; intros e' He'; simpl ; [ | exfalso; clear - r e'; apply R_blt_lt in e' |  ]; try lra.
  - rewrite IHG; rewrite eval_Poly_eval_p_sequent_one.
    unfold eval_to_oRpos; unfold R_to_oRpos.
    lra.
  - rewrite e'.
    unfold eval_to_oRpos in IHG; unfold R_to_oRpos in IHG.
    lra.
Qed.

Lemma eval_Poly_upd_val_vec_lt : forall val a vx vr,
    Forall_inf (fun x => max_var_Poly a < x)%nat vx ->
    eval_Poly (upd_val_vec val vx vr) a = eval_Poly val a.
Proof.
  intros val; induction a; intros vx vr Hall.
  - simpl.
    apply upd_val_vec_not_in.
    intros Hin.
    apply (Forall_inf_forall Hall) in Hin.
    simpl in Hin; lia.
  - reflexivity.
  - simpl; rewrite IHa1; [ rewrite IHa2 | ]; try reflexivity; refine (Forall_inf_arrow _ _ Hall);
      intros a Hlt; simpl in Hlt; lia.
  - simpl; rewrite IHa1; [ rewrite IHa2 | ]; try reflexivity; refine (Forall_inf_arrow _ _ Hall);
      intros a Hlt; simpl in Hlt; lia.
Qed.

Lemma eval_p_hseq_upd_val_vec_lt : forall val G vx vr,
    Forall_inf (fun x => max_var_weight_p_hseq G < x)%nat vx ->
    map (eval_p_sequent (upd_val_vec val vx vr)) G = map (eval_p_sequent val) G.
Proof.
  intros val; induction G; intros vx vr Hall; simpl; try reflexivity.
  rewrite eval_p_sequent_upd_val_vec_lt_max_var ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  rewrite IHG ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  reflexivity.
Qed.

Lemma sum_weight_var_with_coeff_eval_eq : forall val n G L,
    sum_weight_var_with_coeff n (map (eval_p_sequent val) G) L = eval_Poly (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) (map oRpos_to_R L)) (p_sum_weight_var_with_coeff n G (map Poly_var (seq (S (max_var_weight_p_hseq G)) (length L)))).
Proof.
  intros val n G L.
  rewrite eval_Poly_eval_p_hseq; auto.
  2:{ apply map_oRpos_to_R_all_pos. }
  rewrite eval_to_oRpos_to_R_eq.
  2:{ apply map_oRpos_to_R_all_pos. }
  rewrite eval_p_hseq_upd_val_vec_lt; try reflexivity.
  apply forall_Forall_inf.
  intros x Hin.
  case_eq (max_var_weight_p_hseq G <? x)%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H]; auto.
  exfalso.
  apply not_In_inf_seq with (S (max_var_weight_p_hseq G)) (length L) x; try lia.
  apply Hin.
Qed.

Lemma sum_weight_one_with_coeff_eval_eq : forall val G L,
    sum_weight_one_with_coeff (map (eval_p_sequent val) G) L  = eval_Poly (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) (map oRpos_to_R L)) (p_sum_weight_one_with_coeff G (map Poly_var (seq (S (max_var_weight_p_hseq G)) (length L)))).
Proof.
  intros val G L.
  rewrite eval_Poly_eval_p_hseq_one; auto.
  2:{ apply map_oRpos_to_R_all_pos. }
  rewrite eval_to_oRpos_to_R_eq.
  2:{ apply map_oRpos_to_R_all_pos. }
  rewrite eval_p_hseq_upd_val_vec_lt; try reflexivity.
  apply forall_Forall_inf.
  intros x Hin.
  case_eq (max_var_weight_p_hseq G <? x)%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H]; auto.
  exfalso.
  apply not_In_inf_seq with (S (max_var_weight_p_hseq G)) (length L) x; try lia.
  apply Hin.
Qed.

(* Put non basic formula first, i.e., G in the form H | |- T, r.A with A non basic. *)

Fixpoint p_seq_fst_non_basic_term (T : p_sequent) : (Poly * term) :=
  match T with
  | nil => (Poly_cst 0, HMR_one)
  | (a, A) :: T => if (0 <? HMR_complexity_term A)%nat
                   then (a , A)
                   else (p_seq_fst_non_basic_term T)
  end.

Lemma p_seq_fst_non_basic_term_correct :
  forall T,
    (p_seq_is_basic T -> False) ->
    (is_basic (snd (p_seq_fst_non_basic_term T)) -> False).
Proof.
  induction T; intros Hnbs Hbt; [ apply Hnbs; apply Forall_inf_nil | ].
  destruct a as [a A]; simpl in *.
  case_eq (0 <? HMR_complexity_term A)%nat; intros H1; rewrite H1 in Hbt;
    (apply Nat.ltb_lt in H1 + apply Nat.ltb_nlt in H1).
  - apply is_basic_complexity_0 in Hbt.
    simpl in Hbt.
    lia.
  - apply IHT; auto.
    intros H2.
    apply Hnbs.
    apply Forall_inf_cons; auto.
    apply is_basic_complexity_0_inv.
    lia.
Qed.

Lemma p_seq_fst_non_basic_term_well_defined :
  forall val T,
    (0 < HMR_complexity_p_seq T)%nat ->
    p_seq_well_defined val T ->
    0 <= eval_Poly val (fst (p_seq_fst_non_basic_term T)).
Proof.
  intros val; induction T; intros Hlt; [ simpl in Hlt; exfalso; try lia | ].
  intros Hwd.
  destruct a as [a A].
  simpl.
  case_eq (0 <? HMR_complexity_term A)%nat; intros H; auto; inversion Hwd; subst; auto.
  apply IHT; auto.
  apply Nat.ltb_nlt in H.
  simpl in *.
  lia.
Qed.  

Fixpoint p_seq_without_fst_non_basic_term (T : p_sequent) : p_sequent :=
  match T with
  | nil => nil
  | (a, A) :: T => if (0 <? HMR_complexity_term A)%nat
                   then T
                   else (a , A) :: (p_seq_without_fst_non_basic_term T)
  end.

Lemma p_seq_put_non_basic_fst : forall T,
    (p_seq_is_basic T -> False) ->
    Permutation_Type T (p_seq_fst_non_basic_term T :: p_seq_without_fst_non_basic_term T).
Proof.
  induction T; intros Hnb; [ exfalso; apply Hnb; apply Forall_inf_nil | ].
  destruct a as [a A]; simpl.
  case_eq (0 <? HMR_complexity_term A)%nat; intros H1;
    apply Nat.ltb_lt in H1 + apply Nat.ltb_nlt in H1; auto.
  assert (p_seq_is_basic T -> False).
  { intros H; apply Hnb; apply Forall_inf_cons; auto.
    apply is_basic_complexity_0_inv.
    lia. }
  specialize (IHT H).
  transitivity ((a , A) :: p_seq_fst_non_basic_term T :: p_seq_without_fst_non_basic_term T);
    Permutation_Type_solve.
Qed.

Lemma p_seq_without_fst_non_basic_term_well_defined :
  forall val T,
    p_seq_well_defined val T ->
    p_seq_well_defined val (p_seq_without_fst_non_basic_term T).
Proof.
  intros val; induction T; intros Hwd; [apply Forall_inf_nil |].
  destruct a as [a A]; inversion Hwd; subst.
  simpl.
  case_eq (0 <? HMR_complexity_term A)%nat; intros H; try apply Forall_inf_cons; try apply IHT; auto.
Qed.

Fixpoint p_hseq_p_seq_max_complexity (G : p_hypersequent) : p_sequent :=
  match G with
  | nil => nil
  | T :: G => if (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq T)
              then T
              else p_hseq_p_seq_max_complexity G
  end.

Lemma p_hseq_p_seq_max_complexity_well_defined :
  forall val G,
    p_hseq_well_defined val G ->
    p_seq_well_defined val (p_hseq_p_seq_max_complexity G).
Proof.
  intros val; induction G; intros Hwd; [ apply Forall_inf_nil | ].
  inversion Hwd; specialize (IHG X0); subst.
  simpl; case (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); auto.
Qed.

Lemma p_hseq_p_seq_max_complexity_correct :
  forall G,
    HMR_complexity_p_seq (p_hseq_p_seq_max_complexity G) = fst (HMR_complexity_p_hseq G).
Proof.
  induction G; auto.
  simpl.
  case_eq (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); intros H1;
    case_eq (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); intros H2;
      case_eq (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G))%nat; intros H3;
        simpl;
        apply Nat.leb_le in H1 + apply Nat.leb_nle in H1;
        apply Nat.eqb_eq in H2 + apply Nat.eqb_neq in H2;
        apply Nat.ltb_lt in H3 + apply Nat.ltb_nlt in H3;
        try lia.
Qed.

Fixpoint p_hseq_without_max_complexity (G : p_hypersequent) : p_hypersequent :=
  match G with
  | nil => nil
  | T :: G => if (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq T)
              then G
              else T :: p_hseq_without_max_complexity G
  end.

Lemma p_hseq_without_max_complexity_well_defined :
  forall val G,
    p_hseq_well_defined val G ->
    p_hseq_well_defined val (p_hseq_without_max_complexity G).
Proof.
  intros val; induction G; intros Hwd; [apply Forall_inf_nil | ].
  inversion Hwd; subst; specialize (IHG X0).
  simpl; case (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); try apply Forall_inf_cons; auto.
Qed.

Lemma p_hseq_put_max_complexity_fst : forall G,
    G <> nil ->
    Permutation_Type G (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G).
Proof.
  induction G; intros Hnnil; [ exfalso; auto | ].
  simpl.
  case_eq (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); intros H1;
    apply Nat.leb_le in H1 + apply Nat.leb_nle in H1; auto.
  destruct G.
  { exfalso; simpl in H1; lia. }
  assert (p :: G <> nil) as Hnnil'.
  { intros H; inversion H. }
  specialize (IHG Hnnil').
  transitivity (a :: p_hseq_p_seq_max_complexity (p :: G) :: p_hseq_without_max_complexity (p :: G)); Permutation_Type_solve.
Qed.

Definition p_hseq_put_non_basic_fst G :=
  ((p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)) :: p_hseq_without_max_complexity G).

Lemma p_hseq_put_non_basic_fst_modal_complexity :
  forall G,
    (p_hseq_is_basic G -> False) ->
    modal_complexity_p_hseq (p_hseq_put_non_basic_fst G) = modal_complexity_p_hseq G.
Proof.
  intros G Hnb.
  unfold p_hseq_put_non_basic_fst.
  rewrite modal_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
  2:{ symmetry; apply p_seq_put_non_basic_fst.
      intros H.
      apply Hnb.
      apply p_hseq_is_basic_complexity_0_inv.
      rewrite <- p_hseq_p_seq_max_complexity_correct.
      apply p_seq_is_basic_complexity_0.
      apply H. }
  rewrite modal_complexity_perm with _ G; auto.
  symmetry; apply p_hseq_put_max_complexity_fst.
  intros H; apply Hnb; rewrite H.
  apply Forall_inf_nil.
Qed.

Lemma p_hseq_put_non_basic_fst_HMR_complexity :
  forall G,
    (p_hseq_is_basic G -> False) ->
    HMR_complexity_p_hseq (p_hseq_put_non_basic_fst G) = HMR_complexity_p_hseq G.
Proof.
  intros G Hnb.
  apply same_modal_complexity_HMR_complexity.
  apply p_hseq_put_non_basic_fst_modal_complexity; auto.
Qed.

Lemma p_hseq_put_non_basic_fst_correct :
  forall G a A T H,
    (p_hseq_is_basic G -> False) ->
    p_hseq_put_non_basic_fst G = ((a, A) :: T) :: H ->
    is_basic A -> False.
Proof.
  intros G a A T H Hnb Heq Hb.
  unfold p_hseq_put_non_basic_fst in Heq.
  inversion Heq; subst.
  apply p_seq_fst_non_basic_term_correct with (p_hseq_p_seq_max_complexity G).
  - intros Hb'.
    apply Hnb.
    apply p_hseq_is_basic_complexity_0_inv.
    apply p_seq_is_basic_complexity_0 in Hb'.
    rewrite p_hseq_p_seq_max_complexity_correct in Hb'.
    apply Hb'.
  - rewrite H1.
    apply Hb.
Qed.

Lemma p_hseq_put_non_basic_fst_well_defined :
  forall val G,
    (0 < fst (HMR_complexity_p_hseq G))%nat ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val (p_hseq_put_non_basic_fst G).
Proof.
  intros val G Hn0 Hwd.
  apply Forall_inf_cons; (destruct G; [ exfalso; simpl in *; lia | ]).
  - apply Forall_inf_cons.
    + apply p_seq_fst_non_basic_term_well_defined; [ | apply p_hseq_p_seq_max_complexity_well_defined; auto].
      rewrite p_hseq_p_seq_max_complexity_correct.
      apply Hn0.
    + apply p_seq_without_fst_non_basic_term_well_defined.
      apply p_hseq_p_seq_max_complexity_well_defined.
      apply Hwd.
  - apply p_hseq_without_max_complexity_well_defined; apply Hwd.
Qed.

Lemma p_hseq_put_non_basic_fst_HMR :
  forall val G,
    (p_hseq_is_basic G -> False) ->
    HMR_T_M (map (eval_p_sequent val) (p_hseq_put_non_basic_fst G)) ->
    HMR_T_M (map (eval_p_sequent val) G).
Proof.
  intros val G Hnbasic Hpi.
  apply hmrr_ex_hseq with (map (eval_p_sequent val) (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
  { apply Permutation_Type_map.
    symmetry; apply p_hseq_put_max_complexity_fst.
    intros Hnil.
    subst.
    apply Hnbasic; apply Forall_inf_nil. }
  simpl.
  apply hmrr_ex_seq with (eval_p_sequent val (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G))).
  { apply Permutation_Type_eval_p_sequent.
    symmetry; apply p_seq_put_non_basic_fst.
    intros H.
    apply p_seq_is_basic_complexity_0 in H.
    rewrite p_hseq_p_seq_max_complexity_correct in H.
    apply Hnbasic.
    apply p_hseq_is_basic_complexity_0_inv.
    apply H. }
  apply Hpi.
Qed.

Lemma p_hseq_put_non_basic_fst_HMR_inv :
  forall val G,
    (p_hseq_is_basic G -> False) ->
    HMR_T_M (map (eval_p_sequent val) G) ->
    HMR_T_M (map (eval_p_sequent val) (p_hseq_put_non_basic_fst G)).
Proof.
  intros val G Hnbasic Hpi.
  unfold p_hseq_put_non_basic_fst.
  unfold map.
  apply hmrr_ex_seq with (eval_p_sequent val (p_hseq_p_seq_max_complexity G)).
  { apply Permutation_Type_eval_p_sequent.
    apply p_seq_put_non_basic_fst.
    intros H.
    apply p_seq_is_basic_complexity_0 in H.
    rewrite p_hseq_p_seq_max_complexity_correct in H.
    apply Hnbasic.
    apply p_hseq_is_basic_complexity_0_inv.
    apply H. }
  eapply hmrr_ex_hseq; [ | apply Hpi].
  transitivity (map (eval_p_sequent val) (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)); [ | reflexivity ].
  apply Permutation_Type_map.
  apply p_hseq_put_max_complexity_fst.
  intros Hnil.
  subst.
  apply Hnbasic; apply Forall_inf_nil.
Qed.
  
Definition apply_logical_rule_on_p_hypersequent G : (p_hypersequent + (p_hypersequent * p_hypersequent)) :=
  match G with
  | nil => inl nil
  | T :: G => match T with
              | nil => inl (nil :: G)
              | (a, A) :: T => match A with
                               | A1 +S A2 => inl (((a, A1) :: (a, A2) :: T) :: G)
                               | A1 /\S A2 => inr ((((a, A1) :: T) :: G) , (((a, A2) :: T) :: G))
                               | A1 \/S A2 => inl (((a, A2) :: T) :: ( (a, A1) :: T) :: G)
                               | r0 *S A => inl (((Poly_cst (projT1 r0) *R a, A) :: T) :: G)
                               | HMR_zero => inl (T :: G)
                               | _ => inl (((a, A) :: T) :: G)
                               end
              end
  end.

Lemma apply_logical_rule_on_p_hypersequent_inl_well_defined :
  forall val G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val G1.
Proof.
  intros val G G1 Heq Hwd.
  destruct G ; [inversion Heq; apply Forall_inf_nil | ].
  destruct l; [inversion Heq; apply Hwd | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto;
    inversion Hwd; subst;
      inversion X; subst; simpl in *;
        (apply Forall_inf_cons; [ | try apply Forall_inf_cons]); auto;
          apply Forall_inf_cons; auto.
  destruct r as [r Hr].
  clear - H0 Hr.
  simpl; apply R_blt_lt in Hr.
  nra.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_l_well_defined :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1, G2) ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val G1.
Proof.
  intros val G G1 G2 Heq Hwd.
  destruct G ; [inversion Heq | ].
  destruct l; [inversion Heq | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; subst.
  inversion X; subst.
  apply Forall_inf_cons ; [ apply Forall_inf_cons | ]; auto.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_r_well_defined :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1, G2) ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val G2.
Proof.
  intros val G G1 G2 Heq Hwd.
  destruct G ; [inversion Heq | ].
  destruct l; [inversion Heq | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; subst.
  inversion X; subst.
  apply Forall_inf_cons ; [ apply Forall_inf_cons | ]; auto.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inl_HMR :
  forall val G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G) ->
    HMR_T_M (map (eval_p_sequent val) G1).
Proof.
  intros val G G1 Heq Hwd pi.
  destruct G; [ exfalso; apply (HMR_not_empty _ nil pi); auto | ].
  destruct l; [ inversion Heq; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  - inversion Hwd; inversion X; subst.
    simpl in pi.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); simpl in *; lra);
      rewrite He in pi; simpl.
    2:{ apply pi. }
    apply hmrr_Z_inv with ((existT _ (eval_Poly val a) e) :: nil).
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in pi |- *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); simpl in *; lra);
      rewrite He in pi.
    2:{ apply pi. }
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi.
    change ((r, A1) :: (r, A2) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) A1 ++ hseq.vec (r :: nil) A2 ++ eval_p_sequent val l).
    apply hmrr_plus_inv.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); simpl in *; lra);
      case (R_order_dec (projT1 r * eval_Poly val a)); intros e';
        try (exfalso; destruct r as [r Hr]; clear - e e' H2;
             simpl in *;
             apply R_blt_lt in Hr; apply R_blt_lt in e; try (apply R_blt_lt in e');
             nra);
        try (exfalso; rewrite e in e'; apply R_blt_lt in e'; lra);
        rewrite He in pi.
    + replace ((existT (fun x : R => (0 <? x) = true) (projT1 r * eval_Poly val a) e', A)
                 :: eval_p_sequent val l) with
          (hseq.vec (hseq.mul_vec r ((existT (fun x => (0 <? x) = true) (eval_Poly val a) e) :: nil)) A ++ eval_p_sequent val l).
      2:{ simpl.
          replace (time_pos r (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e))
            with (existT (fun x : R => (0 <? x) = true) (projT1 r * eval_Poly val a) e') by (destruct r; apply Rpos_eq; clear; simpl; nra); auto. }
      apply hmrr_mul_inv.
      apply pi.
    + apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in pi |- *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); simpl in *; lra);
      rewrite He in pi.
    2:{ apply hmrr_W; apply pi. }
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi.
    change ((r, A1) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) A1 ++ eval_p_sequent val l).
    change ((r, A2) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) A2 ++ eval_p_sequent val l).
    apply hmrr_max_inv.
    apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inl_HMR_inv :
  forall val G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G1) ->
    HMR_T_M (map (eval_p_sequent val) G).
Proof.
  intros val G G1 Heq Hwd pi.
  destruct G; [ exfalso; apply (HMR_not_empty _ _ pi); inversion Heq; auto | ].
  destruct l; [ inversion Heq; subst; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  - inversion Hwd; inversion X; subst.
    simpl in *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); simpl in *; lra).
    2:{ apply pi. }
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi.
    change ((r, HMR_zero) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) HMR_zero ++ eval_p_sequent val l).
    apply hmrr_Z.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in pi |- *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); simpl in *; lra).
    2:{ rewrite He in pi; apply pi. }
    rewrite He in pi.
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi.
    change ((r, A1 +S A2) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) (A1 +S A2) ++ eval_p_sequent val l).
    apply hmrr_plus.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); simpl in *; lra);
    case_eq (R_order_dec (projT1 r * eval_Poly val a)); intros e' He';
      try (exfalso; destruct r as [r Hr]; clear - e e' H2;
           simpl in *;
           apply R_blt_lt in Hr; apply R_blt_lt in e; try (apply R_blt_lt in e');
           nra);
      try (exfalso; clear - e e'; rewrite e in e'; apply R_blt_lt in e'; lra);
      rewrite He' in pi.
    2:{ apply pi. }
    replace ((existT (fun x : R => (0 <? x) = true) (projT1 r * eval_Poly val a) e', A)
              :: eval_p_sequent val l) with
        (hseq.vec (hseq.mul_vec r ((existT (fun x => (0 <? x) = true) (eval_Poly val a) e) :: nil)) A ++ eval_p_sequent val l) in pi.
    2:{ simpl.
        replace (time_pos r (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e))
          with (existT (fun x : R => (0 <? x) = true) (projT1 r * eval_Poly val a) e') by (destruct r; apply Rpos_eq; clear; simpl; nra); auto. }
    revert pi;set (r' := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi.
    change ((r', r *S A) :: eval_p_sequent val l)
      with (hseq.vec (r' :: nil) (r *S A) ++ eval_p_sequent val l).    
    apply hmrr_mul.
    apply pi.
  - inversion Hwd; inversion X; subst.
    simpl in pi |- *.
    sem_is_pos_decomp val a; intros e He;
      try (exfalso; clear - e H2;
           try (apply R_blt_lt in e); simpl in *; lra);
      rewrite He in pi.
    2:{ apply hmrr_C.
        apply pi. }
    revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi.
    change ((r, A1 \/S A2) :: eval_p_sequent val l) with
        (hseq.vec (r :: nil) (A1 \/S A2) ++ eval_p_sequent val l).
    apply hmrr_max.
    apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_l_HMR :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G) ->
    HMR_T_M (map (eval_p_sequent val) G1).
Proof.
  intros val G G1 G2 Heq Hwd pi.
  destruct G; [ exfalso; apply (HMR_not_empty _ nil pi); auto | ].
  destruct l; [ inversion Heq; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; inversion X; subst.
  simpl in pi |- *.
  sem_is_pos_decomp val a; intros e He;
    try (exfalso; clear - e H2;
         try (apply R_blt_lt in e); simpl in *; lra);
    rewrite He in pi.
  2:{ apply pi. }
  revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi.
  change ((r, A1) :: eval_p_sequent val l) with
      (hseq.vec (r :: nil) A1 ++ eval_p_sequent val l).
  apply hmrr_min_inv_l with A2.
  apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_r_HMR :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G) ->
    HMR_T_M (map (eval_p_sequent val) G2).
Proof.
  intros val G G1 G2 Heq Hwd pi.
  destruct G; [ exfalso; apply (HMR_not_empty _ nil pi); auto | ].
  destruct l; [ inversion Heq; apply pi | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; inversion X; subst.
  simpl in pi |- *.
  sem_is_pos_decomp val a; intros e He;
    try (exfalso; clear - e H2;
         try (apply R_blt_lt in e); simpl in *; lra);
    rewrite He in pi.
  2:{ apply pi. }
  revert pi;set (r := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi.
  change ((r, A2) :: eval_p_sequent val l) with
      (hseq.vec (r :: nil) A2 ++ eval_p_sequent val l).
  apply hmrr_min_inv_r with A1.
  apply pi.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_HMR_inv :
  forall val G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1 , G2) ->
    p_hseq_well_defined val G ->
    HMR_T_M (map (eval_p_sequent val) G1) ->
    HMR_T_M (map (eval_p_sequent val) G2) ->
    HMR_T_M (map (eval_p_sequent val) G).
Proof.
  intros val G G1 G2 Heq Hwd pi1 pi2.
  destruct G; [ exfalso; inversion Heq | ].
  destruct l; [ inversion Heq | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
  inversion Hwd; inversion X; subst.
  simpl in pi1,pi2 |- *.
  sem_is_pos_decomp val a; intros e He;
    try (exfalso; clear - e H2;
         try (apply R_blt_lt in e); simpl in *; lra);
    rewrite He in pi1; rewrite He in pi2.
  2:{ apply pi1. }
  revert pi1 pi2;set (r := (existT (fun x : R => (0 <? x) = true) (eval_Poly val a) e)); intros pi1 pi2.
  change ((r, A1 /\S A2) :: eval_p_sequent val l) with
      (hseq.vec (r :: nil) (A1 /\S A2) ++ eval_p_sequent val l).
  apply hmrr_min; auto.
Qed.
    
Lemma apply_logical_rule_on_p_hypersequent_correct_inl :
  forall G G1 n,
    snd (fst (modal_complexity_p_hseq G)) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inl G1 ->
    modal_complexity_p_hseq G1 <3 modal_complexity_p_hseq G.
Proof.
  intros G G1 n H1 H2.
  unfold modal_complexity_p_hseq in H1.
  simpl in H1.
  remember (p_hseq_put_non_basic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_basic_fst_HMR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_basic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_basic A -> False).
  { apply p_hseq_put_non_basic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_basic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  - rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, HMR_zero) :: l) with (vec (a :: nil) HMR_zero ++ l).
    apply hmrr_Z_decrease_modal_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_basic_fst in *.
    rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
    2:{ symmetry; apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, A1 +S A2) :: l) with (vec (a :: nil) (A1 +S A2) ++ l).
    change ((a, A1) :: (a, A2) :: l) with (vec (a :: nil) A1 ++ vec (a :: nil) A2 ++ l).
    apply hmrr_plus_decrease_modal_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_basic_fst in *.
    rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
    2:{ symmetry; apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, r *S A) :: l) with (vec (a :: nil) (r *S A) ++ l).
    change ((Poly_cst (projT1 r) *R a, A) :: l) with (vec (mul_vec (Poly_cst (projT1 r)) (a :: nil)) A ++ l).
    apply hmrr_mul_decrease_modal_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_basic_fst in *.
    rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
    2:{ symmetry; apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
  - rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
    2:{ intros Hnb.
        apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
    rewrite <- HeqH.
    change ((a, A1 \/S A2) :: l) with (vec (a :: nil) (A1 \/S A2) ++ l).
    change ((a, A1) :: l) with (vec (a :: nil) A1 ++ l).
    change ((a, A2) :: l) with (vec (a :: nil) A2 ++ l).
    apply hmrr_max_decrease_modal_complexity ; [ intros H'; inversion H' | ].
    simpl vec; simpl app.
    rewrite HeqH.
    unfold p_hseq_put_non_basic_fst in *.
    rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
    2:{ symmetry; apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    rewrite complexity_p_hseq_perm with _ G.
    2:{ symmetry; apply p_hseq_put_max_complexity_fst.
        intros Heq; rewrite Heq in H1; inversion H1. }
    rewrite <-p_hseq_p_seq_max_complexity_correct.
    rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
    2:{ apply p_seq_put_non_basic_fst.
        intros Hb.
        apply p_seq_is_basic_complexity_0 in Hb.
        rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
    inversion HeqH; subst; reflexivity.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_correct_inr_l :
  forall G G1 G2 n,
    snd (fst (modal_complexity_p_hseq G)) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inr (G1 , G2) ->
    modal_complexity_p_hseq G1 <3 modal_complexity_p_hseq G.
Proof.
  intros G G1 G2 n H1 H2.
  unfold modal_complexity_p_hseq in H1.
  simpl in H1.
  remember (p_hseq_put_non_basic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_basic_fst_HMR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_basic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_basic A -> False).
  { apply p_hseq_put_non_basic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_basic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
  2:{ intros Hnb.
      apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  rewrite <- HeqH.
  change ((a, A1 /\S A2) :: l) with (vec (a :: nil) (A1 /\S A2) ++ l).
  change ((a, A1) :: l) with (vec (a :: nil) A1 ++ l).
  apply hmrr_min_r_decrease_modal_complexity ; [ intros H'; inversion H' | ].
  simpl vec; simpl app.
  rewrite HeqH.
  unfold p_hseq_put_non_basic_fst in *.
  rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
  2:{ symmetry; apply p_seq_put_non_basic_fst.
      intros Hb.
      apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  rewrite complexity_p_hseq_perm with _ G.
  2:{ symmetry; apply p_hseq_put_max_complexity_fst.
      intros Heq; rewrite Heq in H1; inversion H1. }
  rewrite <-p_hseq_p_seq_max_complexity_correct.
  rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_basic_fst.
      intros Hb.
      apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  inversion HeqH; subst; reflexivity.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_correct_inr_r :
  forall G G1 G2 n,
    snd (fst (modal_complexity_p_hseq G)) = S n ->
    apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inr (G1 , G2) ->
    modal_complexity_p_hseq G2 <3 modal_complexity_p_hseq G.
Proof.
  intros G G1 G2 n H1 H2.
  unfold modal_complexity_p_hseq in H1.
  simpl in H1.
  remember (p_hseq_put_non_basic_fst G) as H.
  destruct H.
  { exfalso.
    rewrite <- p_hseq_put_non_basic_fst_HMR_complexity in H1 ; [ rewrite <- HeqH in H1; inversion H1 |].
    intros Hnb.
    apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  destruct l.
  { unfold p_hseq_put_non_basic_fst in HeqH.
    inversion HeqH. }
  destruct p as [a A].
  assert (is_basic A -> False).
  { apply p_hseq_put_non_basic_fst_correct with G a l H; auto.
    intros Hb.
    apply p_hseq_is_basic_complexity_0 in Hb.
    lia. }
  destruct A; simpl in H2; inversion H2; subst; try (exfalso; now apply H0).
  rewrite <- (p_hseq_put_non_basic_fst_modal_complexity G).
  2:{ intros Hnb.
      apply p_hseq_is_basic_complexity_0 in Hnb; lia. }
  rewrite <- HeqH.
  change ((a, A1 /\S A2) :: l) with (vec (a :: nil) (A1 /\S A2) ++ l).
  change ((a, A2) :: l) with (vec (a :: nil) A2 ++ l).
  apply hmrr_min_l_decrease_modal_complexity ; [ intros H'; inversion H' | ].
  simpl vec; simpl app.
  rewrite HeqH.
  unfold p_hseq_put_non_basic_fst in *.
  rewrite HMR_complexity_perm_fst_seq with _ _ (p_hseq_p_seq_max_complexity G).
  2:{ symmetry; apply p_seq_put_non_basic_fst.
      intros Hb.
      apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  rewrite complexity_p_hseq_perm with _ G.
  2:{ symmetry; apply p_hseq_put_max_complexity_fst.
      intros Heq; rewrite Heq in H1; inversion H1. }
  rewrite <-p_hseq_p_seq_max_complexity_correct.
  rewrite complexity_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_basic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_basic_fst.
      intros Hb.
      apply p_seq_is_basic_complexity_0 in Hb.
      rewrite p_hseq_p_seq_max_complexity_correct in Hb; lia. }
  inversion HeqH; subst; reflexivity.
Qed.

(* end hide *)

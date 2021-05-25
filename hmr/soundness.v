(** * Implementation of Section 4.3 *)
Require Import Rpos.
Require Import RL.hmr.term.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.semantic.
Require Import RL.hmr.interpretation.

Require Import List.
Require Import Lra.

Require Import RL.OLlibs.Permutation_more.

Local Open Scope R_scope.

(** ** all rules are sound *)

Lemma W_sound : forall G T, G <> nil ->  HMR_zero <== (sem_hseq G) -> HMR_zero <== sem_hseq (T :: G).
Proof with try assumption.
  intros G T notEmpty Hleq.
  destruct G; [ now exfalso | ].
  unfold sem_hseq; fold(sem_hseq (s :: G)).
  apply leq_trans with (sem_hseq (s :: G))...
  eapply leq_cong_r; [ apply commu_max | ].
  now apply abso_min.
Qed.

Lemma C_sound : forall G T, sem_hseq (T :: T :: G) === sem_hseq (T :: G).
Proof with try assumption.
  intros G T.
  destruct G.
  - unfold sem_hseq.
    now auto with MGA_solver.
  - unfold sem_hseq; fold (sem_hseq (s :: G)).
    etransitivity ; [apply asso_max | ].
    now auto with MGA_solver.
Qed.

Lemma S_sound : forall G T1 T2, HMR_zero <== sem_hseq ((T1 ++ T2) :: G) -> HMR_zero <== sem_hseq (T1 :: T2 :: G).
Proof with try assumption.
  intros G T1 T2 Hleq.
  destruct G.
  - simpl in *.
    apply leq_div_2.
    eapply leq_cong_l; [ apply mul_2 | ].
    eapply leq_cong_l ;[ apply neutral_plus | ].
    eapply leq_cong_r in Hleq; [ | symmetry; apply sem_seq_plus].
    apply leq_trans with (sem_seq T1 +S sem_seq T2)...
    now apply mean_prop.
  - unfold sem_hseq in *; fold (sem_hseq (l :: G)) in *.
    eapply leq_cong_r; [ apply asso_max | ].
    apply cond_zero_leq_max_2.
    apply leq_antisym.
    + apply leq_trans with (((plus_pos One One) *S  neg (sem_seq T1 \/S sem_seq T2)) /\S neg (sem_hseq (l :: G))).
      * apply leq_min.
        -- apply leq_trans with (neg (sem_seq T1 \/S sem_seq T2)); [auto with MGA_solver | ].
           eapply leq_cong_r ; [apply mul_2 | ].
           eapply leq_cong_l; [symmetry; apply neutral_plus | ].
           eapply leq_cong_l; [apply commu_plus | ].
           apply leq_plus.
           now auto with MGA_solver.
        -- eapply leq_cong_l ; [ apply commu_min | ].
           now auto with MGA_solver.
      * apply leq_trans with (neg (sem_seq T1 +S sem_seq T2) /\S neg (sem_hseq (l :: G))).
        -- apply leq_min.
           ++ apply leq_trans with (plus_pos One One *S neg (sem_seq T1 \/S sem_seq T2)).
              ** now auto with MGA_solver.
              ** eapply leq_cong_l; [apply Rpos_mul_neg | ].
                 apply neg_leq_cond.
                 apply mean_prop.                 
           ++ eapply leq_cong_l; [ apply commu_min | ].
              apply min_leq.
        -- apply cond_min_neg_eq_zero in Hleq.
           eapply leq_cong_l.
           { apply min_left.
             apply max_left.
             apply (@ctxt HMR_cohole).
             symmetry; apply sem_seq_plus. }
           eapply leq_cong_l; [apply Hleq | ].
           apply leq_refl.
    + apply leq_min; now auto with MGA_solver.
Qed.

Lemma M_sound : forall G T1 T2, HMR_zero <== sem_hseq (T1 :: G) -> HMR_zero <== sem_hseq (T2 :: G) ->
                                HMR_zero <== sem_hseq ((T1 ++ T2) :: G).
Proof with try assumption.
  intros [ | T3 G ] T1 T2 Hleq1 Hleq2.
  - simpl in *.
    eapply leq_cong_r ; [ apply sem_seq_plus | ].
    eapply leq_cong_l; [ symmetry; apply neutral_plus | ].
    apply leq_plus_cong...
  - unfold sem_hseq in *; fold (sem_hseq (T3 :: G)) in *; fold (sem_hseq (T3 :: G)) in *; fold (sem_hseq (T3 :: G)).
    eapply leq_cong_r.
    { apply max_left.
      apply sem_seq_plus. }
    apply cond_zero_leq_max_2.
    apply leq_antisym.
    + eapply leq_trans.
      { apply leq_min.
        - eapply leq_trans.
          + apply min_leq.
          + apply neg_subdistri_plus.
        - eapply leq_cong_l; [apply commu_min | ].
          apply min_leq. } 
      eapply leq_trans.
      * apply plus_pos_min; apply zero_leq_neg.
      * eapply leq_cong_r; [ symmetry; apply neutral_plus | ].
        apply leq_plus_cong;
          (eapply leq_cong_r ; [ symmetry; apply cond_min_neg_eq_zero | apply leq_refl]);
          assumption.
    + apply leq_min.
      * eapply leq_cong_r; [apply commu_max | ].
        apply leq_max.
      * eapply leq_cong_r; [apply commu_max | ].
        apply leq_max.
Qed.

Lemma T_sound :  forall G T r,
    HMR_zero <== sem_hseq (seq_mul r T :: G) ->
    HMR_zero <== sem_hseq (T :: G).
Proof with try assumption.
  intros [ | T2 G] T [r Hpos]; 
    remember (existT (fun r : R => (0 <? r)%R = true) r Hpos) as t; intros Hleq.
  - simpl in *.
    eapply leq_cong_r ; [ symmetry; apply mul_1 | ].
    replace One with (time_pos (inv_pos t) t).
    2:{ clear; apply Rpos_eq; destruct t; simpl; apply R_blt_lt in e; rewrite Rinv_l; nra. }
    eapply leq_cong_r; [ symmetry; apply mul_assoc | ].
    apply leq_cong_r with (inv_pos t *S (pos (t *S sem_seq T))).
    { apply mul_right.
      symmetry.
      etransitivity; [ apply commu_max | ].
      apply min_max.
      eapply leq_cong_r; [ | apply Hleq].
      symmetry; apply sem_seq_mul. }
    apply compa_mul_ax.
  - unfold sem_hseq in *; fold (sem_hseq (T2 :: G)) in *.
    apply leq_pos_max_mul_l with t.
    eapply leq_cong_r; [ | apply Hleq].
    apply max_left.
    symmetry; apply sem_seq_mul.
Qed.

(** The following lemma prove both the soundness of the ID rule and the CAN rule *)
Lemma ext_ID_sound : forall G T A r s,
    sum_vec r = sum_vec s -> sem_hseq (T :: G) === sem_hseq ((vec s (-S A) ++ vec r A ++ T) :: G).
Proof.
  intros [ | T2 G] T A r s Heq.
  - simpl.
    etransitivity; [ | symmetry; apply sem_seq_plus ].
    etransitivity; [ | symmetry; apply plus_right; apply sem_seq_plus ].
    etransitivity; [ | symmetry; apply asso_plus].
    etransitivity; [ | apply plus_left; apply commu_plus ].
    destruct r; destruct s.
    + simpl in *.
      etransitivity; [ | apply commu_plus].
      etransitivity; [ | symmetry; apply plus_right; apply neutral_plus].
      symmetry; apply neutral_plus.
    + exfalso.
      destruct r ; simpl in *.
      apply R_blt_lt in e.
      assert (H := (sum_vec_le_0 s)).
      nra.
    + exfalso.
      destruct r ; simpl in *.
      apply R_blt_lt in e.
      assert (H := (sum_vec_le_0 r0)).
      nra.
    + assert (r :: r0 <> nil) as H1 by now auto.
      assert (r1 :: s <> nil) as H2 by now auto.
      etransitivity; [ | apply plus_left; apply plus_left; symmetry; apply (sem_seq_vec _ _ H1)].
      etransitivity; [ | apply plus_left; apply plus_right; symmetry; apply (sem_seq_vec _ _ H2)].
      replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil _ H1)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil _ H2)) by (apply Rpos_eq; simpl in *; nra).
      etransitivity; [ | apply plus_left; apply plus_right; symmetry; apply mul_minus].
      etransitivity; [ | apply plus_left; symmetry; apply opp_plus].
      etransitivity; [ | apply commu_plus].
      symmetry; apply neutral_plus.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    apply max_left.
    etransitivity; [ | symmetry; apply sem_seq_plus ].
    etransitivity; [ | symmetry; apply plus_right; apply sem_seq_plus ].
    etransitivity; [ | symmetry; apply asso_plus].
    etransitivity; [ | apply plus_left; apply commu_plus ].
    destruct r; destruct s.
    + simpl in *.
      etransitivity; [ | apply commu_plus].
      etransitivity; [ | symmetry; apply plus_right; apply neutral_plus].
      symmetry; apply neutral_plus.
    + exfalso.
      destruct r ; simpl in *.
      apply R_blt_lt in e.
      assert (H := (sum_vec_le_0 s)).
      nra.
    + exfalso.
      destruct r ; simpl in *.
      apply R_blt_lt in e.
      assert (H := (sum_vec_le_0 r0)).
      nra.
    + assert (r :: r0 <> nil) as H1 by now auto.
      assert (r1 :: s <> nil) as H2 by now auto.
      etransitivity; [ | apply plus_left; apply plus_left; symmetry; apply (sem_seq_vec _ _ H1)].
      etransitivity; [ | apply plus_left; apply plus_right; symmetry; apply (sem_seq_vec _ _ H2)].
      replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil _ H1)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil _ H2)) by (apply Rpos_eq; simpl in *; nra).
      etransitivity; [ | apply plus_left; apply plus_right; symmetry; apply mul_minus].
      etransitivity; [ | apply plus_left; symmetry; apply opp_plus].
      etransitivity; [ | apply commu_plus].
      symmetry; apply neutral_plus.
Qed.

Lemma Z_sound : forall G T r, sem_hseq (T :: G) === sem_hseq ((vec r HMR_zero ++ T) :: G).
Proof.
  intros [ | T2 G] T [ | r0 r].
  - reflexivity.
  - unfold sem_hseq.
    assert ((r0 :: r) <> nil) as H by now auto.
    symmetry.
    etransitivity; [ apply sem_seq_plus | ].
    etransitivity; [ apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ apply plus_left; apply mul_0 | ].
    etransitivity; [ apply commu_plus | ].
    apply neutral_plus.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    reflexivity.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    apply max_left.
    assert ((r0 :: r) <> nil) as H by now auto.
    symmetry.
    etransitivity; [ apply sem_seq_plus | ].
    etransitivity; [ apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ apply plus_left; apply mul_0 | ].
    etransitivity; [ apply commu_plus | ].
    apply neutral_plus.
Qed.
    
Lemma plus_sound : forall G T A B r, sem_hseq ((vec r A ++ vec r B ++ T) :: G) === sem_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  intros [ | T2 G] T A B r.
  - simpl in *.
    etransitivity; [ apply sem_seq_plus | ].
    etransitivity; [ apply plus_right; apply sem_seq_plus | ].
    etransitivity; [ | symmetry; apply sem_seq_plus].
    destruct r as [ | r0 r].
    + simpl.
      etransitivity; [ apply commu_plus | ].
      etransitivity; [ apply neutral_plus | ].
      etransitivity; [ apply commu_plus | ].
      etransitivity; [ apply neutral_plus | ].
      symmetry.
      etransitivity; [ apply commu_plus | ].
      apply neutral_plus.
    + assert ((r0 :: r) <> nil) as H by now auto.
      etransitivity; [ apply plus_left ; apply (sem_seq_vec _ _ H)|].
      etransitivity; [ apply plus_right; apply plus_left; apply (sem_seq_vec _ _ H)|].
      etransitivity; [ | apply plus_left; symmetry; apply (sem_seq_vec _ _ H)].
      etransitivity; [ | apply plus_left; symmetry; apply mul_distri_term].
      auto.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    apply max_left.
    etransitivity; [ apply sem_seq_plus | ].
    etransitivity; [ apply plus_right; apply sem_seq_plus | ].
    etransitivity; [ | symmetry; apply sem_seq_plus].
    destruct r as [ | r0 r].
    + simpl.
      etransitivity; [ apply commu_plus | ].
      etransitivity; [ apply neutral_plus | ].
      etransitivity; [ apply commu_plus | ].
      etransitivity; [ apply neutral_plus | ].
      symmetry.
      etransitivity; [ apply commu_plus | ].
      apply neutral_plus.
    + assert ((r0 :: r) <> nil) as H by now auto.
      etransitivity; [ apply plus_left ; apply (sem_seq_vec _ _ H)|].
      etransitivity; [ apply plus_right; apply plus_left; apply (sem_seq_vec _ _ H)|].
      etransitivity; [ | apply plus_left; symmetry; apply (sem_seq_vec _ _ H)].
      etransitivity; [ | apply plus_left; symmetry; apply mul_distri_term].
      auto.
Qed.

Lemma mul_sound : forall G T A r0 r, sem_hseq ((vec (mul_vec r0 r) A ++ T) :: G) === sem_hseq ((vec r (r0 *S A) ++ T) :: G).
Proof.
  intros [ | T2 G] T A r0 [ | r' r].
  - simpl; auto.
  - unfold sem_hseq.
    assert ((r' :: r) <> nil)as H by now auto.
    etransitivity; [ apply sem_seq_plus | ].
    etransitivity; [ apply plus_left; apply mul_vec_eq | ].
    etransitivity; [ apply plus_left; apply mul_right; apply (sem_seq_vec _ _ H) | ].
    etransitivity ; [ | symmetry; apply sem_seq_plus].
    etransitivity; [ | symmetry; apply plus_left; apply (sem_seq_vec _ _ H)].
    etransitivity; [ apply plus_left; apply mul_assoc | ].
    replace (time_pos r0 (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r' :: r)) (sum_vec_non_nil _ H))) with (time_pos (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r' :: r)) (sum_vec_non_nil _ H)) r0); auto.
    apply Rpos_eq; destruct r0; simpl; nra.
  - unfold mul_vec; unfold vec.
    reflexivity.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    apply max_left.
    assert ((r' :: r) <> nil)as H by now auto.
    etransitivity; [ apply sem_seq_plus | ].
    etransitivity; [ apply plus_left; apply mul_vec_eq | ].
    etransitivity; [ apply plus_left; apply mul_right; apply (sem_seq_vec _ _ H) | ].
    etransitivity ; [ | symmetry; apply sem_seq_plus].
    etransitivity; [ | symmetry; apply plus_left; apply (sem_seq_vec _ _ H)].
    etransitivity; [ apply plus_left; apply mul_assoc | ].
    replace (time_pos r0 (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r' :: r)) (sum_vec_non_nil _ H))) with (time_pos (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r' :: r)) (sum_vec_non_nil _ H)) r0); auto.
    apply Rpos_eq; destruct r0; simpl; nra.
Qed.        
  
Lemma max_sound : forall G T A B r, sem_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) === sem_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  intros [ | G T2] T A B [ | r0 r].
  - simpl.
    apply max_idempotence.
  - unfold sem_hseq.
    assert ((r0 :: r) <> nil)as H by now auto.
    etransitivity; [ apply max_left; apply sem_seq_plus | ].
    etransitivity; [ apply max_right; apply sem_seq_plus | ].
    etransitivity; [ | symmetry; apply sem_seq_plus].
    etransitivity; [ apply max_left; apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ apply max_right; apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ | symmetry ; apply plus_left; apply (sem_seq_vec _ _ H)].
    remember (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil _ H)) as sr.
    etransitivity; [ | apply plus_left; symmetry; apply mul_distri_max_pos].
    etransitivity; [ | symmetry; apply max_plus].
    apply commu_max.
  - unfold sem_hseq; fold (sem_hseq (G :: T2)).
    unfold vec; unfold app.
    etransitivity; [ apply asso_max | ].
    apply max_left; apply max_idempotence.
  - unfold sem_hseq; fold (sem_hseq (G :: T2)).
    etransitivity; [ apply asso_max | ].
    apply max_left.
    assert ((r0 :: r) <> nil)as H by now auto.
    etransitivity; [ apply max_left; apply sem_seq_plus | ].
    etransitivity; [ apply max_right; apply sem_seq_plus | ].
    etransitivity; [ | symmetry; apply sem_seq_plus].
    etransitivity; [ apply max_left; apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ apply max_right; apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ | symmetry ; apply plus_left; apply (sem_seq_vec _ _ H)].
    remember (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil _ H)) as sr.
    etransitivity; [ | apply plus_left; symmetry; apply mul_distri_max_pos].
    etransitivity; [ | symmetry; apply max_plus].
    apply commu_max.
Qed.

Lemma min_sound : forall G T A  B r, sem_hseq ((vec r A ++ T) :: G) /\S sem_hseq ((vec r B ++ T) :: G) === sem_hseq ((vec r (A /\S B) ++ T) :: G).
  intros [ | T2 G] T A B [ | r0 r].
  - simpl.
    apply leq_refl.
  - unfold sem_hseq.
    assert ((r0 :: r) <> nil)as H by now auto.
    etransitivity; [ apply min_left; apply sem_seq_plus | ].
    etransitivity; [ apply min_left; apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ apply min_right; apply sem_seq_plus | ].
    etransitivity; [ apply min_right; apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ | symmetry; apply sem_seq_plus ].
    etransitivity; [ | symmetry; apply plus_left; apply (sem_seq_vec _ _ H) ].
    remember (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil _ H)) as sr.
    etransitivity; [ | apply plus_left;symmetry; apply mul_distri_min_pos].
    symmetry; apply min_plus.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    unfold vec.
    apply leq_refl.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    etransitivity; [ symmetry; apply max_distri_min | ].
    apply max_left.
    assert ((r0 :: r) <> nil)as H by now auto.
    etransitivity; [ apply min_left; apply sem_seq_plus | ].
    etransitivity; [ apply min_left; apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ apply min_right; apply sem_seq_plus | ].
    etransitivity; [ apply min_right; apply plus_left; apply (sem_seq_vec _ _ H) | ].
    etransitivity; [ | symmetry; apply sem_seq_plus ].
    etransitivity; [ | symmetry; apply plus_left; apply (sem_seq_vec _ _ H) ].
    remember (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil _ H)) as sr.
    etransitivity; [ | apply plus_left;symmetry; apply mul_distri_min_pos].
    symmetry; apply min_plus.
Qed.

Lemma one_sound : forall G T r s, sum_vec s <= sum_vec r -> sem_hseq (T :: G) <== sem_hseq ((vec s HMR_coone ++ vec r HMR_one ++ T) :: G).
Proof.
  intros [ | T2 G] T r s H.
  - simpl.
    eapply leq_cong_r.
    { etransitivity; [ apply sem_seq_plus | ].
      apply plus_right; apply sem_seq_plus. }
    destruct r; destruct s.
    + simpl.
      eapply leq_cong_r; [ | apply leq_refl].
      etransitivity; [ apply commu_plus | ].
      etransitivity; [ apply neutral_plus | ].
      etransitivity; [ apply commu_plus | ].
      apply neutral_plus.
    + simpl in *.
      destruct r as [r Hr].
      exfalso; simpl in *.
      assert (0 <= sum_vec s).
      { clear; induction s as [ | [s Hs] vs]; simpl; try apply R_blt_lt in Hs; try nra. }
      apply R_blt_lt in Hr; nra.
    + assert (r :: r0 <> nil) as Hnnil by now auto.
      eapply leq_cong_r; [ apply plus_right; apply plus_left; apply (sem_seq_vec _ _ Hnnil) | ].
      eapply leq_cong_r.
      { etransitivity; [ apply commu_plus | ].
        apply neutral_plus. }
      eapply leq_cong_l ; [ symmetry; apply neutral_plus | ].
      eapply leq_cong_l ; [ apply commu_plus | ].
      apply leq_plus_cong; try apply leq_refl.
      eapply leq_cong_l; [ symmetry; apply mul_0 | ].
      apply mul_leq.
      apply one_pos.
    + assert (r :: r0 <> nil) as Hnnilr by now auto.
      assert (r1 :: s <> nil) as Hnnils by now auto.
      eapply leq_cong_r.
      { etransitivity.
        - apply plus_left.
          apply (sem_seq_vec _ _ Hnnils).
        - apply plus_right.
          apply plus_left.
          apply (sem_seq_vec _ _ Hnnilr). }
      eapply leq_cong_r; [ apply commu_plus | ].
      eapply leq_cong_r; [ apply plus_left; apply commu_plus | ].
      eapply leq_cong_r; [ symmetry; apply asso_plus | ].
      case_eq (sum_vec (r1 :: s) <? sum_vec (r :: r0)); intros H1; [ | apply R_blt_nlt in H1].
      * change (sum_vec (r :: r0)) with (projT1 (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil (r :: r0) Hnnilr))) in H1.
        change (sum_vec (r1 :: s)) with (projT1 (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil (r1 :: s) Hnnils))) in H1.
        apply R_blt_lt in H1.
        change HMR_coone with (-S HMR_one).
        eapply leq_cong_r ; [ apply plus_right; apply (minus_ax _ _ _ H1) | ].
        eapply leq_cong_l; [ symmetry; apply neutral_plus | ].
        apply leq_plus_cong; try apply leq_refl.
        eapply leq_cong_l ; [ symmetry; apply mul_0 | ].
        apply mul_leq; apply one_pos.
      * replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil (r1 :: s) Hnnils)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil (r :: r0) Hnnilr)).
        2:{ apply Rpos_eq; simpl in *.
            nra. }
        eapply leq_cong_r ; [ apply plus_right; apply opp_plus | ].
        eapply leq_cong_r; [ apply neutral_plus | ].
        apply leq_refl.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    apply max_leq.
    2:{ eapply leq_cong_r ; [ apply commu_max | ].
        apply leq_max. }
    eapply leq_trans; [ | apply leq_max ].
    eapply leq_cong_r.
    { etransitivity; [ apply sem_seq_plus | ].
      apply plus_right; apply sem_seq_plus. }
    destruct r; destruct s.
    + simpl.
      eapply leq_cong_r; [ | apply leq_refl].
      etransitivity; [ apply commu_plus | ].
      etransitivity; [ apply neutral_plus | ].
      etransitivity; [ apply commu_plus | ].
      apply neutral_plus.
    + simpl in *.
      destruct r as [r Hr].
      exfalso; simpl in *.
      assert (0 <= sum_vec s).
      { clear; induction s as [ | [s Hs] vs]; simpl; try apply R_blt_lt in Hs; try nra. }
      apply R_blt_lt in Hr; nra.
    + assert (r :: r0 <> nil) as Hnnil by now auto.
      eapply leq_cong_r; [ apply plus_right; apply plus_left; apply (sem_seq_vec _ _ Hnnil) | ].
      eapply leq_cong_r.
      { etransitivity; [ apply commu_plus | ].
        apply neutral_plus. }
      eapply leq_cong_l ; [ symmetry; apply neutral_plus | ].
      eapply leq_cong_l ; [ apply commu_plus | ].
      apply leq_plus_cong; try apply leq_refl.
      eapply leq_cong_l; [ symmetry; apply mul_0 | ].
      apply mul_leq.
      apply one_pos.
    + assert (r :: r0 <> nil) as Hnnilr by now auto.
      assert (r1 :: s <> nil) as Hnnils by now auto.
      eapply leq_cong_r.
      { etransitivity.
        - apply plus_left.
          apply (sem_seq_vec _ _ Hnnils).
        - apply plus_right.
          apply plus_left.
          apply (sem_seq_vec _ _ Hnnilr). }
      eapply leq_cong_r; [ apply commu_plus | ].
      eapply leq_cong_r; [ apply plus_left; apply commu_plus | ].
      eapply leq_cong_r; [ symmetry; apply asso_plus | ].
      case_eq (sum_vec (r1 :: s) <? sum_vec (r :: r0)); intros H1; [ | apply R_blt_nlt in H1].
      * change (sum_vec (r :: r0)) with (projT1 (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil (r :: r0) Hnnilr))) in H1.
        change (sum_vec (r1 :: s)) with (projT1 (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil (r1 :: s) Hnnils))) in H1.
        apply R_blt_lt in H1.
        change HMR_coone with (-S HMR_one).
        eapply leq_cong_r ; [ apply plus_right; apply (minus_ax _ _ _ H1) | ].
        eapply leq_cong_l; [ symmetry; apply neutral_plus | ].
        apply leq_plus_cong; try apply leq_refl.
        eapply leq_cong_l ; [ symmetry; apply mul_0 | ].
        apply mul_leq; apply one_pos.
      * replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil (r1 :: s) Hnnils)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil (r :: r0) Hnnilr)).
        2:{ apply Rpos_eq; simpl in *.
            nra. }
        eapply leq_cong_r ; [ apply plus_right; apply opp_plus | ].
        eapply leq_cong_r; [ apply neutral_plus | ].
        apply leq_refl.
Qed.
  
Lemma diamond_sound : forall T r s, sum_vec s <= sum_vec r -> HMR_zero <== sem_hseq ((vec s HMR_coone ++ vec r HMR_one ++ T) :: nil) -> HMR_zero <== sem_hseq ((vec s HMR_coone ++ vec r HMR_one ++ seq_diamond T) :: nil).
Proof.
  intros T r s H Hleq.
  simpl in *.
  apply leq_trans with (<S> (sem_seq (vec s HMR_coone ++ vec r HMR_one ++ T))).
  { apply leq_diamond; apply Hleq. }
  eapply leq_cong_l; [ symmetry; apply sem_seq_diamond | ].
  rewrite ? seq_diamond_app.
  rewrite <- ? vec_diamond.
  eapply leq_cong_l; [ apply sem_seq_plus | ].
  eapply leq_cong_l; [ apply plus_right; apply sem_seq_plus | ].
  eapply leq_cong_l ; [ apply asso_plus | ].
  eapply leq_cong_r; [ apply sem_seq_plus | ].
  eapply leq_cong_r; [ apply plus_right; apply sem_seq_plus | ].
  eapply leq_cong_r ; [ apply asso_plus | ].
  apply leq_plus_cong; try apply leq_refl.
  destruct r; destruct s.
  - apply leq_refl.
  - simpl in *.
    destruct r as [r Hr].
    exfalso; simpl in *.
    assert (0 <= sum_vec s).
    { clear; induction s as [ | [s Hs] vs]; simpl; try apply R_blt_lt in Hs; try nra. }
    clear Hleq; apply R_blt_lt in Hr; nra.
  - apply leq_plus_cong; try apply leq_refl.
    assert (r :: r0 <> nil) as Hnnil by now auto.
    eapply leq_cong_r; [ apply (sem_seq_vec _ _ Hnnil) | ].
    eapply leq_cong_l; [ apply (sem_seq_vec _ _ Hnnil) | ].
    apply mul_leq.
    apply diamond_one.
  - assert (r :: r0 <> nil) as Hnnilr by now auto.
    assert (r1 :: s <> nil) as Hnnils by now auto.
    eapply leq_cong_r ; [ apply plus_left; apply (sem_seq_vec _ _ Hnnils) | ].
    eapply leq_cong_r ; [ apply plus_right; apply (sem_seq_vec _ _ Hnnilr) | ].
    eapply leq_cong_l ; [ apply plus_left; apply (sem_seq_vec _ _ Hnnils) | ].
    eapply leq_cong_l ; [ apply plus_right; apply (sem_seq_vec _ _ Hnnilr) | ].
    eapply leq_cong_r; [ apply commu_plus | ].
    eapply leq_cong_l; [ apply commu_plus | ].
    case_eq (sum_vec (r1 :: s) <? sum_vec (r :: r0)); intros H1 ; [ apply R_blt_lt in H1 | apply R_blt_nlt in H1].
    + change (sum_vec (r :: r0)) with (projT1 (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil (r :: r0) Hnnilr))) in H1.
      change (sum_vec (r1 :: s)) with (projT1 (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil (r1 :: s) Hnnils))) in H1.
      change (HMR_coone) with (-S HMR_one).
      change (<S> (-S HMR_one)) with (-S (<S> HMR_one)).
      eapply leq_cong_l ; [ apply (minus_ax _ _ _ H1) | ].
      eapply leq_cong_r ; [ apply (minus_ax _ _ _ H1) | ].
      apply mul_leq.
      apply diamond_one.
    + replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil (r1 :: s) Hnnils)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil (r :: r0) Hnnilr)).
      2:{ apply Rpos_eq; simpl in *; nra. }
      eapply leq_cong_r; [ apply opp_plus | ].
      eapply leq_cong_l; [ apply opp_plus | ].
      apply leq_refl.
Qed.

(** ** HMR is sound *)
Lemma hmr_sound b : forall G, HMR b G -> HMR_zero <== sem_hseq G.
Proof with try assumption.
  intros G pi.
  induction pi.
  - apply leq_refl.
  - apply W_sound ; [now apply (@HMR_not_empty b) | ]...
  - eapply leq_cong_r; [ symmetry; apply C_sound | ].
    apply IHpi.
  - now apply S_sound.
  - now apply M_sound.
  - now apply T_sound with r.
  - change (HMR_covar n) with (-S (HMR_var n)); eapply leq_cong_r; [ symmetry; apply ext_ID_sound | ]; try assumption.
  - eapply leq_cong_r; [ symmetry; apply Z_sound | ]; try assumption.
  - eapply leq_cong_r; [ symmetry; apply plus_sound | ]; try assumption.
  - eapply leq_cong_r; [ symmetry; apply mul_sound | ]; try assumption.
  - eapply leq_cong_r; [ symmetry; apply max_sound | ]; try assumption.
  - eapply leq_cong_r; [ symmetry; apply min_sound | ].
    now apply leq_min.
  - eapply leq_trans ; [ apply IHpi | ].
    now apply one_sound.
  - now apply diamond_sound.
  - destruct G.
    + simpl in *; eapply leq_cong_r; [ symmetry; apply (sem_seq_permutation _ _ p)| ]; try assumption.
    + unfold sem_hseq in *; fold (sem_hseq (l :: G)) in *.
      eapply leq_cong_r; [ symmetry; apply max_left; apply (sem_seq_permutation _ _ p) | ]; try assumption.
  - eapply leq_cong_r; [ symmetry; apply (sem_hseq_permutation _ _ p) | ]; try assumption.
  - eapply leq_cong_r; [ apply ext_ID_sound | ]; try eassumption.
Qed.

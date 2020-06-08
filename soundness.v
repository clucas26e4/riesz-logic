Require Import Rpos.
Require Import term.
Require Import hseq.
Require Import semantic.
Require Import interpretation.

Require Import List.
Require Import Lra.
Require Import Permutation_more.
Local Open Scope R_scope.

(* TODO MOVING (to interpretation) *)
Lemma mul_vec_eq : forall A l r, sem_seq (vec (mul_vec l r) A) === r *S sem_seq (vec l A).
Proof.
  intros A.
  induction l; intros r.
  - simpl; rewrite mul_0; auto.
  - simpl.
    rewrite IHl.
    rewrite <-mul_assoc.
    rewrite mul_distri_term.
    reflexivity.
Qed.

(* all rules are sound *)

Lemma W_sound : forall G T, G <> nil ->  zero <== (sem_hseq G) -> zero <== sem_hseq (T :: G).
Proof with try assumption.
  intros G T notEmpty Hleq.
  destruct G; [ now exfalso | ].
  unfold sem_hseq; fold(sem_hseq (s :: G)).
  apply leq_trans with (sem_hseq (s :: G))...
  rewrite commu_max.
  now apply abso_min.
Qed.

Lemma C_sound : forall G T, sem_hseq (T :: T :: G) === sem_hseq (T :: G).
Proof with try assumption.
  intros G T.
  destruct G.
  - unfold sem_hseq.
    now auto with MGA_solver.
  - unfold sem_hseq; fold (sem_hseq (s :: G)).
    rewrite asso_max.
    now auto with MGA_solver.
Qed.

Lemma S_sound : forall G T1 T2, zero <== sem_hseq ((T1 ++ T2) :: G) -> zero <== sem_hseq (T1 :: T2 :: G).
Proof with try assumption.
  intros G T1 T2 Hleq.
  destruct G.
  - simpl in *.
    apply leq_div_2.
    rewrite mul_2.
    rewrite neutral_plus.
    rewrite sem_seq_plus in Hleq.
    apply leq_trans with (sem_seq T1 +S sem_seq T2)...
    now apply mean_prop.
  - unfold sem_hseq in *; fold (sem_hseq (l :: G)) in *. rewrite (sem_seq_plus T1 T2) in Hleq.
    rewrite asso_max.
    apply cond_zero_leq_max_2.
    apply leq_antisym.
    + apply leq_trans with (((plus_pos One One) *S  neg (sem_seq T1 \/S sem_seq T2)) /\S neg (sem_hseq (l :: G))).
      * apply leq_min.
        -- apply leq_trans with (neg (sem_seq T1 \/S sem_seq T2)); [auto with MGA_solver | ].
           rewrite mul_2.
           rewrite<- (neutral_plus (neg (sem_seq T1 \/S sem_seq T2))) at 1 4.
           rewrite commu_plus.
           apply leq_plus.
           now auto with MGA_solver.
        -- rewrite (commu_min (neg (sem_seq T1 \/S sem_seq T2))).
           now auto with MGA_solver.
      * apply leq_trans with (neg (sem_seq T1 +S sem_seq T2) /\S neg (sem_hseq (l :: G))).
        -- apply leq_min.
           ++ apply leq_trans with (plus_pos One One *S neg (sem_seq T1 \/S sem_seq T2)).
              ** now auto with MGA_solver.
              ** rewrite Rpos_mul_neg.
                 apply neg_leq_cond.
                 apply mean_prop.                 
           ++ rewrite (commu_min (plus_pos One One *S neg (sem_seq T1 \/S sem_seq T2)) (neg (sem_hseq (l :: G)))).
                now auto with MGA_solver.
        -- apply cond_min_neg_eq_zero in Hleq.
           rewrite Hleq.
             now auto with MGA_solver.
    + apply leq_min; now auto with MGA_solver.
Qed.

Lemma M_sound : forall G T1 T2, zero <== sem_hseq (T1 :: G) -> zero <== sem_hseq (T2 :: G) ->
                                zero <== sem_hseq ((T1 ++ T2) :: G).
Proof with try assumption.
  intros [ | T3 G ] T1 T2 Hleq1 Hleq2.
  - simpl in *.
    rewrite sem_seq_plus.
    rewrite <-(neutral_plus zero).
    apply leq_plus_cong...
  - unfold sem_hseq in *; fold (sem_hseq (T3 :: G)) in *; fold (sem_hseq (T3 :: G)) in *; fold (sem_hseq (T3 :: G)).
    rewrite sem_seq_plus.
    apply cond_zero_leq_max_2.
    apply leq_antisym.
    + eapply leq_trans.
      { apply leq_min.
        - eapply leq_trans.
          + apply min_leq.
          + apply neg_subdistri_plus.
        - rewrite (commu_min (neg (sem_seq T1 +S sem_seq T2))).
          apply min_leq. }
      (* NEED MOVING *)
      assert (forall A B C, zero <== A -> zero <== B -> zero <== C -> A +S B /\S C <== (A /\S C) +S (B /\S C)) as plus_pos_min.
      { clear.
        intros A B C H1 H2 H3.
        apply leq_plus_right.
        apply leq_min.
        - apply leq_minus_left.
          rewrite (commu_plus A (B /\S C)).
          apply leq_plus_right.
          apply leq_min.
          + apply leq_minus_left.
            rewrite (commu_plus B A).
            apply min_leq.
          + apply leq_trans with (A +S B /\S C).
            * apply leq_minus_left.
              rewrite <- (neutral_plus (A +S B /\S C)) at 1 3.
              apply leq_plus_cong...
              apply leq_refl.
            * rewrite (commu_min (A +S B) C).
              apply min_leq.
        - apply leq_minus_left.
          rewrite (commu_plus C (B /\S C)).
          apply leq_plus_right.
          apply leq_min.
          + apply leq_minus_left.
            rewrite (commu_plus B C).
            rewrite <-(neutral_plus (A +S B /\S C)).
            apply leq_plus_cong...
            rewrite (commu_min (A +S B) C).
            apply min_leq.
          + apply leq_minus_left.
            rewrite <-(neutral_plus (A +S B /\S C)).
            apply leq_plus_cong...
            rewrite (commu_min (A +S B) C).
            apply min_leq. }            
      eapply leq_trans.
      * apply plus_pos_min; apply zero_leq_neg.
      * rewrite <- (neutral_plus zero) at 5.
        apply leq_plus_cong; (rewrite cond_min_neg_eq_zero ; [ apply leq_refl | ])...
    + apply leq_min.
      * rewrite commu_max.
        apply leq_max.
      * rewrite commu_max.
        apply leq_max.
Qed.

Lemma T_sound :  forall G T r,
    zero <== sem_hseq (seq_mul r T :: G) ->
    zero <== sem_hseq (T :: G).
Proof with try assumption.
  intros [ | T2 G] T [r Hpos]; 
    remember (existT (fun r : R => (0 <? r)%R = true) r Hpos) as t; intros Hleq.
  - simpl in *; rewrite sem_seq_mul in Hleq.
    rewrite <-(mul_1 (sem_seq T)).
    replace One with (time_pos (inv_pos t) t).
    2:{ clear; apply Rpos_eq; destruct t; simpl; apply R_blt_lt in e; rewrite Rinv_l; nra. }
    rewrite <-mul_assoc.
    rewrite <-(min_max _ _ Hleq).
    rewrite commu_max.
    apply compa_mul_ax.
  - unfold sem_hseq in *; fold (sem_hseq (T2 :: G)) in *.
    apply cond_min_neg_eq_zero in Hleq.
    apply cond_zero_leq_max_2.
    apply leq_antisym.
    + rewrite sem_seq_mul in Hleq. rewrite <-Rpos_mul_neg in Hleq.
      case (Rlt_dec 1 r); intros Hlt; [ | case (Rlt_dec r 1); intros Hnlt].
      * rewrite <-Hleq at 3.
        apply leq_min.
        -- apply leq_trans with (neg (sem_seq T)); [ apply min_leq | ].
           rewrite <-(neutral_plus (neg (sem_seq T))) at 1 3.
           rewrite commu_plus.
           apply leq_plus_left.
           rewrite <-(mul_1 (neg (sem_seq T))) at 2.
           rewrite <-mul_minus.
           change (1%R) with (projT1 One) in Hlt.
           replace r with (projT1 t) in Hlt by now rewrite Heqt.
           rewrite (minus_ax _ _ _ Hlt).
           apply leq_cong_r with (minus_pos Hlt *S (pos (neg (sem_seq T)))).
           { rewrite (commu_max (neg (sem_seq T))).
             rewrite (@min_max _ (neg (sem_seq T))); auto with MGA_solver. }
           apply compa_mul_ax.
        -- rewrite (commu_min (neg (sem_seq T)) (neg (sem_hseq (T2 :: G)))).
           apply min_leq.
      * apply (@mul_leq_inv t).
        rewrite mul_distri_min_pos.
        rewrite mul_0.
        rewrite <-Hleq at 3.
        apply leq_min; [apply min_leq | ].
        rewrite (commu_min (t *S neg (sem_seq T)) (t *S neg (sem_hseq (T2 :: G)))).
        apply leq_trans with (t *S neg (sem_hseq (T2 :: G))) ; [ apply min_leq | ].
        rewrite <-(neutral_plus (t *S neg (sem_hseq (T2 :: G)))).
        rewrite commu_plus.
        apply leq_plus_left.
        rewrite <-(mul_1 (neg (sem_hseq (T2 :: G)))) at 1.
        rewrite <-mul_minus.
        change (1%R) with (projT1 One) in Hnlt.
        replace r with (projT1 t) in Hnlt by now rewrite Heqt.
        rewrite (minus_ax _ _ _ Hnlt).
        eapply leq_cong_r with (minus_pos Hnlt *S (pos (neg (sem_hseq (T2 :: G))))).
        { rewrite (commu_max (neg (sem_hseq (T2 :: G)))).
          rewrite (@min_max _ (neg (sem_hseq (T2 :: G)))); auto with MGA_solver. }
        apply compa_mul_ax.
      * assert (t = One) as Heq.
        { apply Rpos_eq; rewrite Heqt;simpl; nra. }
        rewrite <-Hleq at 3.
        rewrite Heq.
        rewrite mul_1.
        apply leq_refl.       
    + apply leq_min; rewrite commu_max; apply leq_max.
Qed.

Lemma ext_ID_sound : forall G T A r s,
    sum_vec r = sum_vec s -> sem_hseq (T :: G) === sem_hseq ((vec s (-S A) ++ vec r A ++ T) :: G).
Proof.
  intros [ | T2 G] T A r s Heq.
  - simpl.
    rewrite ?sem_seq_plus.
    rewrite asso_plus ; rewrite (commu_plus (sem_seq (vec s (-S A)))).
    destruct r; destruct s.
    + simpl in *.
      rewrite commu_plus ; rewrite 2 neutral_plus.
      reflexivity.
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
      rewrite (sem_seq_vec _ _ H1).
      rewrite (sem_seq_vec _ _ H2).
      replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil _ H1)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil _ H2)) by (apply Rpos_eq; simpl in *; nra).
      rewrite mul_minus; rewrite opp_plus.
      rewrite commu_plus; rewrite neutral_plus.
      reflexivity.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    destruct r; destruct s.
    + reflexivity.
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
    + rewrite ? sem_seq_plus.
      assert (r :: r0 <> nil) as H1 by now auto.
      assert (r1 :: s <> nil) as H2 by now auto.
      rewrite (sem_seq_vec _ _ H1).
      rewrite (sem_seq_vec _ _ H2).
      replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil _ H1)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil _ H2)) by (apply Rpos_eq; simpl in *; nra).
      rewrite <- (minus_minus A) at 2 4.
      rewrite (mul_minus _ (-S A)); rewrite asso_plus; rewrite mul_minus; rewrite opp_plus.
      rewrite commu_plus; rewrite neutral_plus.
      reflexivity.
Qed.

Lemma Z_sound : forall G T r, sem_hseq (T :: G) === sem_hseq ((vec r zero ++ T) :: G).
Proof.
  intros [ | T2 G] T [ | r0 r].
  - reflexivity.
  - unfold sem_hseq.
    assert ((r0 :: r) <> nil) as H by now auto.
    rewrite ?sem_seq_plus; rewrite ?(sem_seq_vec _ _ H).
    rewrite mul_0.
    rewrite commu_plus; rewrite neutral_plus; reflexivity.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    reflexivity.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    assert ((r0 :: r) <> nil) as H by now auto.
    rewrite ?sem_seq_plus ; rewrite ?(sem_seq_vec _ _ H).
    rewrite mul_0.
    rewrite commu_plus; rewrite neutral_plus; reflexivity.
Qed.
    
Lemma plus_sound : forall G T A B r, sem_hseq ((vec r A ++ vec r B ++ T) :: G) === sem_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  intros [ | T2 G] T A B r.
  - simpl in *.
    rewrite ?sem_seq_plus.
    destruct r as [ | r0 r].
    + simpl; repeat (rewrite commu_plus ; rewrite ?neutral_plus); auto.
    + assert ((r0 :: r) <> nil) as H by now auto.
      rewrite ? (sem_seq_vec _ _ H).
      rewrite mul_distri_term ; rewrite asso_plus.
      auto.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    destruct r as [ | r0 r].
    + simpl; repeat (rewrite commu_plus ; rewrite ?neutral_plus); auto.
    + assert ((r0 :: r) <> nil) as H by now auto.
      rewrite ? sem_seq_plus; rewrite ? (sem_seq_vec _ _ H).
      rewrite mul_distri_term; rewrite asso_plus.
      auto.
Qed.

Lemma mul_sound : forall G T A r0 r, sem_hseq ((vec (mul_vec r r0) A ++ T) :: G) === sem_hseq ((vec r (r0 *S A) ++ T) :: G).
Proof.
  intros [ | T2 G] T A r0 [ | r' r].
  - simpl; auto.
  - unfold sem_hseq.
    assert ((r' :: r) <> nil)as H by now auto.
    rewrite ?sem_seq_plus; rewrite  ?(sem_seq_vec _ _ H).
    rewrite mul_vec_eq ; rewrite (sem_seq_vec _ _ H).
    rewrite ?mul_assoc.
    replace (time_pos r0 (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r' :: r)) (sum_vec_non_nil _ H))) with (time_pos (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r' :: r)) (sum_vec_non_nil _ H)) r0); auto.
    apply Rpos_eq; destruct r0; simpl; nra.
  - unfold mul_vec; unfold vec.
    reflexivity.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    assert ((r' :: r) <> nil)as H by now auto.
    rewrite ?sem_seq_plus; rewrite  ?(sem_seq_vec _ _ H).
    rewrite mul_vec_eq ; rewrite (sem_seq_vec _ _ H).
    rewrite ?mul_assoc.
    replace (time_pos r0 (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r' :: r)) (sum_vec_non_nil _ H))) with (time_pos (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r' :: r)) (sum_vec_non_nil _ H)) r0); auto.
    apply Rpos_eq; destruct r0; simpl; nra.
Qed.        
  
Lemma max_sound : forall G T A B r, sem_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) === sem_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  intros [ | G T2] T A B [ | r0 r].
  - simpl.
    rewrite max_idempotence; auto.
  - unfold sem_hseq.
    assert ((r0 :: r) <> nil)as H by now auto.
    rewrite ?sem_seq_plus; rewrite  ?(sem_seq_vec _ _ H).
    remember (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil _ H)) as sr.
    rewrite mul_distri_max_pos.
    rewrite max_plus.
    rewrite commu_max.
    auto.
  - unfold sem_hseq; fold (sem_hseq (G :: T2)).
    unfold vec; unfold app.
    rewrite asso_max; rewrite max_idempotence.
    auto.
  - unfold sem_hseq; fold (sem_hseq (G :: T2)).
    assert ((r0 :: r) <> nil)as H by now auto.
    rewrite ?sem_seq_plus; rewrite  ?(sem_seq_vec _ _ H).
    remember (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil _ H)) as sr.
    rewrite asso_max.
    rewrite mul_distri_max_pos.
    rewrite max_plus.
    rewrite (commu_max (sr *S B +S sem_seq T)).
    auto.
Qed.

Lemma min_sound : forall G T A  B r, sem_hseq ((vec r A ++ T) :: G) /\S sem_hseq ((vec r B ++ T) :: G) === sem_hseq ((vec r (A /\S B) ++ T) :: G).
  intros [ | T2 G] T A B [ | r0 r].
  - simpl.
    apply leq_refl.
  - unfold sem_hseq.
    assert ((r0 :: r) <> nil)as H by now auto.
    rewrite ?sem_seq_plus; rewrite  ?(sem_seq_vec _ _ H).
    remember (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil _ H)) as sr.
    rewrite mul_distri_min_pos.
    rewrite min_plus.
    reflexivity.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    unfold vec.
    apply leq_refl.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    assert ((r0 :: r) <> nil)as H by now auto.
    rewrite ?sem_seq_plus; rewrite  ?(sem_seq_vec _ _ H).
    remember (existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil _ H)) as sr.
    rewrite mul_distri_min_pos.
    rewrite min_plus.
    rewrite max_distri_min.
    reflexivity.
Qed.    
                                                                           
Lemma hr_sound b : forall G, HR b G -> zero <== sem_hseq G.
Proof with try assumption.
  intros G pi.
  induction pi.
  - apply leq_refl.
  - apply W_sound ; [now apply (@HR_not_empty b) | ]...
  - now rewrite <-C_sound.
  - now apply S_sound.
  - now apply M_sound.
  - now apply T_sound with r.
  - change (covar n) with (-S (var n)); now rewrite <-ext_ID_sound.
  - now rewrite <-Z_sound.
  - now rewrite <-plus_sound.
  - now rewrite <-mul_sound.
  - now rewrite <-max_sound.
  - rewrite <-min_sound.
    now apply leq_min.
  - destruct G.
    + simpl in *; now rewrite <-(sem_seq_permutation _ _ p).
    + unfold sem_hseq in *; fold (sem_hseq (l :: G)) in *.
        now rewrite <-(sem_seq_permutation _ _ p).
  - now rewrite <-(sem_hseq_permutation _ _ p).
  - rewrite ext_ID_sound; [ apply IHpi | apply e ].
Qed.

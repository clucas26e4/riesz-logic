From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Rpos.
Require Import term.
Require Import hseq.
Require Import semantic.
Require Import interpretation.

Require Import List.
Require Import Lra.
Require Import Permutation_more.
Local Open Scope R_scope.

(* TODO MOVING (to semantic) *)

(* TODO MOVING (to hseq then elsewhere) *)
  
  
(* TODO MOVING (to interpretation) *)

(* all rules are sound *)
Lemma INIT_sound : zero <== sem_hseq (nil :: nil).
Proof.
  by apply leq_refl.
Qed.

Lemma W_sound : forall G T, G <> nil ->  zero <== (sem_hseq G) -> zero <== sem_hseq (T :: G).
Proof with try assumption.
  move => G T notEmpty Hleq.
  destruct G; [ by exfalso | ].
  rewrite /sem_hseq -/(sem_hseq (s :: G)).
  apply leq_trans with (sem_hseq (s :: G))...
  rewrite commu_max.
    by apply abso_min.
Qed.

Lemma C_sound : forall G T, zero <== sem_hseq (T :: T :: G) -> zero <== sem_hseq (T :: G).
Proof with try assumption.
  move => G T Hleq.
  destruct G.
  - rewrite /sem_hseq in Hleq |- *.
    apply leq_cong_r with (sem_seq T \/S sem_seq T)...
    by auto with MGA_solver.
  - move: Hleq; rewrite /sem_hseq-/(sem_hseq (s :: G)) => Hleq.
    move: Hleq; rewrite asso_max => Hleq.
    apply leq_cong_r with (sem_seq T \/S sem_seq T \/S sem_hseq (s :: G))...
    by auto with MGA_solver.
Qed.

Lemma S_sound : forall G T1 T2, zero <== sem_hseq ((T1 ++ T2) :: G) -> zero <== sem_hseq (T1 :: T2 :: G).
Proof with try assumption.
  move => G T1 T2 Hleq.
  destruct G.
  - simpl in *.
    apply leq_div_2.
    rewrite mul_2.
    rewrite neutral_plus.
    move: Hleq; rewrite sem_seq_plus => Hleq.
    apply leq_trans with (sem_seq T1 +S sem_seq T2)...
    by apply mean_prop.
  - move: Hleq; rewrite /sem_hseq-/(sem_hseq (l :: G)) sem_seq_plus => Hleq.
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
           by auto with MGA_solver.
        -- rewrite (commu_min (neg (sem_seq T1 \/S sem_seq T2))).
           by auto with MGA_solver.
      * apply leq_trans with (neg (sem_seq T1 +S sem_seq T2) /\S neg (sem_hseq (l :: G))).
        -- apply leq_min.
           ++ apply leq_trans with (plus_pos One One *S neg (sem_seq T1 \/S sem_seq T2)).
              ** by auto with MGA_solver.
              ** rewrite Rpos_mul_neg.
                 apply neg_leq_cond.
                 apply mean_prop.                 
           ++ rewrite (commu_min (plus_pos One One *S neg (sem_seq T1 \/S sem_seq T2)) (neg (sem_hseq (l :: G)))).
                by auto with MGA_solver.
        -- apply cond_min_neg_eq_zero in Hleq.
           rewrite Hleq.
             by auto with MGA_solver.
    + apply leq_min; by auto with MGA_solver.
Qed.

Lemma M_sound : forall G T1 T2, zero <== sem_hseq (T1 :: G) -> zero <== sem_hseq (T2 :: G) ->
                                zero <== sem_hseq ((T1 ++ T2) :: G).
Proof with try assumption.
  case => [ | T3 G ] T1 T2 Hleq1 Hleq2.
  - move: Hleq1 Hleq2; simpl => Hleq1 Hleq2.
    rewrite sem_seq_plus.
    rewrite <-(neutral_plus zero).
    apply leq_plus_cong...
  - move: Hleq1 Hleq2; rewrite -[sem_hseq (T1 :: T3 :: G)]/(sem_seq T1 \/S sem_hseq (T3 :: G)) -[sem_hseq (T2 :: T3 :: G)]/(sem_seq T2 \/S sem_hseq (T3 :: G)) -[sem_hseq ((T1 ++ T2) :: T3 :: G)]/(sem_seq (T1 ++ T2) \/S sem_hseq (T3 :: G)) => Hleq1 Hleq2.
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
      have plus_pos_min : forall A B C, zero <== A -> zero <== B -> zero <== C -> A +S B /\S C <== (A /\S C) +S (B /\S C).
      { clear.
        move => A B C H1 H2 H3.
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
              rewrite -{1 3}(neutral_plus (A +S B /\S C)).
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
            rewrite -(neutral_plus (A +S B /\S C)).
            apply leq_plus_cong...
            rewrite (commu_min (A +S B) C).
            apply min_leq.
          + apply leq_minus_left.
            rewrite -(neutral_plus (A +S B /\S C)).
            apply leq_plus_cong...
            rewrite (commu_min (A +S B) C).
            apply min_leq. }            
      eapply leq_trans.
      * apply plus_pos_min; apply zero_leq_neg.
      * rewrite - {5}(neutral_plus zero).
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
  case => [ | T2 G] T [r Hpos]; 
    set t := existT (fun r : R => (0 <? r)%R = true) r Hpos => Hleq.
  - move: Hleq; simpl; rewrite sem_seq_mul; move => Hleq.
    rewrite -(mul_1 (sem_seq T)).
    rewrite -(Rpos_inv_l t).
    rewrite -mul_assoc.
    rewrite -(min_max Hleq).
    rewrite commu_max.
    apply compa_mul_ax.
  -  move: Hleq. rewrite -[sem_hseq (seq_mul t T :: T2 :: G)]/(sem_seq (seq_mul t T) \/S sem_hseq (T2 :: G)) -[sem_hseq (T :: T2 :: G)]/(sem_seq T \/S sem_hseq (T2 :: G)) sem_seq_mul => Hleq.
     apply cond_min_neg_eq_zero in Hleq.
     apply cond_zero_leq_max_2.
     apply leq_antisym.
     + move: Hleq; rewrite -Rpos_mul_neg => Hleq.
       case (Rlt_dec 1 r) => Hlt; [ | case (Rlt_dec r 1) => Hnlt].
       * rewrite -{3}Hleq.
         apply leq_min.
         -- apply leq_trans with (neg (sem_seq T)); [ apply min_leq | ].
            rewrite -{1 3}(neutral_plus (neg (sem_seq T))).
            rewrite commu_plus.
            apply leq_plus_left.
            rewrite -{2}(mul_1 (neg (sem_seq T))).
            rewrite -mul_minus.
            change (1%R) with (projT1 One) in Hlt.
            change r with (projT1 t) in Hlt.
            rewrite (minus_ax _ Hlt).
            apply leq_cong_r with (minus_pos Hlt *S (pos (neg (sem_seq T)))).
            { rewrite (commu_max (neg (sem_seq T))).
              rewrite (@min_max _ (neg (sem_seq T))); auto with MGA_solver. }
            apply compa_mul_ax.
         -- rewrite {1 2}(commu_min (neg (sem_seq T)) (neg (sem_hseq (T2 :: G)))).
            apply min_leq.
       * apply (@mul_leq_inv t).
         rewrite mul_distri_min_pos.
         rewrite mul_0.
         rewrite -{3}Hleq.
         apply leq_min; [apply min_leq | ].
         rewrite (commu_min (t *S neg (sem_seq T)) (t *S neg (sem_hseq (T2 :: G)))).
         apply leq_trans with (t *S neg (sem_hseq (T2 :: G))) ; [ apply min_leq | ].
         rewrite -(neutral_plus (t *S neg (sem_hseq (T2 :: G)))).
         rewrite commu_plus.
         apply leq_plus_left.
         rewrite -{1}(mul_1 (neg (sem_hseq (T2 :: G)))).
         rewrite -mul_minus.
         change (1%R) with (projT1 One) in Hnlt.
         change r with (projT1 t) in Hnlt.
         rewrite (minus_ax _ Hnlt).
         eapply leq_cong_r with (minus_pos Hnlt *S (pos (neg (sem_hseq (T2 :: G))))).
         { rewrite (commu_max (neg (sem_hseq (T2 :: G)))).
           rewrite (@min_max _ (neg (sem_hseq (T2 :: G)))); auto with MGA_solver. }
         apply compa_mul_ax.
       * have Heq : t = One.
         { apply Rpos_eq; simpl.
           nra. }
         rewrite -{3}Hleq.
         rewrite Heq.
         rewrite mul_1.
         apply leq_refl.       
     + apply leq_min; rewrite commu_max; apply leq_max.
Qed.

Lemma ID_sound : forall G T n r s,
    sum_vec r = sum_vec s -> 
    zero <== sem_hseq (T :: G) ->
    zero <== sem_hseq ((vec s (covar n) ++ vec r (var n) ++ T) :: G).
Proof.
  move => [ | T2 G] T n r s Heq Hleq.
  - simpl.
    rewrite ?sem_seq_plus.
    rewrite asso_plus (commu_plus (sem_seq (vec s (covar n)))).
    destruct r; destruct s.
    + simpl in *.
      rewrite commu_plus neutral_plus neutral_plus.
      apply Hleq.
    + exfalso.
      destruct r ; simpl in *.
      apply R_blt_lt in e.
      pose H := (sum_vec_le_0 s).
      nra.
    + exfalso.
      destruct r ; simpl in *.
      apply R_blt_lt in e.
      pose H := (sum_vec_le_0 r0).
      nra.
    + have H1 : r :: r0 <> nil by auto.
      have H2 : r1 :: s <> nil by auto.
      rewrite (sem_seq_vec _ H1).
      rewrite (sem_seq_vec _ H2).
      replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil H1)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil H2)) by (apply Rpos_eq; simpl in *; nra).
      change (covar n) with (-S (var n)).
      rewrite mul_minus opp_plus.
      rewrite commu_plus neutral_plus.
      apply Hleq.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    have H : sem_seq (vec s (covar n) ++ vec r (var n) ++ T) === sem_seq T ; [ | rewrite H; clear H; apply Hleq].
    destruct r; destruct s.
    + reflexivity.
    + exfalso.
      destruct r ; simpl in *.
      apply R_blt_lt in e.
      pose H := (sum_vec_le_0 s).
      nra.
    + exfalso.
      destruct r ; simpl in *.
      apply R_blt_lt in e.
      pose H := (sum_vec_le_0 r0).
      nra.
    + have H1 : r :: r0 <> nil by auto.
      have H2 : r1 :: s <> nil by auto.
      rewrite 2?sem_seq_plus.
      rewrite (sem_seq_vec _ H1).
      rewrite (sem_seq_vec _ H2).
      replace (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r :: r0)) (sum_vec_non_nil H1)) with (existT (fun r2 : R => (0 <? r2) = true) (sum_vec (r1 :: s)) (sum_vec_non_nil H2)) by (apply Rpos_eq; simpl in *; nra).
      rewrite asso_plus.
      change (var n) with (-S (covar n)). 
      rewrite mul_minus opp_plus.
      rewrite commu_plus neutral_plus.
      reflexivity.
Qed.

Lemma plus_sound : forall G T A B r, zero <== sem_hseq ((vec r A ++ vec r B ++ T) :: G) -> zero <== sem_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  move => [ | T2 G] T A B r.
  - simpl in *.
    rewrite ?sem_seq_plus.
    destruct r as [ | r0 r].
    + simpl; repeat (rewrite commu_plus ?neutral_plus); auto.
    + have H : (r0 :: r) <> nil by auto.
      rewrite ? (sem_seq_vec _ H).
      rewrite mul_distri_term asso_plus.
      auto.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    destruct r as [ | r0 r].
    + simpl; repeat (rewrite commu_plus ?neutral_plus); auto.
    + have H : (r0 :: r) <> nil by auto.
      rewrite ? sem_seq_plus.
      rewrite ? (sem_seq_vec _ H).
      rewrite mul_distri_term asso_plus.
      auto.
Qed.

Lemma max_sound : forall G T A B r, zero <== sem_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) -> zero <== sem_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  move => [ | G T2] T A B [ | r0 r].
  - simpl.
    rewrite max_idempotence; auto.
  - unfold sem_hseq.
    have H : r0 :: r <> nil by auto.
    rewrite ?sem_seq_plus ?(sem_seq_vec _ H).
    set sr := existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil H).
    rewrite mul_distri_max_pos.
    rewrite max_plus.
    rewrite commu_max.
    auto.
  - unfold sem_hseq; fold (sem_hseq (G :: T2)).
    unfold vec; unfold app.
    rewrite asso_max; rewrite max_idempotence.
    auto.
  - unfold sem_hseq; fold (sem_hseq (G :: T2)).
    have H : r0 :: r <> nil by auto.
    rewrite ?sem_seq_plus ?(sem_seq_vec _ H).
    set sr := existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil H).
    rewrite asso_max.
    rewrite mul_distri_max_pos.
    rewrite max_plus.
    rewrite (commu_max (sr *S B +S sem_seq T)).
    auto.
Qed.

Lemma min_sound : forall G T A  B r, zero <== sem_hseq ((vec r A ++ T) :: G) -> zero <== sem_hseq ((vec r B ++ T) :: G) -> zero <== sem_hseq ((vec r (A /\S B) ++ T) :: G).
  move => [ | T2 G] T A B [ | r0 r].
  - simpl.
    auto.
  - unfold sem_hseq.
    have H : r0 :: r <> nil by auto.
    rewrite ?sem_seq_plus ?(sem_seq_vec _ H).
    set sr := existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil H).
    move => HA HB.
    rewrite mul_distri_min_pos.
    rewrite min_plus.
    apply leq_min; assumption.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    unfold vec.
    auto.
  - unfold sem_hseq; fold (sem_hseq (T2 :: G)).
    have H : r0 :: r <> nil by auto.
    rewrite ?sem_seq_plus ?(sem_seq_vec _ H).
    set sr := existT (fun r1 : R => (0 <? r1) = true) (sum_vec (r0 :: r)) (sum_vec_non_nil H).
    rewrite mul_distri_min_pos.
    rewrite min_plus.
    rewrite max_distri_min.
    move => HA HB.
    apply leq_min; assumption.
Qed.    
                                                                           
Lemma hr_sound : forall G, HR G -> zero <== sem_hseq G.
Proof with try assumption.
  move => G pi.
  induction pi.
  - by apply INIT_sound.
  - apply W_sound ; [by apply HR_not_empty | ]...
  - by apply C_sound.
  - by apply S_sound.
  - by apply M_sound.
  - by apply T_sound with r.
  - by apply ID_sound.
  - by apply plus_sound.
  - by apply max_sound.
  - by apply min_sound.
  - destruct G.
    + simpl in *; by rewrite -(sem_seq_permutation p).
    + unfold sem_hseq in *; fold (sem_hseq (l :: G)) in *.
        by rewrite -(sem_seq_permutation p).
  - by rewrite -(sem_hseq_permutation p).
Qed.

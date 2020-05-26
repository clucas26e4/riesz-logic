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

(* TODO MOVING (to semantic) *)
Lemma neg_leq_cond : forall A B, A <== B -> neg B <== neg A.
Proof with try assumption.
  move => A B Hleq.
  apply max_leq.
  - apply leq_trans with (-S A).
    + apply minus_reverse_leq...
    + apply leq_max.
  - auto with MGA_solver.
Qed.


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
    

Lemma hr_sound : forall G, HR G -> zero <== sem_hseq G.
Proof with try assumption.
  move => G pi.
  induction pi.
  - by apply INIT_sound.
  - apply W_sound ; [by apply HR_not_empty | ]...
  - by apply C_sound.
  - by apply S_sound.
  -

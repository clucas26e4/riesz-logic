Require Import Rpos.
Require Import term.
Require Import hseq.
Require Import semantic.
Require Import interpretation.
Require Import tactics.

Require Import List_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Lra.

Local Open Scope R_scope.

(* First formulation *)
                                                                   
Lemma completeness_1 : forall A B, A === B -> HR true (((One, -S B) :: (One, A) :: nil) :: nil)
with completeness_2 : forall A B, A === B -> HR true (((One, -S A) :: (One, B) :: nil) :: nil).
Proof with try assumption; try reflexivity.
  - intros A B Heq; destruct Heq.
    + change ((One, -S t) :: (One, t) :: nil) with ((vec (One :: nil) (-S t)) ++ (vec (One :: nil) t) ++ nil).
      apply ID_gen...
      apply INIT.
    + apply can with t2 (One :: nil) (One :: nil)...
      apply ex_seq with (((One, -S t2) :: (One, t1) :: nil) ++ ((One, -S t3) :: (One, t2) :: nil)); [ perm_Type_solve | ].
      apply M; [ apply (completeness_1 _ _ Heq1) | apply (completeness_1 _ _ Heq2)].
    + induction c.
      * apply completeness_1.
        apply Heq.
      * eapply ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_2.
        simpl; rewrite minus_minus; apply Heq.
      * simpl; change ((One, -S t) :: (One, t) :: nil) with ((vec (One :: nil) (-S t)) ++ (vec (One :: nil) t) ++ nil).
        apply ID_gen...
        apply INIT.
      * simpl.
        change ((One, covar n) :: (One, var n) :: nil) with ((vec (One :: nil) (covar n)) ++ (vec (One :: nil) (var n)) ++ nil).
        apply ID...
        apply INIT.
      * simpl.
        apply ex_seq with ((vec (One :: nil) (covar n)) ++ (vec (One :: nil) (var n)) ++ nil) ; [perm_Type_solve | ].
        apply ID...
        apply INIT.
      * simpl.
        change ((One, zero) :: (One, zero) :: nil) with ((vec (One:: One:: nil) zero) ++ nil).
        apply Z.
        apply INIT.
      * unfold evalContext; fold evalContext.
        unfold minus; fold minus.
        apply ex_seq with ((vec (One :: nil) (evalContext c1 t1 /\S evalContext c2 t1)) ++ (vec (One :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ nil) ; [ perm_Type_solve | ].
        apply min.
        -- apply ex_seq with  ((vec (One :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (One :: nil) (evalContext c1 t1)) ++ nil); [ perm_Type_solve | ].
           apply max.
           apply W.
           apply IHc1.
        -- apply ex_seq with  ((vec (One :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (One :: nil) (evalContext c2 t1)) ++ nil); [ perm_Type_solve | ].
           apply max.
           eapply ex_hseq ; [ apply Permutation_Type_swap | ].
           apply W.
           eapply ex_seq ; [ | apply IHc2].
           perm_Type_solve.
      * unfold evalContext; fold evalContext.
        unfold minus; fold minus.
        change ((One, -S evalContext c1 t2 /\S -S evalContext c2 t2)
                  :: (One, evalContext c1 t1 \/S evalContext c2 t1) :: nil) with
            ((vec (One ::nil) (-S evalContext c1 t2 /\S -S evalContext c2 t2)) ++ (vec (One ::nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ nil).
        apply min.
        -- apply ex_seq with  ((vec (One :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (One :: nil) (-S evalContext c1 t2)) ++ nil); [ perm_Type_solve | ].
           apply max.
           apply W.
           eapply ex_seq ; [ | apply IHc1].
           perm_Type_solve.
        -- apply ex_seq with  ((vec (One :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (One :: nil) (-S evalContext c2 t2)) ++ nil); [ perm_Type_solve | ].
           apply max.
           eapply ex_hseq ; [ apply Permutation_Type_swap | ].
           apply W.
           eapply ex_seq ; [ | apply IHc2].
           perm_Type_solve.
      * unfold evalContext; fold evalContext; unfold minus; fold minus.
        change ((One, (-S evalContext c1 t2) -S (evalContext c2 t2))
                  :: (One, evalContext c1 t1 +S evalContext c2 t1) :: nil)
          with ((vec (One :: nil) ((-S evalContext c1 t2) -S (evalContext c2 t2))) ++ (vec (One :: nil) (evalContext c1 t1 +S evalContext c2 t1)) ++ nil).
        apply plus.
        apply ex_seq with (vec (One :: nil) (evalContext c1 t1 +S evalContext c2 t1) ++
                               vec (One :: nil) (-S evalContext c1 t2) ++
                               vec (One :: nil) (-S evalContext c2 t2) ++ nil) ; [ perm_Type_solve | ].
        apply plus.
        apply ex_seq with (((One, -S evalContext c1 t2) :: (One, evalContext c1 t1) :: nil) ++ ((One, -S evalContext c2 t2) :: (One, evalContext c2 t1) :: nil)) ; [ perm_Type_solve | ].
        apply M...
      * unfold evalContext; fold evalContext; unfold minus; fold minus.
        change ((One, r *S (-S evalContext c t2)) :: (One, r *S evalContext c t1) :: nil) with ((vec (One :: nil) (r *S (-S evalContext c t2))) ++ (vec (One :: nil) (r *S evalContext c t1)) ++ nil).
        apply mul.
        apply ex_seq with (vec (One :: nil) (r *S evalContext c t1) ++ vec (mul_vec r (One :: nil)) (-S evalContext c t2) ++  nil) ; [ perm_Type_solve | ].
        apply mul.
        apply TR with (inv_pos r).
        simpl.
        replace (time_pos (inv_pos r) (time_pos r One)) with One; [ | destruct r; unfold One; apply Rpos_eq; simpl; rewrite <-Rmult_assoc;rewrite Rinv_l; apply R_blt_lt in e; nra].
        eapply ex_seq; [ | apply IHc].
        perm_Type_solve.
    + apply (completeness_2 _ _ Heq).
    + replace (((One, -S subs t2 n t) :: (One, subs t1 n t) :: nil) :: nil) with (subs_hseq (((One, -S t2) :: (One, t1) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_1; apply Heq.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ex_seq with ((vec (One :: nil) (-S t1)) ++ (vec (One :: nil) (t1)) ++ (vec (One :: nil) (-S t2)) ++ (vec (One :: nil) (t2)) ++ (vec (One :: nil) (-S t3)) ++ (vec (One :: nil) (t3)) ++ nil); [ perm_Type_solve | ].
      do 3 (apply ID_gen; try reflexivity).
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ex_seq with ((vec (One :: nil) (-S t1)) ++ (vec (One :: nil) (t1)) ++ (vec (One :: nil) (-S t2)) ++ (vec (One :: nil) (t2)) ++ nil); [ perm_Type_solve | ].
      do 2 (apply ID_gen; try reflexivity).
      apply INIT.
    + do_HR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply ID_gen...
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      pattern t at 1; rewrite <-(minus_minus t).
      rewrite<- ? app_assoc; apply ID_gen...
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      unfold mul_vec.
      replace (time_pos (minus_pos Hlt) One) with (minus_pos Hlt) by (apply Rpos_eq; destruct a; destruct b; unfold One; unfold minus_pos; unfold time_pos; simpl; nra).
      replace (time_pos a One) with a by (apply Rpos_eq; destruct a; unfold One; unfold time_pos; simpl; nra).
      replace (time_pos b One) with b by (apply Rpos_eq; destruct b; unfold One; unfold time_pos; simpl; nra).
      apply ex_seq with ((vec (minus_pos Hlt :: b :: nil) (-S t)) ++ (vec (a :: nil) t) ++ nil); [ perm_Type_solve | ].
      apply ID_gen ; [ | apply INIT ].
      simpl; destruct a; destruct b; unfold minus_pos.
      simpl; nra.
    + pattern t at 2; rewrite <- minus_minus.
      apply ex_seq with ((vec (One :: nil) (One *S (-S (-S t)))) ++ (vec (One :: nil) (-S t)) ++ nil); [ perm_Type_solve | ].
      apply mul.
      apply ID_gen; [ simpl; nra | apply INIT].
    + unfold minus; fold minus.
      do_HR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply ID_gen ; [ | apply INIT].
      unfold One; destruct x; destruct y; simpl.
      nra.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ex_seq with ((vec (mul_vec x (One :: nil)) (-S t1)) ++ (vec (mul_vec x (One :: nil)) ( t1)) ++ (vec (mul_vec x (One :: nil)) (-S t2))++ (vec (mul_vec x (One :: nil)) (t2)) ++ nil) ; [ perm_Type_solve | ].
      do 2 (apply ID_gen; try reflexivity).
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      unfold mul_vec.
      replace (time_pos (plus_pos x y) One) with (plus_pos x y) by (apply Rpos_eq; destruct x; destruct y; unfold One; unfold minus_pos; unfold time_pos; simpl; nra).
      replace (time_pos x One) with x by (apply Rpos_eq; destruct x; unfold One; unfold time_pos; simpl; nra).
      replace (time_pos y One) with y by (apply Rpos_eq; destruct y; unfold One; unfold time_pos; simpl; nra).
      apply ex_seq with ((vec (x :: y :: nil) (-S t)) ++ (vec (plus_pos x y :: nil) t) ++ nil) ; [ perm_Type_solve | ].
      apply ID_gen; [ | apply INIT].
      destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ID_gen ; [ | apply INIT].
      simpl; nra.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply W; apply W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply ID_gen...
        apply INIT.
      * apply W; eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W.
        pattern t2 at 1; rewrite <- (minus_minus).
        apply ID_gen...
        apply INIT.
      * eapply ex_hseq; [ apply Permutation_Type_swap | apply W ; eapply ex_hseq ; [ apply Permutation_Type_swap | apply W]].
        pattern t3 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * eapply ex_hseq; [ apply Permutation_Type_swap | ]; apply W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
      * apply W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
    + do_HR_logical.
      * apply W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
      * apply W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply W; eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W.
        apply ID_gen...
        apply INIT.
      * eapply ex_hseq; [ apply Permutation_Type_swap | ]; apply W; eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W.
        apply ID_gen...
        apply INIT.
      * apply W; apply W.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * eapply ex_hseq; [ apply Permutation_Type_swap | ]; apply W.
        apply ID_gen...
        apply INIT.
      * apply W.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * pattern t1 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
      * apply W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply W.
        rewrite <- app_assoc.
        apply ID_gen...
        pattern t3 at 1; rewrite<- minus_minus.
        apply ID_gen...
        apply INIT.
      * eapply ex_hseq; [ apply Permutation_Type_swap | ]; apply W.
        rewrite <-app_assoc; apply ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply ID_gen...
        apply INIT.
      * eapply ex_hseq; [ apply Permutation_Type_swap | ]; apply W.
        rewrite <-app_assoc; apply ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply INIT.
      * simpl.
        eapply ex_hseq ; [ apply Permutation_Type_swap | ].
        apply W.
        apply INIT.
  - intros A B Heq; destruct Heq.
    + HR_to_vec.
      apply ID_gen...
      apply INIT.
    + apply can with t2 (One :: nil) (One :: nil)...
      apply ex_seq with (((One, -S t1) :: (One, t2) :: nil) ++ ((One, -S t2) :: (One, t3) :: nil)); [ perm_Type_solve | ].
      apply M; [ apply (completeness_2 _ _ Heq1) | apply (completeness_2 _ _ Heq2)].
    + induction c.
      * apply completeness_2.
        apply Heq.
      * eapply ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_1.
        simpl; rewrite minus_minus; apply Heq.
      * simpl; HR_to_vec.
        apply ID_gen...
        apply INIT.
      * simpl.
        HR_to_vec.
        apply ID...
        apply INIT.
      * simpl.
        apply ex_seq with ((vec (One :: nil) (covar n)) ++ (vec (One :: nil) (var n)) ++ nil) ; [perm_Type_solve | ].
        apply ID...
        apply INIT.
      * simpl.
        do_HR_logical.
        apply INIT.
      * unfold evalContext; fold evalContext.
        unfold minus; fold minus.
        do_HR_logical.
        -- apply W.
           apply IHc1.
        -- eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W; apply IHc2.
      * unfold evalContext; fold evalContext.
        unfold minus; fold minus.
        do_HR_logical.
        -- apply W.
           simpl; eapply ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc1.
        -- eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W.
           eapply ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc2.
      * simpl. do_HR_logical.
        apply ex_seq with (((One, -S evalContext c1 t1) :: (One, evalContext c1 t2) :: nil) ++ ((One, -S evalContext c2 t1) :: (One, evalContext c2 t2) :: nil)) ; [ perm_Type_solve | ].
        apply M...
      * simpl; do_HR_logical.
        apply TR with (inv_pos r).
        simpl.
        replace (time_pos (inv_pos r) (time_pos r One)) with One; [ | destruct r; unfold One; apply Rpos_eq; simpl; rewrite <-Rmult_assoc;rewrite Rinv_l; apply R_blt_lt in e; nra].
        apply IHc.
    + apply (completeness_1 _ _ Heq).
    + replace (((One, -S subs t1 n t) :: (One, subs t2 n t) :: nil) :: nil) with (subs_hseq (((One, -S t1) :: (One, t2) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_2; apply Heq.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ex_seq with ((vec (One :: nil) (-S t1)) ++ (vec (One :: nil) (t1)) ++ (vec (One :: nil) (-S t2)) ++ (vec (One :: nil) (t2)) ++ (vec (One :: nil) (-S t3)) ++ (vec (One :: nil) (t3)) ++ nil); [ perm_Type_solve | ].
      do 3 (apply ID_gen; try reflexivity).
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ex_seq with ((vec (One :: nil) (-S t1)) ++ (vec (One :: nil) (t1)) ++ (vec (One :: nil) (-S t2)) ++ (vec (One :: nil) (t2)) ++ nil); [ perm_Type_solve | ].
      do 2 (apply ID_gen; try reflexivity).
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ID_gen...
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      rewrite minus_minus.
      rewrite<- ? app_assoc; apply ID_gen...
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      unfold mul_vec.
      replace (time_pos (minus_pos Hlt) One) with (minus_pos Hlt) by (apply Rpos_eq; destruct a; destruct b; unfold One; unfold minus_pos; unfold time_pos; simpl; nra).
      replace (time_pos a One) with a by (apply Rpos_eq; destruct a; unfold One; unfold time_pos; simpl; nra).
      replace (time_pos b One) with b by (apply Rpos_eq; destruct b; unfold One; unfold time_pos; simpl; nra).
      rewrite minus_minus.
      apply ex_seq with ((vec (a :: nil) (-S t)) ++ (vec (minus_pos Hlt :: b :: nil) t) ++ nil); [ perm_Type_solve | ].
      apply ID_gen ; [ | apply INIT ].
      simpl; destruct a; destruct b; unfold minus_pos.
      simpl; nra.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ID_gen; [ | apply INIT].
      simpl; nra.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ID_gen ; [ | apply INIT].
      unfold One; destruct x; destruct y; simpl.
      nra.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ex_seq with ((vec (mul_vec x (One :: nil)) (-S t1)) ++ (vec (mul_vec x (One :: nil)) ( t1)) ++ (vec (mul_vec x (One :: nil)) (-S t2))++ (vec (mul_vec x (One :: nil)) (t2)) ++ nil) ; [ perm_Type_solve | ].
      do 2 (apply ID_gen; try reflexivity).
      apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      unfold mul_vec.
      replace (time_pos (plus_pos x y) One) with (plus_pos x y) by (apply Rpos_eq; destruct x; destruct y; unfold One; unfold minus_pos; unfold time_pos; simpl; nra).
      replace (time_pos x One) with x by (apply Rpos_eq; destruct x; unfold One; unfold time_pos; simpl; nra).
      replace (time_pos y One) with y by (apply Rpos_eq; destruct y; unfold One; unfold time_pos; simpl; nra).
      apply ex_seq with ((vec (plus_pos x y :: nil) (-S t)) ++ (vec (x :: y :: nil) t) ++ nil) ; [ perm_Type_solve | ].
      apply ID_gen; [ | apply INIT].
      destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold minus; fold minus.
      do_HR_logical.
      apply ID_gen ; [ | apply INIT].
      simpl; nra.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply W; eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply ID_gen...
        apply INIT.
      * eapply ex_hseq; [ apply Permutation_Type_swap | apply W ; eapply ex_hseq ; [ apply Permutation_Type_swap | apply W]].
        pattern t2 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
      * apply W; apply W.
        pattern t3 at 1; rewrite <- (minus_minus).
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * eapply ex_hseq; [ apply Permutation_Type_swap | ]; apply W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
      * apply W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply ID_gen...
        apply INIT.
      * apply W.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply W; apply W.
        apply ID_gen...
        apply INIT.
      * apply W; eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W.
        apply ID_gen...
        apply INIT.
      * eapply ex_hseq; [ apply Permutation_Type_swap | ]; apply W; eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * eapply ex_hseq; [ apply Permutation_Type_swap | ]; apply W.
        apply ID_gen...
        apply INIT.
      * apply W.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply W.
        apply ID_gen...
        apply INIT.
      * apply W.
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      * apply W; apply W.
        apply ex_seq with ((vec (One :: nil) (-S t1)) ++ (vec (One :: nil) t1) ++ (vec (One :: nil) (-S t3)) ++ (vec (One :: nil) t3) ++ nil); [ perm_Type_solve | ].
        apply ID_gen...
        apply ID_gen...
        apply INIT.
      * apply W.
        eapply ex_hseq ; [ apply Permutation_Type_swap | ]; apply W.
        apply ex_seq with ((vec (One :: nil) (-S t2)) ++ (vec (One :: nil) t2) ++ (vec (One :: nil) (-S t3)) ++ (vec (One :: nil) t3) ++ nil); [ perm_Type_solve | ].
        apply ID_gen...
        apply ID_gen...
        apply INIT.
    + unfold minus; fold minus.
      do_HR_logical.
      simpl.
      eapply ex_hseq ; [ apply Permutation_Type_swap | ].
      apply W.
      apply INIT.
Qed.

(* Second formulation *)

Lemma HR_sem_seq : forall G T D,
    HR true (((One, sem_seq T) :: D) :: G) ->
    HR true ((T ++ D) :: G).
Proof.
  intros G T; revert G; induction T; intros G D pi.
  - simpl in *.
    apply Z_can_inv with (One :: nil).
    apply pi.
  - destruct a as (a , A).
    simpl in *.
    apply ex_seq with (T ++ (a , A) :: D); [ perm_Type_solve | ].
    apply IHT.
    replace a with (time_pos a One) by (destruct a; unfold One; apply Rpos_eq; simpl; nra).
    apply ex_seq with ((vec (mul_vec a (One :: nil)) A) ++ (vec (One :: nil) (sem_seq T)) ++ D) ; [ perm_Type_solve | ].
    apply mul_can_inv.
    apply plus_can_inv.
    apply pi.
Qed.

Lemma HR_sem_hseq : forall G H,
    H <> nil ->
    HR true (((One, sem_hseq H) :: nil) :: G) ->
    HR true (H ++ G).
Proof with try assumption; try reflexivity.
  intros G H Hnnil; revert G.
  induction H; [ now auto | ].
  rename a into T.
  intros G pi.
  destruct H as [ | T2 H ].
  - simpl in *.
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HR_sem_seq...
  - unfold sem_hseq in pi; fold (sem_hseq (T2 :: H)) in pi.
    change ((One, sem_seq T \/S sem_hseq (T2 :: H)) :: nil) with ((vec (One :: nil) (sem_seq T \/S sem_hseq (T2 :: H))) ++ nil) in pi.
    apply max_can_inv in pi.
    apply ex_hseq with ((T2 :: H) ++ (T :: G)); [ perm_Type_solve | ].
    apply IHlist; [ now auto | ].
    apply ex_hseq with (T :: ((One , sem_hseq (T2 :: H)) :: nil) :: G) ; [ perm_Type_solve | ].
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HR_sem_seq.
    eapply ex_hseq ; [ apply Permutation_Type_swap | apply pi].
Qed.

Lemma hr_complete : forall G,
    G <> nil ->
    zero <== sem_hseq G ->
    HR true G.
Proof with try assumption.
  intros G Hnnil Hleq.
  assert (pi := completeness_1 _ _ Hleq).
  replace G with (G ++ nil) by now rewrite app_nil_r.
  apply HR_sem_hseq...
  change ((One , sem_hseq G) :: nil) with ((vec (One :: nil) (sem_hseq G)) ++ nil).
  apply min_can_inv_r with zero.
  apply Z_can_inv with (One :: nil).
  apply pi.
Qed.

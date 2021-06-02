Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.riesz_logic_List_more.
Require Import RL.hr.term.
Require Import RL.hr.hseq.
Require Import RL.hr.hr.
Require Import RL.hr.semantic.
Require Import RL.hr.interpretation.
Require Import RL.hr.tech_lemmas.
Require Import RL.hr.lambda_prop_tools.
Require Import RL.hr.soundness.
Require Import RL.hr.tactics.

Require Import Lra.
Require Import Lia.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** ** First formulation : A = B implies |- 1.A,1.-B and |- 1.B, 1.-A are derivable *)
(** Proof of Lemma 4.20 *)
Lemma completeness_1 : forall A B r, A === B -> HR_M_can (((r, -S B) :: (r, A) :: nil) :: nil)
with completeness_2 : forall A B r, A === B -> HR_M_can (((r, -S A) :: (r, B) :: nil) :: nil).
Proof with try assumption; try reflexivity.
  - intros A B r Heq; destruct Heq.
    + change ((r, -S t) :: (r, t) :: nil) with ((vec (r :: nil) (-S t)) ++ (vec (r :: nil) t) ++ nil).
      apply hrr_ID_gen...
      apply hrr_INIT.
    + apply hrr_can with t2 (r :: nil) (r :: nil)...
      apply hrr_ex_seq with (((r, -S t2) :: (r, t1) :: nil) ++ ((r, -S t3) :: (r, t2) :: nil)); [ Permutation_Type_solve | ].
      apply hrr_M; try reflexivity; [ apply (completeness_1 _ _ _ Heq1) | apply (completeness_1 _ _ _ Heq2)].
    + revert r; induction c; (try rename r into r0); intros r.
      * apply completeness_1.
        apply Heq.
      * eapply hrr_ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_2.
        simpl; rewrite minus_minus; apply Heq.
      * simpl; change ((r, -S t) :: (r, t) :: nil) with ((vec (r :: nil) (-S t)) ++ (vec (r :: nil) t) ++ nil).
        apply hrr_ID_gen...
        apply hrr_INIT.
      * simpl.
        change ((r, RS_covar v) :: (r, RS_var v) :: nil) with ((vec (r :: nil) (RS_covar v)) ++ (vec (r :: nil) (RS_var v)) ++ nil).
        apply hrr_ID...
        apply hrr_INIT.
      * simpl.
        apply hrr_ex_seq with ((vec (r :: nil) (RS_covar v)) ++ (vec (r :: nil) (RS_var v)) ++ nil) ; [Permutation_Type_solve | ].
        apply hrr_ID...
        apply hrr_INIT.
      * simpl.
        change ((r, RS_zero) :: (r, RS_zero) :: nil) with ((vec (r:: r:: nil) RS_zero) ++ nil).
        apply hrr_Z.
        apply hrr_INIT.
      * unfold evalContext; fold evalContext.
        unfold RS_minus; fold RS_minus.
        apply hrr_ex_seq with ((vec (r :: nil) (evalContext c1 t1 /\S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ nil) ; [ Permutation_Type_solve | ].
        apply hrr_min.
        -- apply hrr_ex_seq with  ((vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (r :: nil) (evalContext c1 t1)) ++ nil); [ Permutation_Type_solve | ].
           apply hrr_max.
           apply hrr_W.
           apply IHc1.
        -- apply hrr_ex_seq with  ((vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (r :: nil) (evalContext c2 t1)) ++ nil); [ Permutation_Type_solve | ].
           apply hrr_max.
           eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
           apply hrr_W.
           eapply hrr_ex_seq ; [ | apply IHc2].
           Permutation_Type_solve.
      * unfold evalContext; fold evalContext.
        unfold RS_minus; fold RS_minus.
        change ((r, -S evalContext c1 t2 /\S -S evalContext c2 t2)
                  :: (r, evalContext c1 t1 \/S evalContext c2 t1) :: nil) with
            ((vec (r ::nil) (-S evalContext c1 t2 /\S -S evalContext c2 t2)) ++ (vec (r ::nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ nil).
        apply hrr_min.
        -- apply hrr_ex_seq with  ((vec (r :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c1 t2)) ++ nil); [ Permutation_Type_solve | ].
           apply hrr_max.
           apply hrr_W.
           eapply hrr_ex_seq ; [ | apply IHc1].
           Permutation_Type_solve.
        -- apply hrr_ex_seq with  ((vec (r :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c2 t2)) ++ nil); [ Permutation_Type_solve | ].
           apply hrr_max.
           eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
           apply hrr_W.
           eapply hrr_ex_seq ; [ | apply IHc2].
           Permutation_Type_solve.
      * unfold evalContext; fold evalContext; unfold RS_minus; fold RS_minus.
        change ((r, (-S evalContext c1 t2) -S (evalContext c2 t2))
                  :: (r, evalContext c1 t1 +S evalContext c2 t1) :: nil)
          with ((vec (r :: nil) ((-S evalContext c1 t2) -S (evalContext c2 t2))) ++ (vec (r :: nil) (evalContext c1 t1 +S evalContext c2 t1)) ++ nil).
        apply hrr_plus.
        apply hrr_ex_seq with (vec (r :: nil) (evalContext c1 t1 +S evalContext c2 t1) ++
                               vec (r :: nil) (-S evalContext c1 t2) ++
                               vec (r :: nil) (-S evalContext c2 t2) ++ nil) ; [ Permutation_Type_solve | ].
        apply hrr_plus.
        apply hrr_ex_seq with (((r, -S evalContext c1 t2) :: (r, evalContext c1 t1) :: nil) ++ ((r, -S evalContext c2 t2) :: (r, evalContext c2 t1) :: nil)) ; [ Permutation_Type_solve | ].
        apply hrr_M; try reflexivity; [ apply IHc1 | apply IHc2].
      * unfold evalContext; fold evalContext; unfold RS_minus; fold RS_minus.
        change ((r, r0 *S (-S evalContext c t2)) :: (r, r0 *S evalContext c t1) :: nil) with ((vec (r :: nil) (r0 *S (-S evalContext c t2))) ++ (vec (r :: nil) (r0 *S evalContext c t1)) ++ nil).
        apply hrr_mul.
        apply hrr_ex_seq with (vec (r :: nil) (r0 *S evalContext c t1) ++ vec (mul_vec r0 (r :: nil)) (-S evalContext c t2) ++  nil) ; [ Permutation_Type_solve | ].
        apply hrr_mul.
        simpl.
        eapply hrr_ex_seq; [ | apply IHc].
        Permutation_Type_solve.
    + apply (completeness_2 _ _ _ Heq).
    + replace (((r, -S subs t2 n t) :: (r, subs t1 n t) :: nil) :: nil) with (subs_hseq (((r, -S t2) :: (r, t1) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_1; apply Heq.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can. do_HR_logical.
      apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) (t3)) ++ nil); [ Permutation_Type_solve | ].
      do 3 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ nil); [ Permutation_Type_solve | ].
      do 2 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold HR_M_can; do_HR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply hrr_ID_gen...
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      pattern t at 1; rewrite <-(minus_minus t).
      rewrite<- ? app_assoc; apply hrr_ID_gen...
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      unfold mul_vec.
      apply hrr_ex_seq with ((vec ((time_pos (minus_pos Hlt) r) ::(time_pos b r) :: nil) (-S t)) ++ (vec ((time_pos a r) :: nil) t) ++ nil); [ Permutation_Type_solve | ].
      apply hrr_ID_gen ; [ | apply hrr_INIT ].
      simpl; destruct a; destruct b; destruct r; unfold minus_pos.
      simpl; nra.
    + pattern t at 2; rewrite <- minus_minus.
      apply hrr_ex_seq with ((vec (r :: nil) (One *S (-S (-S t)))) ++ (vec (r :: nil) (-S t)) ++ nil); [ Permutation_Type_solve | ].
      apply hrr_mul.
      apply hrr_ID_gen; [ destruct r; simpl; nra | apply hrr_INIT].
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply hrr_ID_gen ; [ | apply hrr_INIT].
      destruct r; destruct x; destruct y; simpl.
      nra.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (mul_vec x (r :: nil)) (-S t1)) ++ (vec (mul_vec x (r :: nil)) ( t1)) ++ (vec (mul_vec x (r :: nil)) (-S t2))++ (vec (mul_vec x (r :: nil)) (t2)) ++ nil) ; [ Permutation_Type_solve | ].
      do 2 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      unfold mul_vec.
      apply hrr_ex_seq with ((vec ((time_pos x r) :: (time_pos y r) :: nil) (-S t)) ++ (vec (time_pos (plus_pos x y) r :: nil) t) ++ nil) ; [ Permutation_Type_solve | ].
      apply hrr_ID_gen; [ | apply hrr_INIT].
      destruct r; destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen ; [ | apply hrr_INIT].
      simpl; nra.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; apply hrr_W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        pattern t2 at 1; rewrite <- (minus_minus).
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | apply hrr_W ; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | apply hrr_W]].
        pattern t3 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold HR_M_can; do_HR_logical.
      * apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W.
        rewrite <- app_assoc.
        apply hrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        rewrite <-app_assoc; apply hrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        rewrite <-app_assoc; apply hrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_INIT.
      * simpl.
        eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
        apply hrr_W.
        apply hrr_INIT.
  - intros A B r Heq; destruct Heq.
    + unfold HR_M_can; HR_to_vec.
      apply hrr_ID_gen...
      apply hrr_INIT.
    + apply hrr_can with t2 (r :: nil) (r :: nil)...
      apply hrr_ex_seq with (((r, -S t1) :: (r, t2) :: nil) ++ ((r, -S t2) :: (r, t3) :: nil)); [ Permutation_Type_solve | ].
      apply hrr_M; try reflexivity; [ apply (completeness_2 _ _ _ Heq1) | apply (completeness_2 _ _ _ Heq2)].
    + revert r;induction c; try (rename r into r0); intros r.
      * apply completeness_2.
        apply Heq.
      * eapply hrr_ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_1.
        simpl; rewrite minus_minus; apply Heq.
      * unfold HR_M_can; simpl; HR_to_vec.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * simpl; unfold HR_M_can; HR_to_vec.
        apply hrr_ID...
        apply hrr_INIT.
      * simpl.
        apply hrr_ex_seq with ((vec (r :: nil) (RS_covar v)) ++ (vec (r :: nil) (RS_var v)) ++ nil) ; [Permutation_Type_solve | ].
        apply hrr_ID...
        apply hrr_INIT.
      * simpl.
        unfold HR_M_can; do_HR_logical.
        apply hrr_INIT.
      * unfold evalContext; fold evalContext.
        unfold RS_minus; fold RS_minus.
        unfold HR_M_can; do_HR_logical.
        -- apply hrr_W.
           apply IHc1.
        -- eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W; apply IHc2.
      * unfold evalContext; fold evalContext.
        unfold RS_minus; fold RS_minus.
        unfold HR_M_can; do_HR_logical.
        -- apply hrr_W.
           simpl; eapply hrr_ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc1.
        -- eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
           eapply hrr_ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc2.
      * simpl. unfold HR_M_can; do_HR_logical.
        apply hrr_ex_seq with (((r, -S evalContext c1 t1) :: (r, evalContext c1 t2) :: nil) ++ ((r, -S evalContext c2 t1) :: (r, evalContext c2 t2) :: nil)) ; [ Permutation_Type_solve | ].
        apply hrr_M; try reflexivity; [apply IHc1 | apply IHc2].
      * simpl; unfold HR_M_can; do_HR_logical.
        apply IHc.
    + apply (completeness_1 _ _ _ Heq).
    + replace (((r, -S subs t1 n t) :: (r, subs t2 n t) :: nil) :: nil) with (subs_hseq (((r, -S t1) :: (r, t2) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_2; apply Heq.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) (t3)) ++ nil); [ Permutation_Type_solve | ].
      do 3 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ nil); [ Permutation_Type_solve | ].
      do 2 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen...
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      rewrite minus_minus.
      rewrite<- ? app_assoc; apply hrr_ID_gen...
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      unfold mul_vec.
      rewrite minus_minus.
      apply hrr_ex_seq with ((vec (time_pos a r :: nil) (-S t)) ++ (vec (time_pos (minus_pos Hlt) r :: time_pos b r :: nil) t) ++ nil); [ Permutation_Type_solve | ].
      apply hrr_ID_gen ; [ | apply hrr_INIT ].
      destruct r; destruct a; destruct b; unfold minus_pos.
      simpl; nra.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen; [ | apply hrr_INIT].
      destruct r; simpl; nra.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen ; [ | apply hrr_INIT].
      destruct r; destruct x; destruct y; simpl.
      nra.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ex_seq with ((vec (mul_vec x (r :: nil)) (-S t1)) ++ (vec (mul_vec x (r :: nil)) ( t1)) ++ (vec (mul_vec x (r :: nil)) (-S t2))++ (vec (mul_vec x (r :: nil)) (t2)) ++ nil) ; [ Permutation_Type_solve | ].
      do 2 (apply hrr_ID_gen; try reflexivity).
      apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      unfold mul_vec.
      apply hrr_ex_seq with ((vec (time_pos (plus_pos x y) r :: nil) (-S t)) ++ (vec (time_pos x r :: time_pos y r :: nil) t) ++ nil) ; [ Permutation_Type_solve | ].
      apply hrr_ID_gen; [ | apply hrr_INIT].
      destruct r; destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      apply hrr_ID_gen ; [ | apply hrr_INIT].
      simpl; nra.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | apply hrr_W ; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | apply hrr_W]].
        pattern t2 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W; apply hrr_W.
        pattern t3 at 1; rewrite <- (minus_minus).
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W; eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      * apply hrr_W; apply hrr_W.
        apply hrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) t1) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) t3) ++ nil); [ Permutation_Type_solve | ].
        apply hrr_ID_gen...
        apply hrr_ID_gen...
        apply hrr_INIT.
      * apply hrr_W.
        eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hrr_W.
        apply hrr_ex_seq with ((vec (r :: nil) (-S t2)) ++ (vec (r :: nil) t2) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) t3) ++ nil); [ Permutation_Type_solve | ].
        apply hrr_ID_gen...
        apply hrr_ID_gen...
        apply hrr_INIT.
    + unfold RS_minus; fold RS_minus.
      unfold HR_M_can; do_HR_logical.
      simpl.
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hrr_W.
      apply hrr_INIT.
Qed.

(** ** Second formulation *)
(** We use the can rule and the M rule to go from a proof |- 1.G to a proof of G *)
Lemma HR_sem_seq P : forall G T D,
    HR P (((One, sem_seq T) :: D) :: G) ->
    HR (hr_frag_add_CAN (hr_frag_add_M P)) ((T ++ D) :: G).
Proof.
  intros G T; revert P G; induction T; intros P G D pi.
  - simpl in *.
    apply hrr_Z_can_inv with (One :: nil).
    apply HR_le_frag with P; [ | apply pi].
    apply add_M_le_frag.
  - destruct a as (a , A).
    simpl in *.
    apply hrr_ex_seq with (T ++ (a , A) :: D); [ Permutation_Type_solve | ].
    apply (IHT (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_CAN (hr_frag_add_M P))))).
    replace a with (time_pos a One) by (destruct a; unfold One; apply Rpos_eq; simpl; nra).
    apply hrr_ex_seq with ((vec (mul_vec a (One :: nil)) A) ++ (vec (One :: nil) (sem_seq T)) ++ D) ; [ Permutation_Type_solve | ].
    apply hrr_mul_can_inv.
    apply hrr_plus_can_inv.
    apply pi.
Qed.

Lemma HR_sem_hseq P : forall G H,
    H <> nil ->
    HR P (((One, sem_hseq H) :: nil) :: G) ->
    HR (hr_frag_add_CAN (hr_frag_add_M P)) (H ++ G).
Proof with try assumption; try reflexivity.
  intros G H Hnnil; revert P G.
  induction H; [ now auto | ].
  rename a into T.
  intros P G pi.
  destruct H as [ | T2 H ].
  - simpl in *.
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HR_sem_seq...
  - unfold sem_hseq in pi; fold (sem_hseq (T2 :: H)) in pi.
    change ((One, sem_seq T \/S sem_hseq (T2 :: H)) :: nil) with ((vec (One :: nil) (sem_seq T \/S sem_hseq (T2 :: H))) ++ nil) in pi.
    apply hrr_max_can_inv in pi.
    apply hrr_ex_hseq with ((T2 :: H) ++ (T :: G)); [ Permutation_Type_solve | ].
    apply HR_le_frag with (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_CAN (hr_frag_add_M P)))))).
    { destruct P; repeat split; Bool.destr_bool. }
    refine (IHlist _ (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_CAN (hr_frag_add_M P)))) (T :: G) _) ; [ now auto | ].
    apply hrr_ex_hseq with (T :: ((One , sem_hseq (T2 :: H)) :: nil) :: G) ; [ Permutation_Type_solve | ].
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HR_sem_seq.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply pi.
Qed.

(** Proof of the completeness of the system of HR - hr_complete return a T free proof of G *)
Lemma hr_complete : forall G,
    G <> nil ->
    RS_zero <== sem_hseq G ->
    HR_M_can G.
Proof with try assumption.
  intros G Hnnil Hleq.
  assert (pi := completeness_1 _ _ One Hleq).
  replace G with (G ++ nil) by now rewrite app_nil_r.
  apply (@HR_sem_hseq hr_frag_M_can)...
  change ((One , sem_hseq G) :: nil) with ((vec (One :: nil) (sem_hseq G)) ++ nil).
  apply (@hrr_min_can_inv_r hr_frag_M_can) with RS_zero.
  apply (@hrr_Z_can_inv hr_frag_M_can) with (One :: nil)...
Qed.

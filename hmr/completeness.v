(** * Implementation of Section 4.4 *)
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.riesz_logic_List_more.
Require Import RL.hmr.term.
Require Import RL.hmr.hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.semantic.
Require Import RL.hmr.interpretation.
Require Import RL.hmr.tactics.
Require Import RL.hmr.tech_lemmas.
Require Import RL.hmr.lambda_prop_tools.
Require Import RL.hmr.soundness.

Require Import Lra.
Require Import Lia.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(** ** First formulation : A = B implies |- 1.A,1.-B and |- 1.B, 1.-A are derivable *)
(** Proof of Lemma 4.20 *)
Lemma completeness_1 : forall A B r, A === B -> HMR_M_can (((r, -S B) :: (r, A) :: nil) :: nil)
with completeness_2 : forall A B r, A === B -> HMR_M_can (((r, -S A) :: (r, B) :: nil) :: nil).
Proof with try assumption; try reflexivity.
  - intros A B r Heq; destruct Heq.
    + change ((r, -S t) :: (r, t) :: nil) with ((vec (r :: nil) (-S t)) ++ (vec (r :: nil) t) ++ nil).
      apply hmrr_ID_gen...
      apply hmrr_INIT.
    + apply hmrr_can with t2 (r :: nil) (r :: nil)...
      apply hmrr_ex_seq with (((r, -S t2) :: (r, t1) :: nil) ++ ((r, -S t3) :: (r, t2) :: nil)); [ Permutation_Type_solve | ].
      apply hmrr_M; try reflexivity; [ apply (completeness_1 _ _ _ Heq1) | apply (completeness_1 _ _ _ Heq2)].
    + revert r; induction c; (try rename r into r0); intros r.
      * apply completeness_1.
        apply Heq.
      * eapply hmrr_ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_2.
        simpl; rewrite minus_minus; apply Heq.
      * simpl; change ((r, -S t) :: (r, t) :: nil) with ((vec (r :: nil) (-S t)) ++ (vec (r :: nil) t) ++ nil).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * simpl.
        change ((r, HMR_covar v) :: (r, HMR_var v) :: nil) with ((vec (r :: nil) (HMR_covar v)) ++ (vec (r :: nil) (HMR_var v)) ++ nil).
        apply hmrr_ID...
        apply hmrr_INIT.
      * simpl.
        apply hmrr_ex_seq with ((vec (r :: nil) (HMR_covar v)) ++ (vec (r :: nil) (HMR_var v)) ++ nil) ; [Permutation_Type_solve | ].
        apply hmrr_ID...
        apply hmrr_INIT.
      * simpl.
        change ((r, HMR_zero) :: (r, HMR_zero) :: nil) with ((vec (r:: r:: nil) HMR_zero) ++ nil).
        apply hmrr_Z.
        apply hmrr_INIT.
      * unfold evalContext; fold evalContext.
        unfold HMR_minus; fold HMR_minus.
        apply hmrr_ex_seq with ((vec (r :: nil) (evalContext c1 t1 /\S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ nil) ; [ Permutation_Type_solve | ].
        apply hmrr_min.
        -- apply hmrr_ex_seq with  ((vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (r :: nil) (evalContext c1 t1)) ++ nil); [ Permutation_Type_solve | ].
           apply hmrr_max.
           apply hmrr_W.
           apply IHc1.
        -- apply hmrr_ex_seq with  ((vec (r :: nil) (-S evalContext c1 t2 \/S -S evalContext c2 t2)) ++ (vec (r :: nil) (evalContext c2 t1)) ++ nil); [ Permutation_Type_solve | ].
           apply hmrr_max.
           eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
           apply hmrr_W.
           eapply hmrr_ex_seq ; [ | apply IHc2].
           Permutation_Type_solve.
      * unfold evalContext; fold evalContext.
        unfold HMR_minus; fold HMR_minus.
        change ((r, -S evalContext c1 t2 /\S -S evalContext c2 t2)
                  :: (r, evalContext c1 t1 \/S evalContext c2 t1) :: nil) with
            ((vec (r ::nil) (-S evalContext c1 t2 /\S -S evalContext c2 t2)) ++ (vec (r ::nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ nil).
        apply hmrr_min.
        -- apply hmrr_ex_seq with  ((vec (r :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c1 t2)) ++ nil); [ Permutation_Type_solve | ].
           apply hmrr_max.
           apply hmrr_W.
           eapply hmrr_ex_seq ; [ | apply IHc1].
           Permutation_Type_solve.
        -- apply hmrr_ex_seq with  ((vec (r :: nil) (evalContext c1 t1 \/S evalContext c2 t1)) ++ (vec (r :: nil) (-S evalContext c2 t2)) ++ nil); [ Permutation_Type_solve | ].
           apply hmrr_max.
           eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
           apply hmrr_W.
           eapply hmrr_ex_seq ; [ | apply IHc2].
           Permutation_Type_solve.
      * unfold evalContext; fold evalContext; unfold HMR_minus; fold HMR_minus.
        change ((r, (-S evalContext c1 t2) -S (evalContext c2 t2))
                  :: (r, evalContext c1 t1 +S evalContext c2 t1) :: nil)
          with ((vec (r :: nil) ((-S evalContext c1 t2) -S (evalContext c2 t2))) ++ (vec (r :: nil) (evalContext c1 t1 +S evalContext c2 t1)) ++ nil).
        apply hmrr_plus.
        apply hmrr_ex_seq with (vec (r :: nil) (evalContext c1 t1 +S evalContext c2 t1) ++
                               vec (r :: nil) (-S evalContext c1 t2) ++
                               vec (r :: nil) (-S evalContext c2 t2) ++ nil) ; [ Permutation_Type_solve | ].
        apply hmrr_plus.
        apply hmrr_ex_seq with (((r, -S evalContext c1 t2) :: (r, evalContext c1 t1) :: nil) ++ ((r, -S evalContext c2 t2) :: (r, evalContext c2 t1) :: nil)) ; [ Permutation_Type_solve | ].
        apply hmrr_M; try reflexivity; [ apply IHc1 | apply IHc2].
      * unfold evalContext; fold evalContext; unfold HMR_minus; fold HMR_minus.
        change ((r, r0 *S (-S evalContext c t2)) :: (r, r0 *S evalContext c t1) :: nil) with ((vec (r :: nil) (r0 *S (-S evalContext c t2))) ++ (vec (r :: nil) (r0 *S evalContext c t1)) ++ nil).
        apply hmrr_mul.
        apply hmrr_ex_seq with (vec (r :: nil) (r0 *S evalContext c t1) ++ vec (mul_vec r0 (r :: nil)) (-S evalContext c t2) ++  nil) ; [ Permutation_Type_solve | ].
        apply hmrr_mul.
        simpl.
        eapply hmrr_ex_seq; [ | apply IHc].
        Permutation_Type_solve.
      * simpl.
        change ((r, HMR_coone) :: (r, HMR_one) :: nil) with (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
        apply hmrr_one; [ | apply hmrr_INIT].
        simpl; nra.
      * eapply hmrr_ex_seq;  [ apply Permutation_Type_swap | ].
        simpl.
        change ((r, HMR_coone) :: (r, HMR_one) :: nil) with (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
        apply hmrr_one; [ | apply hmrr_INIT].
        simpl; nra.
      * simpl in *.
        change ((r, <S> (-S evalContext c t2)) :: (r, <S> evalContext c t1) :: nil) with (seq_diamond ((r , (-S evalContext c t2)) :: (r , evalContext c t1) :: nil)).
        apply hmrr_diamond_no_one.
        apply IHc.
    + apply (completeness_2 _ _ _ Heq).
    + replace (((r, -S subs t2 n t) :: (r, subs t1 n t) :: nil) :: nil) with (subs_hseq (((r, -S t2) :: (r, t1) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_1; apply Heq.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can. do_HMR_logical.
      apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) (t3)) ++ nil); [ Permutation_Type_solve | ].
      do 3 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ nil); [ Permutation_Type_solve | ].
      do 2 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_M_can; do_HMR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply hmrr_ID_gen...
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      pattern t at 1; rewrite <-(minus_minus t).
      rewrite<- ? app_assoc; apply hmrr_ID_gen...
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      unfold mul_vec.
      apply hmrr_ex_seq with ((vec ((time_pos (minus_pos Hlt) r) ::(time_pos b r) :: nil) (-S t)) ++ (vec ((time_pos a r) :: nil) t) ++ nil); [ Permutation_Type_solve | ].
      apply hmrr_ID_gen ; [ | apply hmrr_INIT ].
      simpl; destruct a; destruct b; destruct r; unfold minus_pos.
      simpl; nra.
    + pattern t at 2; rewrite <- minus_minus.
      apply hmrr_ex_seq with ((vec (r :: nil) (One *S (-S (-S t)))) ++ (vec (r :: nil) (-S t)) ++ nil); [ Permutation_Type_solve | ].
      apply hmrr_mul.
      apply hmrr_ID_gen; [ destruct r; simpl; nra | apply hmrr_INIT].
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      pattern t at 1; rewrite <- minus_minus.
      apply hmrr_ID_gen ; [ | apply hmrr_INIT].
      destruct r; destruct x; destruct y; simpl.
      nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (mul_vec x (r :: nil)) (-S t1)) ++ (vec (mul_vec x (r :: nil)) ( t1)) ++ (vec (mul_vec x (r :: nil)) (-S t2))++ (vec (mul_vec x (r :: nil)) (t2)) ++ nil) ; [ Permutation_Type_solve | ].
      do 2 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      unfold mul_vec.
      apply hmrr_ex_seq with ((vec ((time_pos x r) :: (time_pos y r) :: nil) (-S t)) ++ (vec (time_pos (plus_pos x y) r :: nil) t) ++ nil) ; [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; [ | apply hmrr_INIT].
      destruct r; destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen ; [ | apply hmrr_INIT].
      simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; apply hmrr_W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        pattern t2 at 1; rewrite <- (minus_minus).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | apply hmrr_W ; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | apply hmrr_W]].
        pattern t3 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W.
        rewrite <- app_assoc.
        apply hmrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        rewrite <-app_assoc; apply hmrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        rewrite <-app_assoc; apply hmrr_ID_gen...
        pattern t3 at 1; rewrite<- minus_minus; apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_INIT.
      * simpl.
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
        apply hmrr_W.
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      change (vec (r :: nil) (<S> (-S t1)) ++ vec (r :: nil) (<S> (-S t2)) ++ vec (r :: nil) (<S> (t1 +S t2)) ++ nil)
        with
          (seq_diamond (vec (r :: nil) (-S t1) ++ vec (r :: nil) (-S t2) ++ vec (r :: nil) (t1 +S t2) ++ nil)).
      apply hmrr_diamond_no_one.
      do_HMR_logical.
      apply hmrr_ex_seq with (vec (r :: nil) (-S t2) ++ vec (r :: nil) t2 ++ vec (r :: nil) (-S t1) ++ vec (r :: nil) t1 ++ nil); [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      change (vec (mul_vec r0 (r :: nil)) (<S> (-S t)) ++ vec (r :: nil) (<S> (r0 *S t)) ++ nil)
        with
          (seq_diamond (vec (mul_vec r0 (r :: nil)) (-S t) ++ vec (r :: nil) (r0 *S t) ++ nil)).
      apply hmrr_diamond_no_one.
      do_HMR_logical.
      pattern t at 1.
      rewrite <- minus_minus.
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * change (<S> HMR_one) with (-S (<S> HMR_coone)).
        apply hmrr_ID_gen; try reflexivity.
        apply hmrr_INIT.
      * rewrite app_nil_r.
        change (vec (r :: nil) HMR_one ++ vec (r :: nil) (<S> HMR_coone))
          with
            (vec nil HMR_coone ++ vec (r :: nil) HMR_one ++ seq_diamond (vec (r :: nil) (HMR_coone))).
        apply hmrr_diamond.
        { destruct r as [r Hr]; simpl; apply R_blt_lt in Hr; nra. }
        change HMR_one with (-S HMR_coone).
        rewrite app_nil_l; rewrite <- (app_nil_r (vec (r :: nil) HMR_coone)).
        apply hmrr_ID_gen; try reflexivity.
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical ; try apply hmrr_INIT.
      change (vec (r :: nil) (<S> pos t) ++ nil) with (seq_diamond (vec (r :: nil) (pos t) ++ nil)).
      apply hmrr_diamond_no_one.
      do_HMR_logical; simpl.
      eapply hmrr_ex_hseq;  [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical ; try apply hmrr_INIT.
      change (vec (r :: nil) HMR_one ++ nil)
        with (vec nil HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
      apply hmrr_one; try apply hmrr_INIT.
      destruct r as [r Hr]; simpl.
      apply R_blt_lt in Hr; nra.
  - intros A B r Heq; destruct Heq.
    + unfold HMR_M_can; HMR_to_vec.
      apply hmrr_ID_gen...
      apply hmrr_INIT.
    + apply hmrr_can with t2 (r :: nil) (r :: nil)...
      apply hmrr_ex_seq with (((r, -S t1) :: (r, t2) :: nil) ++ ((r, -S t2) :: (r, t3) :: nil)); [ Permutation_Type_solve | ].
      apply hmrr_M; try reflexivity; [ apply (completeness_2 _ _ _ Heq1) | apply (completeness_2 _ _ _ Heq2)].
    + revert r;induction c; try (rename r into r0); intros r.
      * apply completeness_2.
        apply Heq.
      * eapply hmrr_ex_seq ; [ apply Permutation_Type_swap | ].
        apply completeness_1.
        simpl; rewrite minus_minus; apply Heq.
      * unfold HMR_M_can; simpl; HMR_to_vec.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * simpl; unfold HMR_M_can; HMR_to_vec.
        apply hmrr_ID...
        apply hmrr_INIT.
      * simpl.
        apply hmrr_ex_seq with ((vec (r :: nil) (HMR_covar v)) ++ (vec (r :: nil) (HMR_var v)) ++ nil) ; [Permutation_Type_solve | ].
        apply hmrr_ID...
        apply hmrr_INIT.
      * simpl.
        unfold HMR_M_can; do_HMR_logical.
        apply hmrr_INIT.
      * unfold evalContext; fold evalContext.
        unfold HMR_minus; fold HMR_minus.
        unfold HMR_M_can; do_HMR_logical.
        -- apply hmrr_W.
           apply IHc1.
        -- eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W; apply IHc2.
      * unfold evalContext; fold evalContext.
        unfold HMR_minus; fold HMR_minus.
        unfold HMR_M_can; do_HMR_logical.
        -- apply hmrr_W.
           simpl; eapply hmrr_ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc1.
        -- eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
           eapply hmrr_ex_seq ; [ apply Permutation_Type_swap | ].
           apply IHc2.
      * simpl. unfold HMR_M_can; do_HMR_logical.
        apply hmrr_ex_seq with (((r, -S evalContext c1 t1) :: (r, evalContext c1 t2) :: nil) ++ ((r, -S evalContext c2 t1) :: (r, evalContext c2 t2) :: nil)) ; [ Permutation_Type_solve | ].
        apply hmrr_M; try reflexivity; [apply IHc1 | apply IHc2].
      * simpl; unfold HMR_M_can; do_HMR_logical.
        apply IHc.
      * simpl.
        change ((r, HMR_coone) :: (r, HMR_one) :: nil) with (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
        apply hmrr_one; [ | apply hmrr_INIT].
        simpl; nra.
      * eapply hmrr_ex_seq;  [ apply Permutation_Type_swap | ].
        simpl.
        change ((r, HMR_coone) :: (r, HMR_one) :: nil) with (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil).
        apply hmrr_one; [ | apply hmrr_INIT].
        simpl; nra.
      * simpl in *.
        change ((r, <S> (-S evalContext c t1)) :: (r, <S> evalContext c t2) :: nil) with (seq_diamond ((r , (-S evalContext c t1)) :: (r , evalContext c t2) :: nil)).
        apply hmrr_diamond_no_one.
        apply IHc.
    + apply (completeness_1 _ _ _ Heq).
    + replace (((r, -S subs t1 n t) :: (r, subs t2 n t) :: nil) :: nil) with (subs_hseq (((r, -S t1) :: (r, t2) :: nil) :: nil) n t) by now rewrite <-eq_subs_minus.
      apply subs_proof.
      apply completeness_2; apply Heq.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) (t3)) ++ nil); [ Permutation_Type_solve | ].
      do 3 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) (t1)) ++ (vec (r :: nil) (-S t2)) ++ (vec (r :: nil) (t2)) ++ nil); [ Permutation_Type_solve | ].
      do 2 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen...
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      rewrite minus_minus.
      rewrite<- ? app_assoc; apply hmrr_ID_gen...
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      unfold mul_vec.
      rewrite minus_minus.
      apply hmrr_ex_seq with ((vec (time_pos a r :: nil) (-S t)) ++ (vec (time_pos (minus_pos Hlt) r :: time_pos b r :: nil) t) ++ nil); [ Permutation_Type_solve | ].
      apply hmrr_ID_gen ; [ | apply hmrr_INIT ].
      destruct r; destruct a; destruct b; unfold minus_pos.
      simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen; [ | apply hmrr_INIT].
      destruct r; simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen ; [ | apply hmrr_INIT].
      destruct r; destruct x; destruct y; simpl.
      nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with ((vec (mul_vec x (r :: nil)) (-S t1)) ++ (vec (mul_vec x (r :: nil)) ( t1)) ++ (vec (mul_vec x (r :: nil)) (-S t2))++ (vec (mul_vec x (r :: nil)) (t2)) ++ nil) ; [ Permutation_Type_solve | ].
      do 2 (apply hmrr_ID_gen; try reflexivity).
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      unfold mul_vec.
      apply hmrr_ex_seq with ((vec (time_pos (plus_pos x y) r :: nil) (-S t)) ++ (vec (time_pos x r :: time_pos y r :: nil) t) ++ nil) ; [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; [ | apply hmrr_INIT].
      destruct r; destruct x; destruct y; unfold plus_pos; simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ID_gen ; [ | apply hmrr_INIT].
      simpl; nra.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        pattern t1 at 1; rewrite <- (minus_minus).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | apply hmrr_W ; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | apply hmrr_W]].
        pattern t2 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W; apply hmrr_W.
        pattern t3 at 1; rewrite <- (minus_minus).
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        pattern t1 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        pattern t2 at 1; rewrite <- minus_minus.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W; eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      * apply hmrr_W; apply hmrr_W.
        apply hmrr_ex_seq with ((vec (r :: nil) (-S t1)) ++ (vec (r :: nil) t1) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) t3) ++ nil); [ Permutation_Type_solve | ].
        apply hmrr_ID_gen...
        apply hmrr_ID_gen...
        apply hmrr_INIT.
      * apply hmrr_W.
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]; apply hmrr_W.
        apply hmrr_ex_seq with ((vec (r :: nil) (-S t2)) ++ (vec (r :: nil) t2) ++ (vec (r :: nil) (-S t3)) ++ (vec (r :: nil) t3) ++ nil); [ Permutation_Type_solve | ].
        apply hmrr_ID_gen...
        apply hmrr_ID_gen...
        apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      simpl.
      eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with (seq_diamond (vec (r :: nil) ((-S t1) -S t2) ++ vec (r :: nil) t1 ++ vec (r :: nil) t2 ++ nil)) ; [ Permutation_Type_solve | ].
      apply hmrr_diamond_no_one.
      apply hmrr_plus.
      apply hmrr_ex_seq with (vec (r :: nil) (-S t2) ++ vec (r :: nil) t2 ++ vec (r :: nil) (-S t1) ++ vec (r :: nil) t1 ++ nil) ; [ Permutation_Type_solve | ].
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_ex_seq with (seq_diamond (vec (r :: nil) (r0 *S (-S t)) ++ vec (mul_vec r0 (r :: nil)) t ++ nil)); [Permutation_Type_solve | ].
      apply hmrr_diamond_no_one; apply hmrr_mul.
      apply hmrr_ID_gen; try reflexivity.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      apply hmrr_W.
      change (vec (r :: nil) (<S> HMR_coone) ++ vec (r :: nil) (<S> HMR_one) ++ nil)
        with (seq_diamond (vec (r :: nil) HMR_coone ++ vec (r :: nil) HMR_one ++ nil)).
      apply hmrr_diamond_no_one.
      apply hmrr_one; simpl; try nra.
      apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      simpl.
      eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hmrr_W; apply hmrr_INIT.
    + unfold HMR_minus; fold HMR_minus.
      unfold HMR_M_can; do_HMR_logical.
      simpl.
      eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply hmrr_INIT.
Qed.

(** ** Second formulation *)
(** We use the can rule and the M rule to go from a proof |- 1.G to a proof of G *)
Lemma HMR_sem_seq P : forall G T D,
    HMR P (((One, sem_seq T) :: D) :: G) ->
    HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) ((T ++ D) :: G).
Proof.
  intros G T; revert P G; induction T; intros P G D pi.
  - simpl in *.
    apply hmrr_Z_can_inv with (One :: nil).
    apply HMR_le_frag with P; [ | apply pi].
    apply add_M_le_frag.
  - destruct a as (a , A).
    simpl in *.
    apply hmrr_ex_seq with (T ++ (a , A) :: D); [ Permutation_Type_solve | ].
    apply (IHT (hmr_frag_add_CAN (hmr_frag_add_M (hmr_frag_add_CAN (hmr_frag_add_M P))))).
    replace a with (time_pos a One) by (destruct a; unfold One; apply Rpos_eq; simpl; nra).
    apply hmrr_ex_seq with ((vec (mul_vec a (One :: nil)) A) ++ (vec (One :: nil) (sem_seq T)) ++ D) ; [ Permutation_Type_solve | ].
    apply hmrr_mul_can_inv.
    apply hmrr_plus_can_inv.
    apply pi.
Qed.

Lemma HMR_sem_hseq P : forall G H,
    H <> nil ->
    HMR P (((One, sem_hseq H) :: nil) :: G) ->
    HMR (hmr_frag_add_CAN (hmr_frag_add_M P)) (H ++ G).
Proof with try assumption; try reflexivity.
  intros G H Hnnil; revert P G.
  induction H; [ now auto | ].
  rename a into T.
  intros P G pi.
  destruct H as [ | T2 H ].
  - simpl in *.
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HMR_sem_seq...
  - unfold sem_hseq in pi; fold (sem_hseq (T2 :: H)) in pi.
    change ((One, sem_seq T \/S sem_hseq (T2 :: H)) :: nil) with ((vec (One :: nil) (sem_seq T \/S sem_hseq (T2 :: H))) ++ nil) in pi.
    apply hmrr_max_can_inv in pi.
    apply hmrr_ex_hseq with ((T2 :: H) ++ (T :: G)); [ Permutation_Type_solve | ].
    apply HMR_le_frag with (hmr_frag_add_CAN (hmr_frag_add_M (hmr_frag_add_CAN (hmr_frag_add_M (hmr_frag_add_CAN (hmr_frag_add_M P)))))).
    { destruct P; repeat split; Bool.destr_bool. }
    refine (IHlist _ (hmr_frag_add_CAN (hmr_frag_add_M (hmr_frag_add_CAN (hmr_frag_add_M P)))) (T :: G) _) ; [ now auto | ].
    apply hmrr_ex_hseq with (T :: ((One , sem_hseq (T2 :: H)) :: nil) :: G) ; [ Permutation_Type_solve | ].
    replace T with (T ++ nil) by now rewrite app_nil_r.
    apply HMR_sem_seq.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply pi.
Qed.

(** Proof of the completeness of the system of HMR - hmr_complete return a T free proof of G *)
Lemma hmr_complete : forall G,
    G <> nil ->
    HMR_zero <== sem_hseq G ->
    HMR_M_can G.
Proof with try assumption.
  intros G Hnnil Hleq.
  assert (pi := completeness_1 _ _ One Hleq).
  replace G with (G ++ nil) by now rewrite app_nil_r.
  apply (@HMR_sem_hseq hmr_frag_M_can)...
  change ((One , sem_hseq G) :: nil) with ((vec (One :: nil) (sem_hseq G)) ++ nil).
  apply (@hmrr_min_can_inv_r hmr_frag_M_can) with HMR_zero.
  apply (@hmrr_Z_can_inv hmr_frag_M_can) with (One :: nil)...
Qed.

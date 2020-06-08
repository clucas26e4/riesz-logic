Require Import Rpos.
Require Import term.
Require Import hseq.

Require Import List.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Lra.

Lemma plus_can_inv : forall G T A B r, HR true ((vec r (A +S B) ++ T) :: G) -> HR true ((vec r A ++ vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply can with (A +S B) r r; try reflexivity.
  apply ex_seq with ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) ++ (vec r (A +S B) ++ T)); [ perm_Type_solve | ].
  apply M; [ | apply pi].
  apply ex_hseq with (G ++ ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) :: nil)); [ perm_Type_solve | ].
  apply W_gen.
  unfold minus; fold (-S A); fold (-S B).
  apply plus.
  apply ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B); [ perm_Type_solve | ].
  apply ID_gen; try reflexivity.
  replace (vec r (-S B) ++ vec r B) with (vec r (-S B) ++ vec r B ++ nil) by (now rewrite app_nil_r).
  apply ID_gen; [ reflexivity | apply INIT ].
Qed.

Lemma Z_can_inv : forall G T r, HR true ((vec r zero ++ T) :: G) -> HR true (T :: G).
Proof.
  intros G T r pi.
  apply can with zero r r; try reflexivity.
  apply Z.
  apply pi.
Qed.
  
Lemma mul_can_inv : forall G T A r0 r, HR true ((vec r (r0 *S A) ++ T) :: G) -> HR true ((vec (mul_vec r r0) A ++ T) :: G).
Proof.
  intros G T A r0 r pi.
  apply can with (r0 *S A) r r; try reflexivity.
  apply ex_seq with ((vec r (-S (r0 *S A)) ++ vec (mul_vec r r0) A) ++ (vec r (r0 *S A) ++ T)); [ perm_Type_solve | ].
  apply M; [ | apply pi ].
  apply ex_hseq with (G ++ ((vec r (-S (r0 *S A)) ++ vec (mul_vec r r0) A) :: nil)); [ perm_Type_solve | ].
  apply W_gen.
  unfold minus; fold minus.
  apply mul.
  replace (vec (mul_vec r r0) (-S A) ++ vec (mul_vec r r0) A) with (vec (mul_vec r r0) (-S A) ++ vec (mul_vec r r0) A ++ nil) by (now rewrite app_nil_r).
  apply ID_gen ; [ reflexivity | ].
  apply INIT.
Qed.

Lemma max_can_inv : forall G T A B r, HR true ((vec r (A \/S B) ++ T) :: G) -> HR true ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply can with (A \/S B) r r; try reflexivity.
  apply ex_seq with ( (vec r (-S (A \/S B)) ++ vec r B) ++ (vec r (A \/S B) ++ T)); [perm_Type_solve | ].
  apply M.
  2:{ eapply ex_hseq; [ | apply W; apply pi ].
      apply Permutation_Type_swap. }
  apply ex_hseq with ((vec r A ++ T) :: (vec r (-S (A \/S B)) ++ vec r B) :: G); [ apply Permutation_Type_swap | ].
  apply can with (A \/S B) r r ; try reflexivity.
  apply ex_seq with ( (vec r (-S (A \/S B)) ++ vec r A) ++ (vec r (A \/S B) ++ T)); [perm_Type_solve | ].
  apply M.
  2:{ eapply ex_hseq; [ | apply W; apply pi].
      apply Permutation_Type_swap. }
  unfold minus; fold minus.
  apply min.
  - apply ex_hseq with (( (vec r (-S A /\S -S B) ++ vec r B) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ perm_Type_solve | ].
    apply W_gen.
    replace (vec r (-S A) ++ vec r A) with (vec r (-S A) ++ vec r A ++ nil) by (now rewrite app_nil_r).
    apply ID_gen; [reflexivity | apply INIT].
  - eapply ex_hseq ; [ apply Permutation_Type_swap | ].
    apply min.
    + apply S.
      apply ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B ++ nil) ; [ perm_Type_solve | ].
      apply ID_gen; [ reflexivity | apply ID_gen ; [ reflexivity | ] ].
      apply ex_hseq with (G ++ (nil :: nil)); [ perm_Type_solve | ].
      apply W_gen; apply INIT.
    + rewrite <-(app_nil_r (vec r B)).
      apply ID_gen; [ reflexivity | ].
      eapply ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ (nil :: nil)); [ | apply W_gen; apply INIT ].
      perm_Type_solve.
Qed.

Lemma min_can_inv_l : forall G T A  B r, HR true ((vec r (A /\S B) ++ T) :: G) -> HR true ((vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply can with (A /\S B) r r; try reflexivity.
  apply ex_seq with ((vec r (-S (A /\S B)) ++ vec r A) ++ (vec r (A /\S B) ++ T)); [ perm_Type_solve | ].
  apply M ; [ | apply pi].
  unfold minus; fold minus.
  apply max.
  apply ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ perm_Type_solve | ].
  apply W_gen.
  rewrite <-(app_nil_r (vec r A)).
  apply ID_gen; [ reflexivity | apply INIT].
Qed.

Lemma min_can_inv_r : forall G T A  B r, HR true ((vec r (A /\S B) ++ T) :: G) -> HR true ((vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply can with (A /\S B) r r; try reflexivity.
  apply ex_seq with ((vec r (-S (A /\S B)) ++ vec r B) ++ (vec r (A /\S B) ++ T)); [ perm_Type_solve | ].
  apply M ; [ | apply pi].
  unfold minus; fold minus.
  apply max.
  apply ex_hseq with (((vec r (-S A) ++ vec r B) :: G) ++ ((vec r (-S B) ++ vec r B) :: nil)); [ perm_Type_solve | ].
  apply W_gen.
  rewrite <-(app_nil_r (vec r B)).
  apply ID_gen; [ reflexivity | apply INIT].
Qed.

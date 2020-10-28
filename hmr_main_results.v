(** * Summary of the main results as in Section 4.1 *)
Require Import Rterm.
Require Import Rpos.
Require Import term.
Require Import Rsemantic.
Require Import semantic.
Require Import semantic_Rsemantic_eq.
Require Import hseq.
Require Import completeness.
Require Import soundness.
Require Import interpretation.
Require Import hmr.
Require Import invertibility.
Require Import M_elim.
Require Import can_elim.

Require Import List_more.
Require Import Reals.
Require Import Lra.
Require Import Lia.

Lemma HMR_soundness P : forall G,
    HMR P G ->
    R_zero <R= toRterm (sem_hseq G).
Proof.
  intros G pi.
  change (R_zero /\R (toRterm (sem_hseq G))) with (toRterm (zero /\S sem_hseq G)).
  change (R_zero) with (toRterm zero).
  apply semantic_to_Rsemantic.
  apply hmr_sound with P.
  apply pi.
Qed.

Lemma HMR_completeness : forall G,
    G <> nil ->
    R_zero <R= toRterm (sem_hseq G) ->
    HMR_M_can G.
Proof.
  intros G Hnnil H.
  apply hmr_complete; [ apply Hnnil | ].
  transitivity (NNF (R_zero /\R toRterm (sem_hseq G))).
  - simpl.
    rewrite NNF_toRterm.
    reflexivity.
  - change zero with (NNF (R_zero)).
    apply Rsemantic_to_semantic.
    apply H.
Qed.

Lemma HMR_plus_inv : forall G T A B r, HMR_T_M ((vec r (A +S B) ++ T) :: G) -> HMR_T_M ((vec r A ++ vec r B ++ T) :: G).
Proof.
  apply hmrr_plus_inv.
Qed.

Lemma HMR_Z_inv : forall G T r, HMR_T_M ((vec r zero ++ T) :: G) -> HMR_T_M (T :: G).
Proof.
  apply hmrr_Z_inv.
Qed.
  
Lemma HMR_mul_inv : forall G T A r0 r, HMR_T_M ((vec r (r0 *S A) ++ T) :: G) -> HMR_T_M ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
  apply hmrr_mul_inv.
Qed.

Lemma HMR_max_inv : forall G T A B r, HMR_T_M ((vec r (A \/S B) ++ T) :: G) -> HMR_T_M ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
  apply hmrr_max_inv.
Qed.

Lemma HMR_min_inv_l : forall G T A  B r, HMR_T_M ((vec r (A /\S B) ++ T) :: G) -> HMR_T_M ((vec r A ++ T) :: G).
Proof.
  apply hmrr_min_inv_l.
Qed.

Lemma HMR_min_inv_r : forall G T A  B r, HMR_T_M ((vec r (A /\S B) ++ T) :: G) -> HMR_T_M ((vec r B ++ T) :: G).
Proof.
  apply hmrr_min_inv_r.
Qed.

Lemma HMR_M_elim : forall G, HMR_T_M G -> HMR_T G.
Proof.
  apply hmrr_M_elim.
Qed.

Lemma HMR_can_elim : forall G, HMR_full G -> HMR_T_M G.
Proof.
  apply hmrr_can_elim.
Qed.
  
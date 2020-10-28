(** * Summary of the main results as in Section 3.1 *)
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
Require Import hr.
Require Import invertibility.
Require Import M_elim.
Require Import can_elim.
Require Import decidability.

Require Import List_more.
Require Import Reals.
Require Import Lra.
Require Import Lia.

(** Theorem 3.9 *)
Lemma HR_soundness P : forall G,
    HR P G ->
    R_zero <R= toRterm (sem_hseq G).
Proof.
  intros G pi.
  change (R_zero /\R (toRterm (sem_hseq G))) with (toRterm (zero /\S sem_hseq G)).
  change (R_zero) with (toRterm zero).
  apply semantic_to_Rsemantic.
  apply hr_sound with P.
  apply pi.
Qed.

(** Theorem 3.10 *)
Lemma HR_completeness : forall G,
    G <> nil ->
    R_zero <R= toRterm (sem_hseq G) ->
    HR_M_can G.
Proof.
  intros G Hnnil H.
  apply hr_complete; [ apply Hnnil | ].
  transitivity (NNF (R_zero /\R toRterm (sem_hseq G))).
  - simpl.
    rewrite NNF_toRterm.
    reflexivity.
  - change zero with (NNF (R_zero)).
    apply Rsemantic_to_semantic.
    apply H.
Qed.

(** Theorem 3.11 *)
Lemma HR_plus_inv : forall G T A B r, HR_T_M ((vec r (A +S B) ++ T) :: G) -> HR_T_M ((vec r A ++ vec r B ++ T) :: G).
Proof.
  apply hrr_plus_inv.
Qed.

Lemma HR_Z_inv : forall G T r, HR_T_M ((vec r zero ++ T) :: G) -> HR_T_M (T :: G).
Proof.
  apply hrr_Z_inv.
Qed.
  
Lemma HR_mul_inv : forall G T A r0 r, HR_T_M ((vec r (r0 *S A) ++ T) :: G) -> HR_T_M ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
  apply hrr_mul_inv.
Qed.

Lemma HR_max_inv : forall G T A B r, HR_T_M ((vec r (A \/S B) ++ T) :: G) -> HR_T_M ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
  apply hrr_max_inv.
Qed.

Lemma HR_min_inv_l : forall G T A  B r, HR_T_M ((vec r (A /\S B) ++ T) :: G) -> HR_T_M ((vec r A ++ T) :: G).
Proof.
  apply hrr_min_inv_l.
Qed.

Lemma HR_min_inv_r : forall G T A  B r, HR_T_M ((vec r (A /\S B) ++ T) :: G) -> HR_T_M ((vec r B ++ T) :: G).
Proof.
  apply hrr_min_inv_r.
Qed.

(** Theorem 3.12 *)
Lemma HR_M_elim : forall G, HR_T_M G -> HR_T G.
Proof.
  apply hrr_M_elim.
Qed.

(** Theorem 3.13 *)
Lemma HR_can_elim : forall G, HR_full G -> HR_T_M G.
Proof.
  apply hrr_can_elim.
Qed.

(** Theorem 3.15 *)
(** Proposition 3.16 *)
Lemma HR_without_T_CAN_not_complete :
  { G : _ & zero <== sem_hseq G & (HR_M G -> False) }.
Proof.
  apply HR_M_not_complete.
Qed.
(** Theorem 3.17 *)
Lemma HR_is_decidable : forall G,
    (HR_full G) + (HR_full G -> False).
Proof.
  apply HR_decidable.
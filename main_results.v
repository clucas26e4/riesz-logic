(** * Equational reasoning for modal lattice-ordered Abelian groups *)
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

Require Import List_more.
Require Import Reals.
Require Import Lra.
Require Import Lia.

Lemma HR_soundness b : forall G,
    HR b G ->
    R_zero <R= toRterm (sem_hseq G).
Proof.
  intros G pi.
  change (R_zero /\R (toRterm (sem_hseq G))) with (toRterm (zero /\S sem_hseq G)).
  change (R_zero) with (toRterm zero).
  apply semantic_to_Rsemantic.
  apply hr_sound with b.
  apply pi.
Qed.

Lemma HR_completeness : forall G,
    G <> nil ->
    R_zero <R= toRterm (sem_hseq G) ->
    HR true G.
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

Lemma HR_plus_inv : forall G T A B r, HR false ((vec r (A +S B) ++ T) :: G) -> HR false ((vec r A ++ vec r B ++ T) :: G).
Proof.
Admitted.

Lemma HR_Z_inv : forall G T r, HR false ((vec r zero ++ T) :: G) -> HR false (T :: G).
Proof.
Admitted.
  
Lemma HR_mul_inv : forall G T A r0 r, HR false ((vec r (r0 *S A) ++ T) :: G) -> HR false ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
Admitted.

Lemma HR_max_inv : forall G T A B r, HR false ((vec r (A \/S B) ++ T) :: G) -> HR false ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
Admitted.

Lemma HR_min_inv_l : forall G T A  B r, HR false ((vec r (A /\S B) ++ T) :: G) -> HR false ((vec r A ++ T) :: G).
Proof.
Admitted.

Lemma HR_min_inv_r : forall G T A  B r, HR false ((vec r (A /\S B) ++ T) :: G) -> HR false ((vec r B ++ T) :: G).
Proof.
Admitted.

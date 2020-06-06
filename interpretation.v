From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Rpos.
Require Import term.
Require Import hseq.
Require Import semantic.

Require Import List.
Require Import Lra.
Require Import Permutation_more.

Local Open Scope R_scope.

(* Interpretation of a sequent *)
Fixpoint sem_seq (T1 : sequent) :=
  match T1 with
  | nil => zero
  | ((r , A) :: T1) => (r *S A) +S (sem_seq T1)
  end.

Lemma sem_seq_plus : forall T1 T2, sem_seq (T1 ++ T2) === sem_seq T1 +S sem_seq T2.
Proof.
  induction T1; move=> T2.
  - by rewrite commu_plus neutral_plus.
  - specialize (IHT1 T2).
    destruct a as (r , A).
    simpl; rewrite IHT1.
    by auto with MGA_solver.
Qed.

Lemma sem_seq_mul : forall T r, sem_seq (seq_mul r T) === r *S sem_seq T.
Proof.
  elim => [ | [rA A] T IHT] r.
  - by rewrite mul_0.
  - simpl.
    rewrite IHT.
    rewrite -mul_assoc.
    auto with MGA_solver.
Qed.

Lemma sem_seq_vec : forall r A (Hnnil : r <> nil), sem_seq (vec r A) === (existT _ (sum_vec r) (sum_vec_non_nil Hnnil)) *S A.
Proof.
  induction r => A Hnnil.
  { exfalso; auto. }
  destruct r as [ | b r].
  - simpl in *.
    replace (existT (fun r : R => (0 <? r) = true) (projT1 a + 0) (sum_vec_non_nil Hnnil)) with a by (apply Rpos_eq; simpl; nra).
    auto.
  - have H : b :: r <> nil by auto.
    specialize (IHr A H).
    change (sem_seq (vec (a :: b :: r) A)) with (a *S A +S (sem_seq (vec (b :: r) A))).
    replace (existT (fun r0 : R => (0 <? r0) = true) (sum_vec (a :: b :: r)) (sum_vec_non_nil Hnnil)) with (plus_pos a (existT _ (sum_vec (b :: r)) (sum_vec_non_nil H))) by (destruct a; destruct  b; apply Rpos_eq; simpl; nra).
    rewrite IHr.
    auto with MGA_solver.
Qed.

Lemma sem_seq_permutation : forall T1 T2, Permutation T1 T2 -> sem_seq T1 === sem_seq T2.
Proof.
  move => T1 T2 Hperm; induction Hperm; try destruct x; try destruct y; simpl; try auto with MGA_solver.
  - rewrite 2? asso_plus.
    rewrite (commu_plus (r0 *S t0)); reflexivity.
  - transitivity (sem_seq l'); assumption.
Qed.

    (* Interpretation of a hypersequent *)
Fixpoint sem_hseq G :=
  match G with
  | nil => zero (* should not happen *)
  | T1 :: nil => sem_seq T1
  | T1 :: G => (sem_seq T1) \/S (sem_hseq G)
  end.

Lemma sem_hseq_permutation : forall G1 G2, Permutation G1 G2 -> sem_hseq G1 === sem_hseq G2.
Proof.
  move => G1 G2 Hperm; induction Hperm.
  - reflexivity.
  - destruct l; destruct l'.
    + reflexivity.
    + exfalso; apply (Permutation_nil_cons Hperm).
    + apply Permutation_sym in Hperm.
      exfalso; apply (Permutation_nil_cons Hperm).
    + unfold sem_hseq; fold (sem_hseq (s :: l)); fold (sem_hseq (s0 :: l')).
      rewrite IHHperm; reflexivity.
  - destruct l.
    + simpl; apply commu_max.
    + unfold sem_hseq; fold (sem_hseq (s :: l)); rewrite ?asso_max (commu_max (sem_seq y)); reflexivity.
  - transitivity (sem_hseq l'); assumption.
Qed.

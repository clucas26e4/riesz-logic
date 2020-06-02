From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Rpos.
Require Import term.
Require Import hseq.
Require Import semantic.

Require Import List.

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

    (* Interpretation of a hypersequent *)
Fixpoint sem_hseq G :=
  match G with
  | nil => zero (* should not happen *)
  | T1 :: nil => sem_seq T1
  | T1 :: G => (sem_seq T1) \/S (sem_hseq G)
  end.

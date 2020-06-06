From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Rpos.
Require Import term.

Require Import List.
Require Import Permutation_more.
Require Import Permutation_solve.
Require Import Lra.

Local Open Scope Rpos_scope.

(** * Definition of hr *)

(** ** Sequent *)
                                                
Definition sequent : Set := list (Rpos * term).

Fixpoint seq_mul (r : Rpos) (T : sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (r * a, A) :: (seq_mul r T)
  end.

(* MOVE ?*)
Fixpoint vec (l : list Rpos) (A : term) :=
  match l with
  | nil => nil
  | r :: l => (r , A) :: (vec l A)
  end.

Fixpoint sum_vec (l : list Rpos) :=
  match l with
  | nil => 0%R
  | r :: l => Rplus (projT1 r) (sum_vec l)
  end.

Fixpoint mul_vec (l : list Rpos) r :=
  match l with
  | nil => nil
  | r0 :: l => (time_pos r r0) :: (mul_vec l r)
  end.

Lemma sum_vec_le_0 : forall r, (0 <= sum_vec r)%R.
  induction r; [ | move : a=> [a Ha]; simpl;  apply (R_blt_lt 0 a) in Ha]; simpl; try nra.
Qed.
    
Lemma sum_vec_non_nil : forall r, r <> nil -> (0 <? sum_vec r)%R = true.
  induction r => Hnnil; [auto | ].
  simpl.
  apply R_blt_lt.
  case : a Hnnil => [a Ha] /= => _.
  apply R_blt_lt in Ha.
  pose Hle := (sum_vec_le_0 r).
  nra.
Qed.
(** ** Hypersequent *)

Definition hypersequent : Set := list sequent.

Inductive HR b : hypersequent -> Type :=
| INIT : HR b (nil :: nil)
| W : forall G T, HR b G -> HR b (T :: G)
| C : forall G T, HR b (T :: T :: G) -> HR b (T :: G)
| S : forall G T1 T2, HR b ((T1 ++ T2) :: G) -> HR b (T1 :: T2 :: G)
| M : forall G T1 T2, HR b (T1 :: G) -> HR b (T2 :: G) -> HR b ((T1 ++ T2) :: G)
| T : forall G T r, HR b (seq_mul r T :: G) -> HR b (T :: G)
| ID : forall G T n r s, sum_vec r = sum_vec s -> HR b (T :: G) -> HR b ((vec s (covar n) ++ vec r (var n) ++ T) :: G)
| Z : forall G T r, HR b (T :: G) -> HR b ((vec r zero ++ T) :: G)

| plus : forall G T A B r, HR b ((vec r A ++ vec r B ++ T) :: G) -> HR b ((vec r (A +S B) ++ T) :: G)
| mul : forall G T A r0 r, HR b ((vec (mul_vec r r0) A ++ T) :: G) -> HR b ((vec r (r0 *S A) ++ T) :: G)
| max : forall G T A B r, HR b ((vec r B ++ T) :: (vec r A ++ T) :: G) -> HR b ((vec r (A \/S B) ++ T) :: G)
| min : forall G T A  B r, HR b ((vec r A ++ T) :: G) -> HR b ((vec r B ++ T) :: G) -> HR b ((vec r (A /\S B) ++ T) :: G)
| ex_seq : forall G T1 T2, Permutation T1 T2 -> HR b (T1 :: G) -> HR b (T2 :: G)
| ex_hseq : forall G H, Permutation G H -> HR b G -> HR b H
| can {f : b = true} : forall G T A r s, sum_vec r = sum_vec s -> HR b ((vec s (-S A) ++ vec r A ++ T) :: G) -> HR b (T :: G).

(* Some basic properties *)

Lemma HR_not_empty b : forall G, HR b G -> G <> nil.
Proof.
  move => G pi; induction pi; (try by []).
  move => Heq; apply IHpi; apply Permutation_nil.
  symmetry; by rewrite <- Heq.
Qed.


Lemma HR_no_can_can : forall G, HR false G -> HR true G.
Proof.
  move => G pi.
  induction pi; try now constructor.
  - apply T with r; apply IHpi.
  - apply ex_seq with T1; assumption.
  - apply ex_hseq with G; assumption.
Qed.

Lemma W_gen b : forall G H, HR b G -> HR b (H ++ G).
Proof.
  move => G H; move: G; induction H => G pi.
  - auto.
  - simpl; apply W; apply IHlist; apply pi.
Qed.

Lemma ID_gen b : forall G T A r s, sum_vec r = sum_vec s -> HR b (T :: G) -> HR b ((vec s (-S A) ++ vec r A ++ T) :: G).
Proof.
  move => G T A; move: G T.
  induction A => G T r0 s Heq pi; unfold minus; fold minus.
  - apply ID; assumption.
  - apply ex_seq with (vec r0 (covar n) ++ vec s (var n) ++ T); [ perm_solve | ].
    apply ID; try symmetry; assumption.
  - apply Z; apply Z; apply pi.
  - apply plus.
    apply ex_seq with (vec r0 (A1 +S A2) ++ vec s (-S A1) ++ vec s (-S A2) ++ T); [ perm_solve | ].
    apply plus.
    eapply ex_seq.
    2:{ eapply IHA1; [ apply Heq | ].
        eapply ex_seq.
        2:{ eapply IHA2; [ apply Heq | apply pi ]. }
        perm_solve. }
    perm_solve.
  - apply mul.
    eapply ex_seq with (vec r0 (r *S A) ++ vec (mul_vec s r) (-S A) ++ T) ; [ perm_solve | ].
    apply mul.
    apply ex_seq with (vec (mul_vec s r) (-S A) ++ vec (mul_vec r0 r) A ++ T); [ perm_solve | ].
    apply IHA ; [ | apply pi].
    (* TODO MOVING *)
    have sum_mul_vec : forall l r, sum_vec (mul_vec l r) =  Rmult (projT1 r) (sum_vec l).
    { clear.
      induction l; move => [r Hr].
      - simpl; nra.
      - set t := (existT (fun r0 : R => (0 <? r0)%R = true) r Hr).
        unfold mul_vec; fold (mul_vec l t).
        unfold sum_vec; fold (sum_vec (mul_vec l t)); fold (sum_vec l).
        rewrite IHl.
        unfold t.
        destruct a.
        simpl.
        nra. }
    rewrite ? sum_mul_vec.
    destruct r as [r Hr].
    simpl.
    apply R_blt_lt in Hr.
    nra.
  - apply min.
    + apply ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A1) ++ T); [perm_solve | ].
      apply max.
      apply W.
      eapply ex_seq; [ | apply IHA1; [ apply Heq | apply pi] ].
      perm_solve.
    + apply ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A2) ++ T); [perm_solve | ].
      apply max.
      apply ex_hseq with ((vec r0 A1 ++ vec s (-S A2) ++ T) :: (vec r0 A2 ++ vec s (-S A2) ++ T) :: G) ; [ perm_solve | ]. 
      apply W.
      eapply ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      perm_solve.
  - apply ex_seq with (vec r0 (A1 /\S A2) ++ vec s (-S A1 \/S -S A2) ++ T); [ perm_solve | ].
    apply min.
    + apply ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A1) ++ T); [perm_solve | ].
      apply max.
      apply W.
      apply IHA1; [ apply Heq | apply pi].
    + apply ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A2) ++ T); [perm_solve | ].
      apply max.
      apply ex_hseq with ((vec s (-S A1) ++ vec r0 A2 ++ T) :: (vec s (-S A2) ++ vec r0 A2 ++ T) :: G) ; [ perm_solve | ]. 
      apply W.
      eapply ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      perm_solve.
Qed.
      

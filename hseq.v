From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Rpos.
Require Import term.

Require Import List.
Require Import Permutation.

Local Open Scope Rpos_scope.

(** * Definition of hr *)

(** ** Sequent *)
                                                
Definition sequent : Set := list (Rpos * term).

Fixpoint seq_mul (r : Rpos) (T : sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (r * a, A) :: (seq_mul r T)
  end.

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

(** ** Hypersequent *)

Definition hypersequent : Set := list sequent.

Inductive HR : hypersequent -> Type :=
| INIT : HR (nil :: nil)
| W : forall G T, HR G -> HR (T :: G)
| C : forall G T, HR (T :: T :: G) -> HR (T :: G)
| S : forall G T1 T2, HR ((T1 ++ T2) :: G) -> HR (T1 :: T2 :: G)
| M : forall G T1 T2, HR (T1 :: G) -> HR (T2 :: G) -> HR ((T1 ++ T2) :: G)
| T : forall G T r, HR (seq_mul r T :: G) -> HR (T :: G)
| ID : forall G T n r s, HR (T :: G) -> sum_vec r = sum_vec s -> HR ((vec s (covar n) ++ vec r (var n) ++ T) :: G)
| plus : forall G T A B r, HR ((vec r A ++ vec r B ++ T) :: G) -> HR ((vec r (A +S B) ++ T) :: G)
| ex_seq : forall G T1 T2, Permutation T1 T2 -> HR (T1 :: G) -> HR (T2 :: G)
| ex_hseq : forall G H, Permutation G H -> HR G -> HR H.

(* Some basic properties *)

Lemma HR_not_empty : forall G, HR G -> G <> nil.
Proof.
  move => G pi; induction pi; (try by []).
  move => Heq; apply IHpi; apply Permutation_nil.
  symmetry; by rewrite <- Heq.
Qed.

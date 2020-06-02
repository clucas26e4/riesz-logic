From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Reals.

(** ** Term *)
Require Import List_more.

Inductive Rterm : Type :=
| R_var : nat -> Rterm
| R_zero : Rterm
| R_plus : Rterm -> Rterm -> Rterm
| R_mul : R -> Rterm -> Rterm
| R_max : Rterm -> Rterm -> Rterm
| R_min : Rterm -> Rterm -> Rterm.

(** Notations *)

Notation "A +R B" := (R_plus A B) (at level 20, left associativity).
Notation "A \/R B" := (R_max A B) (at level 40, left associativity).
Notation "A /\R B" := (R_min A B) (at level 45, left associativity).
Notation "-R A" := (R_mul (-1) A) (at level 15).
Notation "A -R B" := (R_plus A (-R B)) (at level 10, left associativity).
Notation "r *R A" := (R_mul r A) (at level 15).

Fixpoint R_sum_term k A :=
  match k with
  | 0 => R_zero
  | 1 => A
  | S n => A +R (R_sum_term n A)
  end.

(** Definition of positive part, negative part and absolute value *)
Notation "'R_pos' A" := (A \/R R_zero) (at level 5).
Notation "'R_neg' A" := ((-R A) \/R R_zero) (at level 5).
Notation "'R_abs' A" := (A \/R (-R A)) (at level 5).

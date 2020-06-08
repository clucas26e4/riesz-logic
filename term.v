Require Import Rpos.

(** ** Term *)
Require Import List_more.

Inductive term : Type :=
| var : nat -> term
| covar : nat -> term
| zero : term
| plus : term -> term -> term
| mul : Rpos -> term -> term
| max : term -> term -> term
| min : term -> term -> term.

Fixpoint minus A :=
  match A with
  | var n => covar n
  | covar n => var n
  | zero => zero
  | plus A B => plus (minus A) (minus B)
  | mul r A => mul r (minus A)
  | max A B => min (minus A) (minus B)
  | min A B => max (minus A) (minus B)
  end.

(** Notations *)
Notation "A +S B" := (plus A B) (at level 20, left associativity).
Notation "A \/S B" := (max A B) (at level 40, left associativity).
Notation "A /\S B" := (min A B) (at level 45, left associativity).
Notation "-S A" := (minus A) (at level 15).
Notation "A -S B" := (plus A (minus B)) (at level 10, left associativity).
Notation "r *S A" := (mul r A) (at level 15).

Fixpoint sum_term k A :=
  match k with
  | 0 => zero
  | 1 => A
  | S n => A +S (sum_term n A)
  end.

(** Definition of positive part, negative part and absolute value *)
Notation "'pos' A" := (A \/S zero) (at level 5).
Notation "'neg' A" := ((-S A) \/S zero) (at level 5).
Notation "'abs' A" := (A \/S (-S A)) (at level 5).

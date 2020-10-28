(** First order logic for the signature (R, +, ., <=, =) where . is an external multiplication by a real scalar *)

Require Export Reals.
Require Import Rpos.
Require Import Bool.
Require Import Lra.
Require Import Permutation_Type.
Require Import List_Type.

Local Open Scope R_scope.

Definition upd_val (v : nat -> R) n r :=
  fun n' => if beq_nat n n' then r else v n'.

Inductive FOL_R_term : Type :=
| FOL_R_var : nat -> FOL_R_term
| FOL_R_cst : R -> FOL_R_term
| FOL_R_mul : FOL_R_term -> FOL_R_term -> FOL_R_term
| FOL_R_add : FOL_R_term -> FOL_R_term -> FOL_R_term.

Notation "f1 *R f2" := (FOL_R_mul f1 f2) (at level 20, left associativity).
Notation "f1 +R f2" := (FOL_R_add f1 f2) (at level 15).

Fixpoint max_var_FOL_R_term t :=
  match t with
  | FOL_R_var n => n
  | FOL_R_cst r => 0%nat
  | FOL_R_mul t1 t2 => Nat.max (max_var_FOL_R_term t1) (max_var_FOL_R_term t2)
  | FOL_R_add t1 t2 => Nat.max (max_var_FOL_R_term t1) (max_var_FOL_R_term t2)
  end.                         

Fixpoint FOL_R_term_sem (v : nat -> R) t :=
  match t with
  | FOL_R_var n => v n
  | FOL_R_cst r => r
  | FOL_R_mul t1 t2 => (FOL_R_term_sem v t1) * (FOL_R_term_sem v t2)
  | FOL_R_add t1 t2 => (FOL_R_term_sem v t1) + (FOL_R_term_sem v t2)
  end.

Inductive FOL_R_pred : Type :=
| FOL_R_eq : FOL_R_term -> FOL_R_term -> FOL_R_pred
| FOL_R_le : FOL_R_term -> FOL_R_term -> FOL_R_pred.

Notation "f1 =R f2" := (FOL_R_eq f1 f2) (at level 50).
Notation "f1 <=R f2" := (FOL_R_le f1 f2) (at level 50).                                            

Fixpoint FOL_R_pred_sem (v : nat -> R) p :=
  match p with
  | FOL_R_eq t1 t2 => (FOL_R_term_sem v t1) = (FOL_R_term_sem v t2)
  | FOL_R_le t1 t2 => (FOL_R_term_sem v t1) <= (FOL_R_term_sem v t2)
  end.

Inductive FOL_R_formula : Type :=
| FOL_R_true : FOL_R_formula
| FOL_R_false : FOL_R_formula
| FOL_R_atoms : FOL_R_pred -> FOL_R_formula
| FOL_R_neg : FOL_R_formula -> FOL_R_formula
| FOL_R_and : FOL_R_formula -> FOL_R_formula -> FOL_R_formula
| FOL_R_or : FOL_R_formula -> FOL_R_formula -> FOL_R_formula
| FOL_R_impl : FOL_R_formula -> FOL_R_formula -> FOL_R_formula
| FOL_R_exists : nat -> FOL_R_formula -> FOL_R_formula
| FOL_R_forall : nat -> FOL_R_formula -> FOL_R_formula.

Notation "f1 \/R f2" := (FOL_R_and f1 f2) (at level 40, left associativity).
Notation "f1 /\R f2" := (FOL_R_or f1 f2) (at level 45, left associativity).
Notation "f1 =>R f2" := (FOL_R_impl f1 f2) (at level 45, left associativity).

Fixpoint FOL_R_formula_sem (v : nat -> R) f : Type :=
  match f with
  | FOL_R_true => True
  | FOL_R_false => False
  | FOL_R_atoms p => FOL_R_pred_sem v p
  | FOL_R_neg f => (FOL_R_formula_sem v f) -> False
  | FOL_R_and f1 f2 => prod (FOL_R_formula_sem v f1) (FOL_R_formula_sem v f2)
  | FOL_R_or f1 f2 => sum (FOL_R_formula_sem v f1) (FOL_R_formula_sem v f2)
  | FOL_R_impl f1 f2 => (FOL_R_formula_sem v f1) -> (FOL_R_formula_sem v f2)
  | FOL_R_exists n f => { r & FOL_R_formula_sem (upd_val v n r) f}
  | FOL_R_forall n f => forall r, FOL_R_formula_sem (upd_val v n r) f
  end.

Axiom FOL_R_decidable : forall f v, (FOL_R_formula_sem v f) + (FOL_R_formula_sem v f -> False).

Definition Permutation_Type_FOL_R_term val l1 l2 := Permutation_Type (map (FOL_R_term_sem val) l1) (map (FOL_R_term_sem val) l2).

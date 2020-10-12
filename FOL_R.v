(** First order logic for the signature (R, +, ., <=, =) where . is an external multiplication by a real scalar *)

Require Export Reals.
Require Import Bool.
Require Import Lra.

Local Open Scope R_scope.

Definition upd_val (v : nat -> R) n r :=
  fun n' => if beq_nat n n' then r else v n'.

Inductive FOL_R_term : Type :=
| FOL_R_var : nat -> FOL_R_term
| FOL_R_cst : R -> FOL_R_term
| FOL_R_mul : R -> FOL_R_term -> FOL_R_term
| FOL_R_add : FOL_R_term -> FOL_R_term -> FOL_R_term.

Fixpoint FOL_R_term_sem (v : nat -> R) t :=
  match t with
  | FOL_R_var n => v n
  | FOL_R_cst r => r
  | FOL_R_mul r t => r * (FOL_R_term_sem v t)
  | FOL_R_add t1 t2 => (FOL_R_term_sem v t1) + (FOL_R_term_sem v t2)
  end.

(* TODO : remove *)
(*
Fixpoint FOL_R_term_subs n t t' :=
  match t with
  | FOL_R_var n' => if (beq_nat n n') then t' else FOL_R_var n'
  | FOL_R_cst r => FOL_R_cst r
  | FOL_R_mul r t => FOL_R_mul r (FOL_R_term_subs n t t')
  | FOL_R_add t1 t2 => FOL_R_add (FOL_R_term_subs n t1 t') (FOL_R_term_subs n t2 t')
  end.
*)

Inductive FOL_R_pred : Type :=
| FOL_R_eq : FOL_R_term -> FOL_R_term -> FOL_R_pred
| FOL_R_le : FOL_R_term -> FOL_R_term -> FOL_R_pred.

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

Definition FOL_R_valid f := forall v, FOL_R_formula_sem v f.

Axiom FOL_R_decidable : forall f, (FOL_R_valid f) + (FOL_R_valid f -> False).

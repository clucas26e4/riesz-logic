Require Import Rpos.

Require Import RL.OLlibs.List_more.
Context {V : Type}.
Hypothesis V_eq : forall (x y : V), {x = y} + {x <> y}.

(** * Definition of terms of Riesz spaces in Negative Normal Form (i.e. built over the signature (0,+,.) where . is the external multiplication by a positive real) *)
(** ** Term *)

Inductive term : Type :=
| RS_var : V -> term
| RS_covar : V -> term
| RS_zero : term
| RS_plus : term -> term -> term
| RS_mul : Rpos -> term -> term
| RS_max : term -> term -> term
| RS_min : term -> term -> term.

Fixpoint RS_minus A :=
  match A with
  | RS_var n => RS_covar n
  | RS_covar n => RS_var n
  | RS_zero => RS_zero
  | RS_plus A B => RS_plus (RS_minus A) (RS_minus B)
  | RS_mul r A => RS_mul r (RS_minus A)
  | RS_max A B => RS_min (RS_minus A) (RS_minus B)
  | RS_min A B => RS_max (RS_minus A) (RS_minus B)
  end.

(** Notations *)
Notation "A +S B" := (RS_plus A B) (at level 20, left associativity).
Notation "A \/S B" := (RS_max A B) (at level 40, left associativity).
Notation "A /\S B" := (RS_min A B) (at level 45, left associativity).
Notation "-S A" := (RS_minus A) (at level 15).
Notation "A -S B" := (RS_plus A (RS_minus B)) (at level 10, left associativity).
Notation "r *S A" := (RS_mul r A) (at level 15).

Fixpoint sum_term k A :=
  match k with
  | 0 => RS_zero
  | 1 => A
  | S n => A +S (sum_term n A)
  end.

(** Complexity *)
Fixpoint RS_outer_complexity_term A :=
  match A with
  | RS_var n => 0
  | RS_covar n => 0
  | RS_zero => 1
  | RS_plus A B => 1 + RS_outer_complexity_term A + RS_outer_complexity_term B
  | RS_min A B => 1 + RS_outer_complexity_term A + RS_outer_complexity_term B
  | RS_max A B => 1 + RS_outer_complexity_term A + RS_outer_complexity_term B
  | RS_mul r A => 1 + RS_outer_complexity_term A
  end.

(** Substitution *)
Fixpoint subs (t1 : term) (x : V) (t2 : term) : term :=
  match t1 with
  | RS_var y => if (V_eq x y) then t2 else RS_var y
  | RS_covar y => if (V_eq x y) then (RS_minus t2) else RS_covar y
  | RS_zero => RS_zero
  | RS_plus t t' => RS_plus (subs t x t2) (subs t' x t2)
  | RS_min t t' => RS_min (subs t x t2) (subs t' x t2)
  | RS_max t t' => RS_max (subs t x t2) (subs t' x t2)
  | RS_mul y t => RS_mul y (subs t x t2)
  end.

(** Definition of positive part, negative part and absolute value *)
Notation "'pos' A" := (A \/S RS_zero) (at level 5).
Notation "'neg' A" := ((-S A) \/S RS_zero) (at level 5).
Notation "'abs' A" := (A \/S (-S A)) (at level 5).

(** Definition of atoms *)
Definition is_atom A :=
  match A with
  | RS_var _ => True
  | RS_covar _ => True
  | _ => False
  end.

Lemma is_atom_outer_complexity_0 : forall A,
    is_atom A -> RS_outer_complexity_term A = 0.
Proof.
  induction A; intros Hat; try now inversion Hat; reflexivity.
Qed.

Lemma is_atom_outer_complexity_0_inv : forall A,
    RS_outer_complexity_term A = 0 -> is_atom A.
Proof.
  induction A; intros H0; try apply I; inversion H0.
Qed.

Lemma term_eq_dec : forall (A B : term) , { A = B } + { A <> B}.
Proof.
  induction A; destruct B; try (right; intro H; now inversion H).
  - case_eq (V_eq v v0); intro H; [left; subst; reflexivity | right].
    intros H'; inversion H'; apply H; assumption.
  - case_eq (V_eq v v0); intro H; [left; subst; reflexivity | right].
    intros H'; inversion H'; apply H; assumption.
  - now left.
  - specialize (IHA1 B1); specialize (IHA2 B2).
    destruct IHA1 as [ Heq | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    destruct IHA2 as [ Heq' | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    left; now subst.
  - specialize (IHA B).
    destruct IHA as [ Heq | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    destruct r as [r Hr] ; destruct r0 as [r0 Hr0].
    case (Req_dec r r0); [intros Heqr; left; replace (existT (fun r1 : R => (0 <? r1)%R = true) r0 Hr0) with (existT (fun r1 : R => (0 <? r1)%R = true) r Hr) by (apply Rpos_eq; simpl; apply Heqr); now subst | intros Hneqr; right; intros H; inversion H; auto].
  - specialize (IHA1 B1); specialize (IHA2 B2).
    destruct IHA1 as [ Heq | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    destruct IHA2 as [ Heq' | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    left; now subst.
  - specialize (IHA1 B1); specialize (IHA2 B2).
    destruct IHA1 as [ Heq | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    destruct IHA2 as [ Heq' | Hneq] ; [ | right; intro H; inversion H; apply Hneq; assumption].
    left; now subst.
Qed.

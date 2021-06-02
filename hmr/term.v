Require Import Rpos.

Require Import RL.OLlibs.List_more.
Context {V : Type}.
Hypothesis V_eq : forall (x y : V), {x = y} + {x <> y}.

(** * Definition of terms of Riesz spaces in Negative Normal Form (i.e. built over the signature (0,+,.) where . is the external multiplication by a positive real) *)
(** ** Term *)

Inductive term : Type :=
| MRS_var : V -> term
| MRS_covar : V -> term
| MRS_zero : term
| MRS_plus : term -> term -> term
| MRS_mul : Rpos -> term -> term
| MRS_max : term -> term -> term
| MRS_min : term -> term -> term
| MRS_one : term
| MRS_coone : term
| MRS_diamond : term -> term.

Fixpoint MRS_minus A :=
  match A with
  | MRS_var n => MRS_covar n
  | MRS_covar n => MRS_var n
  | MRS_zero => MRS_zero
  | MRS_plus A B => MRS_plus (MRS_minus A) (MRS_minus B)
  | MRS_mul r A => MRS_mul r (MRS_minus A)
  | MRS_max A B => MRS_min (MRS_minus A) (MRS_minus B)
  | MRS_min A B => MRS_max (MRS_minus A) (MRS_minus B)
  | MRS_one => MRS_coone
  | MRS_coone => MRS_one
  | MRS_diamond A => MRS_diamond (MRS_minus A)
  end.

(** Notations *)
Notation "A +S B" := (MRS_plus A B) (at level 20, left associativity).
Notation "A \/S B" := (MRS_max A B) (at level 40, left associativity).
Notation "A /\S B" := (MRS_min A B) (at level 45, left associativity).
Notation "-S A" := (MRS_minus A) (at level 15).
Notation "A -S B" := (MRS_plus A (MRS_minus B)) (at level 10, left associativity).
Notation "r *S A" := (MRS_mul r A) (at level 15).
Notation "<S> A" := (MRS_diamond A) (at level 15).

Fixpoint sum_term k A :=
  match k with
  | 0 => MRS_zero
  | 1 => A
  | S n => A +S (sum_term n A)
  end.

(** Complexity *)
Fixpoint MRS_outer_complexity_term A :=
  match A with
  | MRS_var n => 0
  | MRS_covar n => 0
  | MRS_one => 0
  | MRS_coone => 0
  | <S> A => 0
  | MRS_zero => 1
  | MRS_plus A B => 1 + MRS_outer_complexity_term A + MRS_outer_complexity_term B
  | MRS_min A B => 1 + MRS_outer_complexity_term A + MRS_outer_complexity_term B
  | MRS_max A B => 1 + MRS_outer_complexity_term A + MRS_outer_complexity_term B
  | MRS_mul r A => 1 + MRS_outer_complexity_term A
  end.

Fixpoint modal_complexity_term A :=
  match A with
  | MRS_var n => 0
  | MRS_covar n => 0
  | MRS_one => 0
  | MRS_coone => 0
  | <S> A => 1 + modal_complexity_term A
  | MRS_zero => 0
  | MRS_plus A B => Nat.max (modal_complexity_term A) (modal_complexity_term B)
  | MRS_min A B => Nat.max (modal_complexity_term A) (modal_complexity_term B)
  | MRS_max A B => Nat.max (modal_complexity_term A) (modal_complexity_term B)
  | MRS_mul r A => modal_complexity_term A
  end.

Lemma modal_complexity_minus :
  forall A, modal_complexity_term A = modal_complexity_term (-S A).
Proof.
  induction A; simpl; try rewrite IHA; try rewrite IHA1; try rewrite IHA2; reflexivity.
Qed.

(*
Fixpoint max_var_term A :=
  match A with
  | MRS_var n => n
  | MRS_covar n => n
  | MRS_zero => 0%nat
  | MRS_one => 0%nat
  | MRS_coone => 0%nat
  | <S> A => max_var_term A
  | A +S B => Nat.max (max_var_term A) (max_var_term B)
  | r *S A => max_var_term A
  | A /\S B => Nat.max (max_var_term A) (max_var_term B)
  | A \/S B => Nat.max (max_var_term A) (max_var_term B)
  end.
 *)

(** Substitution *)
Fixpoint subs (t1 : term) (x : V) (t2 : term) : term :=
  match t1 with
  | MRS_var y => if (V_eq x y) then t2 else MRS_var y
  | MRS_covar y => if (V_eq x y) then (MRS_minus t2) else MRS_covar y
  | MRS_zero => MRS_zero
  | MRS_plus t t' => MRS_plus (subs t x t2) (subs t' x t2)
  | MRS_min t t' => MRS_min (subs t x t2) (subs t' x t2)
  | MRS_max t t' => MRS_max (subs t x t2) (subs t' x t2)
  | MRS_mul y t => MRS_mul y (subs t x t2)
  | MRS_one => MRS_one
  | MRS_coone => MRS_coone
  | MRS_diamond t => MRS_diamond (subs t x t2)
  end.

(** Definition of positive part, negative part and absolute value *)
Notation "'pos' A" := (A \/S MRS_zero) (at level 5).
Notation "'neg' A" := ((-S A) \/S MRS_zero) (at level 5).
Notation "'abs' A" := (A \/S (-S A)) (at level 5).

(** Definition of atoms *)
Definition is_atom A :=
  match A with
  | MRS_var _ => True
  | MRS_covar _ => True
  | _ => False
  end.

Definition is_basic A :=
  match A with
  | MRS_var _ => True
  | MRS_covar _ => True
  | MRS_one => True
  | MRS_coone => True
  | MRS_diamond A => True
  | _ => False
  end.

Lemma is_atom_outer_complexity_0 : forall A,
    is_atom A -> MRS_outer_complexity_term A = 0.
Proof.
  induction A; intros Hat; try now inversion Hat; reflexivity.
Qed.

Lemma is_basic_outer_complexity_0 : forall A,
    is_basic A -> MRS_outer_complexity_term A = 0.
Proof.
  induction A; intros Hat; try now inversion Hat; reflexivity.
Qed.

Lemma is_basic_outer_complexity_0_inv : forall A,
    MRS_outer_complexity_term A = 0 -> is_basic A.
Proof.
  induction A; intros Hc0; now inversion Hc0.
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
  - left; reflexivity.
  - left; reflexivity.
  - specialize (IHA B) as [ Heq | Hneq ] ; [ left; now subst | right ; intro H; inversion H; apply Hneq; assumption].
Qed.

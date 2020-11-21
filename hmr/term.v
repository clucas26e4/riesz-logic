Require Import Rpos.

Require Import RL.OLlibs.List_more.
(** * Definition of terms of Riesz spaces in Negative Normal Form (i.e. built over the signature (0,+,.) where . is the external multiplication by a positive real) *)
(** ** Term *)

Inductive term : Type :=
| var : nat -> term
| covar : nat -> term
| zero : term
| plus : term -> term -> term
| mul : Rpos -> term -> term
| max : term -> term -> term
| min : term -> term -> term
| one : term
| coone : term
| diamond : term -> term.

Fixpoint minus A :=
  match A with
  | var n => covar n
  | covar n => var n
  | zero => zero
  | plus A B => plus (minus A) (minus B)
  | mul r A => mul r (minus A)
  | max A B => min (minus A) (minus B)
  | min A B => max (minus A) (minus B)
  | one => coone
  | coone => one
  | diamond A => diamond (minus A)
  end.

(** Notations *)
Notation "A +S B" := (plus A B) (at level 20, left associativity).
Notation "A \/S B" := (max A B) (at level 40, left associativity).
Notation "A /\S B" := (min A B) (at level 45, left associativity).
Notation "-S A" := (minus A) (at level 15).
Notation "A -S B" := (plus A (minus B)) (at level 10, left associativity).
Notation "r *S A" := (mul r A) (at level 15).
Notation "<S> A" := (diamond A) (at level 15).

Fixpoint sum_term k A :=
  match k with
  | 0 => zero
  | 1 => A
  | S n => A +S (sum_term n A)
  end.

(** Complexity *)
Fixpoint HMR_complexity_term A :=
  match A with
  | var n => 0
  | covar n => 0
  | one => 0
  | coone => 0
  | <S> A => 0
  | zero => 1
  | plus A B => 1 + HMR_complexity_term A + HMR_complexity_term B
  | min A B => 1 + HMR_complexity_term A + HMR_complexity_term B
  | max A B => 1 + HMR_complexity_term A + HMR_complexity_term B
  | mul r A => 1 + HMR_complexity_term A
  end.

Fixpoint max_diamond_term A :=
  match A with
  | var n => 0
  | covar n => 0
  | one => 0
  | coone => 0
  | <S> A => 1 + max_diamond_term A
  | zero => 0
  | plus A B => Nat.max (max_diamond_term A) (max_diamond_term B)
  | min A B => Nat.max (max_diamond_term A) (max_diamond_term B)
  | max A B => Nat.max (max_diamond_term A) (max_diamond_term B)
  | mul r A => max_diamond_term A
  end.

Lemma max_diamond_minus :
  forall A, max_diamond_term A = max_diamond_term (-S A).
Proof.
  induction A; simpl; try rewrite IHA; try rewrite IHA1; try rewrite IHA2; reflexivity.
Qed.

Fixpoint max_var_term A :=
  match A with
  | var n => n
  | covar n => n
  | zero => 0%nat
  | one => 0%nat
  | coone => 0%nat
  | <S> A => max_var_term A
  | A +S B => Nat.max (max_var_term A) (max_var_term B)
  | r *S A => max_var_term A
  | A /\S B => Nat.max (max_var_term A) (max_var_term B)
  | A \/S B => Nat.max (max_var_term A) (max_var_term B)
  end.

(** Substitution *)
Fixpoint subs (t1 : term) (x : nat) (t2 : term) : term :=
  match t1 with
  | var y => if (beq_nat x y) then t2 else var y
  | covar y => if (beq_nat x y) then (minus t2) else covar y
  | zero => zero
  | plus t t' => plus (subs t x t2) (subs t' x t2)
  | min t t' => min (subs t x t2) (subs t' x t2)
  | max t t' => max (subs t x t2) (subs t' x t2)
  | mul y t => mul y (subs t x t2)
  | one => one
  | coone => coone
  | diamond t => diamond (subs t x t2)
  end.

(** Definition of positive part, negative part and absolute value *)
Notation "'pos' A" := (A \/S zero) (at level 5).
Notation "'neg' A" := ((-S A) \/S zero) (at level 5).
Notation "'abs' A" := (A \/S (-S A)) (at level 5).

(** Definition of atoms *)
Definition is_atom A :=
  match A with
  | var _ => True
  | covar _ => True
  | _ => False
  end.

Definition is_basic A :=
  match A with
  | var _ => True
  | covar _ => True
  | one => True
  | coone => True
  | diamond A => True
  | _ => False
  end.

Lemma is_atom_complexity_0 : forall A,
    is_atom A -> HMR_complexity_term A = 0.
Proof.
  induction A; intros Hat; try now inversion Hat; reflexivity.
Qed.

Lemma is_basic_complexity_0 : forall A,
    is_basic A -> HMR_complexity_term A = 0.
Proof.
  induction A; intros Hat; try now inversion Hat; reflexivity.
Qed.

Lemma is_basic_complexity_0_inv : forall A,
    HMR_complexity_term A = 0 -> is_basic A.
Proof.
  induction A; intros Hc0; now inversion Hc0.
Qed.

Lemma term_eq_dec : forall (A B : term) , { A = B } + { A <> B}.
Proof.
  induction A; destruct B; try (right; intro H; now inversion H).
  - case_eq (n =? n0); intro H; [ apply Nat.eqb_eq in H; rewrite H; now left | apply Nat.eqb_neq in H; right; intro H2; inversion H2; apply H; assumption ].
  - case_eq (n =? n0); intro H; [ apply Nat.eqb_eq in H; rewrite H; now left | apply Nat.eqb_neq in H; right; intro H2; inversion H2; apply H; assumption ].
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

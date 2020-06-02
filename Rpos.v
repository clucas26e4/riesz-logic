From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Export Reals.
Require Import Bool.
Require Import Lra.

Local Open Scope R_scope.
Declare Scope Rpos_scope.

(* Boolean version of Lt for real *)
Definition R_lt_dec (a b : R) : bool.
  case (Rlt_dec a b).
  - move => _; by exact true.
  - move => _; by exact false.
Defined.

Notation "a <? b" := (R_lt_dec a b) : R_scope.

Lemma R_blt_lt : forall a b, a <? b = true <-> a < b.
Proof.
  move => a b.
  rewrite /R_lt_dec.
  split; by case (Rlt_dec a b) => Hlt Hblt //.
Qed.

Lemma R_blt_nlt : forall a b, a <? b = false <-> ~ (a < b).
Proof.
  move => a b.
  rewrite /R_lt_dec.
  split; by case (Rlt_dec a b) => Hlt Hblt //.
Qed.


(* Strictly postive real numbers *)
Definition Rpos := {r : R & 0 <? r = true}.

Definition One : Rpos.
split with 1.
apply R_blt_lt; lra.
Defined.

Definition plus_pos (a b : Rpos) : Rpos.
  move: a b => [a Ha] [b Hb].
  split with (a + b).
  move: Ha Hb; rewrite ? R_blt_lt => Ha Hb; by lra.
Defined.
    
Definition time_pos (a b : Rpos) : Rpos.
  move: a b => [a Ha] [b Hb].
  split with (a * b).
  move: Ha Hb; rewrite ? R_blt_lt => Ha Hb.
  by apply Rmult_lt_0_compat.
Defined.

Definition minus_pos {a b : Rpos} (Rlt: projT1 b < projT1 a) : Rpos.
  move: a b Rlt => [a Ha] [b Hb] /= => Rlt.
  split with (a - b).
  apply R_blt_lt; nra.
Defined.

Definition inv_pos (a : Rpos) : Rpos.
  move: a => [a Ha].
  split with (/ a).
  move: Ha; rewrite ? R_blt_lt => Ha.
  by apply Rinv_0_lt_compat.
Defined.

Notation "a + b" := (plus_pos a b) : Rpos_scope.
Notation "a * b" := (time_pos a b) : Rpos_scope.
Notation "/ a" := (inv_pos a) : Rpos_scope.


Lemma eq_refl_bool_ext : forall b1 b2 : bool, b1 = b2 -> b1 = b2.
Proof.
intros b1 b2 Heq.
destruct b1 ; destruct b2 ; intros ;
  try (apply eq_refl) ;
  subst ; rewrite Heq ; by apply eq_refl.
Defined.

Lemma Rpos_eq : forall (a b : Rpos),
    projT1 a = projT1 b -> a = b.
Proof.
  move => [a Ha] [b Hb] /= Heq.
  move: Ha; rewrite Heq {a Heq} => Hb'.
  have Heq : forall f, f = eq_refl_bool_ext Hb.
  { destruct f.
    revert Hb.
    destruct (0 <? b) ; by reflexivity. }
  by rewrite (Heq Hb) (Heq Hb').
Qed.

Definition le_pos (a b : Rpos) : Prop.
  move: a b => [a Ha] [b Hb].
  by apply ((a <= b)%R).
Defined.

Definition ble_pos (a b : Rpos) : bool.
  move: a b => [a Ha] [b Hb].
  case (Rle_dec a b); move => _; [ by apply true | by apply false].
Defined.

Notation "a <= b" := (le_pos a b) : Rpos_scope.
Notation "a <=? b" := (ble_pos a b) : Rpos_scope.

Local Open Scope Rpos_scope.

(* Properties on strictly positive real numbers *)
Lemma Rpos_inv_r : forall r, r * (/ r) = One.
Proof.
  move => [r Hr].
  apply Rpos_eq => /=.
  apply Rinv_r.
  apply R_blt_lt in Hr.
  by lra.
Qed.

Lemma Rpos_inv_l : forall r, (/ r) * r = One.
Proof.
  move => [r Hr].
  apply Rpos_eq => /=.
  apply Rinv_l.
  apply R_blt_lt in Hr.
  by lra.
Qed.

Lemma ble_le_pos : forall a b, a <=? b = true <-> a <= b.
Proof.
  move => [a Ha] [b Hb] /=.
  by case (Rle_dec a b).
Qed.

Lemma ble_nle_pos : forall a b, a <=? b = false <-> ~ (a <= b).
Proof.
  move => [a Ha] [b Hb] /=.
  by case (Rle_dec a b).
Qed.

Lemma le_pos_dec : forall a b, {a <= b} + {~ (a <= b)}.
Proof.
  move => [a Ha] [b Hb] /=.
  by apply Rle_dec.
Qed.

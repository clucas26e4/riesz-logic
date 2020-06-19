Require Export Reals.
Require Import Bool.
Require Import Lra.

Local Open Scope R_scope.

Lemma Req_dec (a b : R) : {a = b} + {a <> b}.
Proof.
  case (Rle_dec a b); [intros Hle | intros Hnle; right ; nra].
  case (Rle_dec b a); [intros Hle'; left; nra | intros Hnle; right; nra].
Qed.

(* Boolean version of Lt for real *)
Definition R_lt_dec (a b : R) : bool.
  case (Rlt_dec a b).
  - intros _; exact true.
  - intros _; exact false.
Defined.

Notation "a <? b" := (R_lt_dec a b) : R_scope.

Lemma R_blt_lt : forall a b, a <? b = true <-> a < b.
Proof.
  intros a b.
  unfold R_lt_dec.
  split; case (Rlt_dec a b); intros Hlt Hblt; try (now inversion Hblt); auto.
Qed.

Lemma R_blt_nlt : forall a b, a <? b = false <-> ~ (a < b).
Proof.
  intros a b.
  unfold R_lt_dec.
  split; case (Rlt_dec a b); intros Hlt Hblt; try (now inversion Hblt); auto.
  exfalso; apply Hblt; apply Hlt.
Qed.


(* Strictly postive real numbers *)
Definition Rpos := {r : R & 0 <? r = true}.

Definition One : Rpos.
split with 1.
apply R_blt_lt; lra.
Defined.

Definition plus_pos (a b : Rpos) : Rpos.
  destruct a as [a Ha]; destruct b as [b Hb].
  split with (a + b).
  rewrite ? R_blt_lt in *; lra.
Defined.
    
Definition time_pos (a b : Rpos) : Rpos.
  destruct a as [a Ha]; destruct b as [b Hb].
  split with (a * b).
  rewrite ? R_blt_lt in *.
  apply Rmult_lt_0_compat; assumption.
Defined.

Definition minus_pos {a b : Rpos} (Rlt: projT1 b < projT1 a) : Rpos.
  destruct a as [a Ha]; destruct b as [b Hb].
  split with (a - b).
  simpl in Rlt; apply R_blt_lt; nra.
Defined.

Definition inv_pos (a : Rpos) : Rpos.
  destruct a as [a  Ha].
  split with (/ a).
  rewrite R_blt_lt in *.
  now apply Rinv_0_lt_compat.
Defined.

Lemma eq_refl_bool_ext : forall b1 b2 : bool, b1 = b2 -> b1 = b2.
Proof.
intros b1 b2 Heq.
destruct b1 ; destruct b2 ; intros ;
  try (apply eq_refl) ;
  subst ; rewrite Heq ; now apply eq_refl.
Defined.

Lemma Rpos_eq : forall (a b : Rpos),
    projT1 a = projT1 b -> a = b.
Proof.
  intros [a Ha] [b Hb]; simpl; intros Heq.
  revert Ha; rewrite Heq; clear a Heq; intros Hb'.
  assert (forall f, f = eq_refl_bool_ext _ _ Hb) as Heq.
  { destruct f.
    revert Hb.
    destruct (0 <? b) ; reflexivity. }
  rewrite (Heq Hb); now rewrite (Heq Hb').
Qed.

Definition le_pos (a b : Rpos) : Prop.
  destruct a as [a Ha]; destruct b as [b Hb].
  now apply ((a <= b)%R).
Defined.

Definition ble_pos (a b : Rpos) : bool.
  destruct a as [a Ha]; destruct b as [b Hb].
  case (Rle_dec a b); intros _; [ apply true | apply false].
Defined.

(* Properties on strictly positive real numbers *)

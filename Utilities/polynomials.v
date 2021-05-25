(** Real polynomials on multiple variables *)

Require Import riesz_logic_List_more.

Require Export Reals.
Require Import Rpos.
Require Import Bool.
Require Import Lra.
Require Import FunctionalExtensionality.
Require Import Lia.

Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.List_more.

Local Open Scope R_scope.

(* begin hide *)
(** * Operations on valuations *)
Definition upd_val (v : nat -> R) n r :=
  fun n' => if beq_nat n n' then r else v n'.

Fixpoint upd_val_vec (val : nat -> R) (vx : list nat) (vr : list R) :=
  match vx, vr with
  | nil , _ => val
  | _ , nil => val
  | x :: vx, r :: vr => upd_val_vec (upd_val val x r) vx vr
  end.

Lemma upd_val_vec_not_in : forall val L v x,
    (In_inf x v -> False) ->
    upd_val_vec val v L x = val x.
Proof.
  intros val L v; revert val L; induction v; intros val L x Hin.
  - reflexivity.
  - destruct L; [reflexivity | ].
    simpl.
    rewrite IHv.
    2:{ intros H; apply Hin; right; apply H. }
    case_eq (a =? x); intros H; unfold upd_val; rewrite H; [ apply Nat.eqb_eq in H | apply Nat.eqb_neq in H].
    + exfalso.
      apply Hin; left; lia.
    + reflexivity.
Qed.
      
Lemma upd_val_vec_seq_add : forall L v n k1 k2 i,
    upd_val_vec v (seq (k1 + k2) n) L (k1 + k2 + i) = upd_val_vec (fun x => v (k1 + x)%nat) (seq k2 n) L (k2 + i).
Proof.
  intros L v n.
  revert L v; induction n; intros L v k1 k2 i.
  - simpl.
    replace (k1 + k2 + i)%nat with (k1 + (k2 + i))%nat by lia.
    reflexivity.
  - destruct L; simpl; [ replace (k1 + k2 + i)%nat with (k1 + (k2 + i))%nat by lia; reflexivity| ].
    destruct i.
    + rewrite ? upd_val_vec_not_in.
      * unfold upd_val.
        replace (k1 + k2 =? k1 + k2 + 0) with true by (symmetry; apply Nat.eqb_eq; lia).
        replace (k2 =? k2 + 0) with true by (symmetry; apply Nat.eqb_eq; lia).
        reflexivity.
      * apply not_In_inf_seq.
        lia.
      * apply not_In_inf_seq.
        lia.        
    + replace (S (k1 + k2)) with (k1 + S k2)%nat by lia.
      replace (k1 + k2 + S i)%nat with (k1 + (S k2) + i)%nat by lia.
      rewrite IHn.
      replace (k2 + S i)%nat with (S k2 + i)%nat by lia.
      replace (fun x : nat => upd_val v (k1 + k2) r (k1 + x)) with (upd_val (fun x : nat => v (k1 + x)%nat) k2 r) ; [ reflexivity | ].
      apply functional_extensionality.
      intros x.
      unfold upd_val.
      case_eq (k2 =? x) ; intros H.
      * replace (k1 + k2 =? k1 + x) with true; [ reflexivity | ].
        symmetry; apply Nat.eqb_eq; apply Nat.eqb_eq in H.
        lia.
      * replace (k1 + k2 =? k1 + x) with false; [ reflexivity | ].
        symmetry; apply Nat.eqb_neq; apply Nat.eqb_neq in H; lia.
Qed.

Lemma upd_val_vec_eq : forall L v n i,
    upd_val_vec v (seq i (length L)) L (i + n) = nth n L (v (i + n))%nat.
Proof.
  intros L v n i; revert L v n; induction i.
  - induction L; intros v n.
    + destruct n; simpl; try reflexivity.
    + destruct n.
      * simpl.
        rewrite upd_val_vec_not_in; try reflexivity.
        apply not_In_inf_seq; lia.
      * simpl.
        change (v (S n)) with ((fun x => v (S x)) n).
        rewrite <- IHL.
        replace (1%nat) with (1 + 0)%nat by lia.
        replace (S n) with (1 + 0 + n)%nat by lia.
        rewrite upd_val_vec_seq_add.
        simpl.
        replace (fun x : nat => upd_val v 0 a (S x)) with (fun x : nat => v (S x)) ; [reflexivity | ].
        apply functional_extensionality.
        intros x.
        unfold upd_val.
        replace (0 =? S x) with false by (symmetry; apply Nat.eqb_neq; lia).
        reflexivity.
  - intros L v n.
    replace (S i) with (1 + 0 + i)%nat by lia.
    rewrite upd_val_vec_seq_add.
    rewrite IHi.
    replace (1 + 0 + (i + n))%nat with (1 + 0 + i + n)%nat by lia.
    reflexivity.
Qed.

Lemma upd_val_eq : forall val i a,
             upd_val val i a i = a.
Proof.
  intros val i a; unfold upd_val.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma map_upd_val_vec_eq : forall v L i,
    map (upd_val_vec v (seq i (length L)) L) (seq i (length L)) = L.
Proof.
  intros v L i.
  apply nth_ext with 0 0.
  { rewrite map_length; rewrite seq_length.
    reflexivity. }
  intros n.
  intros Hlt.
  rewrite map_length in Hlt; rewrite seq_length in Hlt.
  rewrite nth_indep with _ _ _ _ (upd_val_vec v (seq i (length L)) L 0).
  2:{ rewrite map_length; rewrite seq_length.
      lia. }
  rewrite map_nth.
  rewrite seq_nth; [ | assumption].
  rewrite upd_val_vec_eq.
  rewrite nth_indep with _ _ _ _ 0 ; auto.
Qed.

(* end hide *)

Inductive Poly : Type :=
| Poly_var : nat -> Poly
| Poly_cst : R -> Poly
| Poly_mul : Poly -> Poly -> Poly
| Poly_add : Poly -> Poly -> Poly.

Notation "f1 *R f2" := (Poly_mul f1 f2) (at level 20, left associativity).
Notation "f1 +R f2" := (Poly_add f1 f2) (at level 15).

Fixpoint max_var_Poly t :=
  match t with
  | Poly_var n => n
  | Poly_cst r => 0%nat
  | Poly_mul t1 t2 => Nat.max (max_var_Poly t1) (max_var_Poly t2)
  | Poly_add t1 t2 => Nat.max (max_var_Poly t1) (max_var_Poly t2)
  end.                         

Fixpoint eval_Poly (v : nat -> R) t :=
  match t with
  | Poly_var n => v n
  | Poly_cst r => r
  | Poly_mul t1 t2 => (eval_Poly v t1) * (eval_Poly v t2)
  | Poly_add t1 t2 => (eval_Poly v t1) + (eval_Poly v t2)
  end.

(* begin hide *)
Lemma eval_Poly_upd_val_vec_not_in : forall val vx vr i,
    (In_inf i vx -> False) ->
    eval_Poly (upd_val_vec val vx vr) (Poly_var i) = val i.
Proof.
  intros val vx; revert val; induction vx; intros val vr i Hin; auto.
  destruct vr; auto.
  simpl in *.
  rewrite IHvx.
  2:{ intros H; apply Hin; now right. }
  unfold upd_val.
  case_eq (a =? i); intros; auto.
  exfalso; apply Hin.
  left.
  apply Nat.eqb_eq; apply H.
Qed.

Lemma map_val_seq_var : forall val L i,
    map (eval_Poly (upd_val_vec val (seq i (length L)) L)) (map Poly_var (seq i (length L))) = L.
Proof.
  intros val L i.
  apply nth_ext with 0 0 ; [ rewrite 2 map_length; now rewrite seq_length | ].
  intros n.
  intros H.
  rewrite ? map_length in H; rewrite seq_length in H.
  rewrite nth_indep with _ _ _ _ (eval_Poly (upd_val_vec val (seq i (length L)) L) (Poly_var 0%nat)).
  2:{ rewrite 2 map_length; rewrite seq_length; apply H. }
  rewrite map_nth.
  rewrite map_nth.
  rewrite seq_nth; auto.
  simpl.
  rewrite upd_val_vec_eq.
  apply nth_indep; assumption.
Qed.

Lemma upd_val_term_lt :
  forall val a x r,
    (max_var_Poly a < x)%nat ->
    eval_Poly (upd_val val x r) a = eval_Poly val a.
Proof.
  intros val; induction a; intros x r' Hlt; simpl in *; try rewrite IHa1; try rewrite IHa2; try reflexivity; try lia.
  unfold upd_val.
  replace (x =? n) with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

(* end hide *)

Definition Permutation_Type_Poly val l1 l2 := Permutation_Type (map (eval_Poly val) l1) (map (eval_Poly val) l2).

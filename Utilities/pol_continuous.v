Require Import Reals.
Require Import Lia.
Require Import Lra.

Require Import RL.hmr.term.
Require Import RL.Utilities.polynomials.
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.Lim_seq_US.
Require Import RL.Utilities.R_complements.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.

Require Import List.

(** Definition of a valuation : a function from N to R *)
Definition val_UniformSpace := fct_UniformSpace nat R_UniformSpace.

(** If we have a sequence of function val_n converging toward val_l
    and a sequence u_n of reals converging toward u_l
    and we change (val_n i) by (u_n) for all n
    then the resulting sequence of valuations converges toward val_l except on i, where it converges toward u_l *)
Lemma upd_val_lim : forall (val_n : nat -> val_UniformSpace) i (u_n : nat -> R_UniformSpace) val_l u_l,
    is_lim_seq val_n val_l ->
    is_lim_seq u_n u_l ->
    is_lim_seq (fun n => upd_val (val_n n) i (u_n n)) (upd_val val_l i u_l).
Proof.
  intros.
  apply lim_def_fun_eps.
  intros eps.
  apply lim_def_fun_eps_inv with _ _ eps in H as [N H].
  apply lim_def_eps_inv with _ _ eps in H0 as [N0 H0].
  split with (Nat.max N N0).
  intros n Hle.
  assert (N <= n)%nat by lia; assert (N0 <= n)%nat by lia.
  specialize (H n H1); specialize (H0 n H2).
  intros j.
  case_eq (i =? j); intros Hij; unfold upd_val; rewrite Hij.
  - apply H0.
  - apply H.
Qed.

(** Generalization of the previous lemma, where we change multiple values instead of only one *)
Lemma upd_val_vec_lim : forall k (val_n : nat -> val_UniformSpace) vx (u_n : nat -> list R_UniformSpace) val_l u_l,
    (forall i, length (u_n i) = k) ->
    length vx = k ->
    length u_l = k ->
    is_lim_seq val_n val_l ->
    (forall i, (i < k)%nat -> is_lim_seq (fun n => nth i (u_n n) 0) (nth i u_l 0)) ->
    is_lim_seq (fun n => upd_val_vec (val_n n) vx (u_n n)) (upd_val_vec val_l vx u_l).
Proof.
  induction k; intros val_n vx u_n val_l u_l Hlenun Hlenx Hlenul Hlimval Hlimul.
  - destruct vx; inversion Hlenx.
    simpl.
    apply Hlimval.
  - destruct vx; inversion Hlenx.
    destruct u_l; inversion Hlenul.
    apply is_lim_seq_ext with (fun n0 => upd_val_vec (val_n n0) (n :: vx) (nth 0%nat (u_n n0) 0 :: tl (u_n n0))).
    { intros n0.
      specialize (Hlenun n0).
      destruct (u_n n0); inversion Hlenun; reflexivity. }
    simpl.
    refine (IHk (fun n0 => upd_val (val_n n0) n (nth 0%nat (u_n n0) 0)) vx (fun n => tl (u_n n)) (upd_val val_l n r) u_l _ _ _ _ _); try assumption.
    + intros i.
      specialize (Hlenun i).
      destruct (u_n i); simpl in *; lia.
    + apply upd_val_lim; try assumption.
      apply Hlimul.
      lia.
    + intros i Hlt.
      apply is_lim_seq_ext with (fun n0 => nth (S i) (u_n n0) 0).
      * intros n0.
        specialize (Hlenun n0).
        destruct (u_n n0); inversion Hlenun; reflexivity.
      * apply Hlimul.
        lia.
Qed.

(** The interpretation of polynomial expressions if continous *)
Lemma Poly_continuous : forall (t : Poly) (val : val_UniformSpace), continuous (fun x => eval_Poly x t) val.
Proof.
  induction t; intros val.
  - simpl.
    intros P [e Hloc].
    split with e.
    intros y Hb.
    apply Hloc.
    apply Hb.
  - simpl.
    intros P [e Hloc].
    split with e.
    intros _ _.
    apply Hloc.
    apply ball_center.
  - change (fun x : fct_UniformSpace nat R_UniformSpace => eval_Poly x (t1 *R t2))
      with (fun x => (@mult R_AbsRing) (eval_Poly x t1) (eval_Poly x t2)).
    apply (@continuous_mult (fct_UniformSpace nat R_UniformSpace) R_AbsRing (fun x  => eval_Poly x t1) (fun x => eval_Poly x t2) val); [ apply IHt1 | apply IHt2].
  - change (fun x : fct_UniformSpace nat R_UniformSpace => eval_Poly x (t1 +R t2))
      with (fun x => (@plus R_AbsRing) (eval_Poly x t1) (eval_Poly x t2)).
    apply (@continuous_plus (fct_UniformSpace nat R_UniformSpace) R_AbsRing R_NormedModule (fun x  => eval_Poly x t1) (fun x => eval_Poly x t2) val); [ apply IHt1 | apply IHt2].
Qed.

(** Sequential continuity of the interpretation of polynomial expression, i.e.,
    if we have a polynomial expression t and a sequence of valuation (vn) converging toward vl
    then t(vn) converges toward t(vl) *)
Lemma Poly_lim : forall (t : Poly) (vn : nat -> val_UniformSpace) (vl : val_UniformSpace),
    is_lim_seq vn vl ->
    is_lim_seq (fun n => eval_Poly (vn n) t) (eval_Poly vl t).
Proof.
  intros.
  apply (is_lim_seq_continuous (fun x => eval_Poly x t)).
  - apply Poly_continuous.
  - apply H.
Qed.

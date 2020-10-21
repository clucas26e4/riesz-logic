Require Import Rpos.
Require Import term.
Require Import semantic.
Require Import p_hseq.
Require Import hseq.
Require Import hr.
Require Import hrr_List_more.
Require Import lambda_prop.
Require Import invertibility.
Require Import can_elim.
Require Import M_elim.
Require Import FOL_R.

Require Import lt_nat2.

Require Import CMorphisms.
Require Import List_more.
Require Import List_Type.
Require Import List_Type_more.
Require Import Permutation_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Bool_more.
Require Import Lra.
Require Import Lia.
Require Import FunctionalExtensionality.

Local Open Scope R_scope.

(* TODO : move *)
Lemma Exists_Type_nth A (P : A -> Type) : forall (l : list A) a,
    {i & prod (i < length l)%nat
              (P (nth i l a)) } ->
    Exists_Type P l.
Proof.
  induction l; intros a' [i [Hlen HP]]; [ exfalso; inversion Hlen | ].
  destruct i.
  - apply Exists_Type_cons_hd.
    apply HP.
  - apply Exists_Type_cons_tl.
    apply IHl with a'.
    split with i.
    repeat split; simpl in *; try lia.
    apply HP.
Qed.

Lemma In_Type_seq : forall i k n,
    (i < n)%nat ->
    In_Type (i + k)%nat (seq k n).
Proof.
  intros i k n; revert i k; induction n; intros i k Hlt; try (exfalso; now inversion Hlt).
  destruct i; simpl; [ left; auto | ].
  right.
  replace (S (i + k)) with (i + S k)%nat by lia.
  apply IHn ; lia.
Qed.

Lemma In_Type_rev A : forall (l : list A) a,
    In_Type a l ->
    In_Type a (rev l).
Proof.
  induction l; intros a' Hin; inversion Hin; subst.
  - simpl.
    apply in_Type_or_app.
    right; left; auto.
  - simpl.
    apply in_Type_or_app; left; apply IHl; auto.
Qed.

Lemma In_Type_rev_inv A : forall (l : list A) a,
    In_Type a (rev l) ->
    In_Type a l.
Proof.
  intros l a Hin.
  rewrite <- rev_involutive.
  apply In_Type_rev.
  apply Hin.
Qed.

Lemma In_Type_map_S : forall i l,
    In_Type i l ->
    In_Type (S i) (map S l).
Proof.
  intros i; induction l; intros Hin; inversion Hin; subst; simpl; auto.
Qed.

Lemma not_0_In_Type_map_S : forall l,
    In_Type 0%nat (map S l) ->
    False.
Proof.
  induction l; intros Hin; inversion Hin; subst; simpl; auto.
  inversion H.
Qed.

Lemma In_Type_map_S_inv : forall i l,
    In_Type (S i) (map S l) ->
    In_Type i l.
Proof.
  intros i; induction l; intros Hin; inversion Hin; subst; simpl; auto.
Qed.

Lemma Forall_Type_lt_map_S : forall L n,
    Forall_Type (fun x => x < n)%nat L ->
    Forall_Type (fun x => x < S n)%nat (map S L).
Proof.
  induction L; intros n Hall; [apply Forall_Type_nil | ].
  inversion Hall; subst.
  apply Forall_Type_cons; [ lia | apply IHL; apply X].
Qed.

Lemma not_In_Type_seq : forall k n i,
    (i < k)%nat ->
    In_Type i (seq k n) ->
    False.
Proof.
  intros k n; revert k; induction n; intros k i Hlt Hin; inversion Hin; subst.
  - lia.
  - apply IHn with (S k) i; try assumption.
    lia.
Qed.

Lemma In_Type_seq_lt : forall k n i,
    In_Type i (seq k n) ->
    (i < k + n)%nat.
Proof.
  intros k n; revert k; induction n;  intros k i Hin; inversion Hin.
  - subst; lia.
  - replace (k + S n)%nat with (S k + n)%nat by lia.
    apply IHn.
    apply X.
Qed.

Lemma In_Type_remove_not A : forall eq_dec (l : list A) a,
    In_Type a (remove eq_dec a l) ->
    False.
Proof.
  intros eq_dec; induction l; intros a' Hin; [ inversion Hin | ].
  case_eq (eq_dec a' a); intros H1 H2.
  - subst; rewrite remove_cons in Hin.
    apply IHl with a.
    apply Hin.
  - simpl in Hin.
    rewrite H2 in Hin.
    inversion Hin ; [ apply H1; auto | ].
    apply IHl with a'.
    apply X.
Qed.

Lemma In_Type_remove_In_Type A : forall eq_dec (l : list A) a1 a2,
    In_Type a1 (remove eq_dec a2 l) ->
    (a1 <> a2) * (In_Type a1 l).
Proof.
  intros eq_dec; induction l; intros a1 a2 Hin; [ inversion Hin | ].
  case_eq (eq_dec a2 a); intros H1 H2; simpl in Hin; rewrite H2 in Hin.
  - destruct (IHl a1 a2 Hin) as [Hneq Hin'].
    split; auto.
    right; apply Hin'.
  - inversion Hin; subst.
    + split; auto.
      left; auto.
    + destruct (IHl a1 a2 X) as [Hneq Hin'].
      split; auto.
      right; auto.
Qed.

Lemma In_Type_remove_In_Type_inv A : forall eq_dec (l : list A) a1 a2,
    (a1 <> a2) * (In_Type a1 l) ->
    In_Type a1 (remove eq_dec a2 l).
Proof.
  intros eq_dec; induction l; intros a1 a2 [Hneq Hin]; [ inversion Hin | ].
  inversion Hin.
  - subst.
    simpl.
    case (eq_dec a2 a1); intros H; try (subst; now exfalso).
    clear H.
    left; auto.
  - simpl.
    case (eq_dec a2 a); intros H ; [ | right ]; apply IHl; split; auto.    
Qed.

Lemma rev_reverse_order_gt : forall L,
    (forall i j : nat,
        (j < length L)%nat ->
        (i < j)%nat -> (nth i L 0 > nth j L 0)%nat) ->
    forall i j : nat,
      (i < length (rev L))%nat ->
      (i > j)%nat -> (nth i (rev L) 0 > nth j (rev L) 0)%nat.
Proof.
  intros L H i j Hlen Hgt.
  rewrite rev_length in Hlen.
  rewrite ? rev_nth; try lia.
  apply H; lia.
Qed.

Lemma rev_reverse_order_lt : forall L,
    (forall i j : nat,
        (j < length L)%nat ->
        (i < j)%nat -> (nth i L 0 < nth j L 0)%nat) ->
    forall i j : nat,
      (i < length (rev L))%nat ->
      (i > j)%nat -> (nth i (rev L) 0 < nth j (rev L) 0)%nat.
Proof.
  intros L H i j Hlen Hlt.
  rewrite rev_length in Hlen.
  rewrite ? rev_nth; try lia.
  apply H; lia.
Qed.

Lemma in_Type_map_cons A : forall (a : A) l L,
    In_Type l L ->
    In_Type (a :: l) (map (cons a) L).
Proof.
  intros a l; induction L; intros Hin ; [ inversion Hin | ].
  inversion Hin; subst.
  - simpl; left; reflexivity.
  - simpl; right; apply IHL.
    apply X.
Qed.

Lemma in_Type_map_cons_inv A : forall (a : A) l L,
    In_Type l (map (cons a) L) ->
    { l' & prod (l = a :: l') (In_Type l' L) }.
Proof.
  intros a l L; induction L; intros Hin; inversion Hin; subst.
  - split with a0.
    split; try reflexivity.
    left; reflexivity.
  - destruct (IHL X) as [l' [Heq Hin']].
    split with l'.
    repeat split; try assumption.
    right; apply Hin'.
Qed.

Lemma rev_not_nil A : forall (L : list A),
    L <> nil ->
    rev L <> nil.
Proof.
  destruct L; auto.
  simpl.
  intros _.
  intros H.
  assert (Permutation_Type (a :: rev L) nil); [ rewrite <- H; perm_Type_solve | ].
  symmetry in X; apply Permutation_Type_nil in X.
  inversion X.
Qed.

Lemma rev_nth_all_lt : forall l n,
    (forall i, nth i l 0 < n)%nat ->
    forall i, (nth i (rev l) 0 < n)%nat.
Proof.
  induction l; intros n H i.
  - destruct n; destruct i; auto.
  - simpl.
    case_eq (i <? length (rev l))%nat.
    + intros Hlt.
      rewrite app_nth1 ; [ | apply Nat.ltb_lt in Hlt; apply Hlt].
      apply IHl.
      intros i'.
      apply (H (S i')).
    + intros H'.
      rewrite app_nth2 ; [ | apply Nat.ltb_nlt in H'; lia].
      specialize (H 0%nat); simpl in H.
      remember (length (rev l)).
      clear - H H'.
      revert n0 H'.
      induction i; intros n0 H'.
      * simpl; apply H.
      *  destruct n0; [ destruct i; simpl; lia | ].
         change (S i - S n0)%nat with (i - n0)%nat.
         apply IHi.
         apply H'.
Qed.

Lemma Forall_Type_nth A : forall (P : A -> Type) (l : list A),
    Forall_Type P l ->
    forall (i : nat) (a : A), (i < length l)%nat -> P (nth i l a).
Proof.
  intros P; induction l; intros Hall i a' Hlen; [ exfalso; inversion Hlen | ].
  inversion Hall; subst.
  destruct i; [simpl; apply X | ].
  apply IHl; try assumption.
  simpl in Hlen; lia.
Qed.

Lemma nth_Forall_Type A : forall (P : A -> Type) (l : list A),
    (forall (i : nat) (a : A), (i < length l)%nat -> P (nth i l a)) ->
    Forall_Type P l.
Proof.
  intros P; induction l; intros H; [ apply Forall_Type_nil | ].
  apply Forall_Type_cons.
  - apply (H 0 a)%nat.
    simpl; lia.
  - apply IHl.
    intros i a' Hlen.
    apply (H (S i) a').
    simpl; lia.
Qed.

Fixpoint pos_indexes (L : list R) :=
  match L with
  | nil => nil
  | r :: L => if (0 <? r) then 0%nat :: map S (pos_indexes L) else map S (pos_indexes L)
  end.

Lemma pos_indexes_nth : forall L i,
    In_Type i (pos_indexes L) ->
    0 < nth i L 0.
Proof.
  induction L; intros i Hin; simpl in Hin; try now exfalso.
  case_eq (0 <? a); intros H; rewrite H in Hin.
  - destruct i.
    + apply R_blt_lt in H; apply H.
    + simpl; apply IHL.
      apply In_Type_map_S_inv.
      inversion Hin; [ exfalso; inversion H0 | ].
      apply X.
  - destruct i.
    + exfalso.
      apply not_0_In_Type_map_S with (pos_indexes L).
      apply Hin.
    + apply IHL; apply In_Type_map_S_inv; apply Hin.
Qed.

Lemma pos_indexes_Forall_Type : forall L,
    Forall_Type (fun n : nat => (n < length L)%nat) (pos_indexes L).
Proof.
  induction L; [ apply Forall_Type_nil | ].
  simpl.
  case_eq (0 <? a); intros _.
  - apply Forall_Type_cons.
    + lia.
    + apply Forall_Type_lt_map_S.
      apply IHL.
  - apply Forall_Type_lt_map_S; apply IHL.
Qed.

Lemma pos_indexes_not_In_Type : forall L i,
    (i < length L)%nat ->
    (In_Type i (pos_indexes L) -> False) ->
    (nth i L 0 <= 0).
Proof.
  induction L; intros i Hlen H; try now inversion Hlen.
  simpl in H.
  case_eq (0 <? a); intros Hlt; rewrite Hlt in H.
  - destruct i; [ exfalso; apply H; left; lia | ].
    simpl.
    apply IHL; [ simpl in Hlen; lia | ].
    intros Hin.
    apply H.
    right.
    apply in_Type_map.
    apply Hin.
  - destruct i; [ simpl; apply R_blt_nlt in Hlt; lra | ].
    simpl.
    apply IHL; [simpl in Hlen; lia | ].
    intros Hin.
    apply H.
    apply in_Type_map; apply Hin.
Qed.

Lemma pos_indexes_order : forall L,
    forall i j : nat,
      (j < length (pos_indexes L))%nat ->
      (i < j)%nat -> (nth i (pos_indexes L) 0 < nth j (pos_indexes L) 0)%nat.
Proof.
  induction L; intros i j Hlen Hlt ; [ now inversion Hlen | ].
  simpl.
  case_eq (0 <? a); intros H.
  - simpl in Hlen; rewrite H in Hlen.
    simpl in Hlen.
    destruct j; [inversion Hlt | ].
    destruct i; simpl.
    + rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
      rewrite map_nth.
      lia.
    + rewrite nth_indep with _ _ _ _ 1%nat ; [ | lia].
      rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
      rewrite ? map_nth.
      apply lt_n_S.
      rewrite map_length in Hlen.
      apply IHL; lia.
  - simpl in Hlen; rewrite H in Hlen.
    rewrite nth_indep with _ _ _ _ 1%nat ; [ | lia].
    rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
    rewrite ? map_nth.
    apply lt_n_S.
    rewrite map_length in Hlen.
    apply IHL; lia.
Qed.

Fixpoint p_sum_weight_var_with_coeff n G L :=
  match G, L with
  | _, nil => FOL_R_cst 0
  | nil, _ => FOL_R_cst 0
  | T :: G , r :: L => (r *R sum_weight_p_seq_var n T) +R p_sum_weight_var_with_coeff n G L
  end.

Lemma sum_weight_var_with_coeff_lt_max_var : forall n G L val,
    (max_var_p_hseq G < n)%nat ->
    FOL_R_term_sem val (p_sum_weight_var_with_coeff n G L) = 0.
Proof.
  intros n; induction G; intros L val Hlt; destruct L; auto.
  simpl in *.
  rewrite sum_weight_p_seq_var_lt_max_var; try lia.
  rewrite IHG; try lia.
  lra.
Qed.

Lemma sum_weight_var_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    sum_weight_var_with_coeff n (G1 ++ G2) L = sum_weight_var_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma sum_weight_var_with_coeff_app2 : forall n G1 G2 L1 L2,
    (length L1 = length G1) ->
    sum_weight_var_with_coeff n (G1 ++ G2) (L1 ++ L2) = sum_weight_var_with_coeff n G1 L1 + sum_weight_var_with_coeff n G2 L2.
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl; rewrite IHG1; auto.
  lra.
Qed.

Lemma sum_weight_var_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    sum_weight_var_with_coeff n G (L1 ++ L2) = sum_weight_var_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint sum_weight_covar_with_coeff n G L :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , r :: L => (r * sum_weight_seq_covar n T) + sum_weight_covar_with_coeff n G L
  end.

Lemma sum_weight_covar_with_coeff_lt_max_var : forall n G L,
    (max_var_hseq G < n)%nat ->
    sum_weight_covar_with_coeff n G L = 0.
Proof.
  intros n; induction G; intros L Hlt; destruct L; auto.
  simpl in *.
  rewrite sum_weight_seq_covar_lt_max_var; try lia.
  rewrite IHG; try lia.
  lra.
Qed.

Lemma sum_weight_covar_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    sum_weight_covar_with_coeff n (G1 ++ G2) L = sum_weight_covar_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma sum_weight_covar_with_coeff_app2 : forall n G1 G2 L1 L2,
    (length L1 = length G1) ->
    sum_weight_covar_with_coeff n (G1 ++ G2) (L1 ++ L2) = sum_weight_covar_with_coeff n G1 L1 + sum_weight_covar_with_coeff n G2 L2.
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl; rewrite IHG1; auto.
  lra.
Qed.

Lemma sum_weight_covar_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    sum_weight_covar_with_coeff n G (L1 ++ L2) = sum_weight_covar_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint exists_vec (v : list nat) (f : FOL_R_formula) :=
  match v with
  | nil => f
  | n :: v => FOL_R_exists n (exists_vec v f)
  end.

Fixpoint upd_val_vec (val : nat -> R) (vx : list nat) (vr : list R) :=
  match vx, vr with
  | nil , _ => val
  | _ , nil => val
  | x :: vx, r :: vr => upd_val_vec (upd_val val x r) vx vr
  end.

Lemma cond_FOL_R_exists_vec_formula_sem : forall v f val,
    {vr & prod (length v = length vr) (FOL_R_formula_sem (upd_val_vec val v vr) f)} ->
    FOL_R_formula_sem val (exists_vec v f).
Proof.
  induction v; intros f val [vr [Hlen Hf]].
  - apply Hf.
  - destruct vr; [inversion Hlen | ].
    simpl in *.
    split with r.
    apply IHv.
    split with vr.
    repeat split; auto.
Qed.

Lemma cond_FOL_R_exists_vec_formula_sem_inv : forall v f val,
    FOL_R_formula_sem val (exists_vec v f) ->
    {vr & prod (length v = length vr) (FOL_R_formula_sem (upd_val_vec val v vr) f)}.
Proof.
  induction v; intros f val Hf.
  - split with nil; split; auto.
  - destruct Hf as [r Hf].
    destruct (IHv _ _ Hf) as [vr [Hlen Hf']].
    split with (r :: vr).
    repeat split; simpl in *; try lia.
    apply Hf'.
Qed.

Lemma upd_val_vec_not_in : forall val L v x,
    (In_Type x v -> False) ->
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
      * apply not_In_Type_seq.
        lia.
      * apply not_In_Type_seq.
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

Lemma upd_val_vec_eq : forall L v n,
    upd_val_vec v (seq 0 (length L)) L n = nth n L (v n).
Proof.
  induction L; intros v n.
  - destruct n; reflexivity.
  - destruct n.
    + simpl.
      rewrite upd_val_vec_not_in; try reflexivity.
      apply not_In_Type_seq; lia.
    + simpl.
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
Qed.

Lemma map_upd_val_vec_eq : forall v L,
    map (upd_val_vec v (seq 0 (length L)) L) (seq 0 (length L)) = L.
Proof.
  intros v L.
  apply list_ext.
  { rewrite map_length; rewrite seq_length.
    reflexivity. }
  intros n a0.
  case_eq (n <? length L)%nat.
  - intros Hlt; apply Nat.ltb_lt in Hlt.
    rewrite nth_indep with _ _ _ _ (upd_val_vec v (seq 0 (length L)) L 0).
    2:{ rewrite map_length; rewrite seq_length.
        lia. }
    rewrite map_nth.
    rewrite seq_nth; [ | assumption].
    rewrite upd_val_vec_eq.
    rewrite nth_indep with _ _ _ _ a0 ; auto.
  - intros H; apply Nat.ltb_nlt in H.
    rewrite ? nth_overflow; try lia; auto.
    rewrite map_length; rewrite seq_length.
    lia.
Qed.
 
Lemma sum_weight_with_coeff_eq_var_covar : forall n G L,
    sum_weight_with_coeff n G L = sum_weight_var_with_coeff n G L - sum_weight_covar_with_coeff n G L.
Proof.
  intros n; induction G; intros L; destruct L; simpl; try rewrite IHG; lra.
Qed.

(* return a list of all non empty subsets of [0..n] *)
Fixpoint make_subsets n :=
  match n with
  | 0%nat => nil
  | S n => (n :: nil) :: (map (cons n) (make_subsets n)) ++ make_subsets n
  end.

Lemma cond_is_in_make_subsets : forall n l,
    l <> nil ->
    (forall i, nth i l 0 < n)%nat ->
    (forall i j, (j < length l)%nat -> (i < j)%nat -> (nth i l 0 > nth j l 0)%nat) ->
    In_Type l (make_subsets n).
Proof.
  induction n; intros l Hnnil Hle Hlt.
  - specialize (Hle 0%nat).
    exfalso; destruct l; inversion Hle.
  - destruct l; [exfalso; apply Hnnil; reflexivity | ].
    case_eq (n0 =? n); intros Heq.
    + apply Nat.eqb_eq in Heq; subst.
      destruct l.
      * left; reflexivity.
      * right.
        apply in_Type_or_app; left.
        apply in_Type_map_cons.
        apply IHn.
        -- intros H'; inversion H'.
        -- intros i.
           case_eq (i <? length (n0 :: l))%nat; intros H.
           ++ specialize (Hlt 0%nat (S i)).
              simpl in Hlt.
              change (match i with
                      | 0 => n0
                      | S m => nth m l 0
                      end)%nat with (nth i (n0 :: l) 0)%nat in Hlt.
              apply Nat.ltb_lt in H; simpl in H.
              lia.
           ++ apply Nat.ltb_nlt in H.
              rewrite nth_overflow ; destruct n; try lia.
              exfalso.
              specialize (Hlt 0 1)%nat.
              simpl in Hlt; lia.
        -- intros i j Hlen' Hlt'.
           assert (H' := Hlt (S i) (S j)).
           change (nth (S i) (S n :: n0 :: l) 0%nat) with (nth i (n0 :: l) 0%nat) in *.
           change (nth (S j) (S n :: n0 :: l) 0)%nat with (nth j (n0 :: l) 0%nat) in *.
           apply H'; simpl in *; lia.
    + right; apply in_Type_or_app; right.
      apply IHn.
      -- intros H'; inversion H'.
      -- intros i.
         destruct i; [ specialize (Hle 0%nat); apply Nat.eqb_neq in Heq; simpl in *; lia | ].
         case_eq (S i <? length (n0 :: l))%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H].
         ++ specialize (Hle i).
            specialize (Hlt i (S i)).
            lia.
         ++ rewrite nth_overflow; destruct n; try lia.
            destruct n0; inversion Heq.
            specialize (Hle 0)%nat.
            simpl in Hle; lia.
      -- intros i j Hlen' Hlt'.
         specialize (Hle j); specialize (Hlt i j).
         apply Hlt; lia.
Qed.

Lemma cond_is_in_make_subsets_inv : forall n l,
    In_Type l (make_subsets n) ->
    (l <> nil) * (forall i, nth i l 0 < n)%nat * (forall i j, (j < length l)%nat -> (i < j)%nat -> (nth i l 0 > nth j l 0)%nat).
Proof.
  induction n; intros l; [ intros Hin | intros [Heq | Hin]].
  - inversion Hin.
  - destruct l; [ | destruct l]; inversion Heq; subst.
    repeat split.
    + intros H; inversion H.
    + intros i; destruct i; [ | destruct i]; simpl; lia.
    + intros i j Hlen Hlt.
      destruct j ; [inversion Hlt | ].
      destruct j; try now inversion Hlen.
  - destruct (in_Type_app_or _ _ _ Hin).
    + destruct (in_Type_map_cons_inv _ _ _ _ i) as [l' [Heq Hin']]; subst.
      destruct (IHn l' Hin') as [[Hnnil Hlen] Hlt].
      clear i Hin.
      repeat split.
      * intros H; inversion H.
      * intros i.
        destruct i.
        -- simpl; lia.
        -- specialize (Hlen i).
           simpl.
           lia.
      * intros i j Hlen' Hlt'.
        destruct j; try now inversion Hlt'.
        change (nth (S j) (S n :: l') 0)%nat with (nth j l' 0)%nat.
        destruct i.
        -- simpl.
           specialize (Hlen j).
           lia.
        -- change (nth (S i) (S n :: l') 0)%nat with (nth i l' 0)%nat.
           apply Hlt; simpl in *; lia.
    + specialize (IHn l i).
      clear Hin i.
      destruct IHn as [[Hnil Hlen] Hlt].
      repeat split; auto.
      intro i; specialize (Hlen i); lia.
Qed.    
    
(* return the complementary list of v *)
Fixpoint complementary (v : list nat) n :=
  match v with
  | nil => seq 0%nat n
  | i :: v => remove (Nat.eq_dec) i (complementary v n)
  end.

Lemma In_Type_complementary : forall v n i,
    In_Type i v ->
    In_Type i (complementary v n) ->
    False.
Proof.
  induction v; intros n i Hin1 Hin2; [ inversion Hin1 | ].
  simpl in Hin2.
  case_eq (i =? a); intros H.
  - apply Nat.eqb_eq in H; subst.
    apply In_Type_remove_not in Hin2.
    apply Hin2.
  - inversion Hin1; [ apply Nat.eqb_neq in H; lia | ].
    apply IHv with n i; auto.
    apply In_Type_remove_In_Type in Hin2.
    apply Hin2.
Qed.

Lemma In_Type_complementary_inv : forall v n i,
    (i < n)%nat ->
    (In_Type i (complementary v n) -> False) ->
    In_Type i v.
Proof.
  induction v; intros n i Hlt H.
  - exfalso; apply H.
    replace i with (i + 0)%nat by lia.
    apply In_Type_seq.
    apply Hlt.
  - simpl in *.
    case_eq (a =? i); intros Heq.
    + left.
      apply Nat.eqb_eq in Heq; auto.
    + right.
      apply IHv with n; auto.
      intros Hin.
      apply H.
      apply In_Type_remove_In_Type_inv.
      apply Nat.eqb_neq in Heq; split; auto.    
Qed.

Lemma In_Type_complementary2 : forall v n i,
    In_Type i (complementary v n) ->
    In_Type i v ->
    False.
Proof.
  induction v; intros n i Hin1 Hin2; [ inversion Hin2 | ].
  simpl in Hin1.
  case_eq (i =? a); intros H.
  - apply Nat.eqb_eq in H; subst.
    apply In_Type_remove_not in Hin1.
    apply Hin1.
  - inversion Hin2; [ apply Nat.eqb_neq in H; lia | ].
    apply IHv with n i; auto.
    apply In_Type_remove_In_Type in Hin1.
    apply Hin1.
Qed.

Lemma In_Type_complementary2_inv : forall v n i,
    (i < n)%nat ->
    (In_Type i v -> False) ->
    In_Type i (complementary v n).
Proof.
  induction v; intros n i Hlt H.
  - replace i with (i + 0)%nat by lia.
    apply In_Type_seq.
    apply Hlt.
  - simpl in *.
    case_eq (a =? i); intros Heq.
    + exfalso; apply H; left; apply Nat.eqb_eq; apply Heq.
    + apply In_Type_remove_In_Type_inv.
      apply Nat.eqb_neq in Heq; split; auto.    
Qed.

Lemma complementary_partition : forall v n i,
    (i < n)%nat ->
    (In_Type i v) + (In_Type i (complementary v n)).
Proof.
  intros v n i Hlt.
  assert (Hin := in_Type_dec Nat.eq_dec i v).
  inversion Hin.
  - left; apply X.
  - right.
    apply In_Type_complementary2_inv; auto.
Qed.  
  
Lemma In_Type_complementary_lt : forall L n i,
    In_Type i (complementary L n) ->
    (i < n)%nat.
Proof.
  induction L; intros n i Hin.
  - simpl complementary in Hin.
    replace n with (0 + n)%nat by lia.
    apply In_Type_seq_lt.
    apply Hin.
  - simpl in Hin.
    apply In_Type_remove_In_Type in Hin as [Hneq Hin].
    apply IHL; auto.
Qed.

(* return the conjunction /\(beta_i = 0) for all i \in v *)
Fixpoint FOL_R_all_zero (v : list nat) :=
  match v with
  | nil => FOL_R_true
  | n :: v => FOL_R_and (FOL_R_atoms (FOL_R_eq (FOL_R_var n) (FOL_R_cst 0))) (FOL_R_all_zero v)
  end.

Lemma cond_FOL_R_all_zero_formula_sem : forall v val,
    (forall n, In_Type n v -> val n = 0) ->
    FOL_R_formula_sem val (FOL_R_all_zero v).
Proof.
  induction v; intros val H; [apply I | ].
  split.
  - apply H.
    apply in_Type_eq.
  - apply IHv.
    intros n Hin.
    apply H.
    apply in_Type_cons; apply Hin.
Qed.
    
Lemma cond_FOL_R_all_zero_formula_sem_inv : forall v val,
    FOL_R_formula_sem val (FOL_R_all_zero v) ->
    forall n, In_Type n v -> val n = 0.
Proof.
  induction v; intros val Hf n Hin; inversion Hin; subst.
  - destruct Hf as [Heq _]; apply Heq.
  - destruct Hf as [_ Hf].
    apply IHv; assumption.
Qed.

(* return the conjunction /\(0\leq\beta_i /\ \beta_i = 0) for all in \in v *)
Fixpoint FOL_R_all_gtz (v : list nat ) :=
  match v with
  | nil => FOL_R_true
  | n :: v => FOL_R_and (FOL_R_and (FOL_R_neg (FOL_R_atoms (FOL_R_eq (FOL_R_var n) (FOL_R_cst 0)))) (FOL_R_atoms (FOL_R_le (FOL_R_cst 0) (FOL_R_var n)))) (FOL_R_all_gtz v)
  end.

Lemma cond_FOL_R_all_gtz_formula_sem : forall v val,
    (forall n, In_Type n v -> 0 < val n) ->
    FOL_R_formula_sem val (FOL_R_all_gtz v).
Proof.
  induction v; intros val H; [apply I | ].
  split.
  - specialize (H a (in_Type_eq a v)).
    split; simpl; lra.
  - apply IHv.
    intros n Hin.
    apply H.
    apply in_Type_cons; apply Hin.
Qed.
    
Lemma cond_FOL_R_all_gtz_formula_sem_inv : forall v val,
    FOL_R_formula_sem val (FOL_R_all_gtz v) ->
    forall n, In_Type n v -> 0 < val n.
Proof.
  induction v; intros val Hf n Hin; inversion Hin; subst.
  - destruct Hf as [[Hneq Hle] _].
    simpl in *; lra.
  - destruct Hf as [_ Hf].
    apply IHv; assumption.
Qed.

(* return \sum_i^m \beta_i \sum\vec R_{i,j} *)
Fixpoint FOL_R_sum_var G j m :=
  match m  with
  | 0%nat  => FOL_R_mul (sum_weight_seq_var j (nth 0%nat G nil)) (FOL_R_var 0%nat)
  | S m => FOL_R_add (FOL_R_mul (sum_weight_seq_var j (nth (S m) G nil)) (FOL_R_var (S m))) (FOL_R_sum_var G j m)
  end.

Lemma FOL_R_sum_var_term_sem : forall G j m val,
    FOL_R_term_sem val (FOL_R_sum_var G j m) = sum_weight_var_with_coeff j G (map val (seq 0%nat (S m))).
Proof.
  intros G j; induction m; intros val.
  - simpl.
    destruct G; [ | destruct G]; simpl; lra.
  - simpl.
    rewrite IHm.
    clear IHm.
    change (val 0%nat :: val 1%nat :: map val (seq 2 m)) with (map val (seq 0 (S (S m)))).
    remember (length G).
    revert G j m val Heqn.
    induction n; intros G j m val Heqn.
    + destruct G; [ | inversion Heqn].
      simpl.
      lra.
    + assert (G <> nil) as Hnnil.
      { destruct G; now inversion Heqn. }
      destruct (exists_last Hnnil) as [H [T Heq]].
      rewrite Heq.
      case_eq ((S m <? length H)%nat); intros Hlen; [ apply Nat.ltb_lt in Hlen | apply Nat.ltb_nlt in Hlen ].
      * rewrite app_nth1; try assumption.
        rewrite Heq in Heqn.
        rewrite app_length in Heqn; simpl in Heqn.
        rewrite ? sum_weight_var_with_coeff_app1; try (rewrite map_length; rewrite seq_length).
        -- apply IHn.
           lia.
        -- apply Hlen.
        -- apply Nat.lt_le_incl; apply Hlen.
      * rewrite app_nth2; try lia.
        clear Heq.
        case_eq (S m =? length H); intros Heq; [apply Nat.eqb_eq in Heq | apply Nat.eqb_neq in Heq].
        -- replace ((S m - length H)%nat) with 0%nat by lia.
           rewrite (seq_S _ (S m)).
           rewrite sum_weight_var_with_coeff_app1 ; [ | rewrite map_length; rewrite seq_length;rewrite Heq; apply Nat.le_refl ].
           rewrite map_app; rewrite sum_weight_var_with_coeff_app2 ; [ | rewrite map_length; rewrite seq_length;apply Heq].
           simpl.
           lra.
        -- rewrite (seq_S _ (S m)).
           rewrite Nat.sub_succ_l ; [ | lia].
           rewrite map_app.
           rewrite (sum_weight_var_with_coeff_app3 j (H ++ T :: nil)) ; [ | rewrite map_length; rewrite seq_length; rewrite app_length; simpl; lia].
           remember ((m - length H)%nat).
           destruct n0; simpl; lra.
Qed.
           
(* return \sum_i^m \beta_i \sum\vec S_{i,j} *)
Fixpoint FOL_R_sum_covar G j m :=
  match m  with
  | 0%nat  => FOL_R_mul (sum_weight_seq_covar j (nth 0%nat G nil)) (FOL_R_var 0%nat)
  | S m => FOL_R_add (FOL_R_mul (sum_weight_seq_covar j (nth (S m) G nil)) (FOL_R_var (S m))) (FOL_R_sum_covar G j m)
  end.

Lemma FOL_R_sum_covar_term_sem : forall G j m val,
    FOL_R_term_sem val (FOL_R_sum_covar G j m) = sum_weight_covar_with_coeff j G (map val (seq 0%nat (S m))).
Proof.
  intros G j; induction m; intros val.
  - simpl.
    destruct G; [ | destruct G]; simpl; lra.
  - simpl.
    rewrite IHm.
    clear IHm.
    change (val 0%nat :: val 1%nat :: map val (seq 2 m)) with (map val (seq 0 (S (S m)))).
    remember (length G).
    revert G j m val Heqn.
    induction n; intros G j m val Heqn.
    + destruct G; [ | inversion Heqn].
      simpl.
      lra.
    + assert (G <> nil) as Hnnil.
      { destruct G; now inversion Heqn. }
      destruct (exists_last Hnnil) as [H [T Heq]].
      rewrite Heq.
      case_eq ((S m <? length H)%nat); intros Hlen; [ apply Nat.ltb_lt in Hlen | apply Nat.ltb_nlt in Hlen ].
      * rewrite app_nth1; try assumption.
        rewrite Heq in Heqn.
        rewrite app_length in Heqn; simpl in Heqn.
        rewrite ? sum_weight_covar_with_coeff_app1; try (rewrite map_length; rewrite seq_length).
        -- apply IHn.
           lia.
        -- apply Hlen.
        -- apply Nat.lt_le_incl; apply Hlen.
      * rewrite app_nth2; try lia.
        clear Heq.
        case_eq (S m =? length H); intros Heq; [apply Nat.eqb_eq in Heq | apply Nat.eqb_neq in Heq].
        -- replace ((S m - length H)%nat) with 0%nat by lia.
           rewrite (seq_S _ (S m)).
           rewrite sum_weight_covar_with_coeff_app1 ; [ | rewrite map_length; rewrite seq_length;rewrite Heq; apply Nat.le_refl ].
           rewrite map_app; rewrite sum_weight_covar_with_coeff_app2 ; [ | rewrite map_length; rewrite seq_length;apply Heq].
           simpl.
           lra.
        -- rewrite (seq_S _ (S m)).
           rewrite Nat.sub_succ_l ; [ | lia].
           rewrite map_app.
           rewrite (sum_weight_covar_with_coeff_app3 j (H ++ T :: nil)) ; [ | rewrite map_length; rewrite seq_length; rewrite app_length; simpl; lia].
           remember ((m - length H)%nat).
           destruct n0; simpl; lra.
Qed.

(* return the conjunction /\(\sum_i^m \beta_i \sum\vec R_{i,j} = \sum_i^m \beta_i \sum\vec S_{i,j} *)
Fixpoint FOL_R_all_atoms_eq G k:=
  match k with
  | 0%nat => FOL_R_atoms (FOL_R_eq (FOL_R_sum_var G 0%nat (pred (length G))) (FOL_R_sum_covar G 0%nat (pred (length G))))
  | S k => FOL_R_and (FOL_R_atoms (FOL_R_eq (FOL_R_sum_var G (S k) (pred (length G))) (FOL_R_sum_covar G (S k) (pred (length G))))) (FOL_R_all_atoms_eq G k)
  end.


Lemma cond_FOL_R_all_atoms_eq_formula_sem : forall G k val,
    (forall n, (n <= k)%nat -> sum_weight_with_coeff n G (map val (seq 0 (length G))) = 0) ->
    FOL_R_formula_sem val (FOL_R_all_atoms_eq G k).
Proof.
  intros G; induction k; intros val H.
  - simpl.
    rewrite FOL_R_sum_var_term_sem.
    rewrite FOL_R_sum_covar_term_sem.
    specialize (H 0%nat (Nat.le_refl 0%nat)).
    destruct G; try reflexivity.
    change (S (Init.Nat.pred (length (s :: G)))) with (length (s :: G)).
    rewrite sum_weight_with_coeff_eq_var_covar in H.
    lra.
  - simpl.
    split.
    + rewrite FOL_R_sum_var_term_sem.
      rewrite FOL_R_sum_covar_term_sem.
      specialize (H (S k) (Nat.le_refl (S k))).
      destruct G; try reflexivity.
      change (S (Init.Nat.pred (length (s :: G)))) with (length (s :: G)).
      rewrite sum_weight_with_coeff_eq_var_covar in H.
      lra.
    + apply IHk.
      intros n Hle.
      apply H.
      lia.
Qed.
    
Lemma cond_FOL_R_all_atoms_eq_formula_sem_inv : forall G k val,
    FOL_R_formula_sem val (FOL_R_all_atoms_eq G k) ->
    forall n, (n <= k)%nat -> sum_weight_with_coeff n G (map val (seq 0 (length G))) = 0.
Proof.
  intros G; induction k; intros val Hf n Hle.
  - simpl in Hf.
    destruct n; inversion Hle.
    rewrite sum_weight_with_coeff_eq_var_covar.
    rewrite FOL_R_sum_var_term_sem in Hf.
    rewrite FOL_R_sum_covar_term_sem in Hf.
    destruct G; try (simpl; lra).
    change (S (Init.Nat.pred (length (l :: G)))) with (length (l :: G)) in Hf.
    lra.
  - destruct Hf as [Hf1 Hf2].
    case_eq (n =? S k)%nat; intros Heq.
    + simpl in Hf1.
      rewrite sum_weight_with_coeff_eq_var_covar.
      rewrite FOL_R_sum_var_term_sem in Hf1.
      rewrite FOL_R_sum_covar_term_sem in Hf1.
      destruct G; try (simpl; lra).
      change (S (Init.Nat.pred (length (l :: G)))) with (length (l :: G)) in Hf1.
      apply Nat.eqb_eq in Heq; rewrite Heq.
      lra.
    + apply IHk ; try assumption.
      apply Nat.eqb_neq in Heq.
      lia.
Qed.

(* return the formula corresponding to \phi_{G,v} *)
Definition FOL_R_phi G v := FOL_R_and (FOL_R_all_zero (complementary v (length G))) (FOL_R_and (FOL_R_all_gtz v) (FOL_R_all_atoms_eq G (max_var_hseq G))).

(* Since FOL_R_phi is just an AND (so is implemented as a product), the condition lemmas are not necessary *)

(* return the formula corresponding to \exists \beta_1,....,\beta_n \phi_{G,v} *)
Definition FOL_R_exists_phi G v :=
  exists_vec (seq 0%nat (length G)) (FOL_R_phi G v).

Lemma cond_FOL_R_exists_phi_formula_sem : forall G v val,
    { vr & prod (length vr = length G) (FOL_R_formula_sem (upd_val_vec val (seq 0 (length G)) vr) (FOL_R_phi G v)) } ->
    FOL_R_formula_sem val (FOL_R_exists_phi G v).
Proof.
  intros G v val [vr [Hlen Hf]].
  apply cond_FOL_R_exists_vec_formula_sem.
  split with vr.
  split; auto.
  rewrite seq_length.
  rewrite Hlen; reflexivity.
Qed.  
    
Lemma cond_FOL_R_exists_phi_formula_sem_inv : forall G v val,
    FOL_R_formula_sem val (FOL_R_exists_phi G v) ->
    { vr & prod (length vr = length G) (FOL_R_formula_sem (upd_val_vec val (seq 0 (length G)) vr) (FOL_R_phi G v)) }.
Proof.
  intros G v val Hf.
  apply cond_FOL_R_exists_vec_formula_sem_inv in Hf as [vr [Hlen Hf]].
  split with vr.
  split; auto.
  rewrite seq_length in Hlen; rewrite Hlen; reflexivity.
Qed.

(* return the whole formula for the atomic case *)
Fixpoint FOL_R_atomic_case_aux G V :=
  match V with
  | nil => FOL_R_false
  | v :: V => FOL_R_or (FOL_R_exists_phi G v) (FOL_R_atomic_case_aux G V)
  end.

Lemma cond_FOL_R_atomic_case_aux_formula_sem : forall G V val,
    { v : _ & In_Type v V & FOL_R_formula_sem val (FOL_R_exists_phi G v)} ->
    FOL_R_formula_sem val (FOL_R_atomic_case_aux G V).
Proof.
  intros G; induction V; intros val [v Hin Hf]; inversion Hin; subst.
  - left.
    apply Hf.
  - right.
    apply IHV.
    split with v; assumption.
Qed.

Lemma cond_FOL_R_atomic_case_aux_formula_sem_inv : forall G V val,
    FOL_R_formula_sem val (FOL_R_atomic_case_aux G V) ->
    { v : _ & In_Type v V & FOL_R_formula_sem val (FOL_R_exists_phi G v)}.
Proof.
  intros G V; induction V; intros val Hf; inversion Hf.
  - split with a; auto.
    apply in_Type_eq.
  - destruct (IHV val X) as [v Hin Hf'].
    split with v; try assumption.
    now apply in_Type_cons.
Qed.

Definition FOL_R_atomic_case G  :=
  FOL_R_atomic_case_aux G (make_subsets (length G)).

Lemma HR_FOL_R_equiv : forall G,
    { f & prod
            (HR_full G -> FOL_R_valid f)
            (FOL_R_valid f -> HR_full G) }.
Proof.
  enough (forall G,
             { f & prod
                     (HR_T G -> FOL_R_valid f)
                     (FOL_R_valid f -> HR_full G) }).
  { intros G.
    specialize (X G) as [f [H1 H2]].
    split with f.
    split.
    - intros pi.
      apply H1.
      apply hrr_M_elim.
      apply hrr_can_elim.
      apply pi.
    - apply H2. }
  intros G; remember (HR_complexity_hseq G) as a.
  revert G Heqa.
  apply (lt_nat2_wf_rect a).
  intros n Hind.
  intros G Heqn.
  destruct n as [n m].
  destruct n.
  - split with (FOL_R_atomic_case G).
    split.
    + intros pi.
      unfold FOL_R_atomic_case.
      intros v.
      apply cond_FOL_R_atomic_case_aux_formula_sem.
      apply HR_le_frag with _ (hr_frag_T_M) _ in pi ; [ | repeat split; auto].
      assert (hseq_is_atomic G) as Hat.
      { apply hseq_is_atomic_complexity_0_inv.
        rewrite <- Heqn; reflexivity. }
      destruct (lambda_prop _ Hat pi) as [L [Hlen [[Hex Hall] Hsum]]].
      split with (rev (pos_indexes L)).
      { apply cond_is_in_make_subsets.
        - apply rev_not_nil.
          clear - Hex.
          induction L; [inversion Hex | ].
          inversion Hex; subst.
          + apply R_blt_lt in H0.
            simpl; rewrite H0.
            intros H; inversion H.
          + case_eq (0 <? a); intros H; [ simpl; rewrite H; intros H'; inversion H' | ].
            simpl; rewrite H.
            intros H'; apply map_eq_nil in H'.
            apply IHL; assumption.
        - intros i.
          apply rev_nth_all_lt.
          clear i.
          intros i.
          case_eq (i <? length (pos_indexes L))%nat.
          + intros Hlt; apply Nat.ltb_lt in Hlt.
            apply Forall_Type_nth; try assumption.
            change (list (prod Rpos term)) with sequent.
            rewrite <- Hlen.
            apply pos_indexes_Forall_Type.
          + intros Hlt; apply Nat.ltb_nlt in Hlt; rewrite nth_overflow; destruct G; simpl; try lia.
            apply HR_not_empty in pi.
            exfalso; auto.            
        - intros i j Hlen' Hlt'.
          apply rev_reverse_order_lt; try lia.
          apply pos_indexes_order. }
      apply cond_FOL_R_exists_phi_formula_sem.
      split with L.
      split; [ apply Hlen | ].
      repeat split.
      * apply cond_FOL_R_all_zero_formula_sem.
        intros n Hin.
        change (list (prod Rpos term)) with sequent.
        rewrite <- Hlen.
        rewrite upd_val_vec_eq.
        enough (nth n L (v n) <= 0).
        { apply Forall_Type_nth with _ _ _ n (v n) in Hall; [ lra | ].
          apply In_Type_complementary_lt with (rev (pos_indexes L)).
          change (list (prod Rpos term)) with sequent in Hin.
          rewrite <- Hlen in Hin.
          apply Hin. }
        rewrite nth_indep with _ _ _ _ 0.
        2:{ apply In_Type_complementary_lt with (rev (pos_indexes L)).
            change (list (prod Rpos term)) with sequent in Hin.
            rewrite <- Hlen in Hin.
            apply Hin. }
        apply pos_indexes_not_In_Type.
        -- apply In_Type_complementary_lt with (rev (pos_indexes L)).
           change (list (prod Rpos term)) with sequent in Hin.
           rewrite <- Hlen in Hin.
           apply Hin.
        -- intros H.
           apply In_Type_complementary in Hin; auto.
           apply In_Type_rev.
           apply H.
      * apply cond_FOL_R_all_gtz_formula_sem.
        intros n Hin.
        change (list (prod Rpos term)) with sequent.
        rewrite <- Hlen.
        rewrite upd_val_vec_eq.
        assert (n < length L)%nat as Hlt.
        { apply (@Forall_Type_forall _ (fun x => x < length L)%nat) with (pos_indexes L); [ apply pos_indexes_Forall_Type | ].
          apply In_Type_rev_inv.
          apply Hin. }
        rewrite nth_indep with _ _ _ _ 0; auto.
        apply pos_indexes_nth.
        apply In_Type_rev_inv.
        apply Hin.        
      * apply cond_FOL_R_all_atoms_eq_formula_sem.
        intros n Hlen'.
        change (list (prod Rpos term)) with sequent.
        rewrite <- Hlen.
        rewrite map_upd_val_vec_eq.
        apply Hsum.      
    + intros f.
      unfold FOL_R_atomic_case in f.
      specialize (f (fun x => 0)).
      apply cond_FOL_R_atomic_case_aux_formula_sem_inv in f as [v Hin f].
      apply cond_FOL_R_exists_phi_formula_sem_inv in f as [vr [Hlen f]].
      destruct f as [f1 [f2 f3]].
      apply HR_le_frag with hr_frag_T_M ; [repeat split; auto | ].
      apply lambda_prop_inv.
      { apply hseq_is_atomic_complexity_0_inv.
        rewrite <- Heqn; reflexivity. }
      split with (map (upd_val_vec (fun _ : nat => 0) (seq 0 (length G)) vr) (seq 0 (length G))).
      repeat split.
      * rewrite map_length.
        rewrite seq_length.
        reflexivity.
      * clear f1 f3.
        apply cond_is_in_make_subsets_inv in Hin as [[Hnnil Hle] Hlt].
        destruct v ; [ exfalso; apply Hnnil; auto | ].
        apply Exists_Type_nth with 0.
        split with n.
        split.
        -- rewrite map_length.
           rewrite seq_length.
           apply (Hle 0)%nat.
        -- change sequent with (list (prod Rpos term)).
           rewrite <- Hlen.
           rewrite map_upd_val_vec_eq.
           apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ n in f2.
           2:{ left; auto. }
           rewrite <- Hlen in f2.
           rewrite upd_val_vec_eq in f2.
           apply f2.
      * clear f3.
        change sequent with (list (prod Rpos term)).
        rewrite <- Hlen.
        rewrite map_upd_val_vec_eq.
        apply nth_Forall_Type.
        intros i a' Hlt.
        destruct (complementary_partition v (length vr) i); auto.
        -- apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ i in f2; auto.
           rewrite <- Hlen in f2; rewrite upd_val_vec_eq in f2.
           rewrite nth_indep with _ _ _ _ 0; auto.
           apply Rlt_le.
           apply f2.
        -- rewrite Hlen in i0.
           apply cond_FOL_R_all_zero_formula_sem_inv with _ _ i in f1; auto.
           rewrite <- Hlen in f1.
           rewrite upd_val_vec_eq in f1.
           rewrite nth_indep with _ _ _ _ 0; auto.
           lra.
      * clear f1 f2.
        intros n.
        case_eq (n <=? max_var_hseq G)%nat; intros Hle.
        -- apply cond_FOL_R_all_atoms_eq_formula_sem_inv with _ _ _ n in f3 ; [ | apply Nat.leb_le in Hle; auto].
           apply f3.
        -- apply Nat.leb_nle in Hle.
           clear - Hle.
           rewrite sum_weight_with_coeff_eq_var_covar.
           rewrite sum_weight_var_with_coeff_lt_max_var; try lia.
           rewrite sum_weight_covar_with_coeff_lt_max_var; try lia.
           lra.
  - destruct complexity_hseq_perm_fst with G as [[T H] Hperm Heqc].
    { destruct G; [ | intro H; inversion H].
      inversion Heqn. }
    destruct seq_non_atomic_perm with T as [[A D] Hperm' Hnat].
    { intros Hat.
      apply seq_is_atomic_complexity_0 in Hat.
      rewrite <- Heqn in Heqc; rewrite Heqc in Hat.
      inversion Hat. }
    destruct A as [r A]; simpl in Hnat.
    destruct A; try (exfalso; now apply Hnat).
    + destruct Hind with (HR_complexity_hseq (D :: H)) (D :: H) as [f [H1 H2]].
      * rewrite Heqn.
        rewrite (complexity_hseq_perm _ _ Hperm).
        change sequent with (list (prod Rpos term)).
        rewrite (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change ((r , zero) :: D) with (vec (r :: nil) zero ++ D).
        apply hrr_Z_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change (list (prod Rpos term)) with sequent.
        rewrite <- (complexity_hseq_perm _ _ Hperm).
        rewrite <- (complexity_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * split with f.
        split.
        -- intros pi.
           apply H1.
           apply hrr_M_elim.
           apply hrr_Z_inv with (r :: nil).
           eapply hrr_ex_seq ; [ apply Hperm' | eapply hrr_ex_hseq ; [ apply Hperm | ]].
           eapply HR_le_frag ; [ | apply pi].
           repeat split; auto.
        -- intros  Hf.
           eapply hrr_ex_hseq ; [ symmetry; apply Hperm | eapply hrr_ex_seq ; [ symmetry; apply Hperm' | ]].
           change ((r, zero) :: D) with (vec (r :: nil) zero ++ D).
           apply hrr_Z.
           apply H2.
           apply Hf.
    + destruct Hind with (HR_complexity_hseq ((vec (r :: nil) A1 ++ vec (r :: nil) A2 ++ D) :: H)) ((vec (r :: nil) A1 ++ vec (r :: nil) A2 ++ D) :: H) as [f [H1 H2]].
      * rewrite Heqn.
        rewrite (complexity_hseq_perm _ _ Hperm).
        change sequent with (list (prod Rpos term)).
        rewrite (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change ((r , A1 +S A2) :: D) with (vec (r :: nil) (A1 +S A2) ++ D).
        apply hrr_plus_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change (list (prod Rpos term)) with sequent.
        rewrite <- (complexity_hseq_perm _ _ Hperm).
        rewrite <- (complexity_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * split with f.
        split.
        -- intros pi.
           apply H1.
           apply hrr_M_elim.
           apply hrr_plus_inv.
           eapply hrr_ex_seq ; [ apply Hperm' | eapply hrr_ex_hseq ; [ apply Hperm | ]].
           eapply HR_le_frag ; [ | apply pi].
           repeat split; auto.
        -- intros  Hf.
           eapply hrr_ex_hseq ; [ symmetry; apply Hperm | eapply hrr_ex_seq ; [ symmetry; apply Hperm' | ]].
           change ((r, A1 +S A2) :: D) with (vec (r :: nil) (A1 +S A2) ++ D).
           apply hrr_plus.
           apply H2.
           apply Hf.
    + destruct Hind with (HR_complexity_hseq ((vec (mul_vec r0 (r :: nil)) A ++ D) :: H)) ((vec (mul_vec r0 (r :: nil)) A ++ D) :: H) as [f [H1 H2]].
      * rewrite Heqn.
        rewrite (complexity_hseq_perm _ _ Hperm).
        change sequent with (list (prod Rpos term)).
        rewrite (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change ((r , r0 *S A) :: D) with (vec (r :: nil) (r0 *S A) ++ D).
        apply hrr_mul_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change (list (prod Rpos term)) with sequent.
        rewrite <- (complexity_hseq_perm _ _ Hperm).
        rewrite <- (complexity_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * split with f.
        split.
        -- intros pi.
           apply H1.
           apply hrr_M_elim.
           apply hrr_mul_inv.
           eapply hrr_ex_seq ; [ apply Hperm' | eapply hrr_ex_hseq ; [ apply Hperm | ]].
           eapply HR_le_frag ; [ | apply pi].
           repeat split; auto.
        -- intros  Hf.
           eapply hrr_ex_hseq ; [ symmetry; apply Hperm | eapply hrr_ex_seq ; [ symmetry; apply Hperm' | ]].
           change ((r, r0 *S A) :: D) with (vec (r :: nil) (r0 *S A) ++ D).
           apply hrr_mul.
           apply H2.
           apply Hf.
    + destruct Hind with (HR_complexity_hseq ((vec (r :: nil) A2 ++ D) :: (vec (r :: nil) A1 ++ D) :: H)) ((vec (r :: nil) A2 ++ D) :: (vec (r :: nil) A1 ++ D) :: H) as [f [H1 H2]].
      * rewrite Heqn.
        rewrite (complexity_hseq_perm _ _ Hperm).
        change sequent with (list (prod Rpos term)).
        rewrite (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change ((r , A1 \/S A2) :: D) with (vec (r :: nil) (A1 \/S A2) ++ D).
        apply hrr_max_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change (list (prod Rpos term)) with sequent.
        rewrite <- (complexity_hseq_perm _ _ Hperm).
        rewrite <- (complexity_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * split with f.
        split.
        -- intros pi.
           apply H1.
           apply hrr_M_elim.
           apply hrr_max_inv.
           eapply hrr_ex_seq ; [ apply Hperm' | eapply hrr_ex_hseq ; [ apply Hperm | ]].
           eapply HR_le_frag ; [ | apply pi].
           repeat split; auto.
        -- intros  Hf.
           eapply hrr_ex_hseq ; [ symmetry; apply Hperm | eapply hrr_ex_seq ; [ symmetry; apply Hperm' | ]].
           change ((r, A1 \/S A2) :: D) with (vec (r :: nil) (A1 \/S A2) ++ D).
           apply hrr_max.
           apply H2.
           apply Hf.
    + destruct Hind with (HR_complexity_hseq ((vec (r :: nil) A1 ++ D) :: H)) ((vec (r :: nil) A1 ++ D) :: H) as [f [H1 H2]].
      * rewrite Heqn.
        rewrite (complexity_hseq_perm _ _ Hperm).
        change sequent with (list (prod Rpos term)).
        rewrite (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change ((r , A1 /\S A2) :: D) with (vec (r :: nil) (A1 /\S A2) ++ D).
        apply hrr_min_r_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_hseq_perm_fst_seq _ _ H Hperm').
        change (list (prod Rpos term)) with sequent.
        rewrite <- (complexity_hseq_perm _ _ Hperm).
        rewrite <- (complexity_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * destruct Hind with (HR_complexity_hseq ((vec (r :: nil) A2 ++ D) :: H)) ((vec (r :: nil) A2 ++ D) :: H) as [f2 [H3 H4]].
        -- rewrite Heqn.
           rewrite (complexity_hseq_perm _ _ Hperm).
           change sequent with (list (prod Rpos term)).
           rewrite (complexity_hseq_perm_fst_seq _ _ H Hperm').
           change ((r , A1 /\S A2) :: D) with (vec (r :: nil) (A1 /\S A2) ++ D).
           apply hrr_min_l_decrease_complexity; [ intros H'; inversion H' | ].
           unfold vec; unfold app; rewrite <- (complexity_hseq_perm_fst_seq _ _ H Hperm').
           change (list (prod Rpos term)) with sequent.
           rewrite <- (complexity_hseq_perm _ _ Hperm).
           rewrite <- (complexity_seq_perm _ _ Hperm').
           apply Heqc.
        -- reflexivity.
        -- split with (FOL_R_and f f2).
           split.
           ++ intros pi.
              split.
              ** apply H1.
                 apply hrr_M_elim.
                 apply hrr_min_inv_l with A2.
                 eapply hrr_ex_seq ; [ apply Hperm' | eapply hrr_ex_hseq ; [ apply Hperm | ]].
                 eapply HR_le_frag ; [ | apply pi].
                 repeat split; auto.
              ** apply H3.
                 apply hrr_M_elim.
                 apply hrr_min_inv_r with A1.
                 eapply hrr_ex_seq ; [ apply Hperm' | eapply hrr_ex_hseq ; [ apply Hperm | ]].
                 eapply HR_le_frag ; [ | apply pi].
                 repeat split; auto.
           ++ intros  Hf.
              eapply hrr_ex_hseq ; [ symmetry; apply Hperm | eapply hrr_ex_seq ; [ symmetry; apply Hperm' | ]].
              change ((r, A1 /\S A2) :: D) with (vec (r :: nil) (A1 /\S A2) ++ D).
              apply hrr_min.
              ** apply H2.
                 intro v.
                 destruct (Hf v) as [Hf' _].
                   apply Hf'.
              ** apply H4.
                 intro v.
                 destruct (Hf v) as [_ Hf'].
                 apply Hf'.
Qed.

Lemma HR_decidable : forall G,
    (HR_full G) + (HR_full G -> False).
Proof.
  intros G.
  destruct (HR_FOL_R_equiv G) as [f [H1 H2]].
  destruct (FOL_R_decidable f).
  - left.
    apply H2; apply f0.
  - right.
    intros pi; apply f0; apply H1; apply pi.
Qed.
  

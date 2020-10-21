(** * Tools and lemma used to prove Lemma ?? and ?? more easily *)
Require Import Rpos.
Require Import term.
Require Import semantic.
Require Import hseq.
Require Import hmr.
Require Import riesz_logic_List_more.

Require Import CMorphisms.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Bool_more.
Require Import Lra.
Require Import Lia.
Require Import Wf_nat_more.

Local Open Scope R_scope.

(** Basic operation concerning Option Rpos (the None constructor corresponds to 0) *)
Definition oadd_Rpos o1 o2 :=
  match o1, o2 with
  | None, o2 => o2
  | o1, None => o1
  | Some r1, Some r2 => Some (plus_pos r1 r2)
  end.

Definition mul_Rpos_oRpos r o :=
  match o with
  | None => None
  | Some r1 => Some (time_pos r r1)
  end.

(** Conversion from nat to Option Rpos *)
Definition nat_oRpos n :=
  match n with
  | 0 => None
  | S n => Some (INRpos n)
  end.

                         
(** The sum of the weights of the atoms of G, where each sequent is multiply by a scalar *)
Fixpoint sum_weight_with_coeff n G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , (Some r) :: L => ((projT1 r) * (sum_weight_seq_var n T - sum_weight_seq_covar n T)) + sum_weight_with_coeff n G L
  | T :: G , None :: L => sum_weight_with_coeff n G L
  end.  
Fixpoint sum_weight_with_coeff_one G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , (Some r) :: L => ((projT1 r) * (sum_weight_seq_one T - sum_weight_seq_coone T)) + sum_weight_with_coeff_one G L
  | T :: G , None :: L => sum_weight_with_coeff_one G L
  end.

Lemma sum_weight_with_coeff_all_0 : forall G L n,
    Forall_Type (fun x => x = None) L ->
    sum_weight_with_coeff n G L = 0.
Proof.
  intros G L; revert G; induction L; intros G n Hall; destruct G; try reflexivity.
  inversion Hall; subst.
  simpl.
  rewrite IHL; try assumption; reflexivity.
Qed.

Lemma sum_weight_with_coeff_one_all_0 : forall G L,
    Forall_Type (fun x => x = None) L ->
    sum_weight_with_coeff_one G L = 0.
Proof.
  intros G L; revert G; induction L; intros G Hall; destruct G; try reflexivity.
  inversion Hall; subst.
  simpl.
  rewrite IHL; try assumption; reflexivity.
Qed.

(** The hypersequent obtained by multiplying (or copying) every sequent by the corresponding element of L and then using the S rule until only one sequent remain *)
Fixpoint concat_with_coeff_mul G L :=
  match G, L with
  | _, nil => nil
  | nil, _ => nil
  | T :: G , (Some r) :: L => seq_mul r T ++ concat_with_coeff_mul G L
  | T :: G , None :: L => concat_with_coeff_mul G L
  end.

Fixpoint concat_with_coeff_copy G L :=
  match G, L with
  | _, nil => nil
  | nil, _ => nil
  | T :: G , n :: L => copy_seq n T ++ concat_with_coeff_copy G L
  end.

Lemma sum_weight_with_coeff_perm_r : forall G H L,
    Permutation_Type G H ->
    length L = length G ->
    { L' &
      prod (Permutation_Type L L') 
           ((forall n, sum_weight_with_coeff n G L = sum_weight_with_coeff n H L') *
            (sum_weight_with_coeff_one G L = sum_weight_with_coeff_one H L') *
            (Permutation_Type (concat_with_coeff_mul (only_diamond_hseq G) L) (concat_with_coeff_mul (only_diamond_hseq H) L')))}.
Proof.
  intros G H L Hperm.
  revert L; induction Hperm; intros L Hlen.
  - destruct L; inversion Hlen.
    split with nil.
    repeat split; auto.
  - destruct L; inversion Hlen.
    destruct (IHHperm L H0) as [L' [Hperm' [[Hsum Hone] Hperm'']]].
    split with (o :: L').
    repeat split; auto.
    + intros n; simpl;rewrite (Hsum n); reflexivity.
    + simpl; rewrite Hone; reflexivity.
    + destruct o; simpl; perm_Type_solve.
  - destruct L ;  [ | destruct L] ; inversion Hlen.
    split with (o0 :: o :: L).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct o; destruct o0; simpl; nra.
    + destruct o; destruct o0; simpl; nra.
    + destruct o; destruct o0; simpl; perm_Type_solve.
  - destruct (IHHperm1 L Hlen) as [L' [Hperm' [[Hsum Hone] Hperm'']]].
    destruct (IHHperm2 L') as [L2' [Hperm2' [[Hsum2 Hone2] Hperm2'']]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ symmetry ; apply Hperm' | ].
      etransitivity ; [ | apply Hperm1].
      apply Hlen. }
    split with L2'.
    repeat split; [ perm_Type_solve | | | ].
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
    + etransitivity ; [ apply Hone | apply Hone2].
    + perm_Type_solve.
Qed.

Lemma sum_weight_with_coeff_perm_l : forall G L L',
    Permutation_Type L L' ->
    length L = length G ->
    { H &
      prod (Permutation_Type G H) 
           ((forall n, sum_weight_with_coeff n G L = sum_weight_with_coeff n H L') *
            (sum_weight_with_coeff_one G L = sum_weight_with_coeff_one H L') *
            (Permutation_Type (concat_with_coeff_mul G L) (concat_with_coeff_mul H L')))}.
Proof.
  intros G L L' Hperm.
  revert G; induction Hperm; intros G Hlen.
  - destruct G; inversion Hlen.
    split with nil.
    auto.
  - destruct G; inversion Hlen.
    destruct (IHHperm G H0) as [H [Hperm'[[Hsum Hone] Hpc]]].
    split with (s :: H).
    repeat split; auto.
    + intros n; simpl;rewrite (Hsum n); reflexivity.
    + simpl; rewrite Hone; reflexivity.
    + simpl.
      destruct x; perm_Type_solve.
  - destruct G ;  [ | destruct G] ; inversion Hlen.
    split with (s0 :: s :: G).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct y; destruct x; simpl; nra.
    + destruct y; destruct x; simpl; nra.
    + destruct x; destruct y; simpl; perm_Type_solve.
  - destruct (IHHperm1 G Hlen) as [H [Hperm'[[Hsum Hone] Hpc]]].
    destruct (IHHperm2 H) as [H2 [Hperm2'[[Hsum2 Hone2] Hpc2]]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ | apply Hperm' ].
      etransitivity ; [ symmetry ; apply Hperm1 | ].
      apply Hlen. }
    split with H2.
    repeat split.
    + perm_Type_solve.
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
    + etransitivity ; [ apply Hone | apply Hone2].
    + etransitivity ; [ apply Hpc | apply Hpc2].
Qed.

Lemma sum_weight_with_coeff_perm_r_int : forall G H L,
    Permutation_Type G H ->
    length L = length G ->
    { L' &
      prod (Permutation_Type L L') 
           ((forall n, sum_weight_with_coeff n G (map nat_oRpos L) = sum_weight_with_coeff n H (map nat_oRpos L')) *
            (sum_weight_with_coeff_one G (map nat_oRpos L) = sum_weight_with_coeff_one H (map nat_oRpos L')) *
            (Permutation_Type (concat_with_coeff_copy (only_diamond_hseq G) L) (concat_with_coeff_copy (only_diamond_hseq H) L')))}.
Proof.
  intros G H L Hperm.
  revert L; induction Hperm; intros L Hlen.
  - destruct L; inversion Hlen.
    split with nil.
    repeat split; auto.
  - destruct L; inversion Hlen.
    destruct (IHHperm L H0) as [L' [Hperm' [[Hsum Hone] Hperm'']]].
    split with (n :: L').
    repeat split; auto.
    + intros n'; simpl;rewrite (Hsum n'); reflexivity.
    + simpl; rewrite Hone; reflexivity.
    + perm_Type_solve.
  - destruct L ;  [ | destruct L] ; inversion Hlen.
    split with (n0 :: n :: L).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n'; destruct n; destruct n0; simpl in *; nra.
    + destruct n; destruct n0; simpl; nra.
    + destruct n; destruct n0; simpl; perm_Type_solve.
  - destruct (IHHperm1 L Hlen) as [L' [Hperm' [[Hsum Hone] Hperm'']]].
    destruct (IHHperm2 L') as [L2' [Hperm2' [[Hsum2 Hone2] Hperm2'']]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ symmetry ; apply Hperm' | ].
      etransitivity ; [ | apply Hperm1].
      apply Hlen. }
    split with L2'.
    repeat split; [ perm_Type_solve | | | ].
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
    + etransitivity ; [ apply Hone | apply Hone2].
    + perm_Type_solve.
Qed.

Lemma sum_weight_with_coeff_perm_l_int : forall G L L',
    Permutation_Type L L' ->
    length L = length G ->
    { H &
      prod (Permutation_Type G H) 
           ((forall n, sum_weight_with_coeff n G (map nat_oRpos L) = sum_weight_with_coeff n H (map nat_oRpos L')) *
            (sum_weight_with_coeff_one G (map nat_oRpos L) = sum_weight_with_coeff_one H (map nat_oRpos L')) *
            (Permutation_Type (concat_with_coeff_copy G L) (concat_with_coeff_copy H L')))}.
Proof.
  intros G L L' Hperm.
  revert G; induction Hperm; intros G Hlen.
  - destruct G; inversion Hlen.
    split with nil.
    auto.
  - destruct G; inversion Hlen.
    destruct (IHHperm G H0) as [H [Hperm'[[Hsum Hone] Hpc]]].
    split with (s :: H).
    repeat split; auto.
    + intros n; simpl;rewrite (Hsum n); reflexivity.
    + simpl; rewrite Hone; reflexivity.
    + simpl.
      destruct x; perm_Type_solve.
  - destruct G ;  [ | destruct G] ; inversion Hlen.
    split with (s0 :: s :: G).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct y; destruct x; simpl; nra.
    + destruct y; destruct x; simpl; nra.
    + destruct x; destruct y; simpl; perm_Type_solve.
  - destruct (IHHperm1 G Hlen) as [H [Hperm'[[Hsum Hone] Hpc]]].
    destruct (IHHperm2 H) as [H2 [Hperm2'[[Hsum2 Hone2] Hpc2]]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ | apply Hperm' ].
      etransitivity ; [ symmetry ; apply Hperm1 | ].
      apply Hlen. }
    split with H2.
    repeat split.
    + perm_Type_solve.
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
    + etransitivity ; [ apply Hone | apply Hone2].
    + etransitivity ; [ apply Hpc | apply Hpc2].
Qed.

Lemma concat_with_coeff_mul_only_diamond : forall G L,
    concat_with_coeff_mul (only_diamond_hseq G) L = only_diamond_seq (concat_with_coeff_mul G L).
Proof.
  induction G; intros L; destruct L; auto.
  destruct o; simpl; rewrite IHG; auto.
  rewrite only_diamond_seq_app.
  rewrite only_diamond_seq_mul; reflexivity.
Qed.

Lemma concat_with_coeff_mul_all_0 : forall G L,
    Forall_Type (fun x => x = None) L ->
    concat_with_coeff_mul G L = nil.
Proof.
  intros G L; revert G; induction L; intros G Ha0; destruct G; simpl; auto.
  inversion Ha0; subst.
  apply IHL; assumption.
Qed.

Lemma concat_with_coeff_copy_only_diamond : forall G L,
    concat_with_coeff_copy (only_diamond_hseq G) L = only_diamond_seq (concat_with_coeff_copy G L).
Proof.
  induction G; intros L; destruct L; auto.
  simpl; rewrite IHG; auto.
  rewrite ? only_diamond_seq_app.
  rewrite only_diamond_seq_copy; reflexivity.
Qed.

Lemma concat_with_coeff_copy_all_0 : forall G L,
    Forall_Type (fun x => x = 0%nat) L ->
    concat_with_coeff_copy G L = nil.
Proof.
  intros G L; revert G; induction L; intros G Ha0; destruct G; simpl; auto.
  inversion Ha0; subst.
  apply IHL; assumption.
Qed.

(** point-wise operation on list of (Option Rpos) or nat *)
Fixpoint oadd_Rpos_list L1 L2 :=
  match L1,L2 with
  | nil, _ => nil
  | _, nil => nil
  | o1 :: L1 , o2 :: L2 => (oadd_Rpos o1 o2) :: (oadd_Rpos_list L1 L2)
  end.

Fixpoint add_nat_list L1 L2 :=
  match L1,L2 with
  | nil, _ => nil
  | _, nil => nil
  | n1 :: L1 , n2 :: L2 => ((n1 + n2)%nat) :: (add_nat_list L1 L2)
  end.

Lemma oadd_Rpos_list_length : forall L1 L2,
    length L1 = length L2 ->
    length (oadd_Rpos_list L1 L2) = (length L1).
Proof.
  induction L1; intros L2; try reflexivity.
  intros Heq.
  destruct L2; inversion Heq.
  specialize (IHL1 L2 H0).
  destruct a; destruct o; simpl; rewrite IHL1; reflexivity.
Qed.

Lemma add_nat_list_length : forall L1 L2,
    length L1 = length L2 ->
    length (add_nat_list L1 L2) = (length L1).
Proof.
  induction L1; intros L2; try reflexivity.
  intros Heq.
  destruct L2; inversion Heq.
  specialize (IHL1 L2 H0).
  simpl; rewrite IHL1; reflexivity.
Qed.

Lemma sum_weight_with_coeff_oadd_Rpos_list : forall n G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff n G (oadd_Rpos_list L1 L2) = sum_weight_with_coeff n G L1 + sum_weight_with_coeff n G L2.
Proof.
  intros n G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  destruct a; destruct o; try destruct r; try destruct r0; simpl; nra.
Qed.

Lemma sum_weight_with_coeff_omul_Rpos_list : forall n G L1 r,
    sum_weight_with_coeff n G (map (mul_Rpos_oRpos r) L1) = (projT1 r) * sum_weight_with_coeff n G L1.
Proof.
  intros n G L1; revert G; induction L1; intros G r ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G r).
  destruct a; try destruct r; try destruct r0; simpl in *; nra.
Qed.

Lemma sum_weight_with_coeff_add_nat_list : forall n G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff n G (map nat_oRpos (add_nat_list L1 L2)) = sum_weight_with_coeff n G (map nat_oRpos L1) + sum_weight_with_coeff n G (map nat_oRpos L2).
Proof.
  intros n G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  simpl add_nat_list.
  destruct a; destruct n0; simpl map; simpl sum_weight_with_coeff; try nra.
  - change (match (a + 0)%nat with
             | 0%nat => 1
             | S _ => INR (a + 0) + 1
            end) with (INR (S a + 0)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    rewrite Nat.add_0_r; nra.
  - change (match (a + S n0)%nat with
             | 0%nat => 1
             | S _ => INR (a + S n0) + 1
            end) with (INR (S a + S n0)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    change (match n0 with
            | 0%nat => 1
            | S _ => INR n0 + 1
            end) with (INR (S n0)).
    rewrite plus_INR; nra.
Qed.

Lemma sum_weight_with_coeff_mul_nat_list : forall n G L1 n',
    sum_weight_with_coeff n G (map nat_oRpos (map (Nat.mul (S n')) L1)) = (INR (S n')) * sum_weight_with_coeff n G (map nat_oRpos L1).
Proof.
  intros n G L1; revert G; induction L1; intros G n' ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G n').
  destruct a; simpl map.
  - rewrite Nat.mul_0_r; apply IHL1.
  - simpl sum_weight_with_coeff.
    change (match (a + n' * S a)%nat with
           | 0%nat => 1
           | S _ => INR (a + n' * S a) + 1
            end) with (INR (S n' * S a)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    change (fun m : nat => (m + n' * m)%nat) with (Nat.mul (S n')).
    rewrite mult_INR; nra.
Qed.

Lemma sum_weight_with_coeff_one_oadd_Rpos_list : forall G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff_one G (oadd_Rpos_list L1 L2) = sum_weight_with_coeff_one G L1 + sum_weight_with_coeff_one G L2.
Proof.
  intros G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  destruct a; destruct o; try destruct r; try destruct r0; simpl; nra.
Qed.

Lemma sum_weight_with_coeff_one_omul_Rpos_list : forall G L1 r,
    sum_weight_with_coeff_one G (map (mul_Rpos_oRpos r) L1) = (projT1 r) * sum_weight_with_coeff_one G L1.
Proof.
  intros G L1; revert G; induction L1; intros G r ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G r).
  destruct a; try destruct r; try destruct r0; simpl in *; nra.
Qed.

Lemma sum_weight_with_coeff_one_add_nat_list : forall G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff_one G (map nat_oRpos (add_nat_list L1 L2)) = sum_weight_with_coeff_one G (map nat_oRpos L1) + sum_weight_with_coeff_one G (map nat_oRpos L2).
Proof.
  intros G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  simpl add_nat_list.
  destruct a; destruct n; simpl; try nra.
  - change (match (a + 0)%nat with
             | 0%nat => 1
             | S _ => INR (a + 0) + 1
            end) with (INR (S a + 0)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    rewrite Nat.add_0_r; nra.
  - change (match (a + S n)%nat with
             | 0%nat => 1
             | S _ => INR (a + S n) + 1
            end) with (INR (S a + S n)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    change (match n with
            | 0%nat => 1
            | S _ => INR n + 1
            end) with (INR (S n)).
    rewrite plus_INR; nra.
Qed.

Lemma sum_weight_with_coeff_one_mul_nat_list : forall G L1 n',
    sum_weight_with_coeff_one G (map nat_oRpos (map (Nat.mul (S n')) L1)) = (INR (S n')) * sum_weight_with_coeff_one G (map nat_oRpos L1).
Proof.
  intros G L1; revert G; induction L1; intros G n' ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G n').
  destruct a; simpl.
  - rewrite Nat.mul_0_r; apply IHL1.
  - change (match (a + n' * S a)%nat with
           | 0%nat => 1
           | S _ => INR (a + n' * S a) + 1
            end) with (INR (S n' * S a)).
    change (match a with
            | 0%nat => 1
            | S _ => INR a + 1
            end) with (INR (S a)).
    change (fun m : nat => (m + n' * m)%nat) with (Nat.mul (S n')).
    change (match n' with
            | 0%nat => 1
            | S _ => INR n' + 1
            end) with (INR (S n')).
    rewrite mult_INR; nra.
Qed.

Lemma concat_with_coeff_mul_omul_Rpos_list : forall G L1 r,
    concat_with_coeff_mul G (map (mul_Rpos_oRpos r) L1) = seq_mul r (concat_with_coeff_mul G L1).
Proof.
  induction G; intros L1 r; [ destruct L1; try destruct o; reflexivity | ].
  destruct L1 ; [ reflexivity | ].
  specialize (IHG L1 r).
  destruct o; simpl; rewrite IHG; try reflexivity.
  rewrite <- seq_mul_twice; rewrite seq_mul_app.
  reflexivity.
Qed.

Lemma concat_with_coeff_copy_add_nat_list_perm : forall G L1 L2,
    length L1 = length L2 ->
    Permutation_Type (concat_with_coeff_copy G (add_nat_list L1 L2)) (concat_with_coeff_copy G L1 ++ concat_with_coeff_copy G L2).
Proof.
  intros G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; inversion Hlen ; [ destruct G; simpl; apply Permutation_Type_nil_nil | ].
  destruct G ; [ apply Permutation_Type_nil_nil | ].
  simpl add_nat_list; simpl concat_with_coeff_copy.
  transitivity ((copy_seq a s ++ copy_seq n s) ++ (concat_with_coeff_copy G L1 ++ concat_with_coeff_copy G L2)) ; [ | perm_Type_solve].
  apply Permutation_Type_app ; [ | apply IHL1]; try assumption.
  rewrite copy_seq_plus; reflexivity.
Qed.

Lemma concat_with_coeff_copy_mul_nat_list : forall G L1 n,
    Permutation_Type (concat_with_coeff_copy G (map (Nat.mul n) L1)) (copy_seq n (concat_with_coeff_copy G L1)).
Proof.
  induction G; intros L1 n.
  - destruct L1; simpl; rewrite copy_seq_nil; apply Permutation_Type_nil_nil.
  - destruct L1; simpl ; [ rewrite copy_seq_nil; apply Permutation_Type_nil_nil | ].
    etransitivity ; [ | symmetry; apply copy_seq_app].
    apply Permutation_Type_app ; [ | apply IHG].
    rewrite copy_seq_twice; reflexivity.
Qed.

(** Sufficient conditions for derivability of a basic hypersequent *)
Lemma basic_proof_all_eq P : forall H T,
    seq_is_basic T ->
    hseq_is_basic H -> 
    (forall n, sum_weight_var n (T :: H) = sum_weight_covar n (T :: H)) ->
    (sum_weight_coone (T :: H) <= sum_weight_one (T :: H)) ->
    HMR P ((flat_map only_diamond_seq (T :: H)) :: nil) ->
    HMR P (T :: H).
Proof.
  induction H; intros T.
  - intros Hb _; revert Hb.
    remember (length T).
    revert T Heqn.
    apply (lt_wf_rect n (fun n => forall T : sequent,
                             n = length T ->
                             seq_is_basic T ->
                             (forall n0 : nat, sum_weight_var n0 (T :: nil) = sum_weight_covar n0 (T :: nil)) ->
                             sum_weight_coone (T :: nil) <= sum_weight_one (T :: nil) ->
                             HMR P (flat_map only_diamond_seq (T :: nil) :: nil) ->
                             HMR P (T :: nil))).
    clear n.
    intros n IHn T Hlen Hat Hsum Hone Hstep.
    destruct (seq_basic_decomp_decr T Hat) as [[[[[n0 r] s] D] [Hr [[Hs Hperm] Hdlen]]] | Hnil].
    + eapply hmrr_ex_seq ; [ symmetry; apply Hperm | ].
      apply hmrr_ID.
      { rewrite Hr; rewrite Hs.
        specialize (Hsum n0); simpl in Hsum.
        nra. }
      apply IHn with (length D).
      * lia.
      * reflexivity.
      * apply seq_basic_perm with _ (vec s (covar n0) ++ vec r (var n0) ++ D) in Hat; try assumption.
        apply seq_basic_app_inv_r in Hat.
        apply seq_basic_app_inv_r in Hat.
        apply Hat.
      * intros n1.
        specialize (Hsum n0) as Hrs.
        specialize (Hsum n1).
        simpl in Hsum; rewrite (sum_weight_seq_var_perm _ _ _ Hperm) in Hsum; rewrite (sum_weight_seq_covar_perm _ _ _ Hperm) in Hsum.
        rewrite ? sum_weight_seq_var_app in Hsum; rewrite ? sum_weight_seq_covar_app in Hsum.
        simpl.
        rewrite (sum_weight_seq_covar_vec_neq _ (var n0)) in Hsum; [ | now auto].
        rewrite (sum_weight_seq_var_vec_neq _ (covar n0)) in Hsum; [ | now auto].
        case_eq (n0 =? n1); intros H01.
        -- apply Nat.eqb_eq in H01; subst.
           rewrite sum_weight_seq_covar_vec_covar_eq in Hsum; rewrite sum_weight_seq_var_vec_var_eq in Hsum.
           simpl in Hrs.
           nra.
        -- apply Nat.eqb_neq in H01.
           rewrite sum_weight_seq_covar_vec_neq in Hsum; [ | intros H'; inversion H'; now auto].
           rewrite sum_weight_seq_var_vec_neq in Hsum; [ | intros H'; inversion H'; now auto].
           nra.
      * simpl in Hone; rewrite (sum_weight_seq_one_perm _ _ Hperm) in Hone; rewrite (sum_weight_seq_coone_perm _ _ Hperm) in Hone.
        rewrite ? sum_weight_seq_one_app in Hone; rewrite ? sum_weight_seq_coone_app in Hone.
        simpl.
        rewrite ? sum_weight_seq_coone_vec_neq in Hone; try now auto.
        rewrite ? sum_weight_seq_one_vec_neq in Hone; try now auto.
        nra.
      * simpl; simpl in Hstep.
        eapply hmrr_ex_seq; [ | apply Hstep].
        rewrite 2 app_nil_r.
        replace (only_diamond_seq D) with (only_diamond_seq (vec s (covar n0) ++ vec r (var n0) ++ D)) by (rewrite ? only_diamond_seq_app; rewrite only_diamond_seq_vec_covar; now rewrite only_diamond_seq_vec_var).
        apply only_diamond_seq_perm; apply Hperm.
    + simpl in Hstep; rewrite app_nil_r in Hstep.
      destruct (seq_basic_no_atom T Hat Hnil) as [[[r s] D] Hperm].
      apply hmrr_ex_seq with (vec s coone ++ vec r one ++ seq_diamond D); [ apply Permutation_Type_sym; apply Hperm | ].
      apply hmrr_diamond.
      { simpl in Hone.
        rewrite (sum_weight_seq_coone_perm _ _ Hperm) in Hone; rewrite (sum_weight_seq_one_perm _ _ Hperm) in Hone.
        rewrite ? sum_weight_seq_coone_app in Hone; rewrite ? sum_weight_seq_one_app in Hone.
        rewrite sum_weight_seq_one_vec_one_eq in Hone; rewrite sum_weight_seq_coone_vec_coone_eq in Hone.
        rewrite sum_weight_seq_one_vec_neq in Hone; [ | now auto].
        rewrite sum_weight_seq_coone_vec_neq in Hone; [ | now auto].
        rewrite sum_weight_seq_one_seq_diamond in Hone; rewrite sum_weight_seq_coone_seq_diamond in Hone.
        nra. }
      replace (vec s coone ++ vec r one ++ D) with (only_diamond_seq (vec s coone ++ vec r one ++ seq_diamond D)) by (rewrite ? only_diamond_seq_app; rewrite only_diamond_seq_vec_coone; rewrite only_diamond_seq_vec_one; now rewrite only_diamond_seq_only_diamond).
      eapply hmrr_ex_seq ; [ | apply Hstep].
      apply only_diamond_seq_perm; apply Hperm.
  - intros HatT HatH Hsum Hone Hstep.
    apply hmrr_S.
    apply IHlist.
    + inversion HatH; subst.
      apply seq_basic_app; assumption.
    + inversion HatH; assumption.
    + intros n.
      specialize (Hsum n).
      simpl in *.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      nra.
    + simpl in *.
      rewrite sum_weight_seq_one_app; rewrite sum_weight_seq_coone_app.
      nra.
    + simpl in *.
      rewrite only_diamond_seq_app; rewrite <- app_assoc.
      apply Hstep.
Qed.

(*
Lemma hmrr_fuse :
  forall G T A r1 r2,
    HMR_T_M (((r1, A) :: (r2 , A) :: T) :: G) ->
    HMR_T_M (((plus_pos r1 r2, A) :: T) :: G).
Proof.
  intros G T A r1 r2 pi.
  apply hmrr_can_elim.
  unfold HMR_full.
  change hmr_frag_full with (hmr_frag_add_CAN hmr_frag_full).
  apply hmrr_can_fuse.
  apply HMR_le_frag with hmr_frag_T_M; try assumption.
  repeat split.
Qed.

Lemma hmrr_unfuse :
  forall G T A r1 r2,
    HMR_T_M (((plus_pos r1 r2, A) :: T) :: G) ->
    HMR_T_M (((r1, A) :: (r2 , A) :: T) :: G).
Proof.
  intros G T A r1 r2 pi.
  apply hmrr_can_elim.
  unfold HMR_full.
  change hmr_frag_full with (hmr_frag_add_CAN hmr_frag_full).
  apply hmrr_can_unfuse.
  apply HMR_le_frag with hmr_frag_T_M; try assumption.
  repeat split.
Qed.

Lemma hmrr_unfuse_gen :
  forall G T D r1 r2,
    HMR_T_M ((seq_mul (plus_pos r1 r2) D ++ T) :: G) ->
    HMR_T_M ((seq_mul r1 D ++ seq_mul r2 D ++ T) :: G).
Proof.
  intros G T D r1 r2.
  revert T; induction D; intros T pi; try assumption.
  - destruct a as [a A]; simpl in *.
    apply hmrr_ex_seq with ((time_pos r1 a, A) :: (time_pos r2 a, A) :: seq_mul r1 D ++ seq_mul r2 D ++ T); [ perm_Type_solve | ].
    apply hmrr_unfuse.
    replace (plus_pos (time_pos r1 a) (time_pos r2 a)) with (time_pos (plus_pos r1 r2) a) by (destruct r1; destruct r2; destruct a; apply Rpos_eq; simpl; nra).
    apply hmrr_ex_seq with (seq_mul r1 D ++ seq_mul r2 D ++ (time_pos (plus_pos r1 r2) a, A) :: T) ; [ perm_Type_solve | ].
    apply IHD.
    eapply hmrr_ex_seq ; [ | apply pi].
    perm_Type_solve.
Qed.

Lemma hmrr_fuse_gen :
  forall G T D r1 r2,
    HMR_T_M ((seq_mul r1 D ++ seq_mul r2 D ++ T) :: G) ->
    HMR_T_M ((seq_mul (plus_pos r1 r2) D ++ T) :: G).
Proof.
  intros G T D r1 r2.
  revert T; induction D; intros T pi; try assumption.
  - destruct a as [a A]; simpl in *.
    replace (time_pos (plus_pos r1 r2) a) with (plus_pos (time_pos r1 a) (time_pos r2 a)) by (destruct r1; destruct r2; destruct a; apply Rpos_eq; simpl; nra).
    apply hmrr_fuse.
    apply hmrr_ex_seq with (seq_mul (plus_pos r1 r2) D ++ (time_pos r1 a, A) :: (time_pos r2 a, A) :: T) ; [ perm_Type_solve | ].
    apply IHD.
    eapply hmrr_ex_seq ; [ | apply pi].
    perm_Type_solve.
Qed.

Lemma concat_with_coeff_mul_oadd_Rpos_list_fuse : forall G T H L1 L2,
    length L1 = length L2 ->
    HMR_T_M ((concat_with_coeff_mul G L1 ++ concat_with_coeff_mul G L2 ++ T) :: H) ->
    HMR_T_M ((concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ T) :: H).
Proof.
  intros G T H L1; revert G T H; induction L1; intros G T H L2 Hlen pi; [ destruct L2; inversion Hlen; destruct G; apply pi | ].
  destruct L2; inversion Hlen.
  destruct G; [ apply pi | ].
  destruct a; destruct o; simpl in *.
  - rewrite<- app_assoc; apply hmrr_fuse_gen.
    apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (seq_mul r s ++ seq_mul r0 s ++ T)) ; [ perm_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    perm_Type_solve.
  - apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (seq_mul r s ++ T)) ; [ perm_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    perm_Type_solve.
  - apply hmrr_ex_seq with (concat_with_coeff_mul G (oadd_Rpos_list L1 L2) ++ (seq_mul r s ++ T)) ; [ perm_Type_solve | ].
    apply IHL1; try assumption.
    eapply hmrr_ex_seq ; [ | apply pi].
    perm_Type_solve.
  - apply IHL1; try assumption.
Qed.

Lemma lambda_prop :
  forall G,
    hseq_is_basic G ->
    HMR_T_M G ->
    { L &
      prod (length L = length G)
           ((Exists_Type (fun x => x <> None) L) *
            (forall n, sum_weight_with_coeff n G L = 0) *
            (0 <= sum_weight_with_coeff_one G L) *
            (HMR_T_M ((concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))}.
Proof.
  intros G Ha pi.
  induction pi.
  - split with ((Some One) :: nil).
    repeat split; try reflexivity.
    + apply Exists_Type_cons_hd.
      intros H; inversion H.
    + intros n.
      simpl; nra.
    + simpl; nra.
    + apply hmrr_INIT.
  - inversion Ha; subst.
    destruct (IHpi X0) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with (None :: L).
    repeat split; auto.
    simpl; rewrite Hlen; reflexivity.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_Type_cons ;[ | apply Forall_Type_cons]; try assumption. }
    destruct L; [ | destruct L]; try now inversion Hlen.
    split with ((oadd_Rpos o o0) :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_Type_cons_hd.
        destruct o; [ | exfalso; apply H0; reflexivity].
        destruct o0; intros H; inversion H.
      * inversion X1; subst; auto.
        apply Exists_Type_cons_hd.
        destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intro H; inversion H.
    + intros n.
      specialize (Hsum n).
      destruct o; destruct o0; try destruct r; try destruct r0; simpl; simpl in Hsum; nra.
    + destruct o; destruct o0; try destruct r; try destruct r0; simpl; simpl in Hone; nra.
    + destruct o; destruct o0; simpl; simpl in Hind; try assumption.
      apply hmrr_fuse_gen.
      apply Hind.
  - inversion Ha; inversion X0; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_Type_cons; try assumption.
      apply seq_basic_app; assumption. }
    destruct L; try now inversion Hlen.
    split with (o :: o :: L).
    repeat split; auto.
    + simpl in *; rewrite Hlen; reflexivity.
    + intro n.
      specialize (Hsum n).
      destruct o; auto.
      simpl in *.
      rewrite sum_weight_seq_var_app in Hsum.
      rewrite sum_weight_seq_covar_app in Hsum.
      nra.
    + destruct o; auto.
      simpl in *.
      rewrite sum_weight_seq_one_app in Hone.
      rewrite sum_weight_seq_coone_app in Hone.
      nra.
    + destruct o; try assumption.
      simpl in *.
      rewrite only_diamond_seq_app in Hind.
      rewrite seq_mul_app in Hind.
      rewrite app_assoc; apply Hind.
  - inversion Ha; subst.
    destruct IHpi1 as [L1 [Hlen1 [[[Hex1 Hsum1] Hone1] Hind1]]].
    { apply Forall_Type_cons ; [ apply seq_basic_app_inv_l with T2 | ]; try assumption. }
    destruct L1; try now inversion Hlen1.
    destruct o.
    2:{ split with (None :: L1).
        repeat split; auto. }
    destruct IHpi2 as [L2 [Hlen2 [[[Hex2 Hsum2] Hone2] Hind2]]].
    { apply Forall_Type_cons ; [ apply seq_basic_app_inv_r with T1 | ]; try assumption. }
    destruct L2; try now inversion Hlen2.
    destruct o.
    2:{ split with (None :: L2).
        repeat split; auto. }
    split with ((Some (time_pos r r0)) :: oadd_Rpos_list (map (mul_Rpos_oRpos r0) L1) (map (mul_Rpos_oRpos r) L2)).
    repeat split; auto.
    + simpl in Hlen1, Hlen2; simpl.
      rewrite oadd_Rpos_list_length ; [ rewrite map_length; assumption | ].
      rewrite 2 map_length.
      lia.
    + apply Exists_Type_cons_hd.
      intros H; inversion H.
    + intros n; specialize (Hsum1 n); specialize (Hsum2 n); simpl in Hsum1, Hsum2.
      simpl.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      rewrite sum_weight_with_coeff_oadd_Rpos_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      rewrite 2 sum_weight_with_coeff_omul_Rpos_list.
      destruct r; destruct r0; simpl in *; nra.
    + simpl; simpl in Hone1, Hone2.
      rewrite sum_weight_seq_one_app; rewrite sum_weight_seq_coone_app.
      rewrite sum_weight_with_coeff_one_oadd_Rpos_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      rewrite 2 sum_weight_with_coeff_one_omul_Rpos_list.
      destruct r as [r Hr]; destruct r0 as [r0 Hr0]; simpl in *.
      clear - Hr Hr0 Hone1 Hone2.
      apply R_blt_lt in Hr; apply R_blt_lt in Hr0.
      nra.
    + simpl in Hind1, Hind2 |- *.
      rewrite only_diamond_seq_app; rewrite seq_mul_app.
      rewrite <- (seq_mul_twice (only_diamond_seq T2)).
      replace (time_pos r r0) with (time_pos r0 r) by (destruct r0; destruct r; apply Rpos_eq; simpl; nra).
      rewrite <- seq_mul_twice.
      apply hmrr_ex_seq with ((concat_with_coeff_mul (only_diamond_hseq G) (oadd_Rpos_list (map (mul_Rpos_oRpos r0) L1) (map (mul_Rpos_oRpos r) L2))) ++ (seq_mul r0 (seq_mul r (only_diamond_seq T1)) ++ seq_mul r (seq_mul r0 (only_diamond_seq T2)))) ; [ perm_Type_solve | ].
      apply concat_with_coeff_mul_oadd_Rpos_list_fuse ; [ simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia | ].
      rewrite 2 concat_with_coeff_mul_omul_Rpos_list.
      apply hmrr_ex_seq with (seq_mul r (seq_mul r0 (only_diamond_seq T2) ++ (concat_with_coeff_mul (only_diamond_hseq G) L2)) ++ seq_mul r0 (seq_mul r (only_diamond_seq T1) ++ (concat_with_coeff_mul (only_diamond_hseq G) L1))) ; [ rewrite ? seq_mul_app; perm_Type_solve | ].
      apply hmrr_M; [ reflexivity | | ];
        eapply hmrr_T; try reflexivity;
          rewrite seq_mul_twice; rewrite inv_pos_l; rewrite seq_mul_One; assumption.      
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_Type_cons; try assumption.
      apply seq_basic_mul; apply X. }
    destruct L; try now inversion Hlen.
    destruct o.
    2:{ split with (None :: L).
        repeat split; auto. }
    split with (Some (time_pos r0 r) :: L).
    repeat split; auto.
    + apply Exists_Type_cons_hd; intros H; inversion H.
    + destruct r; destruct r0; simpl in *; intros n; specialize (Hsum n);rewrite sum_weight_seq_var_mul in Hsum; rewrite sum_weight_seq_covar_mul in Hsum; simpl in *.
      nra.
    + destruct r; destruct r0; simpl in *; rewrite sum_weight_seq_one_mul in Hone; rewrite sum_weight_seq_coone_mul in Hone.
      simpl in *; nra.
    + simpl in *.
      rewrite<- seq_mul_twice; rewrite only_diamond_seq_mul.
      apply Hind.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply Forall_Type_cons; try assumption.
      eapply seq_basic_app_inv_r; eapply seq_basic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    + intros n0; specialize (Hsum n0).
      destruct L; try now inversion Hlen.
      simpl; rewrite ? sum_weight_seq_app.
      case_eq (n0 =? n); intros H.
      * apply Nat.eqb_eq in H; subst.
        rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
        rewrite sum_weight_seq_covar_vec_covar_eq;rewrite sum_weight_seq_var_vec_var_eq.
        rewrite sum_weight_seq_var_vec_neq; [ | now auto ]; rewrite sum_weight_seq_covar_vec_neq; [ | now auto].
        simpl in Hsum.
        destruct o; nra.
      * apply Nat.eqb_neq in H.
        rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
        rewrite ? sum_weight_seq_covar_vec_neq ; [ | now auto | intro H'; inversion H'; now auto]; rewrite ? sum_weight_seq_var_vec_neq; [ | intro H'; inversion H'; now auto | now auto ].
        destruct o; simpl in Hsum; auto.
        nra.
    + destruct L; try now inversion Hlen.
      simpl in *; rewrite ? sum_weight_seq_app.
      simpl in *; rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      destruct o; auto.
      rewrite ? sum_weight_seq_coone_vec_neq; try now (intros H; inversion H).
      rewrite ? sum_weight_seq_one_vec_neq; try now (intros H; inversion H).
      nra.
    + unfold only_diamond_hseq; fold only_diamond_hseq.
      rewrite 2 only_diamond_seq_app.
      rewrite only_diamond_seq_vec_var; rewrite only_diamond_seq_vec_covar.
      apply Hind.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_Type_cons ; [ | apply Forall_Type_cons ]; assumption. }
    destruct L ; [ | destruct L]; try now inversion Hlen.
    split with (oadd_Rpos o o0 :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_Type_cons_hd.
        destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intros H; inversion H.
      * inversion X; subst; auto.
        apply Exists_Type_cons_hd; 
          destruct o; destruct o0; try (exfalso; apply H0; reflexivity); intros H; inversion H.
    + intros n.
      simpl.
      specialize (Hsum n).
      destruct o; destruct o0; try destruct r; try destruct r0; simpl in *; nra.
    + destruct o; destruct o0; try destruct r; try destruct r0; simpl in *; nra.
    + destruct o; destruct o0; try apply Hind.
      simpl in *.
      apply hmrr_fuse_gen; apply Hind.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi1 Ha) as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    split with L.
    repeat split; try assumption.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_Type_cons; try assumption.
      eapply seq_basic_app_inv_r; eapply seq_basic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    + intros n; specialize (Hsum n).
      destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite ? sum_weight_seq_var_app; rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_var_vec_neq; try (intros H; now inversion H).
      rewrite ? sum_weight_seq_covar_vec_neq; try (intros H; now inversion H).
      nra.
    + destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      rewrite ? sum_weight_seq_one_vec_one_eq; rewrite ? sum_weight_seq_coone_vec_coone_eq.
      rewrite ? sum_weight_seq_one_vec_neq; try (intros H; now inversion H).
      rewrite ? sum_weight_seq_coone_vec_neq; try (intros H; now inversion H).
      apply (Rmult_le_compat_l (projT1 r1)) in r0.
      2:{ destruct r1 as [r1 Hr1]; simpl.
          clear - Hr1; apply R_blt_lt in Hr1.
          nra. }
      nra.
    + destruct L; try now inversion Hlen.
      destruct o; simpl in *; auto.
      rewrite 2 only_diamond_seq_app; rewrite 2 seq_mul_app.
      rewrite only_diamond_seq_vec_one; rewrite only_diamond_seq_vec_coone.
      rewrite 2 seq_mul_vec_mul_vec.
      rewrite<- ? app_assoc.
      apply hmrr_one; try assumption.
      rewrite 2 mul_vec_sum_vec.
      clear - r0.
      destruct r1 as [r1 Hr1]; simpl; apply R_blt_lt in Hr1; nra.
  - split with (Some One :: nil).
    repeat split; auto.
    + apply Exists_Type_cons_hd; intros H; inversion H.
    + intros n.
      simpl.
      rewrite ? sum_weight_seq_var_app; rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_var_vec_neq; try (intros H; now inversion H).
      rewrite ? sum_weight_seq_covar_vec_neq; try (intros H; now inversion H).
      rewrite sum_weight_seq_var_seq_diamond; rewrite sum_weight_seq_covar_seq_diamond; nra.
    + simpl.
      rewrite ? sum_weight_seq_one_app; rewrite ? sum_weight_seq_coone_app.
      rewrite sum_weight_seq_one_vec_one_eq; rewrite sum_weight_seq_coone_vec_coone_eq.
      rewrite ? sum_weight_seq_one_vec_neq; try (intros H; now inversion H).
      rewrite ? sum_weight_seq_coone_vec_neq; try (intros H; now inversion H).
      rewrite sum_weight_seq_one_seq_diamond; rewrite sum_weight_seq_coone_seq_diamond; nra.
    + simpl.
      rewrite seq_mul_One.
      rewrite ? only_diamond_seq_app.
      rewrite only_diamond_seq_vec_coone; rewrite only_diamond_seq_vec_one; rewrite only_diamond_seq_only_diamond.
      rewrite app_nil_r; apply pi.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { inversion Ha; subst.
      apply Forall_Type_cons; try assumption.
      apply seq_basic_perm with T2; [ perm_Type_solve | apply X]. }
    split with L.
    destruct L; try now inversion Hlen.
    repeat split; auto.
    + intro n; specialize (Hsum n).
      destruct o; simpl in *; auto.
      rewrite <- (sum_weight_seq_var_perm _ _ _ p); rewrite <- (sum_weight_seq_covar_perm _ _ _ p); apply Hsum.
    + destruct o; simpl in *; auto.
      rewrite <- (sum_weight_seq_one_perm _ _ p); rewrite <- (sum_weight_seq_coone_perm _ _ p); apply Hone.
    + destruct o; simpl in *; auto.
      eapply hmrr_ex_seq; [ | apply Hind].
      apply Permutation_Type_app; try reflexivity.
      apply seq_mul_perm.
      apply only_diamond_seq_perm.
      apply p.
  - destruct IHpi as [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    { apply hseq_basic_perm with H; try assumption.
      symmetry; apply p. }
    destruct (sum_weight_with_coeff_perm_r G H L p Hlen) as [L' [Hperm' [[Hsum' Hone'] Hperm'']]].
    split with L'.
    repeat split.
    + apply Permutation_Type_length in p.
      apply Permutation_Type_length in Hperm'.
      etransitivity ; [ | apply p].
      etransitivity ; [ | apply Hlen].
      symmetry; apply Hperm'.
    + apply Exists_Type_Permutation_Type with L; assumption.
    + intros n.
      rewrite <- (Hsum' n); apply Hsum.
    + rewrite <- Hone'; apply Hone.
    + eapply hmrr_ex_seq ; [ | apply Hind].
      apply Hperm''.
  - inversion f.
Qed.

Lemma lambda_prop_inv :
  forall G,
    hseq_is_basic G ->
    { L &
      prod (length L = length G)
           ((Exists_Type (fun x => x <> None) L) *
            (forall n, sum_weight_with_coeff n G L = 0) *
            (0 <= sum_weight_with_coeff_one G L) *
            (HMR_T_M ((concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))} ->
    HMR_T_M G.
Proof.
  enough (forall G H,
             hseq_is_basic G ->
             hseq_is_basic H ->
             { L &
               prod (length L = length G)
                    ((Exists_Type (fun x => x <> None) L) *
                     (forall n, (sum_weight_var n H - sum_weight_covar n H) + sum_weight_with_coeff n G L = 0) *
                     (0 <= (sum_weight_one H - sum_weight_coone H) + sum_weight_with_coeff_one G L) *
                     (HMR_T_M ((flat_map only_diamond_seq H ++ concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))} + HMR_T_M H ->
             HMR_T_M (H ++  G)).
  { intros G Hat [L [Hlen [[[Hex Hsum] Hone] Hind]]].
    change G with (nil ++ G).
    refine (X G nil Hat _ _).
    - apply Forall_Type_nil.
    - left.
      split with L.
      repeat split; auto.
      + intros n; simpl; specialize (Hsum n); nra.
      + simpl; nra. }
  intros G.
  remember (length G) as n.
  revert G Heqn.
  induction n; intros G Heqn H HatG HatH [[L [Hlen [[[Hex Hsum] Hone] Hind]]] | pi].
  - destruct L; inversion Hlen; inversion Hex.
  - destruct G; inversion Heqn; rewrite app_nil_r; apply pi.
  - destruct (Exists_Type_split _ _ _ Hex) as [[[r La] Lb] [Hp HeqL]].
    assert (Permutation_Type L (r :: La ++ Lb)) as Hperm by (rewrite HeqL ; perm_Type_solve).
    destruct (sum_weight_with_coeff_perm_l G _ _ Hperm) as [G' [HpermG [[Hsum' Hone'] Hpc]]].
    { lia. }
    destruct G' as [ | T G'].
    { symmetry in HpermG; apply Permutation_Type_nil in HpermG.
      subst; inversion Heqn. }
    apply hmrr_ex_hseq with (T :: H ++ G') ; [ perm_Type_solve | ].
    destruct r ; [ | exfalso; apply Hp; reflexivity].
    apply hmrr_T with r; try reflexivity.
    change (seq_mul r T :: H ++ G')
      with
        ((seq_mul r T :: H) ++ G').
    assert (hseq_is_basic (T :: G')) as HatG'.
    { apply Forall_Type_Permutation_Type with G; try assumption. }
    apply IHn.
    + apply Permutation_Type_length in HpermG.
      rewrite HpermG in Heqn; simpl in Heqn; inversion Heqn; auto.
    + inversion HatG'; auto.
    + apply Forall_Type_cons; auto.
      apply seq_basic_mul; now inversion HatG'.
    + destruct (Forall_Exists_Type_dec (fun x : option Rpos => x = None)) with (La ++ Lb).
      { intros x.
        destruct x ; [ right; intros H'; inversion H' | left; reflexivity]. }
      * right.
        apply basic_proof_all_eq.
        -- apply seq_basic_mul.
           apply hseq_basic_perm with _ (T :: G') in HatG; try assumption.
           inversion HatG; assumption.
        -- apply HatH.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite (sum_weight_with_coeff_all_0 _ (La ++ Lb)) in Hsum'; try assumption.
           rewrite sum_weight_seq_var_mul; rewrite sum_weight_seq_covar_mul; simpl.
           nra.
        -- simpl in *.
           rewrite (sum_weight_with_coeff_one_all_0 _ (La ++ Lb)) in Hone'; try assumption.
           rewrite sum_weight_seq_one_mul; rewrite sum_weight_seq_coone_mul; simpl.
           nra.
        -- eapply hmrr_ex_seq ; [ | apply Hind].
           rewrite HeqL.
           simpl.
           etransitivity ; [ apply Permutation_Type_app_swap | ].
           apply Permutation_Type_app; [ | reflexivity].
           rewrite concat_with_coeff_mul_only_diamond.
           apply only_diamond_seq_perm.
           rewrite HeqL in Hpc; etransitivity ; [ apply Hpc | ].
           simpl.
           rewrite concat_with_coeff_mul_all_0; try assumption.
           rewrite app_nil_r; reflexivity.
      * left; split with (La ++ Lb).
        repeat split.
        -- rewrite HeqL in Hlen.
           rewrite ? app_length.
           rewrite ? app_length in Hlen; simpl in Hlen.
           lia.
        -- apply e.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite sum_weight_seq_var_mul; rewrite sum_weight_seq_covar_mul; simpl.
           nra.
        -- simpl in *.
           rewrite sum_weight_seq_one_mul; rewrite sum_weight_seq_coone_mul; simpl.
           nra.
        -- eapply hmrr_ex_seq ; [ | apply Hind].
           rewrite HeqL.
           simpl.
           etransitivity ; [ | apply Permutation_Type_app_swap ].
           etransitivity ; [ apply Permutation_Type_app_swap | ].
           rewrite app_assoc.
           apply Permutation_Type_app; [ | reflexivity].
           rewrite 2 concat_with_coeff_mul_only_diamond.
           rewrite <- only_diamond_seq_app.
           apply only_diamond_seq_perm.
           rewrite HeqL in Hpc; etransitivity ; [ apply Hpc | ].
           simpl.
           apply Permutation_Type_app_swap.
  - eapply hmrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply hmrr_W_gen.
    apply pi.
Qed. *)

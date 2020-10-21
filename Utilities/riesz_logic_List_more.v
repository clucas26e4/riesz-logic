Require Import List_Type_more.
Require Import Permutation_Type.
Require Import Permutation_Type_solve.

Lemma Exists_Type_split A : forall P (l : list A),
    Exists_Type P l ->
    {' (a, la, lb) : _ &
                     prod (P a)
                          (l = la ++ a :: lb)}.
Proof.
  intros P l Hex; induction Hex.
  - split with (x , nil, l); repeat split; try assumption; try reflexivity.
  - destruct IHHex as [[[a la] lb] [Hp Heq]].
    split with (a , x :: la, lb); repeat split; try assumption; rewrite Heq; reflexivity.
Qed.

Lemma Forall_Type_Permutation_Type A : forall P (l l' : list A),
    Permutation_Type l l' ->
    Forall_Type P l ->
    Forall_Type P l'.
Proof.
  intros P l l' Hperm.
  induction Hperm; intros Hall.
  - apply Forall_Type_nil.
  - inversion Hall; subst.
    apply Forall_Type_cons ; [ apply X | ].
    apply IHHperm; apply X0.
  - inversion Hall; inversion X0; subst.
    apply Forall_Type_cons;  [ | apply Forall_Type_cons]; assumption.
  - apply IHHperm2.
    apply IHHperm1.
    apply Hall.
Qed.

Lemma Exists_Type_Permutation_Type A : forall P (l l' : list A),
    Permutation_Type l l' ->
    Exists_Type P l ->
    Exists_Type P l'.
Proof.
  intros P l l' Hperm.
  induction Hperm; intros Hex.
  - inversion Hex.
  - inversion Hex; subst.
    + apply Exists_Type_cons_hd; assumption.
    + apply Exists_Type_cons_tl; apply IHHperm; apply X.
  - inversion Hex;  [ | inversion X]; subst.
    + apply Exists_Type_cons_tl; apply Exists_Type_cons_hd; apply X.
    + apply Exists_Type_cons_hd; apply X0.
    + apply Exists_Type_cons_tl; apply Exists_Type_cons_tl; apply X0.
  - apply IHHperm2; apply IHHperm1; apply Hex.
Qed.

Lemma decomp_Permutation_Type_2 A : forall l l' (x y : A),
    Permutation_Type (x :: y :: l) l' ->
    {' (l1,l2,l3) : _ & {l' = l1 ++ x :: l2 ++ y :: l3} +
                        {l' = l1 ++ y :: l2 ++ x :: l3}}.
Proof.
  intros l l' x y Hperm.
  destruct (in_Type_split x l') as [[la lb] Heq].
  { apply Permutation_Type_in_Type with (x :: y :: l); [ apply Hperm | ].
    left; reflexivity. }
  case (in_Type_app_or la lb y).
  { apply Permutation_Type_in_Type with (y :: l) ; [ | left; reflexivity].
    apply Permutation_Type_cons_inv with x.
    rewrite Heq in Hperm; perm_Type_solve. }
  - intros Hin.
    apply in_Type_split in Hin as [[l1 l2] Heq' ].
    split with (l1 , l2 , lb).
    right; subst.
    rewrite <- ? app_assoc; reflexivity.
  - intros Hin.
    apply in_Type_split in Hin as [[l1 l2] Heq' ].
    split with (la , l1 , l2).
    left; subst; reflexivity.
Qed.

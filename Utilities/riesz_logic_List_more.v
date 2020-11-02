Require Import PeanoNat.
Require Import List_Type_more.
Require Import List_more.
Require Import Permutation_Type.
Require Import Permutation_Type_solve.
Require Import Lia.

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
    case_eq (i <? (length (rev l)))%nat.
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

Lemma In_Type_concat {A} :
  forall L (x : A),
    In_Type x (concat L) ->
    {l & prod (In_Type l L) (In_Type x l)}.
Proof.
  induction L; intros x Hin; [ inversion Hin | ].
  simpl in Hin.
  apply in_Type_app_or in Hin.
  destruct Hin.
  - split with a; split; auto.
    left; reflexivity.
  - destruct (IHL x i) as [l [H1 H2]].
    split with l; split; auto.
    right; apply H1.
Qed.

Lemma In_Type_seq_le_start :
  forall i j k,
    In_Type i (seq j k) ->
    (j <= i)%nat.
Proof.
  intros i j k; revert j; induction k; intros j Hin; inversion Hin; subst; try (specialize (IHk (S j) X)); lia.
Qed.

Require Import Rpos.
Require Import riesz_logic_List_more.
Require Import FOL_R.
Require Import lt_nat_tuples.
Require Import RL.hmr.term.
Require Import RL.hmr.semantic.
Require Import RL.hmr.hseq.
Require Import RL.hmr.p_hseq.
Require Import RL.hmr.hmr.
Require Import RL.hmr.lambda_prop_tools.
Require Import RL.hmr.invertibility.
Require Import RL.hmr.can_elim.
Require Import RL.hmr.M_elim.
Require Import RL.hmr.decidability.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.
Require Import Omega.
Require Import ZArith Psatz.
Require Import FunctionalExtensionality.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

(* TODO move *)
Lemma pow_not_0 : forall i j, i <> 0 -> i ^ j <> 0.
Proof.
  intros i; induction j; intros Hn0; simpl; try lia.
Qed.

Definition pow2 x := 2 ^ x.

Lemma pow2_le_mono : forall x y, x <= y -> pow2 x <= pow2 y.
Proof.
  intros x y Hle; unfold pow2.
  apply Nat.pow_le_mono; lia.
Qed.

Lemma pow2_add : forall x y, pow2 (x + y) = pow2 x * pow2 y.
Proof.
  intros x y; unfold pow2.
  apply Nat.pow_add_r.
Qed.

Lemma pow2_S : forall x, pow2 (S x) = 2*(pow2 x).
Proof.
  intros x; unfold pow2.
  reflexivity.
Qed.

Lemma le_1_pow2 : forall x, 1 <= 2^x.
Proof.
  induction x; simpl; try lia.
Qed.

Lemma id_le_pow2 : forall x, x <= 2^x.
Proof.
  induction x; simpl; try lia.
  assert (H := le_1_pow2 x); lia.
Qed.

Fixpoint tetra_2 n j :=
  match n with
  | 0 => j
  | S n => pow2 (tetra_2 n j)
  end.

Lemma tetra_2_le_mono : forall n j k,
    j <= k ->
    tetra_2 n j <= tetra_2 n k.
Proof.
  intros n j k Hle.
  induction n; simpl; try lia.
  apply pow2_le_mono; apply IHn.
Qed.

Lemma tetra_2_pow2 : forall n j,
    tetra_2 n (pow2 j) = tetra_2 (S n) j.
Proof.
  intros n j; induction n; simpl; try lia.
  rewrite IHn.
  reflexivity.
Qed.

Lemma NoDup_inf_rev {A} : forall (l : list A),
    NoDup_inf l ->
    NoDup_inf (rev l).
Proof.
  intros l.
  apply Permutation_Type_NoDup_inf.
  apply Permutation_Type_rev.
Qed.

Lemma NoDup_inf_nth {A} : forall l,
    (forall (a0 : A) i j, i < length l -> j < length l -> i <> j -> nth i l a0 <> nth j l a0) ->
    NoDup_inf l.
Proof.
  intros l; induction l; intros H; [ apply NoDup_inf_nil | ].
  apply NoDup_inf_cons.
  - intros Hin.
    apply (In_inf_nth _ _ a) in Hin as [n Hlen Heq].
    refine (H a 0 (S n) _ _ _ _); simpl; try lia.
    auto.
  - apply IHl.
    intros a0 i j Hlen1 Hlen2 Hneq.
    refine (H a0 (S i) (S j) _ _ _); simpl; lia.
Qed.
    
Lemma list_split_max : forall v,
    v <> nil ->
    {' (la, lb, k) : _ & prod (v = la ++ k :: lb)
                              ((Forall_inf (fun x => x <= k) la) *
                               (Forall_inf (fun x => x <= k) lb))}.
Proof.
  induction v ; [ contradiction | ].
  destruct v; intros _.
  - split with (nil, nil, a).
    repeat split; auto.
  - destruct IHv as [[[la lb] k] [Heq [H1 H2]]]; [ intros H; inversion H | ].
    case_eq (k <=? a); intros H.
    + split with (nil, n :: v, a).
      apply Nat.leb_le in H.
      repeat split; auto.
      rewrite Heq.
      apply Forall_inf_app; [ | apply Forall_inf_cons].
      * refine (Forall_inf_arrow _ _ H1).
        intros a0 H'; lia.
      * apply H.
      * refine (Forall_inf_arrow _ _ H2).
        intros a0 H'; lia.
    + split with (a :: la, lb, k).
      apply Nat.leb_nle in H.
      repeat split; try rewrite Heq; auto.
      apply Forall_inf_cons; auto.
      lia.
Qed.

Lemma Forall_inf_le_not_In_inf : forall l k,
    Forall_inf (fun x => x <= k) l ->
    (In_inf k l -> False) ->
    Forall_inf (fun x => x < k) l.
Proof.
  induction l; intros k Hall Hnin; inversion Hall; subst; auto.
  apply Forall_inf_cons.
  - assert (a <> k).
    { intros H; subst; apply Hnin; left; auto. }
    lia.
  - apply IHl; auto.
    intros Hin; apply Hnin; right; auto.
Qed.
    
Lemma NoDup_inf_lt_length : forall v n,
    Forall_inf (fun x => x < n) v ->
    NoDup_inf v ->
    length v <= n.
Proof.
  intros v; remember (length v).
  revert v Heqn.
  induction n; intros v Heqn k Hall Hndup; try lia.
  assert (v <> nil) as Hnnil.
  { destruct v; try now inversion Heqn; auto. }
  destruct (list_split_max v Hnnil) as [[[la lb] k'] [Heq [H1 H2]]].
  apply Permutation_Type_NoDup_inf with _ _ (k' :: la ++ lb) in Hndup; [ | rewrite Heq;Permutation_Type_solve ].
  inversion Hndup; subst.
  transitivity (S k').
  - apply le_n_S.
    refine (IHn (la ++ lb) _ k' _ _).
    + replace (length (la ++ lb)) with (pred (length (la ++ k' :: lb))) by (rewrite ? app_length; simpl; lia).
      rewrite <- Heqn; reflexivity.
    + apply Forall_inf_le_not_In_inf; [ apply Forall_inf_app | ]; auto.
    + apply X.
  - apply Forall_inf_elt in Hall.
    apply Hall.
Qed.
      
Lemma seq_NoDup_inf : forall i j,
    NoDup_inf (seq i j).
Proof.
  intros i j; revert i; induction j; intros i; simpl.
  - apply NoDup_inf_nil.
  - apply NoDup_inf_cons; auto.
    apply not_In_inf_seq; lia.
Qed.

Lemma remove_NoDup_inf {A} (Eq_dec : forall (a b : A), {a = b} + {a <> b}): forall (a : A) l,
    NoDup_inf l ->
    NoDup_inf (remove Eq_dec a l).
Proof.
  intros a; induction l; intros Hndup; inversion Hndup; subst; simpl; auto.
  case (Eq_dec a a0); intros H.
  - apply IHl; assumption.
  - apply NoDup_inf_cons; [ | apply IHl; assumption].
    intros H1.
    apply H0.
    apply (In_inf_remove_In_inf _ _ _ _ _ H1).
Qed.
    
Lemma complementary_NoDup_inf : forall v n,
    NoDup_inf (complementary v n).
Proof.
  induction v; intros n; simpl.
  - apply seq_NoDup_inf.
  - apply remove_NoDup_inf.
    apply IHv.
Qed.

Lemma remove_length_not_In_inf {A} (Eq_dec : forall (a b : A), {a = b} + {a <> b}): forall (a : A) l,
    (In_inf a l -> False) ->
    length (remove Eq_dec a l) = length l.
Proof.
  intros a; induction l; intros Hnin; simpl; try reflexivity.
  case (Eq_dec a a0); intros H.
  - exfalso; subst.
    apply Hnin.
    left; reflexivity.
  - simpl; rewrite IHl; auto.
    intros Hin; apply Hnin; right; apply Hin.
Qed.

Lemma remove_length_In_inf_no_dup {A} (Eq_dec : forall (a b : A), {a = b} + {a <> b}): forall (a : A) l,
    In_inf a l ->
    NoDup_inf l ->
    length (remove Eq_dec a l) = pred (length l).
Proof.
  intros a l; induction l; intros Hin Hndup; try now inversion Hin.
  inversion Hin; subst.
  - rewrite remove_cons.
    simpl.
    inversion Hndup; subst.
    apply remove_length_not_In_inf.
    apply H0.
  - simpl.
    case (Eq_dec a a0); intros H.
    + apply remove_length_not_In_inf; inversion Hndup; subst; assumption.
    +  inversion Hndup; subst.
       simpl; rewrite IHl; try assumption.
       destruct l; simpl; try lia.
       inversion X.
Qed.    

Lemma complementary_length_lt_no_dup : forall v n,
    Forall_inf (fun x => x < n) v ->
    NoDup_inf v ->
    length (complementary v n) = n - (length v).
Proof.
  induction v; intros n Hall Hndup; simpl.
  - rewrite seq_length; lia.
  - inversion Hall; subst.
    inversion Hndup; subst.
    specialize (IHv n X X0).
    rewrite remove_length_In_inf_no_dup.
    + rewrite IHv.
      lia.
    + apply In_inf_complementary2_inv; assumption.
    + apply complementary_NoDup_inf.
Qed.

Lemma make_subsets_length : forall k,
    length (make_subsets k) = pred (2 ^ k).
Proof.
  induction k; simpl; try lia.
  rewrite app_length; rewrite map_length.
  rewrite IHk.
  assert (2 ^ k <> 0).
  { apply pow_not_0; lia. }
  lia.
Qed.  

(** Necessary definition *)
Fixpoint complexity_A n :=
  match n with
  | 0 => HMR_var n
  | S n => (<S> (complexity_A n)) \/S (<S> (complexity_A n))
  end.


(** Size of the formula return by the decidability algorithm *)

Definition H_shape i j k (T : p_sequent) :=
  {' (r, s) : _ & prod (Permutation_Type T (vec r (<S> (complexity_A i)) ++ vec s (complexity_A (S i))))
                       ((length r = j) *
                        (length s = k))}.

Lemma H_shape_complexity : forall i j k T,
    H_shape i j k T ->
    HMR_complexity_p_seq T = k.
Proof.
  intros i j k T Hshape.
  destruct Hshape as [[r s] [Hperm [H1 H2]]].
  rewrite complexity_p_seq_perm with _ (vec r (<S> complexity_A i) ++ vec s (complexity_A (S i))); auto.
  rewrite complexity_p_seq_app.
  rewrite 2 complexity_p_seq_vec; rewrite H2; rewrite H1.
  simpl.
  lia.
Qed.

Lemma p_seq_fst_non_basic_term_H_shape :
  forall i j k T,
    H_shape i j (S k) T ->
    {r & p_seq_fst_non_basic_term T = (r, complexity_A (S i))}.
Proof.
  intros i j k T Hshape; revert i j k Hshape; induction T; intros i j k Hshape.
  - destruct Hshape as [[r s] [Hperm [H1 H2]]].
    apply Permutation_Type_length in Hperm; rewrite app_length in Hperm; rewrite 2 vec_length in Hperm; simpl in *; lia.
  - destruct a as [a A].
    simpl p_seq_fst_non_basic_term.
    destruct Hshape as [[r s] [Hperm [H1 H2]]].
    assert (In_inf (a, A) (vec r (<S> complexity_A i) ++ vec s (complexity_A (S i)))).
    { apply Permutation_Type_in_inf with ((a, A) :: T); auto.
      left; reflexivity. }
    apply in_inf_app_or in X.
    destruct X.
    + apply in_inf_vec_eq_term in i0; destruct i0 as [Heq Hin]; subst.
      replace (0 <? HMR_complexity_term (<S> complexity_A i)) with false.
      2:{ symmetry; apply Nat.ltb_nlt; simpl; lia. }
      apply in_inf_split in Hin as [[ra rb] Heqr].
      refine (IHT i (length (ra ++ rb)) k _).
      split with (ra ++ rb, s).
      repeat split.
      * rewrite Heqr in Hperm.
        rewrite vec_app in *.
        simpl in *.
        Permutation_Type_solve.
      * apply H2.
    + apply in_inf_vec_eq_term in i0; destruct i0 as [Heq Hin]; subst.
      replace (0 <? HMR_complexity_term (complexity_A (S i))) with true.
      2:{ symmetry; apply Nat.ltb_lt; simpl; lia. }
      split with a; auto.
Qed.

Lemma p_seq_without_fst_non_basic_term_H_shape :
  forall i j k T,
    H_shape i j (S k) T ->
    H_shape i j k (p_seq_without_fst_non_basic_term T).
Proof.
  intros i j k T Hshape; revert i j k Hshape; induction T; intros i j k Hshape.
  - destruct Hshape as [[r s] [Hperm [H1 H2]]].
    apply Permutation_Type_length in Hperm; rewrite app_length in Hperm; rewrite 2 vec_length in Hperm; simpl in *; lia.
  - destruct a as [a A].
    simpl p_seq_fst_non_basic_term.
    destruct Hshape as [[r s] [Hperm [H1 H2]]].
    assert (In_inf (a, A) (vec r (<S> complexity_A i) ++ vec s (complexity_A (S i)))).
    { apply Permutation_Type_in_inf with ((a, A) :: T); auto.
      left; reflexivity. }
    apply in_inf_app_or in X.
    destruct X.
    + apply in_inf_vec_eq_term in i0; destruct i0 as [Heq Hin]; subst.
      replace (0 <? HMR_complexity_term (<S> complexity_A i)) with false.
      2:{ symmetry; apply Nat.ltb_nlt; simpl; lia. }
      apply in_inf_split in Hin as [[ra rb] Heqr].
      assert (H_shape i (length (ra ++ rb)) (S k) T).
      { split with (ra ++ rb, s).
        repeat split.
        * rewrite Heqr in Hperm.
          rewrite vec_app in *.
          simpl in *.
          Permutation_Type_solve.
        * apply H2. }
      specialize (IHT i (length (ra ++ rb)) k X).
      destruct IHT as [[r' s'] [Hperm' [H1' H2']]].
      split with (a :: r', s').
      repeat split.
      * simpl in *.
        Permutation_Type_solve.
      * rewrite Heqr; rewrite app_length in *; simpl; lia.
      * apply H2'.
    + apply in_inf_vec_eq_term in i0; destruct i0 as [Heq Hin]; subst.
      replace (0 <? HMR_complexity_term (complexity_A (S i))) with true.
      2:{ symmetry; apply Nat.ltb_lt; simpl; lia. }
      simpl.
      apply in_inf_split in Hin as [[sa sb] Heq].
      split with (r, sa ++ sb).
      repeat split.
      * rewrite Heq in Hperm; rewrite vec_app in *.
        simpl in *; Permutation_Type_solve.
      * rewrite Heq in H2; rewrite app_length in *.
        simpl in *; lia.
Qed.

Lemma Forall_inf_H_shape_complexity_not_nil : forall i j k G,
    G <> nil ->
    Forall_inf (H_shape i j k) G ->
    fst (HMR_complexity_p_hseq G) = k.
Proof.
  intros i j k G Hnnil Hall.
  induction G; [ exfalso; contradiction | ].
  inversion Hall; subst.
  destruct G.
  - simpl.
    rewrite H_shape_complexity with i j k _; auto.
    case_eq (k =? 0); intros H; auto.
    apply Nat.eqb_eq in H.
    simpl; lia.
  - clear Hnnil; assert (p :: G <> nil) as Hnnil.
    { intros H; inversion H. }
    specialize (IHG Hnnil X0).
    remember (p :: G); clear - IHG X.
    simpl.
    rewrite IHG.
    rewrite H_shape_complexity with i j k _; auto.
    rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma Forall_inf_H_shape_complexity_le : forall i j k G,
    Forall_inf (H_shape i j k) G ->
    fst (HMR_complexity_p_hseq G) <= k.
Proof.
  intros i j k G Hall.
  induction G; [ simpl; lia | ].
  inversion Hall; subst.
  specialize (IHG X0).
  simpl.
  apply H_shape_complexity in X.
  case_eq (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); intros H; (apply Nat.eqb_eq in H + apply Nat.eqb_neq in H); simpl; try lia.
  replace (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) with false; simpl; try lia.
  symmetry; apply Nat.ltb_nlt; lia.
Qed.
  
Definition H_shape_hseq i j k l (G : p_hypersequent) :=
  {' (G1, G2) : _ & prod (Permutation_Type G (G1 ++ G2))
                         ((length G2 = l) *
                          (Forall_inf (H_shape i (S j) k) G1) *
                          (Forall_inf (H_shape i j (S k)) G2))}.

Lemma H_shape_hseq_complexity_S_l : forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    fst (HMR_complexity_p_hseq G) = S k.
Proof.
  intros i j k l G Hshape.
  destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
  rewrite complexity_p_hseq_perm with _ (G1 ++ G2); auto.
  rewrite complexity_p_hseq_app.
  apply Forall_inf_H_shape_complexity_le in H2.
  apply Forall_inf_H_shape_complexity_not_nil in H3.
  2:{ intros H; subst; inversion H1. }
  lia.
Qed.

Lemma H_shape_hseq_complexity_le : forall i j k l G,
    H_shape_hseq i j k l G ->
    fst (HMR_complexity_p_hseq G) <= S k.
Proof.
  intros i j k l G Hshape.
  destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
  rewrite complexity_p_hseq_perm with _ (G1 ++ G2); auto.
  rewrite complexity_p_hseq_app.
  apply Forall_inf_H_shape_complexity_le in H2.
  apply Forall_inf_H_shape_complexity_le in H3.
  lia.
Qed.

Lemma p_hseq_without_max_complexity_H_shape :
  forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    H_shape_hseq i j k l (p_hseq_without_max_complexity G).
Proof.
  intros i j k l G Hshape.
  induction G.
  - destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
    apply Permutation_Type_length in Hperm; rewrite app_length in Hperm; simpl in Hperm.
    exfalso; lia.
  - assert (Hc := H_shape_hseq_complexity_S_l i j k l (a :: G) Hshape).
    destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
    simpl.
    case_eq (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); intros H.
    + assert (In_inf a (G1 ++ G2)).
      { apply Permutation_Type_in_inf with (a :: G); auto.
        left; reflexivity. }
      apply in_inf_app_or in X; destruct X.
      * apply Forall_inf_forall with _ _ _ a in H2; auto.
        apply H_shape_complexity in H2.
        apply Nat.leb_le in H.
        simpl in Hc.
        exfalso.
        revert Hc; case (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); [ | case (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) ]; simpl; intros Hc; lia.
      * apply in_inf_split in i0 as [[G2a G2b] Heq]; subst.
        split with (G1, (G2a ++ G2b)).
        repeat split.
        -- Permutation_Type_solve.
        -- rewrite app_length in *; simpl in H1; lia.
        -- apply H2.
        -- apply Forall_inf_app; [ apply Forall_inf_app_l in H3 | apply Forall_inf_app_r in H3; inversion H3]; assumption.
    + assert (In_inf a (G1 ++ G2)).
      { apply Permutation_Type_in_inf with (a :: G); auto.
        left; reflexivity. }
      apply in_inf_app_or in X; destruct X.
      * assert (H_shape_hseq i j k (S l) G).
        { apply in_inf_split in i0 as [[G1a G1b] Heq]; subst.
          split with ((G1a ++ G1b), G2).
          repeat split.
          - Permutation_Type_solve.
          - apply H1.
          - apply Forall_inf_app; [ apply Forall_inf_app_l in H2 | apply Forall_inf_app_r in H2; inversion H2]; assumption.
          - apply H3. }
        specialize (IHG X).
        destruct IHG as [[G1' G2'] [Hperm' [ [H1' H2'] H3']]].
        split with (a :: G1', G2'); repeat split; try auto.
        -- Permutation_Type_solve.
        -- apply Forall_inf_cons; auto.
           apply Forall_inf_forall with _ _ _ a in H2; auto.
      * assert (H_shape_hseq i j k l G).
        { apply in_inf_split in i0 as [[G2a G2b] Heq]; subst.
          split with (G1, (G2a ++ G2b)).
          repeat split.
          - Permutation_Type_solve.
          - rewrite app_length in *; simpl in H1; lia.
          - apply H2.
          - apply Forall_inf_app; [ apply Forall_inf_app_l in H3 | apply Forall_inf_app_r in H3; inversion H3]; assumption. }
        apply Forall_inf_forall with _ _ _ a in H3; auto.
        apply H_shape_complexity in H3.
        apply Nat.leb_nle in H.
        simpl in Hc.
        exfalso.
        revert Hc; case (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); [ | case (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) ]; simpl; intros Hc; try lia.
        apply H_shape_hseq_complexity_le in X.
        lia.
Qed.

Lemma p_hseq_p_seq_max_complexity_H_shape :
  forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    H_shape i j (S k) (p_hseq_p_seq_max_complexity G).
Proof.
  intros i j k l G Hshape.
  induction G.
  - destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
    apply Permutation_Type_length in Hperm; rewrite app_length in Hperm; simpl in Hperm.
    exfalso; lia.
  - assert (Hc := H_shape_hseq_complexity_S_l i j k l (a :: G) Hshape).
    destruct Hshape as [[G1 G2] [Hperm [ [H1 H2] H3]]].
    simpl.
    case_eq (fst (HMR_complexity_p_hseq G) <=? HMR_complexity_p_seq a); intros H.
    + assert (In_inf a (G1 ++ G2)).
      { apply Permutation_Type_in_inf with (a :: G); auto.
        left; reflexivity. }
      apply in_inf_app_or in X; destruct X.
      * apply Forall_inf_forall with _ _ _ a in H2; auto.
        apply H_shape_complexity in H2.
        apply Nat.leb_le in H.
        simpl in Hc.
        exfalso.
        revert Hc; case (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); [ | case (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) ]; simpl; intros Hc; lia.
      * apply Forall_inf_forall with _ _ _ a in H3; auto.
    + assert (In_inf a (G1 ++ G2)).
      { apply Permutation_Type_in_inf with (a :: G); auto.
        left; reflexivity. }
      apply in_inf_app_or in X; destruct X.
      * apply IHG.
        apply in_inf_split in i0 as [[G1a G1b] Heq]; subst.
        split with ((G1a ++ G1b), G2).
        repeat split.
        -- Permutation_Type_solve.
        -- apply H1.
        -- apply Forall_inf_app; [ apply Forall_inf_app_l in H2 | apply Forall_inf_app_r in H2; inversion H2]; assumption.
        -- apply H3.
      * assert (H_shape_hseq i j k l G).
        { apply in_inf_split in i0 as [[G2a G2b] Heq]; subst.
          split with (G1, (G2a ++ G2b)).
          repeat split.
          - Permutation_Type_solve.
          - rewrite app_length in *; simpl in H1; lia.
          - apply H2.
          - apply Forall_inf_app; [ apply Forall_inf_app_l in H3 | apply Forall_inf_app_r in H3; inversion H3]; assumption. }
        apply Forall_inf_forall with _ _ _ a in H3; auto.
        apply H_shape_complexity in H3.
        apply Nat.leb_nle in H.
        simpl in Hc.
        exfalso.
        revert Hc; case (HMR_complexity_p_seq a =? fst (HMR_complexity_p_hseq G)); [ | case (HMR_complexity_p_seq a <? fst (HMR_complexity_p_hseq G)) ]; simpl; intros Hc; try lia.
        apply H_shape_hseq_complexity_le in X.
        lia.
Qed.  

Lemma p_hseq_put_non_basic_fst_H_shape :
  forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    {' (r, T, H) & prod (p_hseq_put_non_basic_fst G = ((r, complexity_A (S i)) :: T) :: H)
                        ((H_shape i j k T) *
                         (H_shape_hseq i j k l H)) }.
Proof.
  intros i j k l G Hshape.
  unfold p_hseq_put_non_basic_fst.
  assert (Hshape_max_c := p_hseq_p_seq_max_complexity_H_shape i j k l G Hshape).
  assert (Hshape_wo_max_c := p_hseq_without_max_complexity_H_shape i j k l G Hshape).
  assert (Hshape_T := p_seq_without_fst_non_basic_term_H_shape i j k _ Hshape_max_c).
  destruct (p_seq_fst_non_basic_term_H_shape i j k _ Hshape_max_c) as [r A].
  split with (r, p_seq_without_fst_non_basic_term (p_hseq_p_seq_max_complexity G), p_hseq_without_max_complexity G); repeat split; auto.
  rewrite A; reflexivity.
Qed.

Lemma apply_logical_rule_H_shape :
  forall i j k l G,
    H_shape_hseq i j k (S l) G ->
    { H & prod (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = inl H)
               (H_shape_hseq i j k l H) }.
Proof.
  intros i j k l G Hshape.
  destruct (p_hseq_put_non_basic_fst_H_shape i j k l G Hshape) as [[[r T] H] [Heq [Hshape1 Hshape2]]].
  remember (apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G)).
  destruct s.
  - remember (p_hseq_put_non_basic_fst G) as H'.
    clear HeqH'.
    split with p; split; [reflexivity |].
    destruct H'.
    + inversion Heq.
    + destruct l0.
      * inversion Heq.
      * destruct p0 as [a A].
        inversion Heq; subst.
        simpl in Heqs.
        inversion Heqs; subst.
        destruct Hshape2 as [[G1 G2] [Hperm [[H1 H2] H3]]].
        split with (((r, <S> complexity_A i) :: T) :: ((r, <S> complexity_A i) :: T) :: G1, G2).
        repeat split.
        -- Permutation_Type_solve.
        -- apply H1.
        -- destruct Hshape1 as [[r' s'] [Hperm' [H1' H2']]].
           repeat apply Forall_inf_cons.
           ++ split with (r :: r', s').
              repeat split.
              ** simpl; Permutation_Type_solve.
              ** simpl; lia.
              ** apply H2'.
           ++ split with (r :: r', s').
              repeat split.
              ** simpl; Permutation_Type_solve.
              ** simpl; lia.
              ** apply H2'.
           ++ apply H2.
        -- apply H3.
  - rewrite Heq in Heqs.
    inversion Heqs.
Qed.

Lemma H_shape_hseq_0 :
  forall i j k G,
    H_shape_hseq i j (S k) 0 G ->
    H_shape_hseq i (S j) k (length G) G.
Proof.
  intros i j k G Hshape.
  destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
  split with (nil, G1).
  destruct G2; [ | inversion H1].
  repeat split; auto.
  - Permutation_Type_solve.
  - apply Permutation_Type_length in Hperm.
    rewrite app_length in Hperm; simpl in Hperm; lia.
Qed.

Lemma nb_exists_FOL_R_basic_case_aux_indep_acc (G : p_hypersequent) (V : list (list nat)) n (Heqn : max_diamond_p_hseq G = n) (acc1 acc2 : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
    nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc1) =
    nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc2)
with nb_exists_HMR_dec_formula_aux_indep_acc (G : p_hypersequent) (x: nat) (Heqx : snd (fst (modal_complexity_p_hseq G)) = x) p (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p) (acc1 acc2 : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) :
         nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc1) =
         nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc2).
Proof.
  - destruct acc1 as [acc1]; destruct acc2 as [acc2].
    destruct V; destruct n.
    + reflexivity.
    + reflexivity.
    + simpl.
      apply f_equal2_plus; [ reflexivity | ].
      refine (nb_exists_FOL_R_basic_case_aux_indep_acc _ _ _ _ (acc1 _ _) (acc2 _ _)).
    + simpl; rewrite ? nb_exists_FOL_R_exists_vec; simpl.
      repeat (apply f_equal2_plus; try reflexivity).
      * refine (nb_exists_HMR_dec_formula_aux_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _)).
      * refine (nb_exists_FOL_R_basic_case_aux_indep_acc _ _ _ _ (acc1 _ _) (acc2 _ _)).
  - destruct acc1 as [acc1]; destruct acc2 as [acc2].
    destruct x.
    + simpl.
      refine (nb_exists_FOL_R_basic_case_aux_indep_acc _ _ _ _ (acc1 _ _) (acc2 _ _)).
    + destruct p.
      * refine (nb_exists_HMR_dec_formula_aux_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _)).
      * destruct p.
        simpl; apply f_equal2_plus.
        -- refine (nb_exists_HMR_dec_formula_aux_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _)).
        -- refine (nb_exists_HMR_dec_formula_aux_indep_acc _ _ _ _ _ (acc1 _ _) (acc2 _ _)).
Qed.

Fixpoint nb_exists_FOL_R_basic_aux_sub 
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = S n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  forall v,
    In_inf v V ->
    nb_exists_FOL_R_formula (HMR_dec_formula_aux (flat_map (fun i : nat => seq_mul (FOL_R_var (S (max_var_weight_p_hseq G) + i)) (only_diamond_p_seq (nth i G nil))) v :: nil)
                         _
                         (eq_refl _)
                         _
                         (eq_refl _)
                         (Acc_inv acc _
                                  (lt_nat3_to_lt_nat4
                                     _
                                     _
                                     _
                                     _
                                     (modal_complexity_only_diamond_p_seq _ _ _ _ Heqn)))) <= nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V (S n) Heqn acc).
Proof.
  intros v Hin.
  destruct acc as [acc].
  destruct V; inversion Hin; subst.
  - simpl; rewrite nb_exists_FOL_R_exists_vec.
    simpl; lia.
  - transitivity (nb_exists_FOL_R_formula
                    (FOL_R_basic_case_aux G V (S n) Heqn
                                          (acc
                                             (modal_complexity_p_hseq G,
                                              (fix length (l : list (list nat)) : nat :=
                                                 match l with
                                                 | nil => 0
                                                 | _ :: l' => S (length l')
                                                 end) V)
                                             (lt_nat4_last (modal_complexity_p_hseq G)
                                                           ((fix length (l : list (list nat)) : nat :=
                                                               match l with
                                                               | nil => 0
                                                               | _ :: l' => S (length l')
                                                               end) V)
                                                           (S
                                                              ((fix length (l : list (list nat)) : nat :=
                                                                  match l with
                                                                  | nil => 0
                                                                  | _ :: l' => S (length l')
                                                                  end) V))
                                                           (Nat.lt_succ_diag_r
                                                              ((fix length (l : list (list nat)) : nat :=
                                                                  match l with
                                                                  | nil => 0
                                                                  | _ :: l' => S (length l')
                                                                  end) V)))))); [ | simpl; lia].
    etransitivity.
    2:{ refine (nb_exists_FOL_R_basic_aux_sub G V n Heqn _ v X). }
    apply Nat.eq_le_incl.
    apply nb_exists_HMR_dec_formula_aux_indep_acc.
Qed.

Lemma H_shape_hseq_only_diamond :
  forall i j n G,
    G <> nil ->
    H_shape_hseq (S i) j 0 0 G ->
    H_shape_hseq i 0 (pred (length G * (S j))) 1 (flat_map (fun i0 : nat => seq_mul (FOL_R_var (n + i0)) (only_diamond_p_seq (nth i0 G nil))) (seq 0 (length G)) :: nil).
Proof.
  intros i j n G Hnnil Hshape.
  split with (nil , (flat_map
                       (fun i0 : nat =>
                          seq_mul (FOL_R_var (n + i0))
                                  (only_diamond_p_seq (nth i0 G nil))) (seq 0 (length G)) :: nil)).
  repeat split; auto.
  destruct Hshape as [[G1 G2] [Hperm [[H1 H2] _]]].
  destruct G2; [ clear H1 | exfalso; simpl in *; lia].
  rewrite app_nil_r in Hperm.
  apply Forall_inf_Permutation_Type with _ _ _ G in H2; [ | symmetry; apply Hperm].
  clear - H2 Hnnil.
  revert n.
  induction G; [ contradiction | ].
  intros n.
  destruct G.
  - simpl.
    rewrite app_nil_r.
    apply Forall_inf_cons; [ | apply Forall_inf_nil].
    inversion H2; subst.
    destruct X as [[r s] [Hperm [H3 H4]]].
    destruct s; [ | exfalso; simpl in*; lia].
    split with (nil, mul_vec (FOL_R_var (n + 0)) r).
    repeat split.
    + simpl.
      simpl in Hperm.
      rewrite app_nil_r in Hperm.
      destruct (Permutation_Type_vec_decomp _ _ _ Hperm) as [vs [Heqvr Hpermvr]].
      rewrite Heqvr.
      rewrite only_diamond_p_seq_vec_diamond.
      rewrite seq_mul_vec_eq_vec_mul_vec.
      apply Permutation_Type_vec.
      apply Permutation_Type_mul_vec.
      symmetry; apply Hpermvr.
    + rewrite mul_vec_length.
      lia.
  - assert (p :: G <> nil) by (intros H; inversion H).
    remember (p :: G) as G'.
    inversion H2.
    specialize (IHG H X0 (S n)).
    clear G HeqG' Hnnil H1 H3 X0 x l.
    simpl.
    rewrite <- seq_shift.
    rewrite flat_map_map.
    apply Forall_inf_cons; [ | apply Forall_inf_nil].
    inversion IHG; subst.
    clear X1.
    destruct X0 as [[r s] [Hperm [Hr Hs]]].
    destruct r; [ | exfalso; simpl in *; lia ].
    clear Hr.
    split with (nil, mul_vec (FOL_R_var (n + 0)) (map fst (only_diamond_p_seq a)) ++ s).
    repeat split.
    + simpl.
      rewrite vec_app.
      apply Permutation_Type_app.
      2:{ erewrite flat_map_ext; [apply Hperm |].
          intros x; simpl.
          replace (n + S x) with (S (n + x)) by lia.
          reflexivity. }
      destruct X as [[ra sa] [Hperma [Hra Hsa]]].
      destruct sa; [ | exfalso; simpl in *; lia].
      simpl in *.
      rewrite app_nil_r in Hperma.
      transitivity (vec (mul_vec (FOL_R_var (n + 0)) ra) (<S> complexity_A i \/S <S> complexity_A i)).
      * rewrite <- seq_mul_vec_eq_vec_mul_vec.
        apply seq_mul_perm.
        replace (vec ra (<S> complexity_A i \/S <S> complexity_A i)) with (only_diamond_p_seq (vec ra (<S> (<S> complexity_A i \/S <S> complexity_A i)))).
        2:{ apply only_diamond_p_seq_vec_diamond. }
        apply only_diamond_p_seq_perm.
        apply Hperma.
      * rewrite <- 2 seq_mul_vec_eq_vec_mul_vec.
        apply seq_mul_perm.
        apply Permutation_Type_vec.
        destruct (Permutation_Type_vec_decomp _ _ _ Hperma) as [vs [Heqvs Hpermvs]].
        rewrite Heqvs.
        rewrite only_diamond_p_seq_vec_diamond.
        rewrite Heqvs in Hperma.
        apply Permutation_Type_vec_inv in Hperma.
        etransitivity ; [symmetry; apply Hperma |].
        clear.
        induction vs; simpl; auto.
    + rewrite app_length; rewrite mul_vec_length.
      rewrite map_length.
      destruct X as [[ra sa] [Hperma [Hra Hsa]]].
      destruct sa; [ | exfalso; simpl in *; lia].
      simpl in Hperma.
      rewrite app_nil_r in Hperma.
      replace (length (only_diamond_p_seq a)) with (length (vec ra (<S> complexity_A i \/S <S> complexity_A i))).
      * rewrite vec_length.
        destruct G'; [ contradiction | ].
        simpl; simpl in Hs.
        lia.        
      * replace (vec ra (<S> complexity_A i \/S <S> complexity_A i)) with (only_diamond_p_seq (vec ra (<S> (<S> complexity_A i \/S <S> complexity_A i)))).
        2:{ apply only_diamond_p_seq_vec_diamond. }
        apply Permutation_Type_length.
        apply only_diamond_p_seq_perm.
        symmetry; apply Hperma.
Qed.

Lemma nb_exists_HMR_dec_formula_aux_complexity_basic
      (G : p_hypersequent)
      x
      (Heqx : snd (fst (modal_complexity_p_hseq G)) = x)
      p
      (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) :
  forall acc',
    x = 0 ->
    nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc) =
    nb_exists_FOL_R_formula (FOL_R_basic_case_aux
                               G
                               (map (@rev nat) (make_subsets (length G)))
                               _
                               (eq_refl _)
                               acc').
Proof.
  intros acc' Heq0.
  destruct acc as [acc].
  destruct x; inversion Heq0.
  simpl.
  apply nb_exists_FOL_R_basic_case_aux_indep_acc.
Qed.

Lemma nb_exists_FOL_R_all_zero :
  forall k v,
    nb_exists_FOL_R_formula (FOL_R_all_zero k v) = 0.
Proof.
  intros k v.
  induction v; simpl; lia.
Qed.

Lemma nb_exists_FOL_R_all_gtz :
  forall k v,
    nb_exists_FOL_R_formula (FOL_R_all_gtz k v) = 0.
Proof.
  intros k v.
  induction v; simpl; lia.
Qed.

Lemma nb_exists_FOL_R_all_atoms_eq :
  forall G k,
    nb_exists_FOL_R_formula (FOL_R_all_atoms_eq G k) = 0.
Proof.
  intros G k.
  induction k; simpl; lia.
Qed.

Lemma nb_exists_FOL_R_phi : forall G l, nb_exists_FOL_R_formula (FOL_R_phi G l) = 0.
Proof.
  intros G l; simpl.
  rewrite nb_exists_FOL_R_all_zero.
  rewrite nb_exists_FOL_R_all_gtz.
  rewrite nb_exists_FOL_R_all_atoms_eq.
  reflexivity.
Qed.

Fixpoint nb_exists_FOL_R_basic_case_aux_complexity_no_diamond
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  n = 0 ->
  nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc) = length G * length V.
Proof.
  intros H.
  destruct acc as [acc].
  destruct n; inversion H.
  destruct V.
  - simpl; lia.
  - simpl.
    rewrite nb_exists_FOL_R_exists_vec.
    rewrite (nb_exists_FOL_R_basic_case_aux_complexity_no_diamond G V
                                                                  0%nat
                                                                  Heqn
                                                                  (acc _
                                                                       (lt_nat4_last
                                                                          _
                                                                          _
                                                                     _
                                                                     (Nat.lt_succ_diag_r _)))); auto.
    rewrite seq_length.
    rewrite nb_exists_FOL_R_phi.
    symmetry.
    lia.
Qed.

Fixpoint nb_exists_FOL_R_basic_case_aux_complexity_le
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  length G * length V <= nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc).
Proof.
  destruct acc as [acc].
  destruct n.
  { rewrite nb_exists_FOL_R_basic_case_aux_complexity_no_diamond; auto. }
  destruct V.
  - simpl; lia.
  - simpl.
    rewrite nb_exists_FOL_R_exists_vec.
    specialize (nb_exists_FOL_R_basic_case_aux_complexity_le G V
                                                             (S n)
                                                             Heqn
                                                             (acc _
                                                                  (lt_nat4_last
                                                                     _
                                                                     _
                                                                     _
                                                                     (Nat.lt_succ_diag_r _)))); auto.
    rewrite seq_length.
    lia.
Qed.
                                                                           
Lemma FOL_R_basic_aux_complexity
      (G : p_hypersequent)
      (V : list (list nat))
      n
      (Heqn : max_diamond_p_hseq G = n)
      (acc : Acc lt_nat4 (modal_complexity_p_hseq G , length V)) :
  forall i j,
    In_inf (seq 0 (length G)) V ->
    H_shape_hseq i j 0 0 G ->
    pow2 j <= pred (length G) ->
    tetra_2 i j <= nb_exists_FOL_R_formula (FOL_R_basic_case_aux G V n Heqn acc)
with HMR_dec_formula_aux_complexity
       (G : p_hypersequent)
       (x: nat)
       (Heqx : snd (fst (modal_complexity_p_hseq G)) = x)
       p
       (Heqp : apply_logical_rule_on_p_hypersequent (p_hseq_put_non_basic_fst G) = p)
       (acc : Acc lt_nat4 (modal_complexity_p_hseq G, S (length (make_subsets (length G))))) :
       forall i j k l,
         G <> nil ->
         H_shape_hseq i j k l G ->
         pow2 j <= pred (length G + l) ->
         tetra_2 i (j + k) <= nb_exists_FOL_R_formula (HMR_dec_formula_aux G x Heqx p Heqp acc).
Proof.
  - intros i j Hin Hshape Hlen.
    destruct acc as [acc].
    destruct n.
    + replace i with 0 in *.
      2:{ clear - Heqn Hshape Hlen.
          destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
          destruct G2; [ | exfalso; simpl in *; lia ].
          destruct G1.
          { apply Permutation_Type_length in Hperm.
            unfold pow2 in *; simpl in *.
            assert (H := le_1_pow2 j).
            lia. }
          destruct i; auto.
          exfalso.
          inversion H2; subst.
          destruct X as [[vr vs] [Hperm' [H4 H5]]].
          rewrite max_diamond_p_hseq_perm with _ (p :: G1) in Heqn by Permutation_Type_solve.
          simpl in Heqn.
          destruct vr; try now inversion H4.
          simpl in Hperm'.
          assert (In_inf (f , <S> (complexity_A (S i))) p).
          { apply Permutation_Type_in_inf with ((f, <S> (<S> complexity_A i \/S <S> complexity_A i))
                                               :: vec vr (<S> (<S> complexity_A i \/S <S> complexity_A i)) ++
                                               vec vs
                                               (<S> (<S> complexity_A i \/S <S> complexity_A i) \/S
                                                                                                  <S> (<S> complexity_A i \/S <S> complexity_A i))); [symmetry; apply Hperm' | ].
            left; reflexivity. }
          apply in_inf_split in X as [[pa pb] Heq].
          rewrite Heq in Heqn.
          rewrite max_diamond_p_seq_app in Heqn.
          change (max_diamond_p_seq ((f, <S> complexity_A (S i)) :: pb)) with (max (S (max_diamond_term (complexity_A (S i)))) (max_diamond_p_seq pb)) in Heqn.
          lia. }
      simpl.
      destruct V.
      * exfalso; contradiction.
      * clear Hin.
        simpl.
        rewrite nb_exists_FOL_R_exists_vec.
        rewrite seq_length.
        transitivity (pow2 j); try lia.
        apply id_le_pow2.
    + destruct i.
      { simpl tetra_2.
        etransitivity ; [ | apply nb_exists_FOL_R_basic_case_aux_complexity_le].
        destruct V; [inversion Hin | ].
        simpl.
        transitivity (pow2 j); try lia.
        apply id_le_pow2. }
      etransitivity.
      2:{ apply nb_exists_FOL_R_basic_aux_sub.
          apply Hin. }
      etransitivity.
      2:{ apply (HMR_dec_formula_aux_complexity _ _ _ _ _ _ i 0 (pred (length G * (S j))) 1).
          - intros H; inversion H.
          - apply H_shape_hseq_only_diamond.
            + destruct G; inversion Heqn.
              intros H; inversion H.
            + apply Hshape.
          - unfold pow2; simpl; lia. }
      simpl.
      transitivity (tetra_2 i (pow2 j)).
      * rewrite tetra_2_pow2.
        reflexivity.
      * apply tetra_2_le_mono.
        lia.
  - intros i j k l Hnnil Hshape Hlen.
    destruct acc as [acc].
    destruct x.
    + simpl.
      replace k with 0 in *.
      2:{ clear - Hnnil Hshape Heqx.
          destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
          rewrite modal_complexity_perm with _ (G1 ++ G2) in Heqx; auto.
          simpl in Heqx.
          rewrite complexity_p_hseq_app in Heqx.
          destruct G1; [ destruct G2 | ].
          - simpl in Hperm.
            symmetry in Hperm; apply Permutation_Type_nil in Hperm.
            contradiction.
          - inversion H3; subst.
            destruct X as [[vr vs] [Hperm1 [Heq1 Heq2]]].
            destruct vs; [ exfalso; simpl in *; inversion Heq2 | ].
            simpl in Hperm1.
            assert (In_inf (f, complexity_A (S i)) p).
            { symmetry in Hperm1.
              apply (Permutation_Type_in_inf _ Hperm1).
              apply in_inf_or_app.
              right; left; reflexivity. }
            apply in_inf_split in X as [[p1 p2] Heq].
            rewrite Heq in Heqx.
            rewrite complexity_p_hseq_cons in Heqx.
            rewrite complexity_p_seq_app in Heqx.
            simpl in Heqx.
            lia.
          - inversion H2; subst.
            destruct X as [[vr vs] [Hperm1 [Heq1 Heq2]]].
            destruct k; auto.
            destruct vs; [ exfalso; simpl in *; inversion Heq2 | ].
            simpl in Hperm1.
            assert (In_inf (f, complexity_A (S i)) p).
            { symmetry in Hperm1.
              apply (Permutation_Type_in_inf _ Hperm1).
              apply in_inf_or_app.
              right; left; reflexivity. }
            apply in_inf_split in X as [[p1 p2] Heq].
            rewrite Heq in Heqx.
            rewrite complexity_p_hseq_cons in Heqx.
            rewrite complexity_p_seq_app in Heqx.
            simpl in Heqx.
            lia. }
      replace l with 0 in *.
      2:{ clear - Hnnil Hshape Heqx.
          destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
          rewrite modal_complexity_perm with _ (G1 ++ G2) in Heqx; auto.
          simpl in Heqx.
          rewrite complexity_p_hseq_app in Heqx.
          destruct G2.
          - apply H1.
          - inversion H3; subst.
            destruct X as [[vr vs] [Hperm1 [Heq1 Heq2]]].
            destruct vs; [ exfalso; simpl in *; inversion Heq2 | ].
            simpl in Hperm1.
            assert (In_inf (f, complexity_A (S i)) p).
            { symmetry in Hperm1.
              apply (Permutation_Type_in_inf _ Hperm1).
              apply in_inf_or_app.
              right; left; reflexivity. }
            apply in_inf_split in X as [[p1 p2] Heq].
            rewrite Heq in Heqx.
            rewrite complexity_p_hseq_cons in Heqx.
            rewrite complexity_p_seq_app in Heqx.
            simpl in Heqx.
            lia. }
      etransitivity.
      2:{ refine (FOL_R_basic_aux_complexity _ _ _ _ _ _ _ _ Hshape _).
          - rewrite <- (rev_involutive (seq _ _)).
            apply in_inf_map.
            apply cond_is_in_make_subsets.
            + apply rev_not_nil.
              destruct G; [contradiction | ].
              intros H'; inversion H'.
            + clear - Hnnil.
              apply rev_nth_all_lt.
              intros i.
              case_eq (i <? length G); intros H; (apply Nat.ltb_lt in H + apply Nat.ltb_nlt in H).
              * rewrite seq_nth; lia.
              * rewrite nth_overflow; [ | rewrite seq_length; lia].
                destruct G; [ contradiction | simpl; lia].
            + clear - Hnnil.
              intros i j H1 H2.
              apply rev_reverse_order_lt; try assumption.
              clear.
              intros i j H1 H2.
              rewrite seq_length in H1.
              rewrite ? seq_nth; lia.
          - lia. }
      simpl.
      apply tetra_2_le_mono.
      unfold pow2; simpl; lia.
    + destruct l.
      * destruct k.
        { exfalso.
          clear - Hnnil Hshape Heqx.
          destruct Hshape as [[G1 G2] [Hperm [[H1 H2] H3]]].
          rewrite modal_complexity_perm with _ (G1 ++ G2) in Heqx; auto.
          simpl in Heqx.
          rewrite complexity_p_hseq_app in Heqx.
          destruct G2; [ | simpl in H1; exfalso; lia].
          simpl in *.
          assert (fst (HMR_complexity_p_hseq G1) = 0).
          { clear - H2.
            induction G1; auto.
            inversion H2; subst.
            specialize (IHG1 X0).
            destruct X as [[vr vs] [Hperm [Heq1 Heq2]]].
            destruct vs; [ | exfalso; simpl in *; lia].
            rewrite complexity_p_hseq_cons.
            rewrite (complexity_p_seq_perm _ _ Hperm).
            rewrite complexity_p_seq_app.
            rewrite ? complexity_p_seq_vec.
            simpl.
            lia. }
          lia. }          
        apply H_shape_hseq_0 in Hshape.
        assert {n & length G = S n} as [n Heqn].
        { destruct G; inversion Heqx.
          split with (length G).
          reflexivity. }
        rewrite Heqn in Hshape.
        destruct (p_hseq_put_non_basic_fst_H_shape i (S j) k n G Hshape) as [[[r T] H] [Heq [Hshape1 Hshape2]]].
        destruct p.
        2:{ exfalso.
            rewrite Heq in Heqp.
            inversion Heqp. }
        simpl.
        etransitivity.
        2:{ refine (HMR_dec_formula_aux_complexity p
                                                   _
                                                   eq_refl
                                                   _
                                                   eq_refl
                                                   (acc _
                                                        (lt_nat3_to_lt_nat4 _ _ _ _
                                                                            (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp)))
                                                   i (S j) k n
                                                   _
                                                   _
                                                   _); try lia.
            { intros H'.
              rewrite Heq in Heqp.
              rewrite H' in Heqp.
              inversion Heqp. }
            2:{ replace (length p) with (S (length G)).
                2:{ replace (length G) with (length (((r, complexity_A (S i)) :: T) :: H)).
                    - rewrite Heq in Heqp.
                      inversion Heqp.
                      reflexivity.
                    - rewrite <- Heq.
                      clear - Heqx.
                      unfold p_hseq_put_non_basic_fst.
                      simpl.
                      change (S (length (p_hseq_without_max_complexity G))) with (length (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
                      apply Permutation_Type_length.
                      symmetry; apply p_hseq_put_max_complexity_fst.
                      intros H; subst; inversion Heqx. }                
                rewrite pow2_S; rewrite Heqn in *.
                lia. }
            destruct Hshape2 as [[G1 G2] [Hperm [[H1 H2] H3]]].
            split with (((r, <S> complexity_A i) :: T) :: ((r, <S> complexity_A i) :: T) :: G1, G2).
            rewrite Heq in Heqp.
            simpl in Heqp.
            inversion Heqp.
            repeat split.
            - Permutation_Type_solve.
            - apply H1.
            - destruct Hshape1 as [[r' s'] [Hperm' [H1' H2']]].
              repeat apply Forall_inf_cons.
              + split with (r :: r', s').
                repeat split.
                * simpl; Permutation_Type_solve.
                * simpl; lia.
                * apply H2'.
              + split with (r :: r', s').
              repeat split.
                * simpl; Permutation_Type_solve.
                * simpl; lia.
                * apply H2'.
              + apply H2.
            - apply H3. }
        replace (length p) with (S (length G)).
        2:{ replace (length G) with (length (((r, complexity_A (S i)) :: T) :: H)).
            - rewrite Heq in Heqp.
              inversion Heqp.
              reflexivity.
            - rewrite <- Heq.
              clear - Heqx.
              unfold p_hseq_put_non_basic_fst.
              simpl.
              change (S (length (p_hseq_without_max_complexity G))) with (length (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
              apply Permutation_Type_length.
              symmetry; apply p_hseq_put_max_complexity_fst.
              intros H; subst; inversion Heqx. }
        apply tetra_2_le_mono.
        lia.
      * destruct (p_hseq_put_non_basic_fst_H_shape i j k l G Hshape) as [[[r T] H] [Heq [Hshape1 Hshape2]]].
        destruct p.
        2:{ exfalso.
            rewrite Heq in Heqp.
            inversion Heqp. }
        simpl.
        etransitivity.
        2:{ refine (HMR_dec_formula_aux_complexity p
                                                   _
                                                   eq_refl
                                                   _
                                                   eq_refl
                                                   (acc _
                                                        (lt_nat3_to_lt_nat4 _ _ _ _
                                                                            (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp)))
                                                   i j k l
                                                   _
                                                   _
                                                   _); try lia.
            { intros H'.
              rewrite Heq in Heqp.
              rewrite H' in Heqp.
              inversion Heqp. }
            2:{ replace (length p) with (S (length G)).
                2:{ replace (length G) with (length (((r, complexity_A (S i)) :: T) :: H)).
                    - rewrite Heq in Heqp.
                      inversion Heqp.
                      reflexivity.
                    - rewrite <- Heq.
                      clear - Heqx.
                      unfold p_hseq_put_non_basic_fst.
                      simpl.
                      change (S (length (p_hseq_without_max_complexity G))) with (length (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
                      apply Permutation_Type_length.
                      symmetry; apply p_hseq_put_max_complexity_fst.
                      intros H; subst; inversion Heqx. }
                lia. }
            destruct Hshape2 as [[G1 G2] [Hperm [[H1 H2] H3]]].
            split with (((r, <S> complexity_A i) :: T) :: ((r, <S> complexity_A i) :: T) :: G1, G2).
            rewrite Heq in Heqp.
            simpl in Heqp.
            inversion Heqp.
            repeat split.
            - Permutation_Type_solve.
            - apply H1.
            - destruct Hshape1 as [[r' s'] [Hperm' [H1' H2']]].
              repeat apply Forall_inf_cons.
              + split with (r :: r', s').
                repeat split.
                * simpl; Permutation_Type_solve.
                * simpl; lia.
                * apply H2'.
              + split with (r :: r', s').
              repeat split.
                * simpl; Permutation_Type_solve.
                * simpl; lia.
                * apply H2'.
              + apply H2.
            - apply H3. }
        replace (length p) with (S (length G)).
        2:{ replace (length G) with (length (((r, complexity_A (S i)) :: T) :: H)).
            - rewrite Heq in Heqp.
              inversion Heqp.
              reflexivity.
            - rewrite <- Heq.
              clear - Heqx.
              unfold p_hseq_put_non_basic_fst.
              simpl.
              change (S (length (p_hseq_without_max_complexity G))) with (length (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
              apply Permutation_Type_length.
              symmetry; apply p_hseq_put_max_complexity_fst.
              intros H; subst; inversion Heqx. }
        apply tetra_2_le_mono.
        lia.
Qed.

Lemma decidability_non_elementary :
  forall i,
    tetra_2 i 0 <= nb_exists_FOL_R_formula (HMR_dec_formula (((FOL_R_cst 1, complexity_A (S i)) :: nil) :: nil)).
Proof.
  intro i.
  change 0 with (0 + 0) at 1.
  apply HMR_dec_formula_aux_complexity with 1.
  - intros H; inversion H.
  - split with (nil, (((FOL_R_cst 1, complexity_A (S i)) :: nil) :: nil)).
    repeat split.
    + Permutation_Type_solve.
    + apply Forall_inf_nil.
    + apply Forall_inf_cons ; [ | apply Forall_inf_nil].
      split with (nil, (FOL_R_cst 1 :: nil)).
      repeat split.
      simpl.
      reflexivity.
  - unfold pow2; simpl; lia.
Qed.

Require Import Rpos.
Require Import riesz_logic_List_more.
Require Import FOL_R.
Require Import lt_nat_tuples.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import RL.hr.p_hseq.
Require Import RL.hr.hr.
Require Import RL.hr.lambda_prop_tools.
Require Import RL.hr.invertibility.
Require Import RL.hr.can_elim.
Require Import RL.hr.M_elim.
Require Import RL.hr.decidability.

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
Fixpoint nb_operator A :=
  match A with
  | A +S B => 1 + nb_operator A + nb_operator B
  | A /\S B => 1 + nb_operator A + nb_operator B
  | A \/S B => 1 + nb_operator A + nb_operator B
  | r *S A => 1 + nb_operator A
  | _ => 0
  end.

Definition nb_op_p_seq (T : p_sequent) := fold_right (fun x y => nb_operator (snd x) + y) 0 T.

Definition nb_op_p_hseq (G : p_hypersequent) := fold_right (fun x y => nb_op_p_seq x + y) 0 G.

Definition nbVar_p_hseq G := 1 + max_var_p_hseq G.

Definition nbVar_hseq G := 1 + max_var_hseq G.

Fixpoint nbMax_term A :=
  match A with
  | HR_var _ => 0
  | HR_covar _ => 0
  | HR_zero => 0
  | A +S B => nbMax_term A + nbMax_term B
  | A /\S B => nbMax_term A + nbMax_term B
  | A \/S B => 1 + nbMax_term A + nbMax_term B
  | _ *S A => nbMax_term A
  end.

Definition nbMax_p_seq (T : p_sequent) := fold_right (fun x y => nbMax_term (snd x) + y) 0 T.

Definition nbMax_p_hseq (G : p_hypersequent) := fold_right (fun x y => pow2 (nbMax_p_seq x) + y) 0 G.

Definition nbMax_seq (T : sequent) := fold_right (fun x y => nbMax_term (snd x) + y) 0 T.

Definition nbMax_hseq (G : hypersequent) := fold_right (fun x y => pow2 (nbMax_seq x) + y) 0 G.

Lemma nbMax_term_atomic : forall A,
    is_atom A ->
    nbMax_term A = 0.
Proof.
  induction A; intros Hat; inversion Hat; subst; simpl in *; lia.
Qed.

Lemma nbMax_p_seq_atomic : forall T,
    p_seq_is_atomic T ->
    nbMax_p_seq T = 0.
Proof.
  induction T; try destruct a as [a A]; intros Hat; inversion Hat; subst; simpl in *; try rewrite nbMax_term_atomic; auto.
Qed.

Lemma nbMax_p_hseq_atomic : forall G,
    p_hseq_is_atomic G ->
    nbMax_p_hseq G = length G.
Proof.
  induction G; intros Hat; inversion Hat; subst; simpl in *; try rewrite nbMax_p_seq_atomic; auto; (specialize (IHG X0)); try lia.
Qed.

Fixpoint nbMin_term A :=
  match A with
  | HR_var _ => 0
  | HR_covar _ => 0
  | HR_zero => 0
  | A +S B => nbMin_term A + nbMin_term B
  | A /\S B => 1 + nbMin_term A + nbMin_term B
  | A \/S B => nbMin_term A + nbMin_term B
  | _ *S A => nbMin_term A
  end.

Definition nbMin_p_seq (T : p_sequent) := fold_right (fun x y => nbMin_term (snd x) + y) 0 T.

Definition nbMin_p_hseq (G : p_hypersequent) := fold_right (fun x y => pow2 (nbMax_p_seq x) * nbMin_p_seq x + y) 0 G.

Definition nbMin_seq (T : sequent) := fold_right (fun x y => nbMin_term (snd x) + y) 0 T.

Definition nbMin_hseq (G : hypersequent) := fold_right (fun x y => pow2 (nbMax_seq x) * nbMin_seq x + y) 0 G.

Lemma nbMin_term_atomic : forall A,
    is_atom A ->
    nbMin_term A = 0.
Proof.
  induction A; intros Hat; inversion Hat; subst; simpl in *; lia.
Qed.

Lemma nbMin_p_seq_atomic : forall T,
    p_seq_is_atomic T ->
    nbMin_p_seq T = 0.
Proof.
  induction T; try destruct a as [a A]; intros Hat; inversion Hat; subst; simpl in *; try rewrite nbMin_term_atomic; auto.
Qed.

Lemma nbMin_p_hseq_atomic : forall G,
    p_hseq_is_atomic G ->
    nbMin_p_hseq G = 0.
Proof.
  induction G; intros Hat; inversion Hat; subst; simpl in *; try rewrite nbMin_p_seq_atomic; auto; (specialize (IHG X0)); try lia.
Qed.

Definition nb_p_seq (G : p_hypersequent) := length G.

Definition nb_seq (G : hypersequent) := length G.

Definition degree_p_seq (T : p_sequent) := fold_right (fun x y => max (degree_FOL_R_term (fst x)) y) 0 T.

Definition degree_p_hseq (G : p_hypersequent) := fold_right (fun x y => max (degree_p_seq x) y) 0 G.

(** Size of the formula return by the decidability algorithm *)
Lemma degree_FOL_R_all_zero : forall k v,
    degree_FOL_R_formula (FOL_R_all_zero k v) <= 1.
Proof.
  intros k; induction v; [simpl; lia | ].
  simpl.
  fold (max 1 (degree_FOL_R_formula (FOL_R_all_zero k v))).
  lia.
Qed.

Lemma nb_pol_FOL_R_all_zero : forall k v,
    nb_pol_FOL_R_formula (FOL_R_all_zero k v) = length v.
Proof.
  intros k; induction v; simpl; lia.
Qed.

Lemma nb_exists_FOL_R_all_zero : forall k v,
    nb_exists_FOL_R_formula (FOL_R_all_zero k v) = 0.
Proof.
  intros k; induction v; simpl; lia.
Qed.

Lemma degree_FOL_R_all_gtz : forall k v,
    degree_FOL_R_formula (FOL_R_all_gtz k v) <= 1.
Proof.
  intros k; induction v; [simpl; lia | ].
  simpl.
  fold (max 1 (degree_FOL_R_formula (FOL_R_all_gtz k v))).
  lia.
Qed.

Lemma nb_pol_FOL_R_all_gtz : forall k v,
    nb_pol_FOL_R_formula (FOL_R_all_gtz k v) = 2 * length v.
Proof.
  intros k; induction v; simpl; lia.
Qed.

Lemma nb_exists_FOL_R_all_gtz : forall k v,
    nb_exists_FOL_R_formula (FOL_R_all_gtz k v) = 0.
Proof.
  intros k; induction v; simpl; lia.
Qed.

Lemma degree_sum_weight_p_seq_var : forall k T,
    degree_FOL_R_term (sum_weight_p_seq_var k T) <= degree_p_seq T.
Proof.
  intros k; induction T; simpl; try lia.
  destruct a as [r A].
  destruct A; try lia.
  case (k =? n); simpl; lia.
Qed.

Lemma degree_p_sum_weight_var_with_coeff : forall k i G L,
    Forall_inf (fun x => degree_FOL_R_term x <= i) L ->
    (degree_FOL_R_term (p_sum_weight_var_with_coeff k G L)) <= degree_p_hseq G + i.
Proof.
  intros k i.
  induction G; intros L Hall; destruct L; simpl; try lia.
  inversion Hall; subst.
  specialize (IHG L X).
  assert (H := degree_sum_weight_p_seq_var k a).
  lia.
Qed.

Lemma degree_sum_weight_p_seq_covar : forall k T,
    degree_FOL_R_term (sum_weight_p_seq_covar k T) <= degree_p_seq T.
Proof.
  intros k; induction T; simpl; try lia.
  destruct a as [r A].
  destruct A; try lia.
  case (k =? n); simpl; lia.
Qed.

Lemma degree_p_sum_weight_covar_with_coeff : forall k i G L,
    Forall_inf (fun x => degree_FOL_R_term x <= i) L ->
    (degree_FOL_R_term (p_sum_weight_covar_with_coeff k G L)) <= degree_p_hseq G + i.
Proof.
  intros k i.
  induction G; intros L Hall; destruct L; simpl; try lia.
  inversion Hall; subst.
  specialize (IHG L X).
  assert (H := degree_sum_weight_p_seq_covar k a).
  lia.
Qed.  

Lemma degree_FOL_R_all_atoms_eq : forall G k,
    degree_FOL_R_formula (FOL_R_all_atoms_eq G k) <= 1 + degree_p_hseq G.
Proof.
  intros G.
  assert (Forall_inf (fun x => degree_FOL_R_term x <= 1) (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) as Hall.
  { remember (seq (S (max_var_weight_p_hseq G)) (length G)).
    clear.
    induction l; simpl; [apply Forall_inf_nil | apply Forall_inf_cons]; auto. }
  induction k; simpl.
  - assert (Hvar := degree_p_sum_weight_var_with_coeff 0 1 G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))) Hall).
    assert (Hcovar := degree_p_sum_weight_covar_with_coeff 0 1 G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))) Hall).
    lia.
  - assert (Hvar := degree_p_sum_weight_var_with_coeff (S k) 1 G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))) Hall).
    assert (Hcovar := degree_p_sum_weight_covar_with_coeff (S k) 1 G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))) Hall).
    lia.
Qed.

Lemma nb_pol_FOL_R_all_atoms_eq : forall G k,
    nb_pol_FOL_R_formula (FOL_R_all_atoms_eq G k) = 1 + k.
Proof.
  intros G; induction k; simpl; try lia.
Qed.

Lemma nb_exists_FOL_R_all_atoms_eq : forall G k,
    nb_exists_FOL_R_formula (FOL_R_all_atoms_eq G k) = 0.
Proof.
  intros G; induction k; simpl; lia.
Qed.  

Lemma degree_FOL_R_phi : forall G v,
    degree_FOL_R_formula (FOL_R_phi G v) <= 1 + degree_p_hseq G.
Proof.
  intros G v.
  simpl.
  assert (H1 := degree_FOL_R_all_zero (S (max_var_weight_p_hseq G)) (complementary v (length G))).
  assert (H2 := degree_FOL_R_all_gtz (S (max_var_weight_p_hseq G)) v).
  assert (H3 := degree_FOL_R_all_atoms_eq G (max_var_p_hseq G)).
  lia.
Qed.

Lemma nb_pol_FOL_R_phi : forall G v,
    Forall_inf (fun x => x < length G) v ->
    NoDup_inf v ->
    nb_pol_FOL_R_formula (FOL_R_phi G v) <= 2 * (length G) + nbVar_p_hseq G.
Proof.
  intros G v Hall Hndup; simpl.
  assert (H1 := nb_pol_FOL_R_all_zero (S (max_var_weight_p_hseq G)) (complementary v (length G))).
  assert (H2 := nb_pol_FOL_R_all_gtz (S (max_var_weight_p_hseq G)) v).
  assert (H3 := nb_pol_FOL_R_all_atoms_eq G (max_var_p_hseq G)).
  unfold nbVar_p_hseq.
  rewrite complementary_length_lt_no_dup in H1; auto.
  rewrite H1, H2, H3.
  assert (H4 := NoDup_inf_lt_length v (length G) Hall Hndup).  
  lia.
Qed.

Lemma nb_exists_FOL_R_phi : forall G v,
    nb_exists_FOL_R_formula (FOL_R_phi G v) = 0.
Proof.
  intros G v; simpl.
  assert (H1 := nb_exists_FOL_R_all_zero (S (max_var_weight_p_hseq G)) (complementary v (length G))).
  assert (H2 := nb_exists_FOL_R_all_gtz (S (max_var_weight_p_hseq G)) v).
  assert (H3 := nb_exists_FOL_R_all_atoms_eq G (max_var_p_hseq G)).
  lia.
Qed.

Lemma degree_FOL_R_exists_vec : forall f v,
    degree_FOL_R_formula (exists_vec v f) = degree_FOL_R_formula f.
Proof.
  intros f; induction v; simpl; auto.
Qed.


Lemma nb_pol_FOL_R_exists_vec : forall f v,
    nb_pol_FOL_R_formula (exists_vec v f) = nb_pol_FOL_R_formula f.
Proof.
  intros f; induction v; simpl; auto.
Qed.

Lemma nb_exists_FOL_R_exists_vec : forall f v,
    nb_exists_FOL_R_formula (exists_vec v f) = length v + nb_exists_FOL_R_formula f.
Proof.
  intros f; induction v; simpl; auto.
Qed.

Lemma degree_FOL_R_exists_phi : forall G v,
    degree_FOL_R_formula (FOL_R_exists_phi G v) <= 1 + degree_p_hseq G.
Proof.
  intros G v.
  unfold FOL_R_exists_phi.
  rewrite degree_FOL_R_exists_vec.
  apply degree_FOL_R_phi.
Qed.

Lemma nb_pol_FOL_R_exists_phi : forall G v,
    Forall_inf (fun x => x < length G) v ->
    NoDup_inf v ->
    nb_pol_FOL_R_formula (FOL_R_exists_phi G v) <= 2 * (length G) + nbVar_p_hseq G.
Proof.
  intros G v.
  unfold FOL_R_exists_phi.
  rewrite nb_pol_FOL_R_exists_vec.
  apply nb_pol_FOL_R_phi.
Qed.

Lemma nb_exists_FOL_R_exists_phi : forall G v,
    nb_exists_FOL_R_formula (FOL_R_exists_phi G v) = nb_p_seq G.
Proof.
  intros G v.
  unfold FOL_R_exists_phi.
  rewrite nb_exists_FOL_R_exists_vec.
  rewrite nb_exists_FOL_R_phi.
  rewrite seq_length.
  unfold nb_p_seq; lia.
Qed.

Lemma degree_FOL_R_atomic_case_aux : forall G V,
    degree_FOL_R_formula (FOL_R_atomic_case_aux G V) <= 1 + degree_p_hseq G.
Proof.
  intros G V.
  induction V; simpl; try lia.
  assert (H := degree_FOL_R_exists_phi G a).
  lia.
Qed.

Lemma nb_pol_FOL_R_atomic_case_aux : forall G V,
    Forall_inf (fun v => Forall_inf (fun x => x < length G) v) V ->
    Forall_inf (fun v => NoDup_inf v) V ->
    nb_pol_FOL_R_formula (FOL_R_atomic_case_aux G V) <= (length V) * (2 * (length G) + nbVar_p_hseq G).
Proof.
  intros G V.
  induction V; simpl; try lia.
  intros HallV1 HallV2; inversion HallV1; inversion HallV2; subst.
  assert (H := nb_pol_FOL_R_exists_phi G a X X1).
  specialize (IHV X0 X2).
  lia.  
Qed.

Lemma nb_exists_FOL_R_atomic_case_aux : forall G V,
    nb_exists_FOL_R_formula (FOL_R_atomic_case_aux G V) = length V * nb_p_seq G.
Proof.
  intros G V.
  induction V; simpl; try lia.
  assert (H := nb_exists_FOL_R_exists_phi G a).
  lia.
Qed.

Lemma degree_FOL_R_atomic_case : forall G,
    degree_FOL_R_formula (FOL_R_atomic_case G) <= 1 + degree_p_hseq G.
Proof.
  intros G.
  unfold FOL_R_atomic_case.
  apply (degree_FOL_R_atomic_case_aux G (map (rev (A:=nat)) (make_subsets (length G)))).
Qed.

Lemma nb_pol_FOL_R_atomic_case : forall G,
    nb_pol_FOL_R_formula (FOL_R_atomic_case G) <= (2^(nb_p_seq G)) * (2 * (length G) + nbVar_p_hseq G).
Proof.
  intros G.
  unfold FOL_R_atomic_case.
  assert (H := nb_pol_FOL_R_atomic_case_aux G (map (rev (A:=nat)) (make_subsets (length G)))).
  unfold nb_p_seq.
  rewrite map_length in H; rewrite make_subsets_length in H.
  transitivity (pred (2 ^ length G) * (2 * length G + nbVar_p_hseq G)); try lia.
  apply H.
  - apply forall_Forall_inf.
    intros v Hin.
    apply in_inf_map_inv in Hin as [vx Heq Hin].
    apply cond_is_in_make_subsets_inv in Hin as [[Hnil H1] H2].
    rewrite <- Heq.
    apply Forall_inf_rev.
    apply nth_Forall_inf; intros.
    rewrite nth_indep with _ _ _ _ 0; auto.
  - apply forall_Forall_inf.
    intros v Hin.
    apply in_inf_map_inv in Hin as [vx Heq' Hin].
    apply cond_is_in_make_subsets_inv in Hin as [[Hnil H1] H2].
    rewrite <- Heq'.
    apply NoDup_inf_rev.
    apply NoDup_inf_nth.
    intros a i j Hlen1 Hlen2 Hneq Heq.
    rewrite nth_indep with _ _ _ _ 0 in Heq; auto.
    rewrite nth_indep with _ _ j _ 0 in Heq; auto.
    case_eq (i <? j); intros H';
      (apply Nat.ltb_lt in H' + apply Nat.ltb_nlt in H').
    + specialize (H2 i j Hlen2 H').
      lia.
    + assert (j < i) by lia.
      specialize (H2 j i Hlen1 H0).
      lia.    
Qed.

Lemma nb_exists_FOL_R_atomic_case : forall G,
    nb_exists_FOL_R_formula (FOL_R_atomic_case G) = pred (2^(nb_p_seq G)) * nb_p_seq G.
Proof.
  intros G.
  unfold FOL_R_atomic_case.
  rewrite <- make_subsets_length.
  rewrite <- map_length with _ _ (@rev nat) _.
  unfold nb_p_seq.
  apply nb_exists_FOL_R_atomic_case_aux.
Qed.

Lemma degree_p_hseq_perm : forall G1 G2,
    Permutation_Type G1 G2 ->
    degree_p_hseq G1 = degree_p_hseq G2.
Proof.
  intros G1 G2 Hperm.
  induction Hperm; simpl; try lia.
Qed.

Lemma degree_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    degree_p_seq T1 = degree_p_seq T2.
Proof.
  intros T1 T2 Hperm.
  induction Hperm; simpl; try lia.
Qed.

Lemma p_hseq_put_non_atomic_fst_degree : forall G,
    fst (HR_complexity_p_hseq G) <> 0 ->
    degree_p_hseq (p_hseq_put_non_atomic_fst G) = degree_p_hseq G.
Proof.
  intros G Hn0.
  rewrite (degree_p_hseq_perm G (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G)).
  2:{ apply p_hseq_put_max_complexity_fst.
      destruct G; try contradiction.
      intros H; inversion H. }
  simpl.
  rewrite (degree_p_seq_perm (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G))).
  2:{ apply p_seq_put_non_atomic_fst.
      intros H.
      apply p_seq_is_atomic_complexity_0 in H.
      rewrite p_hseq_p_seq_max_complexity_correct in H.
      contradiction. }
  simpl; lia.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inl_degree :
  forall G G1,
    apply_logical_rule_on_p_hypersequent G = inl G1 ->
    degree_p_hseq G1 <= degree_p_hseq G.
Proof.
  intros G G1 Heq.
  destruct G ; [inversion Heq; reflexivity| ].
  destruct l; [inversion Heq; reflexivity | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst;
    simpl in *; try lia.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_l_degree :
  forall G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1, G2) ->
    degree_p_hseq G = degree_p_hseq G1.
Proof.
  intros G G1 G2 Heq.
  destruct G ; [inversion Heq | ].
  destruct l; [inversion Heq | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
Qed.

Lemma apply_logical_rule_on_p_hypersequent_inr_r_degree :
  forall G G1 G2,
    apply_logical_rule_on_p_hypersequent G = inr (G1, G2) ->
    degree_p_hseq G = degree_p_hseq G2.
Proof.
  intros G G1 G2 Heq.
  destruct G ; [inversion Heq | ].
  destruct l; [inversion Heq | ].
  destruct p as [a A].
  destruct A; inversion Heq; subst; auto.
Qed.

Lemma max_var_p_hseq_perm : forall G H,
    Permutation_Type G H ->
    max_var_p_hseq G = max_var_p_hseq H.
Proof.
  intros G H Hperm.
  induction Hperm; simpl; lia.
Qed.

Lemma max_var_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    max_var_p_seq T1 = max_var_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; simpl; try destruct x; try destruct y; try lia.
Qed.

Lemma nbVar_p_hseq_put_non_atomic_fst : forall G,
    fst (HR_complexity_p_hseq G) <> 0 ->
    nbVar_p_hseq (p_hseq_put_non_atomic_fst G) = nbVar_p_hseq G.
Proof.
  intros G Heq.
  unfold p_hseq_put_non_atomic_fst.
  unfold nbVar_p_hseq.
  unfold max_var_p_hseq; fold max_var_p_hseq.
  rewrite max_var_p_seq_perm with _ (p_hseq_p_seq_max_complexity G).
  2:{ symmetry; apply p_seq_put_non_atomic_fst.
      intros Hin.
      apply p_seq_is_atomic_complexity_0 in Hin.
      rewrite p_hseq_p_seq_max_complexity_correct in Hin; contradiction. }
  rewrite max_var_p_hseq_perm with G (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G); try reflexivity.
  apply p_hseq_put_max_complexity_fst.
  intros Hnil; destruct G; inversion Hnil; contradiction.
Qed.

Lemma nb_p_seq_p_hseq_put_non_atomic_fst : forall G,
    fst (HR_complexity_p_hseq G) <> 0 ->
    nb_p_seq (p_hseq_put_non_atomic_fst G) = nb_p_seq G.
Proof.
  intros G Heq.
  unfold p_hseq_put_non_atomic_fst; unfold nb_p_seq.
  rewrite Permutation_Type_length with _ G (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G); try reflexivity.
  apply p_hseq_put_max_complexity_fst.
  intros Hnil; destruct G; inversion Hnil; contradiction.
Qed.

Lemma nbMin_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    nbMin_p_seq T1 = nbMin_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; simpl; lia.
Qed.

Lemma nbMax_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    nbMax_p_seq T1 = nbMax_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; simpl; lia.
Qed.

Lemma nbMin_p_hseq_perm : forall G H,
    Permutation_Type G H ->
    nbMin_p_hseq G = nbMin_p_hseq H.
Proof.
  intros G H Hperm; induction Hperm; simpl; try lia.
Qed.

Lemma nbMax_p_hseq_perm : forall G H,
    Permutation_Type G H ->
    nbMax_p_hseq G = nbMax_p_hseq H.
Proof.
  intros G H Hperm; induction Hperm; simpl; try lia.
Qed.

Lemma nbMin_p_hseq_put_non_atomic_fst : forall G,
    fst (HR_complexity_p_hseq G) <> 0 ->
    nbMin_p_hseq (p_hseq_put_non_atomic_fst G) = nbMin_p_hseq G.
Proof.
  intros G Heq.
  rewrite nbMin_p_hseq_perm with G (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G).
  2:{ apply p_hseq_put_max_complexity_fst.
      intros Hnnil; destruct G; inversion Hnnil; contradiction. }
  simpl.
  rewrite nbMin_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_atomic_fst.
      intros Hin; apply p_seq_is_atomic_complexity_0 in Hin.
      rewrite p_hseq_p_seq_max_complexity_correct in Hin; contradiction. }
  rewrite nbMax_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_atomic_fst.
      intros Hin; apply p_seq_is_atomic_complexity_0 in Hin.
      rewrite p_hseq_p_seq_max_complexity_correct in Hin; contradiction. }
  simpl; try lia.
Qed.

Lemma nbMax_p_hseq_put_non_atomic_fst : forall G,
    fst (HR_complexity_p_hseq G) <> 0 ->
    nbMax_p_hseq (p_hseq_put_non_atomic_fst G) = nbMax_p_hseq G.
Proof.
  intros G Heq.
  rewrite nbMax_p_hseq_perm with G (p_hseq_p_seq_max_complexity G :: p_hseq_without_max_complexity G).
  2:{ apply p_hseq_put_max_complexity_fst.
      intros Hnnil; destruct G; inversion Hnnil; contradiction. }
  simpl.
  rewrite nbMax_p_seq_perm with (p_hseq_p_seq_max_complexity G) (p_seq_fst_non_atomic_term (p_hseq_p_seq_max_complexity G) :: p_seq_without_fst_non_atomic_term (p_hseq_p_seq_max_complexity G)).
  2:{ apply p_seq_put_non_atomic_fst.
      intros Hin; apply p_seq_is_atomic_complexity_0 in Hin.
      rewrite p_hseq_p_seq_max_complexity_correct in Hin; contradiction. }
  simpl; try lia.
Qed.

Fixpoint degree_HR_dec_formula_aux G x Heqx p Heqp acc :
    degree_FOL_R_formula (HR_dec_formula_aux G x Heqx p Heqp acc)  <= 1 + degree_p_hseq G.
Proof.
  destruct acc as [acc].
  destruct x.
  - simpl.
    apply degree_FOL_R_atomic_case.
  - destruct p.
    + transitivity (1 + degree_p_hseq p).
      2:{ assert (H := apply_logical_rule_on_p_hypersequent_inl_degree (p_hseq_put_non_atomic_fst G) p Heqp).
      rewrite p_hseq_put_non_atomic_fst_degree in H; lia. }
      refine (degree_HR_dec_formula_aux p _ eq_refl _ eq_refl
                                            (acc _
                                                 (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp))).
    + destruct p as [p1 p2].
      unfold HR_dec_formula_aux; fold HR_dec_formula_aux.
      rewrite degree_FOL_R_and.
      apply Nat.max_lub.
      * transitivity (1 + degree_p_hseq p1).
        2:{ assert (H := apply_logical_rule_on_p_hypersequent_inr_l_degree (p_hseq_put_non_atomic_fst G) p1 p2 Heqp).
            rewrite p_hseq_put_non_atomic_fst_degree in H; lia. }
        refine (degree_HR_dec_formula_aux p1 _ eq_refl _ eq_refl
                                          (acc _
                                               (apply_logical_rule_on_p_hypersequent_correct_inr_l G p1 p2 x Heqx Heqp))).
      * transitivity (1 + degree_p_hseq p2).
        2:{ assert (H := apply_logical_rule_on_p_hypersequent_inr_r_degree (p_hseq_put_non_atomic_fst G) p1 p2 Heqp).
            rewrite p_hseq_put_non_atomic_fst_degree in H; lia. }
        refine (degree_HR_dec_formula_aux p2 _ eq_refl _ eq_refl
                                          (acc _
                                               (apply_logical_rule_on_p_hypersequent_correct_inr_r G p1 p2 x Heqx Heqp))).
Qed.

Fixpoint nb_pol_HR_dec_formula_aux G x Heqx p Heqp acc :
    nb_pol_FOL_R_formula (HR_dec_formula_aux G x Heqx p Heqp acc)  <= pow2 (nbMin_p_hseq G + nbMax_p_hseq G)*(2 * (nbMax_p_hseq G) + nbVar_p_hseq G). 
Proof.
  destruct acc as [acc].
  destruct x.
  - simpl.
    assert (H := nb_pol_FOL_R_atomic_case G).
    rewrite nbMax_p_hseq_atomic.
    2:{ apply p_hseq_is_atomic_complexity_0_inv; auto. }
    rewrite nbMin_p_hseq_atomic.
    2:{ apply p_hseq_is_atomic_complexity_0_inv; auto. }
    unfold nb_p_seq in *.
    unfold pow2.
    transitivity (2 ^ length G * (2 * length G + nbVar_p_hseq G)); try lia.
    apply Nat.mul_le_mono; try lia.
    apply Nat.pow_le_mono_r; lia.
  - destruct p.
    + specialize (nb_pol_HR_dec_formula_aux p _ eq_refl _ eq_refl
                                            (acc _
                                                 (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp))) as Hind.
      transitivity (pow2 (nbMin_p_hseq p + nbMax_p_hseq p) *  (2 * nbMax_p_hseq p + nbVar_p_hseq p)); try assumption.
      rewrite <- (nbMin_p_hseq_put_non_atomic_fst G) by lia.
      rewrite <- (nbMax_p_hseq_put_non_atomic_fst G) by lia.
      rewrite <- (nbVar_p_hseq_put_non_atomic_fst G) by lia.
      remember (p_hseq_put_non_atomic_fst G) as H.
      clear - Heqp.
      destruct H; try now inversion Heqp.
      destruct l; try now inversion Heqp.
      destruct p0 as [a A].
      destruct A; inversion Heqp; subst; unfold nbVar_p_hseq; simpl; try lia.
      * repeat ((apply Nat.mul_le_mono + apply plus_le_compat + apply pow2_le_mono + apply le_n_S); try lia).
      * remember (nbMax_term A2); remember (nbMax_term A1); remember (nbMax_p_seq l); remember (nbMin_term A1); remember (nbMin_term A2); remember (nbMin_p_seq l); remember (nbMin_p_hseq H); remember (nbMax_p_hseq H); remember (max_var_term A1); remember (max_var_term A2); remember (max_var_p_seq l); remember (max_var_p_hseq H).
        unfold pow2 in *.
        clear.
        apply Nat.mul_le_mono.
        -- apply pow2_le_mono.
           clear.
           transitivity ((2 ^ (n + n1) * (n3 + n4) + (2 ^ (n0 + n1) * (n2 + n4)) + (2 ^ (n + n1) + (2 ^ (n0 + n1)))) + n5 + n6); try lia.
           transitivity ((2 ^ S (n0 + n + n1) * (n2 + n3 + n4) + 2 ^ S (n0 + n + n1)) + n5 + n6); try lia.
           apply Nat.add_le_mono; try lia.
           apply Nat.add_le_mono; try lia.
           transitivity ((2 ^ (n + n1) + 2 ^ (n0 + n1)) * (n2 + n3 + n4) + (2 ^ (n + n1) + 2 ^ (n0 + n1))); try lia.
           apply Nat.add_le_mono.
           ++ apply Nat.mul_le_mono; try lia.
              rewrite pow2_S.
              simpl; unfold pow2.
              rewrite Nat.add_0_r.
              apply Nat.add_le_mono;
                apply pow2_le_mono; lia.
           ++ rewrite pow2_S.
              simpl; unfold pow2.
              rewrite Nat.add_0_r.
              apply Nat.add_le_mono;
                apply pow2_le_mono; lia.
        -- apply Nat.add_le_mono; try lia.
           rewrite pow2_S.
           transitivity ((2 ^ (n + n1) + 2 ^ (n0 + n1) + 2 ^ (n + n1) + 2 ^ (n0 + n1)) + n6 + n6); try lia.
           transitivity ((2 * pow2 (n0 + n + n1) + 2 * pow2 (n0 + n + n1)) + n6 + n6); try lia.
           simpl.
           rewrite ? Nat.add_0_r; rewrite ? Nat.add_assoc.
           repeat (apply Nat.add_le_mono); try apply pow2_le_mono; lia.
    + destruct p as [p1 p2].
      specialize (nb_pol_HR_dec_formula_aux p1 _ eq_refl _ eq_refl
                                            (acc _
                                                 (apply_logical_rule_on_p_hypersequent_correct_inr_l G p1 p2 x Heqx Heqp))) as Hind1.
      specialize (nb_pol_HR_dec_formula_aux p2 _ eq_refl _ eq_refl
                                            (acc _
                                                 (apply_logical_rule_on_p_hypersequent_correct_inr_r G p1 p2 x Heqx Heqp))) as Hind2.
      transitivity (pow2 (nbMin_p_hseq p1 + nbMax_p_hseq p1) * (2 * nbMax_p_hseq p1 + nbVar_p_hseq p1) + pow2 (nbMin_p_hseq p2 + nbMax_p_hseq p2) * (2 * nbMax_p_hseq p2 + nbVar_p_hseq p2)).
      { simpl in *; lia. }
      rewrite <- (nbMin_p_hseq_put_non_atomic_fst G) by lia.
      rewrite <- (nbMax_p_hseq_put_non_atomic_fst G) by lia.
      rewrite <- (nbVar_p_hseq_put_non_atomic_fst G) by lia.
      remember (p_hseq_put_non_atomic_fst G) as H.
      clear - Heqp.
      destruct H; try now inversion Heqp.
      destruct l; try now inversion Heqp.
      destruct p as [a A].
      destruct A; inversion Heqp; subst; unfold nbVar_p_hseq; simpl; try lia.
      unfold HR_dec_formula_aux; fold HR_dec_formula_aux.
      remember (nbMax_term A2); remember (nbMax_term A1); remember (nbMax_p_seq l); remember (nbMin_term A1); remember (nbMin_term A2); remember (nbMin_p_seq l); remember (nbMin_p_hseq H); remember (nbMax_p_hseq H); remember (max_var_term A1); remember (max_var_term A2); remember (max_var_p_seq l); remember (max_var_p_hseq H).
      transitivity
        (pow2 (pow2 (n0 + n1) * (n2 + n4) + n5 + (pow2 (n0 + n1) + n6)) * (pow2 (n0 + n + n1) + n6 + (pow2 (n0 + n + n1) + n6) + S (Nat.max (Nat.max (max n7 n8) n9) n10))
         + (pow2 (pow2 (n + n1) * (n3 + n4) + n5 + (pow2 (n + n1) + n6)) * (pow2 (n0 + n + n1) + n6 + (pow2 (n0 + n + n1) + n6) + S (Nat.max (Nat.max (max n7 n8) n9) n10)))); try lia.
      { rewrite ? Nat.add_0_r.
        repeat ((apply Nat.mul_le_mono + apply plus_le_compat + apply pow2_le_mono + apply le_n_S); try lia). }
      transitivity ((pow2 (pow2 (n0 + n1) * (n2 + n4) + n5 + (pow2 (n0 + n1) + n6)) + pow2 (pow2 (n + n1) * (n3 + n4) + n5 + (pow2 (n + n1) + n6))) * (pow2 (n0 + n + n1) + n6 + (pow2 (n0 + n + n1) + n6) + S (Nat.max (Nat.max (max n7 n8) n9) n10))); try lia.
      apply Nat.mul_le_mono; try lia.
      transitivity (pow2 (S (pow2 (n0 + n + n1) * (n2 + n3 + n4) + n5 + (pow2 (n0 + n + n1) + n6)))).
      2:{ apply pow2_le_mono.
          rewrite <- ? Nat.add_succ_l.
          apply Nat.add_le_mono; try lia.
          apply Nat.add_le_mono; try lia.
          simpl.
          rewrite <- mult_n_Sm.
          assert (1 <= pow2 (n0 + n + n1)).
          { unfold pow2.
            remember (n0 + n + n1); clear.
            induction n11; simpl; lia. }
          lia. }
      rewrite pow2_S; simpl.
      rewrite Nat.add_0_r.
      apply Nat.add_le_mono;
        apply pow2_le_mono; apply Nat.add_le_mono; apply Nat.add_le_mono; try lia;
          try apply Nat.mul_le_mono; try apply pow2_le_mono; lia.
Qed.

Fixpoint nb_exists_HR_dec_formula_aux G x Heqx p Heqp acc :
    nb_exists_FOL_R_formula (HR_dec_formula_aux G x Heqx p Heqp acc)  <= pow2 (nbMin_p_hseq G + nbMax_p_hseq G)*(nbMax_p_hseq G). 
Proof.
  destruct acc as [acc].
  destruct x.
  - simpl.
    assert (H := nb_exists_FOL_R_atomic_case G).
    rewrite nbMax_p_hseq_atomic.
    2:{ apply p_hseq_is_atomic_complexity_0_inv; auto. }
    rewrite nbMin_p_hseq_atomic.
    2:{ apply p_hseq_is_atomic_complexity_0_inv; auto. }
    unfold nb_p_seq in *.
    rewrite H.
    unfold pow2.
    simpl.
    lia.
  - destruct p.
    + specialize (nb_exists_HR_dec_formula_aux p _ eq_refl _ eq_refl
                                               (acc _
                                                    (apply_logical_rule_on_p_hypersequent_correct_inl G p x Heqx Heqp))) as Hind.
      transitivity (pow2 (nbMin_p_hseq p + nbMax_p_hseq p) *  (nbMax_p_hseq p)); try assumption.
      rewrite <- (nbMin_p_hseq_put_non_atomic_fst G) by lia.
      rewrite <- (nbMax_p_hseq_put_non_atomic_fst G) by lia.
      remember (p_hseq_put_non_atomic_fst G) as H.
      clear - Heqp.
      destruct H; try now inversion Heqp.
      destruct l; try now inversion Heqp.
      destruct p0 as [a A].
      destruct A; inversion Heqp; subst; unfold nbVar_p_hseq; simpl; try lia.
      * repeat ((apply Nat.mul_le_mono + apply plus_le_compat + apply pow2_le_mono + apply le_n_S); try lia).
      * remember (nbMax_term A2); remember (nbMax_term A1); remember (nbMax_p_seq l); remember (nbMin_term A1); remember (nbMin_term A2); remember (nbMin_p_seq l); remember (nbMin_p_hseq H); remember (nbMax_p_hseq H); remember (max_var_term A1); remember (max_var_term A2); remember (max_var_p_seq l); remember (max_var_p_hseq H).
        unfold pow2 in *.
        clear.
        apply Nat.mul_le_mono.
        -- apply pow2_le_mono.
           transitivity ((2 ^ (n + n1) * (n3 + n4) + (2 ^ (n0 + n1) * (n2 + n4)) + (2 ^ (n + n1) + (2 ^ (n0 + n1)))) + n5 + n6); try lia.
           transitivity ((2 ^ S (n0 + n + n1) * (n2 + n3 + n4) + 2 ^ S (n0 + n + n1)) + n5 + n6); try lia.
           apply Nat.add_le_mono; try lia.
           apply Nat.add_le_mono; try lia.
           transitivity ((2 ^ (n + n1) + 2 ^ (n0 + n1)) * (n2 + n3 + n4) + (2 ^ (n + n1) + 2 ^ (n0 + n1))); try lia.
           apply Nat.add_le_mono.
           ++ apply Nat.mul_le_mono; try lia.
              rewrite pow2_S.
              simpl; unfold pow2.
              rewrite Nat.add_0_r.
              apply Nat.add_le_mono;
                apply pow2_le_mono; lia.
           ++ rewrite pow2_S.
              simpl; unfold pow2.
              rewrite Nat.add_0_r.
              apply Nat.add_le_mono;
                apply pow2_le_mono; lia.
        -- rewrite Nat.add_assoc.
           apply Nat.add_le_mono; try lia.
           rewrite pow2_S.
           simpl.
           rewrite Nat.add_0_r.
           apply Nat.add_le_mono; apply pow2_le_mono; lia.
    + destruct p as [p1 p2].
      specialize (nb_exists_HR_dec_formula_aux p1 _ eq_refl _ eq_refl
                                            (acc _
                                                 (apply_logical_rule_on_p_hypersequent_correct_inr_l G p1 p2 x Heqx Heqp))) as Hind1.
      specialize (nb_exists_HR_dec_formula_aux p2 _ eq_refl _ eq_refl
                                            (acc _
                                                 (apply_logical_rule_on_p_hypersequent_correct_inr_r G p1 p2 x Heqx Heqp))) as Hind2.
      transitivity (pow2 (nbMin_p_hseq p1 + nbMax_p_hseq p1) * (nbMax_p_hseq p1) + pow2 (nbMin_p_hseq p2 + nbMax_p_hseq p2) * (nbMax_p_hseq p2)).
      { simpl in *; lia. }
      rewrite <- (nbMin_p_hseq_put_non_atomic_fst G) by lia.
      rewrite <- (nbMax_p_hseq_put_non_atomic_fst G) by lia.
      remember (p_hseq_put_non_atomic_fst G) as H.
      clear - Heqp.
      destruct H; try now inversion Heqp.
      destruct l; try now inversion Heqp.
      destruct p as [a A].
      destruct A; inversion Heqp; subst; unfold nbVar_p_hseq; simpl; try lia.
      unfold HR_dec_formula_aux; fold HR_dec_formula_aux.
      remember (nbMax_term A2); remember (nbMax_term A1); remember (nbMax_p_seq l); remember (nbMin_term A1); remember (nbMin_term A2); remember (nbMin_p_seq l); remember (nbMin_p_hseq H); remember (nbMax_p_hseq H); remember (max_var_term A1); remember (max_var_term A2); remember (max_var_p_seq l); remember (max_var_p_hseq H).
      clear.
      transitivity
        (pow2 (pow2 (n0 + n1) * (n2 + n4) + n5 + (pow2 (n0 + n1) + n6)) * (pow2 (n0 + n + n1) + n6)
         + (pow2 (pow2 (n + n1) * (n3 + n4) + n5 + (pow2 (n + n1) + n6)) * (pow2 (n0 + n + n1) + n6))); try lia.
      { rewrite ? Nat.add_0_r.
        repeat ((apply Nat.mul_le_mono + apply plus_le_compat + apply pow2_le_mono + apply le_n_S); try lia). }
      transitivity ((pow2 (pow2 (n0 + n1) * (n2 + n4) + n5 + (pow2 (n0 + n1) + n6)) + pow2 (pow2 (n + n1) * (n3 + n4) + n5 + (pow2 (n + n1) + n6))) * (pow2 (n0 + n + n1) + n6)); try lia.
      apply Nat.mul_le_mono; try lia.
      transitivity (pow2 (S (pow2 (n0 + n + n1) * (n2 + n3 + n4) + n5 + (pow2 (n0 + n + n1) + n6)))).
      2:{ apply pow2_le_mono.
          rewrite <- ? Nat.add_succ_l.
          apply Nat.add_le_mono; try lia.
          apply Nat.add_le_mono; try lia.
          simpl.
          rewrite <- mult_n_Sm.
          assert (1 <= pow2 (n0 + n + n1)).
          { unfold pow2.
            remember (n0 + n + n1); clear.
            induction n7; simpl; lia. }
          lia. }
      rewrite pow2_S; simpl.
      rewrite Nat.add_0_r.
      apply Nat.add_le_mono;
        apply pow2_le_mono; apply Nat.add_le_mono; apply Nat.add_le_mono; try lia;
          try apply Nat.mul_le_mono; try apply pow2_le_mono; lia.
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

Lemma le_pow2_add : forall x y, x <> 0 -> y <> 0 ->2^x + 2^y <= 2^(x + y).
Proof.
  induction x; intros y Hxn0; simpl; try lia.
  destruct x.
  - clear.
    induction y; simpl; try lia.
    intros Hyn0.
    destruct y; simpl; try lia.
    simpl in *.
    assert (S y <> 0) by auto.
    specialize (IHy H).
    lia.
  - assert (S x <> 0) by auto.
    intros Hyn0.
    specialize (IHx y H Hyn0).
    lia.
Qed.

Lemma le_nbMin_nb_op_term : forall A,
    nbMin_term A <= nb_operator A.
Proof.
  induction A; simpl; lia.
Qed.

Lemma le_nbMax_nb_op_term : forall A,
    nbMax_term A <= nb_operator A.
Proof.
  induction A; simpl; lia.
Qed.

Lemma le_nbMin_nb_op_p_seq : forall T,
    nbMin_p_seq T <= nb_op_p_seq T.
Proof.
  induction T; simpl; try lia.
  destruct a as [a A].
  destruct A; simpl; try (assert (H := le_nbMin_nb_op_term A));
    try (assert (H1 := le_nbMin_nb_op_term A1));
    try (assert (H2 := le_nbMin_nb_op_term A2)); lia.
Qed.

Lemma le_nbMax_nb_op_p_seq : forall T,
    nbMax_p_seq T <= nb_op_p_seq T.
Proof.
  induction T; simpl; try lia.
  destruct a as [a A].
  destruct A; simpl; try (assert (H := le_nbMax_nb_op_term A));
    try (assert (H1 := le_nbMax_nb_op_term A1));
    try (assert (H2 := le_nbMax_nb_op_term A2)); lia.
Qed.

Lemma le_nbMax_nbMin_nb_op_term : forall A,
    nbMax_term A + nbMin_term A <= nb_operator A.
Proof.
  induction A; simpl; lia.
Qed.

Lemma le_nbMax_nbMin_nb_op_p_seq : forall T,
    nbMax_p_seq T + nbMin_p_seq T <= nb_op_p_seq T.
Proof.
  induction T; simpl; try lia.
  destruct a as [a A].
  destruct A; simpl; try (assert (H := le_nbMax_nbMin_nb_op_term A));
    try (assert (H1 := le_nbMax_nbMin_nb_op_term A1));
    try (assert (H2 := le_nbMax_nbMin_nb_op_term A2));try lia.
Qed.
  
Lemma le_nbMin_nb_op_p_hseq : forall G,
    G <> nil ->
    nbMin_p_hseq G <= pow2 (nb_op_p_hseq G + nb_p_seq G).
Proof.
  induction G; simpl; try lia; intros _.
  assert (Hmin := le_nbMin_nb_op_p_seq a).
  assert (Hmax := le_nbMax_nb_op_p_seq a).
  assert (Hmax_min := le_nbMax_nbMin_nb_op_p_seq a).
  case_eq (nb_op_p_seq a =? 0); intros H; (apply Nat.eqb_eq in H + apply Nat.eqb_neq in H).
  { replace (nb_op_p_seq a + nb_op_p_hseq G + S (nb_p_seq G)) with (S (nb_op_p_hseq G + nb_p_seq G)) by lia.
    rewrite pow2_S.
    destruct G; try (simpl; lia).
    assert (p :: G <> nil) by (intros H'; inversion H').
    specialize (IHG H0).
    lia. }
  etransitivity; [ apply Nat.add_le_mono;
                   [ apply Nat.mul_le_mono; [ reflexivity | apply id_le_pow2 ]
                   | ] | ].
  { destruct G.
    apply (Nat.le_0_l (pow2 (nb_op_p_hseq nil + nb_p_seq nil))).
    apply IHG.
    intros H'; inversion H'. }
  unfold pow2; rewrite <-Nat.pow_add_r.
  replace (nb_op_p_seq a + nb_op_p_hseq G + S (nb_p_seq G)) with (nb_op_p_seq a + S (nb_op_p_hseq G + nb_p_seq G)) by lia.
  etransitivity; [ | apply le_pow2_add; lia].
  apply Nat.add_le_mono; apply pow2_le_mono; lia.
Qed.

Lemma le_nbMax_nb_op_p_hseq : forall G,
    G <> nil ->
    nbMax_p_hseq G <= pow2 (nb_op_p_hseq G + nb_p_seq G).
Proof.
  induction G; simpl; try lia.
  assert (Hmin := le_nbMin_nb_op_p_seq a).
  assert (Hmax := le_nbMax_nb_op_p_seq a).
  assert (Hmax_min := le_nbMax_nbMin_nb_op_p_seq a).
  case_eq (nb_op_p_seq a =? 0); intros H; (apply Nat.eqb_eq in H + apply Nat.eqb_neq in H).
  { intros _.
    replace (nb_op_p_seq a + nb_op_p_hseq G + S (nb_p_seq G)) with (S (nb_op_p_hseq G + nb_p_seq G)) by lia.
    rewrite pow2_S.
    destruct G.
    { replace (nbMax_p_seq a) with 0 by lia.
      simpl; lia. }
    assert (p :: G <> nil) by (intros H'; inversion H').
    specialize (IHG H0).
    replace (nbMax_p_seq a) with 0 by lia.
    change (pow2 0) with 1.
    assert (H' := le_1_pow2 (nb_op_p_hseq (p :: G) + nb_p_seq (p :: G))).
    unfold Nat.mul; fold Nat.mul.
    unfold pow2.
    rewrite Nat.add_0_r.
    apply Nat.add_le_mono; assumption. }
  intros _.
  replace (nb_op_p_seq a + nb_op_p_hseq G + S (nb_p_seq G)) with (nb_op_p_seq a + S (nb_op_p_hseq G + nb_p_seq G)) by lia.
  etransitivity; [ | apply le_pow2_add; lia].
  apply Nat.add_le_mono; [apply pow2_le_mono; lia | ].
  destruct G.
  { simpl; lia. }
  etransitivity ; [ apply IHG ; intros H'; inversion H' | ].
  apply pow2_le_mono.
  lia.
Qed.

Lemma degree_HR_dec_formula_simpl : forall G x Heqx p Heqp acc,
    degree_FOL_R_formula (HR_dec_formula_aux G x Heqx p Heqp acc)  <= 1 + degree_p_hseq G.
Proof.
  apply degree_HR_dec_formula_aux.
Qed.                     

Lemma nb_exists_HR_dec_formula_simpl : forall G x Heqx p Heqp acc,
    nb_exists_FOL_R_formula (HR_dec_formula_aux G x Heqx p Heqp acc)  <= pow2 (3*pow2 (nb_op_p_hseq G + nb_p_seq G)).
Proof.
  destruct G.
  { intros x Heqx p Heqp acc.
    destruct acc as [acc].
    destruct x; [ | inversion Heqx].
    simpl; lia. }
  remember (p :: G) as G'.
  assert (G' <> nil) as Hnnil.
  { rewrite HeqG'; intros H; inversion H. }
  clear - Hnnil.
  etransitivity; [ apply nb_exists_HR_dec_formula_aux | ].
  etransitivity; [ apply Nat.mul_le_mono ; [ reflexivity | apply id_le_pow2] | ].
  unfold pow2.
  rewrite <- Nat.pow_add_r.
  apply pow2_le_mono.
  unfold Nat.mul.
  rewrite Nat.add_0_r; rewrite Nat.add_assoc.
  apply Nat.add_le_mono; [apply Nat.add_le_mono | ];
    try apply le_nbMin_nb_op_p_hseq;
    try apply le_nbMax_nb_op_p_hseq; assumption.
Qed.
  
Lemma nb_pol_HR_dec_formula_simpl : forall G x Heqx p Heqp acc,
    nb_pol_FOL_R_formula (HR_dec_formula_aux G x Heqx p Heqp acc)  <= pow2 (4 * pow2 (nb_op_p_hseq G + nb_p_seq G))*(1 + nbVar_p_hseq G).
Proof.
  destruct G.
  { intros x Heqx p Heqp acc.
    destruct acc as [acc].
    destruct x; [ | inversion Heqx].
    simpl; lia. }
  remember (p :: G) as G'.
  assert (G' <> nil) as Hnnil.
  { rewrite HeqG'; intros H; inversion H. }
  clear - Hnnil.
  etransitivity; [ apply nb_pol_HR_dec_formula_aux | ].
  etransitivity; [ apply Nat.mul_le_mono ; [ reflexivity | apply Nat.add_le_mono; [ apply id_le_pow2 | reflexivity] ] | ].
  rewrite ? Nat.mul_add_distr_l.
  apply Nat.add_le_mono.
  - unfold pow2; rewrite <- Nat.pow_add_r.
    rewrite Nat.mul_1_r.
    apply pow2_le_mono.
    unfold Nat.mul.
    rewrite ? Nat.add_0_r; rewrite <- ? Nat.add_assoc.
    repeat (apply Nat.add_le_mono);
      try apply le_nbMin_nb_op_p_hseq;
      try apply le_nbMax_nb_op_p_hseq; try assumption.
  - apply Nat.mul_le_mono; [ | reflexivity ].
    transitivity (pow2 (2* pow2 (nb_op_p_hseq G' + nb_p_seq G'))); [ | apply pow2_le_mono; lia].
    apply pow2_le_mono.
    unfold Nat.mul.
    rewrite ? Nat.add_0_r; rewrite <- ? Nat.add_assoc.
    repeat (apply Nat.add_le_mono);
      try apply le_nbMin_nb_op_p_hseq;
      try apply le_nbMax_nb_op_p_hseq; try assumption.
Qed.  

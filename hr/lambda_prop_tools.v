Require Import Rpos.
Require Import riesz_logic_List_more.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import RL.hr.hr.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

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

Lemma concat_with_coeff_mul_all_0 : forall G L,
    Forall_inf (fun x => x = None) L ->
    concat_with_coeff_mul G L = nil.
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
  transitivity ((copy_seq a s ++ copy_seq n s) ++ (concat_with_coeff_copy G L1 ++ concat_with_coeff_copy G L2)) ; [ | Permutation_Type_solve].
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
Lemma atomic_proof_all_eq P : forall H T,
    seq_is_atomic T ->
    hseq_is_atomic H -> 
    (forall n, sum_weight_var n (T :: H) = 0) ->
    HR P (T :: H).
Proof.
  induction H; intros T.
  - intros Hb _; revert Hb.
    remember (length T).
    revert T Heqn.
    apply (lt_wf_rect n (fun n => forall T : sequent,
                             n = length T ->
                             seq_is_atomic T ->
                             (forall n0 : term.V, sum_weight_var n0 (T :: nil) = 0) ->
                             HR P (T :: nil))).
    clear n.
    intros n IHn T Hlen Hat Hsum.
    destruct (seq_atomic_decomp_decr T Hat) as [[[[[n0 r] s] D] [Hr [Hperm Hdlen]]] | Hnil].
    + eapply hrr_ex_seq ; [ symmetry; apply Hperm | ].
      apply hrr_ID.
      { specialize (Hsum n0); simpl in Hsum.
        nra. }
      apply IHn with (length D).
      * lia.
      * reflexivity.
      * apply seq_atomic_perm with _ (vec s (RS_covar n0) ++ vec r (RS_var n0) ++ D) in Hat; try assumption.
        apply seq_atomic_app_inv_r in Hat.
        apply seq_atomic_app_inv_r in Hat.
        apply Hat.
      * intros n1.
        specialize (Hsum n0) as Hrs.
        specialize (Hsum n1).
        simpl in Hsum; rewrite (sum_weight_var_seq_perm _ _ _ Hperm) in Hsum.
        rewrite ? sum_weight_var_seq_app in Hsum.
        simpl.
        case_eq (term.V_eq n0 n1); intros H01 He.
        -- subst.
           rewrite sum_weight_var_seq_vec_covar_eq in Hsum; rewrite sum_weight_var_seq_vec_var_eq in Hsum.
           simpl in Hrs.
           nra.
        -- rewrite sum_weight_var_seq_vec_neq in Hsum; [ | intros H'; inversion H'; now auto | intros H'; inversion H'; now auto].
           rewrite sum_weight_var_seq_vec_neq in Hsum; [ | intros H'; inversion H'; now auto | intros H'; inversion H'; now auto].
           nra.
    + destruct T.
      { apply hrr_INIT. }
      destruct p as [a A].
      inversion Hat; subst.
      destruct A; try (now inversion X); exfalso; apply Hnil with v;
        [ left | right ]; left; reflexivity.
  - intros HatT HatH Hsum.
    apply hrr_S.
    apply IHlist.
    + inversion HatH; subst.
      apply seq_atomic_app; assumption.
    + inversion HatH; assumption.
    + intros n.
      specialize (Hsum n).
      simpl in *.
      rewrite sum_weight_var_seq_app.
      nra.
Qed.

(** ** sum_weight_(co)var_with_coeff *)
Fixpoint sum_weight_var_with_coeff n G (L : list (option Rpos)) :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , None :: L => sum_weight_var_with_coeff n G L
  | T :: G , (Some r) :: L => ((projT1 r) * sum_weight_var_seq n T) + sum_weight_var_with_coeff n G L
  end.

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
  simpl in *; rewrite IHG1; auto.
  destruct o ; lra.
Qed.

Lemma sum_weight_var_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    sum_weight_var_with_coeff n G (L1 ++ L2) = sum_weight_var_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Lemma concat_with_coeff_copy_all_0 : forall G L,
    Forall_inf (fun x => x = 0%nat) L ->
    concat_with_coeff_copy G L = nil.
Proof.
  intros G L; revert G; induction L; intros G Ha0; destruct G; simpl; auto.
  inversion Ha0; subst.
  apply IHL; assumption.
Qed.

Lemma sum_weight_var_with_coeff_oadd_Rpos_list : forall n G L1 L2,
    length L1 = length L2 ->
    sum_weight_var_with_coeff n G (oadd_Rpos_list L1 L2) = sum_weight_var_with_coeff n G L1 + sum_weight_var_with_coeff n G L2.
Proof.
  intros n G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  destruct a; destruct o; try destruct r; try destruct r0; simpl; nra.
Qed.

Lemma sum_weight_var_with_coeff_omul_Rpos_list : forall n G L1 r,
    sum_weight_var_with_coeff n G (map (mul_Rpos_oRpos r) L1) = (projT1 r) * sum_weight_var_with_coeff n G L1.
Proof.
  intros n G L1; revert G; induction L1; intros G r ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G r).
  destruct a; try destruct r; try destruct r0; simpl in *; nra.
Qed.

Lemma sum_weight_var_with_coeff_add_nat_list : forall n G L1 L2,
    length L1 = length L2 ->
    sum_weight_var_with_coeff n G (map nat_oRpos (add_nat_list L1 L2)) = sum_weight_var_with_coeff n G (map nat_oRpos L1) + sum_weight_var_with_coeff n G (map nat_oRpos L2).
Proof.
  intros n G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  simpl add_nat_list.
  destruct a; destruct n0; simpl map; simpl sum_weight_var_with_coeff; try nra.
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

Lemma sum_weight_var_with_coeff_mul_nat_list : forall n G L1 n',
    sum_weight_var_with_coeff n G (map nat_oRpos (map (Nat.mul (S n')) L1)) = (INR (S n')) * sum_weight_var_with_coeff n G (map nat_oRpos L1).
Proof.
  intros n G L1; revert G; induction L1; intros G n' ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G n').
  destruct a; simpl map.
  - rewrite Nat.mul_0_r; apply IHL1.
  - simpl sum_weight_var_with_coeff.
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

Lemma sum_weight_var_with_coeff_perm_r : forall G H L,
    Permutation_Type G H ->
    length L = length G ->
    { L' &
      prod (Permutation_Type L L') 
           ((forall n, sum_weight_var_with_coeff n G L = sum_weight_var_with_coeff n H L'))}.
Proof.
  intros G H L Hperm.
  revert L; induction Hperm; intros L Hlen.
  - destruct L; inversion Hlen.
    split with nil.
    repeat split; auto.
  - destruct L; inversion Hlen.
    destruct (IHHperm L H0) as [L' [Hperm' Hsum]].
    split with (o :: L').
    repeat split; auto.
    + intros n; simpl;rewrite (Hsum n); reflexivity.
  - destruct L ;  [ | destruct L] ; inversion Hlen.
    split with (o0 :: o :: L).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct o; destruct o0; simpl; nra.
  - destruct (IHHperm1 L Hlen) as [L' [Hperm' Hsum]].
    destruct (IHHperm2 L') as [L2' [Hperm2' Hsum2]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ symmetry ; apply Hperm' | ].
      etransitivity ; [ | apply Hperm1].
      apply Hlen. }
    split with L2'.
    repeat split; [ Permutation_Type_solve |  ].
    intros n.
    etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
Qed.

Lemma sum_weight_var_with_coeff_perm_l : forall G L L',
    Permutation_Type L L' ->
    length L = length G ->
    { H &
      prod (Permutation_Type G H) 
           ((forall n, sum_weight_var_with_coeff n G L = sum_weight_var_with_coeff n H L') )}.
Proof.
  intros G L L' Hperm.
  revert G; induction Hperm; intros G Hlen.
  - destruct G; inversion Hlen.
    split with nil.
    auto.
  - destruct G; inversion Hlen.
    destruct (IHHperm G H0) as [H [Hperm' Hsum]].
    split with (s :: H).
    repeat split; auto.
    intros n; simpl;rewrite (Hsum n); reflexivity.
  - destruct G ;  [ | destruct G] ; inversion Hlen.
    split with (s0 :: s :: G).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct y; destruct x; simpl; nra.
  - destruct (IHHperm1 G Hlen) as [H [Hperm' Hsum]].
    destruct (IHHperm2 H) as [H2 [Hperm2' Hsum2]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ | apply Hperm' ].
      etransitivity ; [ symmetry ; apply Hperm1 | ].
      apply Hlen. }
    split with H2.
    repeat split.
    + Permutation_Type_solve.
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
Qed.

Lemma sum_weight_var_with_coeff_perm_r_int : forall G H L,
    Permutation_Type G H ->
    length L = length G ->
    { L' &
      prod (Permutation_Type L L') 
           (forall n, sum_weight_var_with_coeff n G (map nat_oRpos L) = sum_weight_var_with_coeff n H (map nat_oRpos L'))}.
Proof.
  intros G H L Hperm.
  revert L; induction Hperm; intros L Hlen.
  - destruct L; inversion Hlen.
    split with nil.
    repeat split; auto.
  - destruct L; inversion Hlen.
    destruct (IHHperm L H0) as [L' [Hperm' Hsum]].
    split with (n :: L').
    repeat split; auto.
    + intros n'; simpl;rewrite (Hsum n'); reflexivity.
  - destruct L ;  [ | destruct L] ; inversion Hlen.
    split with (n0 :: n :: L).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n'; destruct n; destruct n0; simpl in *; nra.
  - destruct (IHHperm1 L Hlen) as [L' [Hperm' Hsum]].
    destruct (IHHperm2 L') as [L2' [Hperm2' Hsum2]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ symmetry ; apply Hperm' | ].
      etransitivity ; [ | apply Hperm1].
      apply Hlen. }
    split with L2'.
    repeat split; [ Permutation_Type_solve |  ].
    intros n.
    etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
Qed.

Lemma sum_weight_var_with_coeff_perm_l_int : forall G L L',
    Permutation_Type L L' ->
    length L = length G ->
    { H &
      prod (Permutation_Type G H) 
           (forall n, sum_weight_var_with_coeff n G (map nat_oRpos L) = sum_weight_var_with_coeff n H (map nat_oRpos L'))}.
Proof.
  intros G L L' Hperm.
  revert G; induction Hperm; intros G Hlen.
  - destruct G; inversion Hlen.
    split with nil.
    auto.
  - destruct G; inversion Hlen.
    destruct (IHHperm G H0) as [H [Hperm' Hsum]].
    split with (s :: H).
    repeat split; auto.
    + intros n; simpl;rewrite (Hsum n); reflexivity.
  - destruct G ;  [ | destruct G] ; inversion Hlen.
    split with (s0 :: s :: G).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; destruct y; destruct x; simpl; nra.
  - destruct (IHHperm1 G Hlen) as [H [Hperm' Hsum]].
    destruct (IHHperm2 H) as [H2 [Hperm2' Hsum2]].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ | apply Hperm' ].
      etransitivity ; [ symmetry ; apply Hperm1 | ].
      apply Hlen. }
    split with H2.
    repeat split.
    + Permutation_Type_solve.
    + intros n.
      etransitivity ; [ apply (Hsum n) | apply (Hsum2 n)].
Qed.

Lemma sum_weight_var_with_coeff_all_0 :
  forall G L n,
    Forall_inf (fun x => x = None) L ->
    sum_weight_var_with_coeff n G L = 0.
Proof.
  intros G L; revert G; induction L; intros G n Hall; destruct G; try reflexivity.
  inversion Hall; subst.
  specialize (IHL G n X).
  simpl; apply IHL.
Qed.

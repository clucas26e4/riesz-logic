Require Import Rpos.
Require Import term.
Require Import semantic.
Require Import hseq.
Require Import hr.
Require Import hrr_List_more.

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
  
Fixpoint sum_weight_with_coeff n G L :=
  match G, L with
  | _, nil => 0
  | nil, _ => 0
  | T :: G , r :: L => (r * (sum_weight_seq_var n T - sum_weight_seq_covar n T)) + sum_weight_with_coeff n G L
  end.

Fixpoint add_R_list L1 L2 :=
  match L1,L2 with
  | nil, _ => nil
  | _, nil => nil
  | r1 :: L1 , r2 :: L2 => (r1 + r2) :: (add_R_list L1 L2)
  end.

Fixpoint add_nat_list L1 L2 :=
  match L1,L2 with
  | nil, _ => nil
  | _, nil => nil
  | n1 :: L1 , n2 :: L2 => ((n1 + n2)%nat) :: (add_nat_list L1 L2)
  end.

Lemma add_R_list_length : forall L1 L2,
    length L1 = length L2 ->
    length (add_R_list L1 L2) = (length L1).
Proof.
  induction L1; intros L2; try reflexivity.
  intros Heq.
  destruct L2; inversion Heq.
  specialize (IHL1 L2 H0).
  simpl; rewrite IHL1; reflexivity.
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

Lemma Forall_Type_R_pos_add_R_list : forall L1 L2,
    Forall_Type (fun x => 0 <= x) L1 ->
    Forall_Type (fun x => 0 <= x) L2 ->
    Forall_Type (fun x => 0 <= x) (add_R_list L1 L2).
Proof.
  induction L1; intros L2 Hall1 Hall2; destruct L2; simpl; try apply Forall_Type_nil.
  inversion Hall1; inversion Hall2; subst.
  apply Forall_Type_cons; auto.
  nra.
Qed.

Lemma Forall_Type_R_pos_Rmult : forall r L1,
    0 <= r ->
    Forall_Type (fun x => 0 <= x) L1 ->
    Forall_Type (fun x => 0 <= x) (map (Rmult r) L1).
Proof.
  intros r; induction L1; intros Hr Hall1; auto.
  inversion Hall1; subst; apply Forall_Type_cons; auto.
  nra.
Qed.

Lemma sum_weight_with_coeff_add_R_list : forall n G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff n G (add_R_list L1 L2) = sum_weight_with_coeff n G L1 + sum_weight_with_coeff n G L2.
Proof.
  intros n G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  simpl; nra.
Qed.

Lemma sum_weight_with_coeff_mul_R_list : forall n G L1 r,
    sum_weight_with_coeff n G (map (Rmult r) L1) = r * sum_weight_with_coeff n G L1.
Proof.
  intros n G L1; revert G; induction L1; intros G r ; [ destruct G; simpl; nra | ].
  destruct G; [simpl ; nra | ].
  specialize (IHL1 G r).
  simpl in *; nra.
Qed.

Lemma sum_weight_with_coeff_add_nat_list : forall n G L1 L2,
    length L1 = length L2 ->
    sum_weight_with_coeff n G (map INR (add_nat_list L1 L2)) = sum_weight_with_coeff n G (map INR L1) + sum_weight_with_coeff n G (map INR L2).
Proof.
  intros n G L1; revert G; induction L1; intros G L2 Hlen; destruct L2; try (now inversion Hlen); [ destruct G; simpl; nra | ].
  destruct G; [ simpl ; nra | ].
  inversion Hlen.
  specialize (IHL1 G L2 H0).
  simpl add_nat_list.
  simpl.
  rewrite plus_INR; nra.
Qed.

Lemma sum_weight_with_coeff_mul_nat_list : forall n G L1 n',
    sum_weight_with_coeff n G (map INR (map (Nat.mul (S n')) L1)) = (INR (S n')) * sum_weight_with_coeff n G (map INR L1).
Proof.
  intros n G L1; revert G; induction L1; intros G n' ; [ destruct G; simpl; nra | ].
  destruct G; [ destruct a; simpl ; nra | ].
  specialize (IHL1 G n').
  simpl map.
  change ((a + n' * a)%nat) with (((S n') * a)%nat).
  rewrite mult_INR.
  simpl sum_weight_with_coeff.
  change (match n' with
          | 0%nat => 1
          | S _ => INR n' + 1
          end) with (INR (S n')).
  change (fun m : nat => (m + n' * m)%nat) with (Nat.mul (S n')).
  nra.
Qed.

Lemma sum_weight_with_coeff_perm_r : forall G H L,
    Permutation_Type G H ->
    length L = length G ->
    { L' &
      prod (Permutation_Type L L') 
           (forall n, sum_weight_with_coeff n G L = sum_weight_with_coeff n H L')}.
Proof.
  intros G H L Hperm.
  revert L; induction Hperm; intros L Hlen.
  - destruct L; inversion Hlen.
    split with nil.
    split; auto.
  - destruct L; inversion Hlen.
    destruct (IHHperm L H0) as [L' [Hperm' H]].
    split with (r :: L').
    repeat split; auto.
    intros n; simpl;rewrite (H n); reflexivity.
  - destruct L ;  [ | destruct L] ; inversion Hlen.
    split with (r0 :: r :: L).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; simpl; nra.
  - destruct (IHHperm1 L Hlen) as [L' [Hperm' H]].
    destruct (IHHperm2 L') as [L'' [Hperm'' H']].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ symmetry ; apply Hperm' | ].
      etransitivity ; [ | apply Hperm1].
      apply Hlen. }
    split with L''.
    repeat split; [ perm_Type_solve | ].
    intros n.
    etransitivity ; [ apply (H n) | apply (H' n)].
Qed.

Lemma sum_weight_with_coeff_perm_l : forall G L L',
    Permutation_Type L L' ->
    length L = length G ->
    { H &
      prod (Permutation_Type G H) 
           (forall n, sum_weight_with_coeff n G L = sum_weight_with_coeff n H L')}.
Proof.
  intros G L L' Hperm.
  revert G; induction Hperm; intros G Hlen.
  - destruct G; inversion Hlen.
    split with nil.
    split; auto.
  - destruct G; inversion Hlen.
    destruct (IHHperm G H0) as [H [Hperm' H']].
    split with (s :: H).
    repeat split; auto.
    intros n; simpl;rewrite (H' n); reflexivity.
  - destruct G ;  [ | destruct G] ; inversion Hlen.
    split with (s0 :: s :: G).
    repeat split.
    + apply Permutation_Type_swap.
    + intros n; simpl; nra.
  - destruct (IHHperm1 G Hlen) as [H [Hperm' H']].
    destruct (IHHperm2 H) as [H2 [Hperm'' H'']].
    { apply Permutation_Type_length in Hperm1.
      apply Permutation_Type_length in Hperm2.
      apply Permutation_Type_length in Hperm'.
      etransitivity;  [ | apply Hperm' ].
      etransitivity ; [ symmetry ; apply Hperm1 | ].
      apply Hlen. }
    split with H2.
    repeat split; [ perm_Type_solve | ].
    intros n.
    etransitivity ; [ apply (H' n) | apply (H'' n)].
Qed.

Lemma sum_weight_with_coeff_all_0 : forall G L n,
    Forall_Type (fun x => x = 0) L ->
    sum_weight_with_coeff n G L = 0.
Proof.
  intros G L; revert G; induction L; intros G n Hall; destruct G; try reflexivity.
  simpl.
  inversion Hall; subst.
  rewrite IHL; try assumption.
  nra.
Qed.

Lemma lambda_prop :
  forall G,
    hseq_is_atomic G ->
    HR_T_M G ->
    { L &
      prod (length L = length G)
           ((Exists_Type (fun x => 0 < x) L) *
            (Forall_Type (fun x => 0 <= x) L) *
            (forall n, sum_weight_with_coeff n G L = 0))}.
Proof.
  intros G Ha pi.
  induction pi.
  - split with (1 :: nil).
    repeat split; try reflexivity.
    + apply Exists_Type_cons_hd.
      nra.
    + apply Forall_Type_cons; [ | apply Forall_Type_nil].
      nra.
    + intros n.
      simpl; nra.
  - inversion Ha; subst.
    destruct (IHpi X0) as [L [Hlen [[Hex Hall] Hsum]]].
    split with (0 :: L).
    repeat split; auto.
    + simpl; rewrite Hlen; reflexivity.
    + apply Forall_Type_cons; try assumption; try nra.
    + intros n.
      simpl.
      rewrite (Hsum n).
      nra.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[Hex Hall] Hsum]]].
    { apply Forall_Type_cons ;[ | apply Forall_Type_cons]; try assumption. }
    destruct L; [ | destruct L]; try now inversion Hlen.
    split with ((r + r0) :: L).
    inversion Hall; inversion X1; subst.
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_Type_cons_hd.
        nra.
      * inversion X3; subst; auto.
        apply Exists_Type_cons_hd; nra.
    + apply Forall_Type_cons; try assumption; nra.
    + intros n.
      simpl.
      specialize (Hsum n).
      simpl in Hsum.
      nra.
  - inversion Ha; inversion X0; subst.
    destruct IHpi as [L [Hlen [[Hex Hall] Hsum]]].
    { apply Forall_Type_cons; try assumption.
      apply seq_atomic_app; assumption. }
    destruct L; try now inversion Hlen.
    split with (r :: r :: L).
    inversion Hall; subst.
    repeat split; auto.
    + simpl in *; rewrite Hlen; reflexivity.
    + intro n.
      specialize (Hsum n).
      simpl in *.
      rewrite sum_weight_seq_var_app in Hsum.
      rewrite sum_weight_seq_covar_app in Hsum.
      nra.
  - inversion Ha; subst.
    destruct IHpi1 as [L1 [Hlen1 [[Hex1 Hall1] Hsum1]]].
    { apply Forall_Type_cons ; [ apply seq_atomic_app_inv_l with T2 | ]; try assumption. }
    destruct L1; try now inversion Hlen1.
    destruct (Req_dec r 0).
    { split with (0 :: L1).
      repeat split; auto.
      - inversion Hex1; subst; try now (exfalso; nra).
        apply Exists_Type_cons_tl.
        apply X1.
      - apply Forall_Type_cons ; [ lra | ].
        inversion Hall1; assumption.
      - intros n; specialize (Hsum1 n).
        rewrite e in Hsum1.
        simpl in *; nra. }
    destruct IHpi2 as [L2 [Hlen2 [[Hex2 Hall2] Hsum2]]].
    { apply Forall_Type_cons ; [ apply seq_atomic_app_inv_r with T1 | ]; try assumption. }
    destruct L2; try now inversion Hlen2.
    destruct (Req_dec r0 0).
    { split with (0 :: L2).
      repeat split; auto.
      - inversion Hex2; subst; try now (exfalso; nra).
        apply Exists_Type_cons_tl.
        apply X1.
      - apply Forall_Type_cons ; [ lra | ].
        inversion Hall2; assumption.
      - intros n0; specialize (Hsum2 n0).
        rewrite e in Hsum2.
        simpl in *; nra. }
    rename n into Hnr; rename n0 into Hnr0.
    split with ((r * r0) :: add_R_list (map (Rmult r0) L1) (map (Rmult r) L2)).
    repeat split; auto.
    + simpl in Hlen1, Hlen2; simpl.
      rewrite add_R_list_length ; [ rewrite map_length; assumption | ].
      rewrite 2 map_length.
      lia.
    + apply Exists_Type_cons_hd.
      inversion Hall2; inversion Hall1; subst.
      nra.
    + inversion Hall1; inversion Hall2; subst.
      apply Forall_Type_cons; [ nra | ].
      apply Forall_Type_R_pos_add_R_list; apply Forall_Type_R_pos_Rmult; assumption.
    + intros n; specialize (Hsum1 n); specialize (Hsum2 n); simpl in Hsum1, Hsum2.
      simpl.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      rewrite sum_weight_with_coeff_add_R_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      rewrite 2 sum_weight_with_coeff_mul_R_list.
      simpl in *; nra.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[Hex Hall] Hsum]]].
    { apply Forall_Type_cons; try assumption.
      apply seq_atomic_mul; apply X. }
    destruct L; try now inversion Hlen.
    inversion Hall; subst.
    destruct r as [r Hbr]; simpl in *.
    assert (0 < r) as Hr by (apply R_blt_lt; assumption).
    split with (r0 * r :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_Type_cons_hd.
        nra.
      * apply Exists_Type_cons_tl; apply X2.
    + apply Forall_Type_cons; try assumption; try nra.
    + intros n; specialize (Hsum n);rewrite sum_weight_seq_var_mul in Hsum; rewrite sum_weight_seq_covar_mul in Hsum; simpl in *.
      nra.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [[Hex Hall] Hsum]]].
    { apply Forall_Type_cons; try assumption.
      eapply seq_atomic_app_inv_r; eapply seq_atomic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    intros n0; specialize (Hsum n0).
    destruct L; try now inversion Hlen.
    simpl; rewrite ? sum_weight_seq_app.
    case_eq (n0 =? n); intros H.
    + apply Nat.eqb_eq in H; subst.
      rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
      rewrite sum_weight_seq_covar_vec_covar_eq;rewrite sum_weight_seq_var_vec_var_eq.
      rewrite sum_weight_seq_var_vec_neq; [ | now auto ]; rewrite sum_weight_seq_covar_vec_neq; [ | now auto].
      simpl in Hsum.
      nra.
    + apply Nat.eqb_neq in H.
      rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_covar_vec_neq ; [ | now auto | intro H'; inversion H'; now auto]; rewrite ? sum_weight_seq_var_vec_neq; [ | intro H'; inversion H'; now auto | now auto ].
      simpl in Hsum.
      nra.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[Hex Hall] Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[Hex Hall] Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [[Hex Hall] Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct IHpi as [L [Hlen [[Hex Hall] Hsum]]].
    { inversion Ha; subst.
      apply Forall_Type_cons ; [ | apply Forall_Type_cons ]; assumption. }
    destruct L ; [ | destruct L]; try now inversion Hlen.
    inversion Hall; inversion X; subst.
    split with (r + r0 :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_Type_cons_hd.
        nra.
      * inversion X1; subst; auto.
        apply Exists_Type_cons_hd; nra.
    + apply Forall_Type_cons; try assumption; nra.
    + intros n.
      simpl.
      specialize (Hsum n).
      simpl in Hsum.
      nra.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi1 Ha) as [L [Hlen [[Hex Hall] Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct IHpi as [L [Hlen [[Hex Hall] Hsum]]].
    { inversion Ha; subst.
      apply Forall_Type_cons; try assumption.
      apply seq_atomic_perm with T2; [ perm_Type_solve | apply X]. }
    split with L.
    destruct L; try now inversion Hlen.
    repeat split; auto.
    intro n; specialize (Hsum n).
    simpl in *.
    rewrite <- (sum_weight_seq_var_perm _ _ _ p); rewrite <- (sum_weight_seq_covar_perm _ _ _ p); apply Hsum.
  - destruct IHpi as [L [Hlen [[Hex Hall] Hsum]]].
    { apply hseq_atomic_perm with H; try assumption.
      symmetry; apply p. }
    destruct (sum_weight_with_coeff_perm_r G H L p Hlen) as [L' [Hperm' H']].
    split with L'.
    repeat split.
    + apply Permutation_Type_length in p.
      apply Permutation_Type_length in Hperm'.
      etransitivity ; [ | apply p].
      etransitivity ; [ | apply Hlen].
      symmetry; apply Hperm'.
    + apply Exists_Type_Permutation_Type with L; assumption.
    + apply Forall_Type_Permutation_Type with L; assumption.
    + intros n.
      rewrite <- (H' n); apply Hsum.
  - inversion f.
Qed.

Lemma atomic_proof_all_eq P : forall H T,
    seq_is_atomic T ->
    hseq_is_atomic H -> 
    (forall n, sum_weight_var n (T :: H) = sum_weight_covar n (T :: H)) ->
    HR P (T :: H).
Proof.
  induction H; intros T.
  - intros Hat _; revert Hat.
    remember (length T).
    revert T Heqn.
    apply (lt_wf_rect n (fun n => forall T : sequent,
                             n = length T ->
                             seq_is_atomic T ->
                             (forall n0 : nat, sum_weight_var n0 (T :: nil) = sum_weight_covar n0 (T :: nil)) ->
                             HR P (T :: nil))).
    clear n.
    intros n IHn T Hlen Hat H.
    destruct (seq_atomic_decomp_decr T Hat) as [[[[[n0 r] s] D] [Hr [[Hs Hperm] Hdlen]]] | Hnil].
    + eapply hrr_ex_seq ; [ symmetry; apply Hperm | ].
      apply hrr_ID.
      { rewrite Hr; rewrite Hs.
        specialize (H n0); simpl in H.
        nra. }
      apply IHn with (length D).
      * lia.
      * reflexivity.
      * apply seq_atomic_perm with _ (vec s (covar n0) ++ vec r (var n0) ++ D) in Hat; try assumption.
        apply seq_atomic_app_inv_r in Hat.
        apply seq_atomic_app_inv_r in Hat.
        apply Hat.
      * intros n1.
        specialize (H n0) as Hrs.
        specialize (H n1).
        simpl in H; rewrite (sum_weight_seq_var_perm _ _ _ Hperm) in H; rewrite (sum_weight_seq_covar_perm _ _ _ Hperm) in H.
        rewrite ? sum_weight_seq_var_app in H; rewrite ? sum_weight_seq_covar_app in H.
        simpl.
        rewrite (sum_weight_seq_covar_vec_neq _ (var n0)) in H; [ | now auto].
        rewrite (sum_weight_seq_var_vec_neq _ (covar n0)) in H; [ | now auto].
        case_eq (n0 =? n1); intros H01.
        -- apply Nat.eqb_eq in H01; subst.
           rewrite sum_weight_seq_covar_vec_covar_eq in H; rewrite sum_weight_seq_var_vec_var_eq in H.
           simpl in Hrs.
           nra.
        -- apply Nat.eqb_neq in H01.
           rewrite sum_weight_seq_covar_vec_neq in H; [ | intros H'; inversion H'; now auto].
           rewrite sum_weight_seq_var_vec_neq in H; [ | intros H'; inversion H'; now auto].
           nra.
    + rewrite Hnil; apply hrr_INIT.
  - intros HatT HatH Heq.
    apply hrr_S.
    apply IHlist.
    + inversion HatH; subst.
      apply seq_atomic_app; assumption.
    + inversion HatH; assumption.
    + intros n.
      specialize (Heq n).
      simpl in *.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      nra.
Qed.
         
Lemma lambda_prop_inv :
  forall G,
    hseq_is_atomic G ->
    { L &
      prod (length L = length G)
           ((Exists_Type (fun x => 0 < x) L) *
            (Forall_Type (fun x => 0 <= x) L) *
            (forall n, sum_weight_with_coeff n G L = 0))} ->
    HR_T_M G.
Proof.
  enough (forall G H,
             hseq_is_atomic G ->
             hseq_is_atomic H ->
             { L &
               prod (length L = length G)
                    ((Exists_Type (fun x => 0 < x) L) *
                     (Forall_Type (fun x => 0 <= x) L) *
                     (forall n, (sum_weight_var n H - sum_weight_covar n H) + sum_weight_with_coeff n G L = 0))} + HR_T_M H ->
             HR_T_M (H ++  G)).
  { intros G Hat [L [Hlen [[Hex Hall] Hsum]]].
    change G with (nil ++ G).
    refine (X G nil Hat _ _).
    - apply Forall_Type_nil.
    - left.
      split with L.
      repeat split; auto.
      intros n; specialize (Hsum n); simpl in *; nra. }
  intros G.
  remember (length G) as n.
  revert G Heqn.
  induction n; intros G Heqn H HatG HatH [ [L [Hlen [[Hex Hall] Hsum]]] | pi].
  - destruct L; inversion Hlen; inversion Hex.
  - destruct G; inversion Heqn; rewrite app_nil_r; apply pi.
  - destruct (Exists_Type_split _ _ _ Hex) as [[[r La] Lb] [Hp HeqL]].
    assert (Permutation_Type L (r :: La ++ Lb)) as Hperm by (rewrite HeqL ; perm_Type_solve).
    destruct (sum_weight_with_coeff_perm_l G _ _ Hperm) as [G' [HpermG Hsum']].
    { lia. }
    destruct G' as [ | T G'].
    { symmetry in HpermG; apply Permutation_Type_nil in HpermG.
      subst; inversion Heqn. }
    apply hrr_ex_hseq with (T :: H ++ G') ; [ perm_Type_solve | ].
    apply R_blt_lt in Hp.
    apply hrr_T with (existT _ r Hp); try reflexivity.
    change (seq_mul (existT (fun r0 : R => (0 <? r0) = true) r Hp) T :: H ++ G')
      with
        ((seq_mul (existT (fun r0 : R => (0 <? r0) = true) r Hp) T :: H) ++ G').
    assert (hseq_is_atomic (T :: G')) as HatG'.
    { apply Forall_Type_Permutation_Type with G; try assumption. }
    apply IHn.
    + apply Permutation_Type_length in HpermG.
      rewrite HpermG in Heqn; simpl in Heqn; inversion Heqn; auto.
    + inversion HatG'; auto.
    + apply Forall_Type_cons; auto.
      apply seq_atomic_mul; now inversion HatG'.
    + destruct (Forall_Exists_Type_dec (fun x => x = 0)) with (La ++ Lb).
      { intros x.
        case_eq (x <? 0) ; case_eq (0 <? x); intros H1; intros H2.
        - apply R_blt_lt in H1; apply R_blt_lt in H2.
          exfalso; nra.
        - apply R_blt_nlt in H1; apply R_blt_lt in H2.
          right; intros H0; nra.
        - apply R_blt_lt in H1; apply R_blt_nlt in H2.
          right; intros H0; nra.
        - apply R_blt_nlt in H1; apply R_blt_nlt in H2.
          left; nra. }
      * right.
        apply atomic_proof_all_eq.
        -- apply seq_atomic_mul.
           apply hseq_atomic_perm with _ (T :: G') in HatG; try assumption.
           inversion HatG; assumption.
        -- apply HatH.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite (sum_weight_with_coeff_all_0 _ (La ++ Lb)) in Hsum'; try assumption.
           rewrite sum_weight_seq_var_mul; rewrite sum_weight_seq_covar_mul; simpl.
           nra.
      * left; split with (La ++ Lb).
        repeat split.
        -- rewrite HeqL in Hlen.
           rewrite ? app_length.
           rewrite ? app_length in Hlen; simpl in Hlen.
           lia.
        -- rewrite HeqL in Hall.
           clear - e Hall.
           induction La.
           ++ inversion Hall; subst.
              clear - e X.
              induction Lb; try now inversion e.
              inversion e; subst.
              ** apply Exists_Type_cons_hd.
                 inversion X; subst.
                 nra.
              ** apply Exists_Type_cons_tl.
                 inversion X; subst.
                 apply IHLb; try assumption.
           ++ simpl in *.
              inversion e; subst.
              ** apply Exists_Type_cons_hd.
                 inversion Hall; subst.
                 nra.
              ** apply Exists_Type_cons_tl.
                 inversion Hall; subst.
                 now apply IHLa.
        -- rewrite HeqL in Hall.
           destruct (Forall_Type_app_inv _ _ _ Hall).
           inversion f0; subst.
           now apply Forall_Type_app.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite sum_weight_seq_var_mul; rewrite sum_weight_seq_covar_mul; simpl.
           nra.
  - eapply hrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply hrr_W_gen.
    apply pi.
Qed.

Lemma int_lambda_prop :
  forall G,
    hseq_is_atomic G ->
    HR_M G ->
    { L &
      prod (length L = length G)
           ((Exists_Type (fun x => (0 < x)%nat) L) *
            (forall n, sum_weight_with_coeff n G (map (fun x => INR x) L) = 0))}.
Proof.
  intros G Ha pi.
  induction pi.
  - split with (1%nat :: nil).
    repeat split; try reflexivity.
    + apply Exists_Type_cons_hd.
      lia.
    + intros n.
      simpl; nra.
  - inversion Ha; subst.
    destruct (IHpi X0) as [L [Hlen [Hex Hsum]]].
    split with (0%nat :: L).
    repeat split; auto.
    + simpl; rewrite Hlen; reflexivity.
    + intros n.
      simpl.
      rewrite (Hsum n).
      nra.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [Hex Hsum]]].
    { apply Forall_Type_cons ;[ | apply Forall_Type_cons]; try assumption. }
    destruct L; [ | destruct L]; try now inversion Hlen.
    split with (((n + n0)%nat) :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_Type_cons_hd.
        lia.
      * inversion X1; subst; auto.
        apply Exists_Type_cons_hd; lia.
    + intros n1.
      simpl.
      specialize (Hsum n1).
      simpl in Hsum.
      rewrite plus_INR.
      nra.
  - inversion Ha; inversion X0; subst.
    destruct IHpi as [L [Hlen [Hex Hsum]]].
    { apply Forall_Type_cons; try assumption.
      apply seq_atomic_app; assumption. }
    destruct L; try now inversion Hlen.
    split with (n :: n :: L).
    repeat split; auto.
    + simpl in *; rewrite Hlen; reflexivity.
    + intro n1.
      specialize (Hsum n1).
      simpl in *.
      rewrite sum_weight_seq_var_app in Hsum.
      rewrite sum_weight_seq_covar_app in Hsum.
      nra.
  - inversion Ha; subst.
    destruct IHpi1 as [L1 [Hlen1 [Hex1 Hsum1]]].
    { apply Forall_Type_cons ; [ apply seq_atomic_app_inv_l with T2 | ]; try assumption. }
    destruct L1; try now inversion Hlen1.
    destruct n.
    { split with (0%nat :: L1).
      repeat split; auto.
      intros n; specialize (Hsum1 n).
      simpl in *; nra. }
    destruct IHpi2 as [L2 [Hlen2 [Hex2 Hsum2]]].
    { apply Forall_Type_cons ; [ apply seq_atomic_app_inv_r with T1 | ]; try assumption. }
    destruct L2; try now inversion Hlen2.
    destruct n0.
    { split with (0%nat :: L2).
      repeat split; auto.
      intros n0; specialize (Hsum2 n0).
      simpl in *; nra. }
    split with (((S n) * (S n0))%nat :: add_nat_list (map (Nat.mul (S n0)) L1) (map (Nat.mul (S n)) L2)).
    repeat split; auto.
    + simpl in Hlen1, Hlen2; simpl.
      rewrite add_nat_list_length ; [ rewrite map_length; assumption | ].
      rewrite 2 map_length.
      lia.
    + apply Exists_Type_cons_hd.
      lia.
    + intros n1; specialize (Hsum1 n1); specialize (Hsum2 n1); simpl in Hsum1, Hsum2.
      simpl.
      rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app.
      rewrite sum_weight_with_coeff_add_nat_list ; [ | simpl in Hlen1, Hlen2; simpl; rewrite 2 map_length; lia].
      change (fun m : nat => (m + n0 * m)%nat) with (Nat.mul (S n0)).
      change (fun m : nat => (m + n * m)%nat) with (Nat.mul (S n)).
      change (fun x : nat => INR x) with INR in *.
      rewrite 2 sum_weight_with_coeff_mul_nat_list.
      change (match (n0 + n * S n0)%nat with
              | 0%nat => 1
              | S _ => INR (n0 + n * S n0) + 1
              end)
        with (INR ((S n) * (S n0))).
      change (match n with
              | 0%nat => 1
              | S _ => INR n + 1
              end) with (INR (S n)) in Hsum1.
      change (match n0 with
              | 0%nat => 1
              | S _ => INR n0 + 1
              end) with (INR (S n0)) in Hsum2.
      rewrite mult_INR.
      nra.
  - inversion f.
  - inversion Ha; subst.
    destruct IHpi as [L [Hlen [Hex Hsum]]].
    { apply Forall_Type_cons; try assumption.
      eapply seq_atomic_app_inv_r; eapply seq_atomic_app_inv_r; apply X. }
    split with L.
    repeat split; auto.
    intros n0; specialize (Hsum n0).
    destruct L; try now inversion Hlen.
    simpl; rewrite ? sum_weight_seq_app.
    case_eq (n0 =? n); intros H.
    + apply Nat.eqb_eq in H; subst.
      rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
      rewrite sum_weight_seq_covar_vec_covar_eq;rewrite sum_weight_seq_var_vec_var_eq.
      rewrite sum_weight_seq_var_vec_neq; [ | now auto ]; rewrite sum_weight_seq_covar_vec_neq; [ | now auto].
      simpl in Hsum.
      nra.
    + apply Nat.eqb_neq in H.
      rewrite ? sum_weight_seq_var_app;rewrite ? sum_weight_seq_covar_app.
      rewrite ? sum_weight_seq_covar_vec_neq ; [ | now auto | intro H'; inversion H'; now auto]; rewrite ? sum_weight_seq_var_vec_neq; [ | intro H'; inversion H'; now auto | now auto ].
      simpl in Hsum.
      nra.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [Hex Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [Hex Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi Ha) as [L [Hlen [Hex Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct IHpi as [L [Hlen [Hex Hsum]]].
    { inversion Ha; subst.
      apply Forall_Type_cons ; [ | apply Forall_Type_cons ]; assumption. }
    destruct L ; [ | destruct L]; try now inversion Hlen.
    split with ((n + n0)%nat :: L).
    repeat split; auto.
    + inversion Hex; subst.
      * apply Exists_Type_cons_hd.
        lia.
      * inversion X; subst; auto.
        apply Exists_Type_cons_hd; lia.
    + intros n1.
      simpl.
      specialize (Hsum n1).
      simpl in Hsum.
      rewrite plus_INR.
      nra.
  - destruct r; [ | inversion Ha; inversion X; inversion X1].
    destruct (IHpi1 Ha) as [L [Hlen [Hex Hsum]]].
    split with L.
    repeat split; try assumption.
  - destruct IHpi as [L [Hlen [Hex Hsum]]].
    { inversion Ha; subst.
      apply Forall_Type_cons; try assumption.
      apply seq_atomic_perm with T2; [ perm_Type_solve | apply X]. }
    split with L.
    destruct L; try now inversion Hlen.
    repeat split; auto.
    intro n1; specialize (Hsum n1).
    simpl in *.
    rewrite <- (sum_weight_seq_var_perm _ _ _ p); rewrite <- (sum_weight_seq_covar_perm _ _ _ p); apply Hsum.
  - destruct IHpi as [L [Hlen [Hex Hsum]]].
    { apply hseq_atomic_perm with H; try assumption.
      symmetry; apply p. }
    destruct (sum_weight_with_coeff_perm_r G H (map (fun x => INR x) L) p) as [L' [Hperm' H']].
    { rewrite map_length.
      apply Hlen. }
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym Hperm')) as [L'' Heq Hperm''].
    split with L''.
    repeat split.
    + apply Permutation_Type_length in p.
      apply Permutation_Type_length in Hperm'.
      apply Permutation_Type_length in Hperm''.
      lia.
    + apply Exists_Type_Permutation_Type with L; assumption.
    + intros n.
      rewrite <- Heq.
      rewrite <- (H' n); apply Hsum.
  - inversion f.
Qed.
         
Lemma int_lambda_prop_inv :
  forall G,
    hseq_is_atomic G ->
    { L &
      prod (length L = length G)
           ((Exists_Type (fun x => (0 < x)%nat) L) *
            (forall n, sum_weight_with_coeff n G (map (fun x => INR x) L) = 0))} ->
    HR_M G.
Proof.
  enough (forall G H,
             hseq_is_atomic G ->
             hseq_is_atomic H ->
             { L &
               prod (length L = length G)
                    ((Exists_Type (fun x => (0 < x)%nat) L) *
                     (forall n, (sum_weight_var n H - sum_weight_covar n H) + sum_weight_with_coeff n G (map (fun x => INR x) L) = 0))} + HR_M H ->
             HR_M (H ++  G)).
  { intros G Hat [L [Hlen [Hex Hsum]]].
    change G with (nil ++ G).
    refine (X G nil Hat _ _).
    - apply Forall_Type_nil.
    - left.
      split with L.
      repeat split; auto.
      intros n; specialize (Hsum n); simpl in *; nra. }
  intros G.
  remember (length G) as n.
  revert G Heqn.
  induction n; intros G Heqn H HatG HatH [ [L [Hlen [Hex Hsum]]] | pi].
  - destruct L; inversion Hlen; inversion Hex.
  - destruct G; inversion Heqn; rewrite app_nil_r; apply pi.
  - destruct (Exists_Type_split _ _ _ Hex) as [[[r La] Lb] [Hp HeqL]].
    assert (Permutation_Type (map (fun x => INR x) L) (map (fun x => INR x) (r :: La ++ Lb))) as Hperm by (rewrite HeqL ; perm_Type_solve).
    destruct (sum_weight_with_coeff_perm_l G _ _ Hperm) as [G' [HpermG Hsum']].
    { rewrite map_length; lia. }
    destruct G' as [ | T G'].
    { symmetry in HpermG; apply Permutation_Type_nil in HpermG.
      subst; inversion Heqn. }
    apply hrr_ex_hseq with (T :: H ++ G') ; [ perm_Type_solve | ].
    apply lt_INR in Hp.
    change (INR 0) with 0 in Hp.
    apply (Permutation_Type_Forall_Type _ _ _ HpermG) in HatG.
    inversion HatG; clear x l H1 H2.
    destruct r.
    { exfalso.
      simpl in Hp; nra. }
    apply R_blt_lt in Hp.
    apply hrr_C_copy with r.
    change (copy_seq (S r) T :: H ++ G') with ((copy_seq (S r) T :: H) ++ G').
    apply IHn.
    + rewrite (Permutation_Type_length HpermG) in Heqn; simpl in Heqn.
      apply eq_add_S; apply Heqn.
    + apply X0.
    + apply Forall_Type_cons; try assumption.
      apply copy_seq_atomic; assumption.
    + destruct (Forall_Exists_Type_dec (fun x => x = 0%nat)) with (La ++ Lb).
      { intro x; destruct x; [ left | right]; lia. }
      * right.
        apply atomic_proof_all_eq.
        -- apply copy_seq_atomic; assumption.
        -- apply HatH.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           change (match r with
                   | 0%nat => 1
                   | S _ => INR r + 1
                   end) with (INR (S r)) in *.
           rewrite (sum_weight_with_coeff_all_0 _ (map (fun x => INR x) (La ++ Lb))) in Hsum'.
           ++ rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app; rewrite sum_weight_seq_var_copy; rewrite sum_weight_seq_covar_copy; simpl.
              rewrite S_INR in Hsum'.
              nra.
           ++ remember (La ++ Lb); clear - f.
              induction l; simpl in *; auto.
              inversion f; subst.
              apply Forall_Type_cons; auto.
      * left.
        split with (La ++ Lb).
        repeat split.
        -- rewrite HeqL in Hlen.
           rewrite app_length; rewrite app_length in Hlen; simpl in *.
           lia.
        -- clear - e.
           induction La.
           ++ induction Lb; try now inversion e.
              inversion e; subst.
              ** apply Exists_Type_cons_hd.
                 lia.
              ** apply Exists_Type_cons_tl.
                 apply IHLb; try assumption.
           ++ simpl in *.
              inversion e; subst.
              ** apply Exists_Type_cons_hd.
                 lia.
              ** apply Exists_Type_cons_tl.
                 now apply IHLa.
        -- intros n0.
           specialize (Hsum' n0); specialize (Hsum n0).
           simpl in *.
           rewrite sum_weight_seq_var_app; rewrite sum_weight_seq_covar_app; rewrite sum_weight_seq_var_copy; rewrite sum_weight_seq_covar_copy; simpl.
           change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)) in *.
           rewrite S_INR in Hsum'; nra.
  - eapply hrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply hrr_W_gen.
    apply pi.
Qed.

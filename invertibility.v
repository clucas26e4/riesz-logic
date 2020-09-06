Require Import Rpos.
Require Import term.
Require Import semantic.
Require Import hseq.
Require Import hr.

Require Import CMorphisms.
Require Import List_Type_more.
Require Import Permutation_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Bool_more.
Require Import Lra.

Definition Allperm := (Forall2_Type (Permutation_Type (A:=Rpos * term))).

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
    
Lemma decomp_M_case : forall T1 T2 r D A,
    Permutation_Type (T1 ++ T2) (vec r A ++ D) ->
    {' (D1, D2, r1, r2) : _ &
                          prod (Permutation_Type r (r1 ++ r2))
                               ((Permutation_Type D (D1 ++ D2)) *
                                (Permutation_Type T1 (vec r1 A ++ D1)) *
                                (Permutation_Type T2 (vec r2 A ++ D2)))}.
Proof.
  intros T1 T2 r D A Hperm.
  revert T1 T2 D Hperm; induction r; intros T1 T2 D Hperm.
  - simpl in Hperm.
    split with (T1 , T2, nil, nil).
    simpl; repeat split; try perm_Type_solve.
  - simpl in Hperm.
    case (in_Type_app_or T1 T2 (a , A)).
    + apply Permutation_Type_in_Type with ((a, A) :: vec r A ++ D); try perm_Type_solve.
      left; reflexivity.
    + intros Hin.
      apply in_Type_split in Hin as [[l1 l2] Heq].
      destruct (IHr (l1 ++ l2) T2 D) as [[[[D1 D2] r1'] r2] [H1' [[H2 H3] H4]]].
      * apply Permutation_Type_cons_inv with (a, A).
        rewrite Heq in Hperm; perm_Type_solve.
      * split with (D1, D2, (a :: r1'), r2).
        rewrite Heq; simpl; repeat split; try perm_Type_solve.
    + intros Hin.
      apply in_Type_split in Hin as [[l1 l2] Heq].
      destruct (IHr T1 (l1 ++ l2) D) as [[[[D1 D2] r1'] r2] [H1' [[H2 H3] H4]]].
      * apply Permutation_Type_cons_inv with (a, A).
        rewrite Heq in Hperm; perm_Type_solve.
      * split with (D1, D2, r1', (a :: r2)).
        rewrite Heq; simpl; repeat split; try perm_Type_solve.
Qed.

Lemma perm_decomp_vec_ID_case : forall T D n r s t A,
    A <> covar n ->
    A <> var n ->
    Permutation_Type (vec s (covar n) ++ vec t (var n) ++ T) (vec r A ++ D) ->
    {' (Ta, Tb, Da, Db) : _ &
                          prod (Permutation_Type T (Ta ++ Tb))
                               ((Permutation_Type D (Da ++ Db)) *
                                (Permutation_Type (vec s (covar n) ++ vec t (var n)) Da) *
                                (Permutation_Type (vec r A) Ta) *
                                (Permutation_Type Tb Db)) }.
Proof.
  intros T D n r s t A Hnc Hnv Hperm.
  revert D r Hperm; induction s; [ induction t | ]; intros D r Hperm.
  - split with (vec r A , D, nil, D).
    repeat split; try assumption; try reflexivity.
  - simpl in *.
    assert (In_Type (a, var n) D) as HinD.
    { destruct (in_Type_app_or (vec r A) D (a , var n)).
      + apply Permutation_Type_in_Type with ((a, var n) :: vec t (var n) ++ T); try assumption.
        left; reflexivity.
      + exfalso.
        clear - i Hnv.
        induction r; inversion i.
        * inversion H.
          apply Hnv; apply H2.
        * apply IHr; apply X.
      + assumption. }
    destruct (Add_Type_inv _ _ HinD) as [D' Hadd].
    apply Permutation_Type_Add_Type in Hadd.
    destruct (IHt D' r) as [ [[[Ta Tb] Da ] Db] [H1 [[[H2 H3] H4] H5]]].
    { apply Permutation_Type_cons_inv with (a, var n).
      etransitivity; [ apply Hperm | ].
      perm_Type_solve. }
    split with (Ta, Tb, ((a, var n):: Da), Db).
    repeat split; try assumption; try reflexivity; try perm_Type_solve.
  - simpl in *.
    assert (In_Type (a, covar n) D) as HinD.
    { destruct (in_Type_app_or (vec r A) D (a , covar n)).
      + apply Permutation_Type_in_Type with ((a, covar n) :: vec s (covar n) ++ vec t (var n) ++ T); try assumption.
        left; reflexivity.
      + exfalso.
        clear - i Hnc.
        induction r; inversion i.
        * inversion H.
          apply Hnc; apply H2.
        * apply IHr; apply X.
      + assumption. }
    destruct (Add_Type_inv _ _ HinD) as [D' Hadd].
    apply Permutation_Type_Add_Type in Hadd.
    destruct (IHs D' r) as [ [[[Ta Tb] Da ] Db] [H1 [[[H2 H3] H4] H5]]].
    { apply Permutation_Type_cons_inv with (a, covar n).
      perm_Type_solve. }
    split with (Ta, Tb, ((a, covar n):: Da), Db).
    repeat split; try assumption; try reflexivity; try perm_Type_solve.
Qed.



Lemma perm_decomp_vec_neq : forall T D r s A B,
    A <> B ->
    Permutation_Type (vec s B ++ T) (vec r A ++ D) ->
    {' (Ta, Tb, Da, Db) : _ &
                          prod (Permutation_Type T (Ta ++ Tb))
                               ((Permutation_Type D (Da ++ Db)) *
                                (Permutation_Type (vec s B) Da) *
                                (Permutation_Type (vec r A) Ta) *
                                (Permutation_Type Tb Db)) }.
Proof.
  intros T D r s A B Hneq Hperm.
  revert D r Hperm; induction s; intros D r Hperm.
  - split with (vec r A , D, nil, D).
    repeat split; try assumption; try reflexivity.
  - simpl in *.
    assert (In_Type (a, B) D) as HinD.
    { destruct (in_Type_app_or (vec r A) D (a , B)).
      + apply Permutation_Type_in_Type with ((a, B) :: vec s B ++ T); try assumption.
        left; reflexivity.
      + exfalso.
        clear - i Hneq.
        induction r; inversion i.
        * inversion H.
          apply Hneq; apply H2.
        * apply IHr; apply X.
      + assumption. }
    destruct (Add_Type_inv _ _ HinD) as [D' Hadd].
    apply Permutation_Type_Add_Type in Hadd.
    destruct (IHs D' r) as [ [[[Ta Tb] Da ] Db] [H1 [[[H2 H3] H4] H5]]].
    { apply Permutation_Type_cons_inv with (a, B).
      etransitivity; [ apply Hperm | ].
      perm_Type_solve. }
    split with (Ta, Tb, ((a, B):: Da), Db).
    repeat split; try assumption; try reflexivity; try perm_Type_solve.
Qed.

Lemma perm_decomp_vec_eq : forall T D r s A,
    Permutation_Type (vec s A ++ T) (vec r A ++ D) ->
    {' (a , b , c , T', D') : _ &
                     prod (Permutation_Type r  (a ++ b))
                          ((Permutation_Type s  (b ++ c)) *
                           (Permutation_Type T (vec a A ++ T')) *
                           (Permutation_Type D (vec c A ++ D')) *
                           (Permutation_Type T' D')) }.
Proof.
  intros T D r s A Hperm.
  revert D r Hperm; induction s; intros D r Hperm.
  + split with (r, nil, nil, D , D).
    repeat split; try perm_Type_solve.
  + simpl in Hperm.
    case (in_Type_app_or (vec r A) D (a , A)).
    * apply Permutation_Type_in_Type with ((a, A) :: vec s A ++ T); [apply Hperm | ].
      left; reflexivity.
    * intro Hin.
      assert { r' & Permutation_Type r (a :: r')}.
      { clear - Hin.
        induction r.
        - inversion Hin.
        - simpl in Hin.
          destruct Hin as [Heq | Hin].
          + inversion Heq; split with r; simpl; reflexivity.
          + specialize (IHr Hin) as [r' Hperm].
            split with (a0 :: r').
            perm_Type_solve. }
      destruct X as [r' Hperm'].
      destruct (IHs D r') as [ [[[[a1 b1] c1] T'] D'] [H1 [[[H2 H3] H4] H5]]].
      { apply Permutation_Type_cons_inv with (a, A).
        transitivity (vec r A ++ D); try perm_Type_solve.
        change ((a, A) :: vec r' A ++ D) with (vec (a :: r') A ++ D).
        apply Permutation_Type_app; try reflexivity.
        apply vec_perm; apply Hperm'. }
      split with (a1 , a :: b1, c1, T' , D').
      repeat split; try perm_Type_solve.
    * intro Hin.
      destruct (Add_Type_inv _ _ Hin) as [D' Hadd].
      apply Permutation_Type_Add_Type in Hadd.
      destruct (IHs D' r) as [ [[[[a1 b1] c1] T'] D''] [H1 [[[H2 H3] H4] H5]]].
      { apply Permutation_Type_cons_inv with (a, A).
        perm_Type_solve. }
      split with (a1, b1, a :: c1 , T', D'').
      repeat split; try perm_Type_solve.
Qed.

Lemma hrr_Z_inv_gen P : forall L,
    HR P (map (fun x => (vec (fst x) zero ++ snd x)) L) ->
    HR P (map (fun x => (snd x)) L).
Proof.
  intros L.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) zero ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) zero ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; simpl; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L; [ | destruct L]; try now inversion Hperm.
    simpl in Hperm; inversion Hperm; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r T]; destruct r; destruct T; try now inversion X.
    apply hrr_INIT.
  - destruct L; try now inversion Hperm.
    simpl; apply hrr_W.
    apply IHpi.
    simpl in Hperm; now inversion Hperm.
  - destruct L; try now inversion Hperm.
    simpl; apply hrr_C.
    change ((snd p)
                    :: (snd p) :: map (fun x =>(snd x)) L)
      with
        (map (fun x  => snd x) (p :: p :: L)).
    apply IHpi.
    inversion Hperm.
    apply Forall2_Type_cons ; [ | apply Forall2_Type_cons]; assumption.
  - destruct L; [ | destruct L]; try now inversion Hperm.
    destruct p as [r1 T1']; destruct p0 as [r2 T2'].
    simpl in Hperm.
    inversion Hperm; inversion X0; subst.
    simpl; apply hrr_S; try assumption.
    change ((T1' ++ T2') :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1 ++ r2, T1' ++ T2') :: L)).
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    rewrite vec_app; perm_Type_solve.    
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hrr_ex_seq with (D1 ++ D2).
    { perm_Type_solve. }
    apply hrr_M; try assumption.
    + change (D1 :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, D1) :: L)).
      apply IHpi1.
      simpl; apply Forall2_Type_cons ; assumption.
    + change (D2 :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r2, D2) :: L)).
      apply IHpi2.
      simpl; apply Forall2_Type_cons ; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hrr_ex_seq with (seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      reflexivity. }
    change (seq_mul r T' :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((mul_vec r r', seq_mul r T') :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    rewrite <- seq_mul_vec_mul_vec; rewrite <- seq_mul_app.
    apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (zero <> (covar n)) as Hnc by now auto.
    assert (zero <> (var n)) as Hnv by now auto.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ Db).
    { perm_Type_solve. }
    apply hrr_ID; try assumption.
    change (Db :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    destruct (perm_decomp_vec_eq _ _ _ _ _ X) as [ [[[[a1 b1] c1] T'] D'] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec c1 zero ++ T').
    { perm_Type_solve. }
    apply hrr_Z.
    change (T' :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with ( map (fun x : list Rpos * list (Rpos * term) => snd x) ((a1 , T') :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (zero <> A +S B) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A +S B) ++ Db).
    { perm_Type_solve. }
    apply hrr_plus; try assumption.
    change ((vec r A ++ vec r B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec r A ++ vec r B ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (zero <> r0 *S A) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (r0 *S A) ++ Db).
    { perm_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec (mul_vec r0 r) A ++ Db).
    { perm_Type_solve. }
    change ((vec (mul_vec r0 r) A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec (mul_vec r0 r) A ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (zero <> A \/S B) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A \/S B) ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_max; try assumption.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r A ++ Db).
    { perm_Type_solve. }
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r B ++ Db).
    { perm_Type_solve. }
    change ((vec r B ++ Db) :: (vec r A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec r B ++ Db) :: (r1, vec r A ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | assumption] ]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (zero <> A /\S B) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A /\S B) ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_min; try assumption.
    + apply hrr_ex_seq with (vec r A ++ Db).
      { perm_Type_solve. }
      change ((vec r A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec r A ++ Db) :: L)).
      apply IHpi1.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
    + apply hrr_ex_seq with (vec r B ++ Db).
      { perm_Type_solve. }
      change ((vec r B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec r B ++ Db) :: L)).
      apply IHpi2.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) zero ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hrr_can with A r s; try assumption.
    apply hrr_ex_seq with (vec s (-S A) ++ vec r A ++ T1).
    { perm_Type_solve. }
    change ((vec s (-S A) ++ vec r A ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec s (-S A) ++ vec r A ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.
    
Lemma hrr_plus_inv_gen P : forall L A B,
    HR P (map (fun x => (vec (fst x) (A +S B) ++ snd x)) L) ->
    HR P (map (fun x => (vec (fst x) A ++ vec (fst x) B ++ snd x)) L).
Proof.
  intros L A B.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A +S B) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A +S B) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; simpl; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L; [ | destruct L]; try now inversion Hperm.
    inversion Hperm; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; try now inversion X.
    apply hrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_W.
    apply IHpi.
    assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_C.
    change ((vec (fst p) A ++ vec (fst p) B ++ snd p)
              :: (vec (fst p) A ++ vec (fst p) B ++ snd p)
              :: map
              (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x)
              L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x)
           (p :: p :: L)).
    apply IHpi.
    simpl.
    do 2 (apply Forall2_Type_cons; try assumption).
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [p1 p2];
      destruct p0 as [p1' p2'];
      remember ((p1 ++ p1'), (p2 ++ p2')) as p'';
      (apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((p1, p2) :: (p1',p2') :: L)) ; [ apply Permutation_Type_map; perm_Type_solve | ]).
    simpl in *;
      apply hrr_S;
      (apply hrr_ex_seq with (vec (fst p'') A ++ vec (fst p'') B ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (fst p'') A ++ vec (fst p'') B ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p'' :: L));
      apply IHpi;
      simpl; apply Forall2_Type_cons;
        [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hrr_ex_seq with ((vec r1 A ++ vec r1 B ++ D1) ++ (vec r2 A ++ vec r2 B ++ D2)).
    { transitivity (vec (r1 ++ r2) A ++ vec (r1 ++ r2) B ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm; perm_Type_solve | ].
      apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
    apply hrr_M; try assumption.
    + change ((vec r1 A ++ vec r1 B ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, D1) :: L)).
      apply IHpi1.
      simpl; apply Forall2_Type_cons ;  assumption.
    + change ((vec r2 A ++ vec r2 B ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r2, D2) :: L)).
      apply IHpi2.
      simpl; apply Forall2_Type_cons ; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hrr_ex_seq with (vec (mul_vec r r') A ++ vec (mul_vec r r') B ++ seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      repeat (apply Permutation_Type_app; try reflexivity). }
    change ((vec (mul_vec r r') A ++ vec (mul_vec r r') B ++ seq_mul r T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((mul_vec r r', seq_mul r T') :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    rewrite <- seq_mul_vec_mul_vec; rewrite <- seq_mul_app.
    apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> (covar n)) as Hnc by now auto.
    assert (A +S B <> (var n)) as Hnv by now auto.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 A ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hrr_ID; try assumption.
    change ((vec r1 A ++ vec r1 B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> zero) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r zero ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_Z; try assumption.
    change ((vec r1 A ++ vec r1 B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    case (term_eq_dec (A +S B) (A0 +S B0)).
    + intros H; inversion H; subst.
      destruct (perm_decomp_vec_eq _ _ _ _ _ X) as [ [[[[a1 b1] c1] T'] D'] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec c1 (A0 +S B0) ++ vec (a1 ++ b1) A0 ++ vec (a1 ++ b1) B0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      apply hrr_plus.
      apply hrr_ex_seq with (vec a1 A0 ++ vec a1 B0 ++ (vec r A0 ++ vec r B0 ++ T')).
      { transitivity (vec a1 A0 ++ vec a1 B0 ++ (vec (b1 ++ c1) A0 ++ vec (b1 ++ c1) B0 ++ T')); [ do 2 (apply Permutation_Type_app ; [ reflexivity | ]) ; do 2 (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve) | ].
        rewrite ? vec_app.
        perm_Type_solve. }
      change ((vec a1 A0 ++ vec a1 B0 ++ vec r A0 ++ vec r B0 ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ vec (fst x) B0 ++ snd x) L)
        with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ vec (fst x) B0 ++ snd x) ((a1 , vec r A0 ++ vec r B0 ++ T') :: L)).
      apply IHpi.
      simpl.
      apply Forall2_Type_cons; [ | assumption].
      transitivity (vec (b1 ++ c1) A0 ++ vec (b1 ++ c1) B0 ++ T).
      { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
      etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
      perm_Type_solve.      
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 A ++ vec r1 B ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hrr_plus; try assumption.
      apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)).
      { perm_Type_solve. }
      change ((vec r1 A ++ vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r A0 ++ vec r B0 ++ Db) :: L)).
      apply IHpi.
      simpl.
      apply Forall2_Type_cons; [ | assumption].
      perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> r0 *S A0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 A ++ vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec (mul_vec r0 r) A0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> A0 \/S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_max; try assumption.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)).
    { perm_Type_solve. }
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)) :: (vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r B0 ++ Db) :: (r1, vec r A0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | assumption] ]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> A0 /\S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_min; try assumption.
    + apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      change ((vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r A0 ++ Db) :: L)).
      apply IHpi1.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
    + apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)).
      { perm_Type_solve. }
      change ((vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r B0 ++ Db) :: L)).
      apply IHpi2.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A +S B) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hrr_can with A0 r s; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec r1 A ++ vec r1 B ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.
    
Lemma hrr_mul_inv_gen P : forall L a A,
    HR P (map (fun x => (vec (fst x) (a *S A) ++ snd x)) L) ->
    HR P (map (fun x => (vec (mul_vec a (fst x)) A ++ snd x)) L).
Proof with try assumption.
  intros L a A.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (a *S A) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (a *S A) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; try now inversion X.
    apply hrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_W.
    apply IHpi...
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_C.
    change ((vec (mul_vec a (fst p)) A ++ snd p)
              :: (vec (mul_vec a (fst p)) A ++ snd p)
              :: map
              (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x)
              L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x)
           (p :: p :: L)).
    apply IHpi.
    simpl.
    do 2 (apply Forall2_Type_cons; try assumption).
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [p1 p2];
      destruct p0 as [p1' p2'];
      remember ((p1 ++ p1'), (p2 ++ p2')) as p'';
      (apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((p1, p2) :: (p1',p2') :: L)) ; [ apply Permutation_Type_map; perm_Type_solve | ]);
      simpl in *;
      apply hrr_S;
      (apply hrr_ex_seq with (vec (mul_vec a (fst p'')) A ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? mul_vec_app; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (mul_vec a (fst p'')) A ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) (L))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) (p'' :: L));
      apply IHpi;
      simpl; apply Forall2_Type_cons;
         [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hrr_ex_seq with ((vec (mul_vec a r1) A ++ D1) ++ (vec (mul_vec a r2) A ++ D2)).
    { transitivity (vec (mul_vec a (r1 ++ r2)) A ++ (D1 ++ D2)) ; [rewrite ? mul_vec_app; rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm; apply mul_vec_perm; perm_Type_solve | ].
      perm_Type_solve. }
    apply hrr_M; try assumption.
    + change ((vec (mul_vec a r1) A ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, D1) :: L)).
      apply IHpi1.
      simpl; apply Forall2_Type_cons ; assumption.
    + change ((vec (mul_vec a r2) A ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r2, D2) :: L)).
      apply IHpi2.
      simpl; apply Forall2_Type_cons ; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hrr_ex_seq with (vec (mul_vec a (mul_vec r r')) A ++ seq_mul r T').
    { rewrite mul_vec_mul_vec_comm.
      rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      repeat (apply Permutation_Type_app; try reflexivity). }
    change ((vec (mul_vec a (mul_vec r r')) A ++ seq_mul r T') :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((mul_vec r r', seq_mul r T') :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    rewrite <- seq_mul_vec_mul_vec; rewrite <- seq_mul_app.
    apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (a *S A <> (covar n)) as Hnc by now auto.
    assert (a *S A <> (var n)) as Hnv by now auto.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec (mul_vec a r1) A  ++ Db).
    { perm_Type_solve. }
    apply hrr_ID; try assumption.
    change ((vec (mul_vec a r1) A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (a *S A <> zero) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r zero ++ vec (mul_vec a r1) A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_Z; try assumption.
    change ((vec (mul_vec a r1) A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (a *S A <> A0 +S B) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 +S B) ++ vec (mul_vec a r1) A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_plus; try assumption.
    apply hrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r A0 ++ vec r B ++ Db)).
    { perm_Type_solve. }
    change ((vec (mul_vec a r1) A ++ (vec r A0 ++ vec r B ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec r A0 ++ vec r B ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    case (term_eq_dec (a *S A) (r0 *S A0)).
    + intros H; inversion H; subst.
      destruct (perm_decomp_vec_eq _ _ _ _ _ X) as [ [[[[a1 b1] c1] T'] D'] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec c1 (r0 *S A0) ++ vec (mul_vec r0 (a1 ++ b1)) A0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm; apply mul_vec_perm; symmetry; assumption).
        perm_Type_solve. }
      apply hrr_mul.
      apply hrr_ex_seq with (vec (mul_vec r0 a1) A0 ++ (vec (mul_vec r0 r) A0 ++ T')).
      { transitivity (vec (mul_vec r0 a1) A0 ++ (vec (mul_vec r0 (b1 ++ c1)) A0 ++ T')); [ apply Permutation_Type_app ; try apply Permutation_Type_app; try (apply vec_perm; apply mul_vec_perm); try perm_Type_solve | ].
        rewrite ? mul_vec_app; rewrite ? vec_app.
        perm_Type_solve. }
      change ((vec (mul_vec r0 a1) A0 ++ vec (mul_vec r0 r) A0 ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec r0 (fst x)) A0 ++ snd x) L)
        with ( map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec r0 (fst x)) A0 ++ snd x) ((a1 , vec (mul_vec r0 r) A0 ++ T') :: L)).
      apply IHpi.
      simpl.
      apply Forall2_Type_cons; [ | assumption].
      transitivity (vec (mul_vec r0 (b1 ++ c1)) A0 ++ T).
      { repeat (try apply Permutation_Type_app; try (apply vec_perm; apply mul_vec_perm); try perm_Type_solve). }
      etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; apply mul_vec_perm; symmetry; apply H2')); reflexivity] ].
      perm_Type_solve.      
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec r (r0 *S A0) ++ vec (mul_vec a r1) A ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hrr_mul; try assumption.
      apply hrr_ex_seq with (vec (mul_vec a r1) A ++ (vec (mul_vec r0 r) A0 ++ Db)).
      { perm_Type_solve. }
      change ((vec (mul_vec a r1) A ++ (vec (mul_vec r0 r) A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec (mul_vec r0 r) A0 ++ Db) :: L)).
      apply IHpi.
      simpl.
      apply Forall2_Type_cons; [ | assumption].
      perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (a *S A <> A0 \/S B) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 \/S B) ++ vec (mul_vec a r1) A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_max; try assumption.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r A0 ++ Db)).
    { perm_Type_solve. }
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r B ++ Db)).
    { perm_Type_solve. }
    change ((vec (mul_vec a r1) A ++ (vec r B ++ Db)) :: (vec (mul_vec a r1) A ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec r B ++ Db) :: (r1, vec r A0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | assumption] ]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (a *S A <> A0 /\S B) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 /\S B) ++ vec (mul_vec a r1) A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_min; try assumption.
    + apply hrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      change ((vec (mul_vec a r1) A ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec r A0 ++ Db) :: L)).
      apply IHpi1.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
    + apply hrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r B ++ Db)).
      { perm_Type_solve. }
      change ((vec (mul_vec a r1) A ++ (vec r B ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec r B ++ Db) :: L)).
      apply IHpi2.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (a *S A) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hrr_can with A0 r s; try assumption.
    apply hrr_ex_seq with (vec (mul_vec a r1) A ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec (mul_vec a r1) A ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.

Lemma hrr_max_inv_gen :
  forall L A B,
    HR_T_M (map (fun x => (vec (fst x) (A \/S B) ++ snd x)) L) ->
    HR_T_M (map (fun x => (vec (fst x) A ++ snd x)) L ++ map (fun x => (vec (fst x) B ++ snd x)) L).
Proof.
  intros L A B.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A \/S B) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A \/S B) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L ; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; inversion X.
    simpl; apply hrr_W; apply hrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_W.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_app_comm | ].
    simpl; apply hrr_W.
    eapply hrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply IHpi.
    assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_C.
    change ((vec (fst p) A ++ snd p) :: (vec (fst p) A  ++ snd p) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ (vec (fst p) B ++ snd p) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p :: p :: L) ++ (vec (fst p) B ++ snd p) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L).
    eapply hrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    simpl; apply hrr_C.
    change ((vec (fst p) B ++ snd p)
              :: (vec (fst p) B ++ snd p)
              :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L ++
              (vec (fst p) A ++ snd p)
              :: (vec (fst p) A ++ snd p)
              :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x)
              L)
      with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (p :: p :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p :: p :: L)).
    eapply hrr_ex_hseq ; [ apply Permutation_Type_app_comm | ].
    apply IHpi.
    simpl.
    do 2 (apply Forall2_Type_cons; try assumption).
  - destruct L; [ | destruct L]; inversion Hperm; inversion X0; subst.
    destruct p as [p1 p2];
      destruct p0 as [p1' p2'];
      remember ((p1 ++ p1'), (p2 ++ p2')) as p'';
      (apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((p1, p2) :: (p1',p2') :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((p1, p2) :: (p1',p2') :: L)) ; [ apply Permutation_Type_app; apply Permutation_Type_map; perm_Type_solve | ]);
      simpl in *;
      apply hrr_S;
      (apply hrr_ex_seq with (vec (fst p'') A ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (fst p'') A ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (L) ++ (vec p1 B ++ p2) :: (vec p1' B ++ p2') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (L))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p'' :: L) ++ (vec p1 B ++ p2) :: (vec p1' B ++ p2') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (L));
      (eapply hrr_ex_hseq ; [ apply Permutation_Type_app_comm | ]);
      simpl; apply hrr_S;
        (apply hrr_ex_seq with (vec (fst p'') B ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
        change ((vec (fst p'') B ++ snd p'')
                  :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (L) ++
                  (vec (fst p'') A ++ snd p'')
                  :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x)
                  (L))
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (p'' :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p'' :: L));
        (eapply hrr_ex_hseq ; [ apply Permutation_Type_app_comm | ]);
        apply IHpi;
        simpl; apply Forall2_Type_cons;
          [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hrr_ex_seq with ((vec r1 A ++ D1) ++ (vec r2 A ++ D2)).
    { transitivity (vec (r1 ++ r2) A ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm| ] ; perm_Type_solve. }
    assert (HR_T_M ((vec r1 A ++ D1) :: (vec r1 B ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as pi11.
    { eapply hrr_ex_hseq ; [ | apply (IHpi1 ((r1, D1) :: L))].
      { perm_Type_solve. }
      simpl.
      apply Forall2_Type_cons; [ | assumption].
      perm_Type_solve. }
    assert (HR_T_M ((vec r2 A ++ D2) :: (vec r2 B ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as pi22.
    { eapply hrr_ex_hseq ; [ | apply (IHpi2 ((r2, D2) :: L))].
      { perm_Type_solve. }
      simpl.
      apply Forall2_Type_cons; [ | assumption].
      perm_Type_solve. }
    assert (HR_T_M ((vec r2 A ++ D2) :: (vec r1 B ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as pi21.
    { destruct r1 ; [ | destruct r2 ].
      - apply hrr_W; apply hrr_C.
        apply pi11.
      - eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
        apply hrr_W; apply hrr_C.
        apply pi22.
      - apply hrr_C.
        change (hr_frag_T_M) with (hr_frag_add_T hr_frag_T_M); apply hrr_T_vec with (r0 :: r1); try now auto.
        apply hrr_ex_hseq with ( (vec (r0 :: r1) B ++ D1) 
                                   :: (vec (r2 :: r3) A ++ D2)
                                   :: seq_mul_vec (r0 :: r1) (vec (r2 :: r3) A ++ D2)
                                   :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++
                                   map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L).
        { etransitivity ; [ apply Permutation_Type_swap | etransitivity ; [ | apply Permutation_Type_swap ]].
          apply Permutation_Type_skip.
          apply Permutation_Type_swap. }
        apply hrr_C;try reflexivity; change (hr_frag_T_M) with (hr_frag_add_T hr_frag_T_M); apply hrr_T_vec with (r2 :: r3); try now auto.
        eapply hrr_ex_hseq ; [ apply Permutation_Type_skip; etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
        apply hrr_S.
        apply hrr_ex_seq with (seq_mul_vec (r2 :: r3) (vec (r0 :: r1) A ++ D1) ++ seq_mul_vec (r0 :: r1) (vec (r2 :: r3) B ++ D2)).
        { etransitivity ; [ apply Permutation_Type_app; apply seq_mul_vec_app_r | ].
          etransitivity ; [ | apply Permutation_Type_app; symmetry; apply seq_mul_vec_app_r].
          etransitivity ; [ apply Permutation_Type_app; (apply Permutation_Type_app ; [ apply seq_mul_vec_vec | reflexivity ] ) | ].
          perm_Type_solve. }
        apply hrr_M; try reflexivity.
        + change hr_frag_T_M with (hr_frag_add_T (hr_frag_add_M hr_frag_T_M)); apply hrr_T_vec_inv.
          eapply hrr_ex_hseq ; [ etransitivity ; [apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
          apply hrr_W.
          apply pi11.
        + change hr_frag_T_M with (hr_frag_add_T (hr_frag_add_M hr_frag_T_M)); apply hrr_T_vec_inv.
          eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
          apply hrr_W.
          eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
          apply pi22. }
    assert (HR_T_M ((vec r1 A ++ D1) :: (vec r2 B ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as pi12.
    { destruct r1 ; [ | destruct r2 ].
      - eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
        apply hrr_W; apply hrr_C.
        apply pi11.
      - apply hrr_W; apply hrr_C.
        apply pi22.
      - apply hrr_C.
        change (hr_frag_T_M) with (hr_frag_add_T hr_frag_T_M); apply hrr_T_vec with (r2 :: r3); try now auto.
        eapply hrr_ex_hseq ; [ etransitivity ; [ apply Permutation_Type_swap | etransitivity ; [ apply Permutation_Type_skip; apply Permutation_Type_swap | apply Permutation_Type_swap ]] | ].
        apply hrr_C;try reflexivity; change (hr_frag_T_M) with (hr_frag_add_T hr_frag_T_M); apply hrr_T_vec with (r0 :: r1); try now auto.
        eapply hrr_ex_hseq ; [ apply Permutation_Type_skip; etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
        apply hrr_S.
        apply hrr_ex_seq with (seq_mul_vec (r2 :: r3) (vec (r0 :: r1) B ++ D1) ++ seq_mul_vec (r0 :: r1) (vec (r2 :: r3) A ++ D2)).
        { etransitivity ; [ apply Permutation_Type_app; apply seq_mul_vec_app_r | ].
          etransitivity ; [ | apply Permutation_Type_app; symmetry; apply seq_mul_vec_app_r].
          etransitivity ; [ apply Permutation_Type_app; (apply Permutation_Type_app ; [ apply seq_mul_vec_vec | reflexivity ] ) | ].
          perm_Type_solve. }
        apply hrr_M; try reflexivity.
        + change hr_frag_T_M with (hr_frag_add_T (hr_frag_add_M hr_frag_T_M)); apply hrr_T_vec_inv.
          eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
          apply hrr_W.
          eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
          apply pi11.
        + change hr_frag_T_M with (hr_frag_add_T (hr_frag_add_M hr_frag_T_M)); apply hrr_T_vec_inv.
          eapply hrr_ex_hseq ; [ etransitivity ; [apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
          apply hrr_W.
          apply pi22. }
    eapply hrr_ex_hseq ; [ apply Permutation_Type_skip; apply Permutation_Type_middle | ].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with ((vec r1 B ++ D1) ++ (vec r2 B ++ D2)).
    { transitivity (vec (r1 ++ r2) B ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm| ] ; perm_Type_solve. }
    apply hrr_M; try reflexivity ; (eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]); apply hrr_M; try reflexivity; try assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    rewrite seq_mul_app; rewrite seq_mul_vec_mul_vec.
    eapply hrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hrr_T with r; try assumption.
    rewrite seq_mul_app; rewrite seq_mul_vec_mul_vec.
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((mul_vec r r', seq_mul r T') :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((mul_vec r r', seq_mul r T') :: L)).
    { etransitivity ; [ apply Permutation_Type_app_comm | simpl; apply Permutation_Type_skip].
      reflexivity. }
    apply IHpi.      
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    rewrite <- seq_mul_vec_mul_vec; rewrite <- seq_mul_app.
    apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> (covar n)) as Hnc by now auto.
    assert (A \/S B <> (var n)) as Hnv by now auto.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hrr_ID; try assumption.
    eapply hrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hrr_ID; try assumption.
    eapply hrr_ex_hseq; [ |  apply (IHpi ((r1 , Db) :: L))].
    { simpl.
      perm_Type_solve. }
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> zero) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r zero ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hrr_Z; try assumption.
    eapply hrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hrr_ex_seq with (vec r zero ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hrr_Z; try assumption.
    eapply hrr_ex_hseq; [ |  apply (IHpi ((r1 , Db) :: L))].
    { simpl.
      perm_Type_solve. }
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> A0 +S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hrr_plus; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ (vec r A0 ++ vec r B0 ++ Db)) ; [ perm_Type_solve | ].
    eapply hrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hrr_plus; try assumption.
    apply hrr_ex_seq with (vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)) ; [ perm_Type_solve | ].
    eapply hrr_ex_hseq; [ |  apply (IHpi ((r1 , vec r A0 ++ vec r B0 ++ Db) :: L))].
    { simpl.
      perm_Type_solve. }
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> r0 *S A0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ (vec (mul_vec r0 r) A0 ++ Db)) ; [ perm_Type_solve | ].
    eapply hrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)) ; [ perm_Type_solve | ].
    eapply hrr_ex_hseq; [ |  apply (IHpi ((r1 , vec (mul_vec r0 r) A0 ++ Db) :: L))].
    { simpl.
      perm_Type_solve. }
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    case (term_eq_dec (A \/S B) (A0 \/S B0)).
    + intros H; inversion H; subst.
      destruct (perm_decomp_vec_eq _ _ _ _ _ X) as [ [[[[a1 b1] c1] T'] D'] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec c1 (A0 \/S B0) ++ vec (a1 ++ b1) A0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      apply hrr_max.
      apply hrr_W.
      apply hrr_ex_seq with (vec a1 A0 ++ (vec r A0 ++ T')).
      { transitivity (vec a1 A0 ++ (vec (b1 ++ c1) A0 ++ T')); [ apply Permutation_Type_app ; [ reflexivity | ] ;try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve | ].
        rewrite ? vec_app.
        perm_Type_solve. }
      eapply hrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ]; simpl.
      apply hrr_ex_seq with (vec c1 (A0 \/S B0) ++ vec (a1 ++ b1) B0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      apply hrr_max.
      eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hrr_W.
      apply hrr_ex_seq with (vec a1 B0 ++ (vec r B0 ++ T')).
      { transitivity (vec a1 B0 ++ (vec (b1 ++ c1) B0 ++ T')); [ apply Permutation_Type_app ; [ reflexivity | ] ;try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve | ].
        rewrite ? vec_app.
        perm_Type_solve. }
      eapply hrr_ex_hseq ; [ etransitivity ; [ apply Permutation_Type_middle | symmetry; rewrite app_comm_cons; symmetry; apply Permutation_Type_app_comm ] | ].
      simpl; apply C_A_B.
      eapply hrr_ex_hseq ; [ etransitivity ; [ apply Permutation_Type_skip; apply Permutation_Type_swap | apply Permutation_Type_swap ] | ].
      eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
      simpl; apply C_A_B.
      eapply hrr_ex_hseq ; [ | apply (IHpi ((a1, vec r B0 ++ T') :: (a1, vec r A0 ++ T') :: L))].
      { simpl.
        do 2 (apply Permutation_Type_skip).
        etransitivity ; [ apply Permutation_Type_app_comm | ].
        simpl; do 2 (apply Permutation_Type_skip).
        apply Permutation_Type_app_comm. }
      simpl.
      apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | assumption]]; perm_Type_solve.    
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 A ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hrr_max; try assumption.
      apply hrr_ex_seq with (vec r1 A ++ (vec r B0 ++ Db)).
      { perm_Type_solve. }
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hrr_ex_seq with (vec r1 A ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      rewrite 2 app_comm_cons.
      eapply hrr_ex_hseq;  [ apply Permutation_Type_app_comm | ].
      simpl;apply hrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 B ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hrr_max; try assumption.
      apply hrr_ex_seq with (vec r1 B ++ (vec r B0 ++ Db)).
      { perm_Type_solve. }
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hrr_ex_seq with (vec r1 B ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      eapply hrr_ex_hseq ; [ | apply (IHpi ((r1, vec r B0 ++ Db) :: (r1 , vec r A0 ++ Db) :: L)) ].
      { etransitivity ; [ apply Permutation_Type_app_comm | ].
        rewrite ? app_comm_cons.
        apply Permutation_Type_app; simpl; apply Permutation_Type_swap. }        
      simpl.
      apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | assumption] ]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> A0 /\S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    assert (HR_T_M ((vec r1 A ++ vec r A0 ++ Db) :: (vec r1 B ++ vec r A0 ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as piAA.
    { eapply hrr_ex_hseq ; [ | apply (IHpi1 ((r1 , vec r A0 ++ Db) :: L)) ].
      { simpl.
        apply Permutation_Type_skip.
        etransitivity; [ apply Permutation_Type_app_comm | ].
        simpl; apply Permutation_Type_skip.
        apply Permutation_Type_app_comm. }
      simpl.
      apply Forall2_Type_cons; [ |  assumption]; perm_Type_solve. }
    assert (HR_T_M ((vec r1 A ++ vec r B0 ++ Db) :: (vec r1 B ++ vec r B0 ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as piBB.
    { eapply hrr_ex_hseq ; [ | apply (IHpi2 ((r1 , vec r B0 ++ Db) :: L)) ].
      { simpl.
        apply Permutation_Type_skip.
        etransitivity; [ apply Permutation_Type_app_comm | ].
        simpl; apply Permutation_Type_skip.
        apply Permutation_Type_app_comm. }
      simpl.
      apply Forall2_Type_cons; [ |  assumption]; perm_Type_solve. }
    assert (HR_T_M ((vec r1 A ++ vec r A0 ++ Db) :: (vec r1 B ++ vec r B0 ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as piAB.
    { apply hrr_C.
      eapply hrr_ex_hseq; [ etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
      apply hrr_C.
      eapply hrr_ex_hseq; [ etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
      apply hrr_S.
      apply hrr_ex_seq with ((vec r1 A ++ vec r B0 ++ Db) ++ (vec r1 B ++ vec r A0 ++ Db)).
      { rewrite <- ? app_assoc.
        apply Permutation_Type_app; try reflexivity.
        rewrite ? app_assoc; apply Permutation_Type_app; try reflexivity.
        etransitivity ; [ | apply Permutation_Type_app_comm].
        perm_Type_solve. }
      apply hrr_M; try reflexivity; [ eapply hrr_ex_hseq ;
                                      [ etransitivity ;
                                        [ apply Permutation_Type_swap |
                                          apply Permutation_Type_skip; apply Permutation_Type_swap ] |];
                                      apply hrr_W |
                                      eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ];
                                      apply hrr_W;
                                      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap  | ] ]; try assumption. }
    assert (HR_T_M ((vec r1 A ++ vec r B0 ++ Db) :: (vec r1 B ++ vec r A0 ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as piBA.
    { apply hrr_C.
      eapply hrr_ex_hseq; [ etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
      apply hrr_C.
      eapply hrr_ex_hseq; [ etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
      apply hrr_S.
      apply hrr_ex_seq with ((vec r1 A ++ vec r A0 ++ Db) ++ (vec r1 B ++ vec r B0 ++ Db)).
      { rewrite <- ? app_assoc.
        apply Permutation_Type_app; try reflexivity.
        rewrite ? app_assoc; apply Permutation_Type_app; try reflexivity.
        etransitivity ; [ | apply Permutation_Type_app_comm].
        perm_Type_solve. }
      apply hrr_M; try reflexivity; [ eapply hrr_ex_hseq ;
                                      [ etransitivity ;
                                        [ apply Permutation_Type_swap |
                                          apply Permutation_Type_skip; apply Permutation_Type_swap ] |];
                                      apply hrr_W |
                                      eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ];
                                      apply hrr_W;
                                      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap  | ] ]; try assumption. }
    eapply hrr_ex_hseq; [ apply Permutation_Type_skip; apply Permutation_Type_middle | ].
    apply hrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 A ++ Db); [ perm_Type_solve | ].
    apply hrr_min;
      (eapply hrr_ex_seq with (vec r1 A ++ vec r _ ++ Db) ; [ rewrite ? app_assoc; apply Permutation_Type_app; try apply Permutation_Type_app_comm; try reflexivity | ]);
      (eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ]);
      (apply hrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 B ++ Db); [ perm_Type_solve | ]);
      apply hrr_min;
      (eapply hrr_ex_seq with (vec r1 B ++ vec r _ ++ Db) ; [ rewrite ? app_assoc; apply Permutation_Type_app; try apply Permutation_Type_app_comm; try reflexivity | ]);
      (eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ]);
      assumption.
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A \/S B) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_app; apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hrr_can with A0 r s; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    rewrite app_comm_cons.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_app_comm | ].
    simpl; apply hrr_can with A0 r s; try assumption.
    apply hrr_ex_seq with (vec r1 B ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    eapply hrr_ex_hseq; [ | apply (IHpi ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L))].
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      reflexivity. }
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.
    
Lemma hrr_min_inv_gen_l : forall L A B,
    HR_T_M (map (fun x => (vec (fst x) (A /\S B) ++ snd x)) L) ->
    HR_T_M (map (fun x => (vec (fst x) A ++ snd x)) L).
Proof.
  intros L A B.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; inversion X.
    apply hrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_W.
    apply IHpi.
    assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_C.
    change ((vec (fst p) A ++ snd p)
              :: (vec (fst p) A ++ snd p)
              :: map
              (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x)
              L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x)
           (p :: p :: L)).
    apply IHpi.
    do 2 (apply Forall2_Type_cons; try assumption).
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [p1 p2];
      destruct p0 as [p1' p2'];
      remember ((p1 ++ p1'), (p2 ++ p2')) as p'';
      (apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((p1, p2) :: (p1',p2') :: L )) ; [ apply Permutation_Type_map; perm_Type_solve | ]);
      simpl in *;
      apply hrr_S;
      (apply hrr_ex_seq with (vec (fst p'') A ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (fst p'') A ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (L ))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p'' :: L ));
      apply IHpi;
      simpl; apply Forall2_Type_cons;
        [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hrr_ex_seq with ((vec r1 A ++ D1) ++ (vec r2 A ++ D2)).
    { transitivity (vec (r1 ++ r2) A ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
    apply hrr_M; try assumption.
    + change ((vec r1 A ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, D1) :: L)).
      apply IHpi1.
      simpl; apply Forall2_Type_cons ; assumption.
    + change ((vec r2 A ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r2, D2) :: L)).
      apply IHpi2.
      simpl; apply Forall2_Type_cons ; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hrr_ex_seq with (vec (mul_vec r r') A ++ seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      repeat (apply Permutation_Type_app; try reflexivity). }
    change ((vec (mul_vec r r') A ++ seq_mul r T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((mul_vec r r', seq_mul r T') :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    rewrite <- seq_mul_vec_mul_vec; rewrite <- seq_mul_app.
    apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> (covar n)) as Hnc by now auto.
    assert (A /\S B <> (var n)) as Hnv by now auto.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hrr_ID; try assumption.
    change ((vec r1 A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> zero) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r zero ++ vec r1 A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_Z; try assumption.
    change ((vec r1 A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> A0 +S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_plus; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ (vec r A0 ++ vec r B0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 A ++ (vec r A0 ++ vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec r A0 ++ vec r B0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> r0 *S A0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ (vec (mul_vec r0 r) A0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 A ++ (vec (mul_vec r0 r) A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec (mul_vec r0 r) A0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> A0 \/S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_max; try assumption.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r1 A ++ (vec r A0 ++ Db)).
    { perm_Type_solve. }
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r1 A ++ (vec r B0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 A ++ (vec r B0 ++ Db)) :: (vec r1 A ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec r B0 ++ Db) :: (r1, vec r A0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | assumption] ]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    case (term_eq_dec (A /\S B) (A0 /\S B0)).
    + intros H; inversion H; subst.
      destruct (perm_decomp_vec_eq _ _ _ _ _ X) as [ [[[[a1 b1] c1] T'] D'] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec c1 (A0 /\S B0) ++ vec (a1 ++ b1) A0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      assert (HR_T_M ((vec a1 A0 ++ (vec r A0  ++ T')) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) L)) as piA.
      { change ((vec a1 A0  ++ vec r A0  ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) L)
          with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) ((a1 , vec r A0 ++ T') :: L)).
        apply IHpi1.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        transitivity (vec (b1 ++ c1) A0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve. }
      assert (HR_T_M ((vec a1 A0 ++ (vec r B0  ++ T')) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) L)) as piB.
      { change ((vec a1 A0  ++ vec r B0  ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) L)
          with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) ((a1 , vec r B0 ++ T') :: L)).
        apply IHpi2.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        transitivity (vec (b1 ++ c1) B0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve. }
      apply hrr_min.
      * apply hrr_ex_seq with (vec a1 A0 ++ (vec r A0  ++ T')).
        { transitivity (vec a1 A0  ++ (vec (b1 ++ c1) A0 ++ T')); [ apply Permutation_Type_app; try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve | ].
          rewrite ? vec_app.
          perm_Type_solve. }
        apply piA.
      * rewrite vec_app.
        apply hrr_ex_seq with (vec c1 B0 ++ vec b1 A0 ++ vec a1 A0 ++ T'); [ perm_Type_solve | ].
        apply mix_A_B.
        -- eapply hrr_ex_seq ; [ | apply piA].
           rewrite ? app_assoc.
           apply Permutation_Type_app; try reflexivity.
           etransitivity; [ apply Permutation_Type_app_comm | ].
           apply Permutation_Type_app ; try reflexivity.
           rewrite <- vec_app.
           apply vec_perm.
           perm_Type_solve.
        -- eapply hrr_ex_seq ; [ | apply piB].
           rewrite ? app_assoc.
           apply Permutation_Type_app; try reflexivity.
           etransitivity; [ apply Permutation_Type_app_comm | ].
           apply Permutation_Type_app ; try reflexivity.
           rewrite <- vec_app.
           apply vec_perm.
           perm_Type_solve.
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 A ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hrr_min; try assumption.
      * apply hrr_ex_seq with (vec r1 A ++ (vec r A0 ++ Db)).
        { perm_Type_solve. }
        change ((vec r1 A ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec r A0 ++ Db) :: L)).
        apply IHpi1.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        perm_Type_solve.
      * apply hrr_ex_seq with (vec r1 A ++ (vec r B0 ++ Db)).
        { perm_Type_solve. }
        change ((vec r1 A ++ (vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec r B0 ++ Db) :: L)).
        apply IHpi2.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hrr_can with A0 r s; try assumption.
    apply hrr_ex_seq with (vec r1 A  ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec r1 A ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.
    
Lemma hrr_min_inv_gen_r : forall L A B,
    HR_T_M (map (fun x => (vec (fst x) (A /\S B) ++ snd x)) L) ->
    HR_T_M (map (fun x => (vec (fst x) B ++ snd x)) L).
Proof.
  intros L A B.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L ; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; inversion X.
    apply hrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_W.
    apply IHpi.
    assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_C.
    change ((vec (fst p) B ++ snd p)
              :: (vec (fst p) B ++ snd p)
              :: map
              (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x)
              L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x)
           (p :: p :: L)).
    apply IHpi.
    do 2 (apply Forall2_Type_cons; try assumption).
  - destruct L ; [ | destruct L]; inversion Hperm; inversion X0; subst.
    destruct p as [p1 p2];
      destruct p0 as [p1' p2'];
      remember ((p1 ++ p1'), (p2 ++ p2')) as p'';
      (apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((p1, p2) :: (p1',p2') :: L )) ; [ apply Permutation_Type_map; perm_Type_solve | ]);
      simpl in *;
      apply hrr_S;
      (apply hrr_ex_seq with (vec (fst p'') B ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (fst p'') B ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (L ))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (p'' :: L ));
      apply IHpi;
      simpl; apply Forall2_Type_cons;
        [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hrr_ex_seq with ((vec r1 B ++ D1) ++ (vec r2 B ++ D2)).
    { transitivity (vec (r1 ++ r2) B ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
    apply hrr_M; try assumption.
    + change ((vec r1 B ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, D1) :: L)).
      apply IHpi1.
      simpl; apply Forall2_Type_cons ; assumption.
    + change ((vec r2 B ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r2, D2) :: L)).
      apply IHpi2.
      simpl; apply Forall2_Type_cons ; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hrr_ex_seq with (vec (mul_vec r r') B ++ seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      repeat (apply Permutation_Type_app; try reflexivity). }
    change ((vec (mul_vec r r') B ++ seq_mul r T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((mul_vec r r', seq_mul r T') :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    rewrite <- seq_mul_vec_mul_vec; rewrite <- seq_mul_app.
    apply seq_mul_perm; assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> (covar n)) as Hnc by now auto.
    assert (A /\S B <> (var n)) as Hnv by now auto.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hrr_ID; try assumption.
    change ((vec r1 B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> zero) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r zero ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_Z; try assumption.
    change ((vec r1 B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> A0 +S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_plus; try assumption.
    apply hrr_ex_seq with (vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec r A0 ++ vec r B0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> r0 *S A0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec (mul_vec r0 r) A0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> A0 \/S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_max; try assumption.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r1 B ++ (vec r A0 ++ Db)).
    { perm_Type_solve. }
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r1 B ++ (vec r B0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 B ++ (vec r B0 ++ Db)) :: (vec r1 B ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec r B0 ++ Db) :: (r1, vec r A0 ++ Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | assumption] ]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    case (term_eq_dec (A /\S B) (A0 /\S B0)).
    + intros H; inversion H; subst.
      destruct (perm_decomp_vec_eq _ _ _ _ _ X) as [ [[[[a1 b1] c1] T'] D'] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec c1 (A0 /\S B0) ++ vec (a1 ++ b1) B0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      assert (HR_T_M ((vec a1 B0 ++ (vec r B0  ++ T')) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) L)) as piB.
      { change ((vec a1 B0  ++ vec r B0  ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) L)
          with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) ((a1 , vec r B0 ++ T') :: L)).
        apply IHpi2.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        transitivity (vec (b1 ++ c1) B0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve. }
      assert (HR_T_M ((vec a1 B0 ++ (vec r A0  ++ T')) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) L)) as piA.
      { change ((vec a1 B0  ++ vec r A0  ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) L)
          with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) ((a1 , vec r A0 ++ T') :: L)).
        apply IHpi1.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        transitivity (vec (b1 ++ c1) A0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve. }
      apply hrr_min.
      * rewrite vec_app.
        apply hrr_ex_seq with (vec c1 A0 ++ vec b1 B0 ++ vec a1 B0 ++ T'); [ perm_Type_solve | ].
        apply mix_A_B.
        -- eapply hrr_ex_seq ; [ | apply piB].
           rewrite ? app_assoc.
           apply Permutation_Type_app; try reflexivity.
           etransitivity; [ apply Permutation_Type_app_comm | ].
           apply Permutation_Type_app ; try reflexivity.
           rewrite <- vec_app.
           apply vec_perm.
           perm_Type_solve.
        -- eapply hrr_ex_seq ; [ | apply piA].
           rewrite ? app_assoc.
           apply Permutation_Type_app; try reflexivity.
           etransitivity; [ apply Permutation_Type_app_comm | ].
           apply Permutation_Type_app ; try reflexivity.
           rewrite <- vec_app.
           apply vec_perm.
           perm_Type_solve.
      * apply hrr_ex_seq with (vec a1 B0 ++ (vec r B0  ++ T')).
        { transitivity (vec a1 B0  ++ (vec (b1 ++ c1) B0 ++ T')); [ apply Permutation_Type_app; try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve | ].
          rewrite ? vec_app.
          perm_Type_solve. }
        apply piB.
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 B ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hrr_min; try assumption.
      * apply hrr_ex_seq with (vec r1 B ++ (vec r A0 ++ Db)).
        { perm_Type_solve. }
        change ((vec r1 B ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec r A0 ++ Db) :: L)).
        apply IHpi1.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        perm_Type_solve.
      * apply hrr_ex_seq with (vec r1 B ++ (vec r B0 ++ Db)).
        { perm_Type_solve. }
        change ((vec r1 B ++ (vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec r B0 ++ Db) :: L)).
        apply IHpi2.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hrr_can with A0 r s; try assumption.
    apply hrr_ex_seq with (vec r1 B  ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec r1 B ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.

Lemma hrr_Z_inv : forall G T r,  HR_T_M ((vec r zero ++ T) :: G) -> HR_T_M (T :: G).
Proof.
  intros G.
  assert ({ L & prod
                  ( G = map (fun x : list Rpos * list (Rpos * term) => vec (fst x) zero ++ snd x) L)
                  ( G =  map (fun x : list Rpos * list (Rpos * term) =>  snd x) L) }) as [L [H1 H2]].
  { induction G.
    - split with nil; split;reflexivity.
    - destruct IHG as [ L [ H1 H2 ] ].
      split with ((nil, a) :: L).
      split; simpl; [rewrite H1 | rewrite H2]; reflexivity. }
  intros T r pi.
  replace (T :: G) with (map (fun x : list Rpos * list (Rpos * term) =>  snd x) ((r , T) :: L)) by (simpl; rewrite H2; reflexivity).
  apply hrr_Z_inv_gen.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hrr_plus_inv : forall G T A B r, HR_T_M ((vec r (A +S B) ++ T) :: G) -> HR_T_M ((vec r A ++ vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  assert ({ L & prod
                  ( G = map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A +S B) ++ snd x) L)
                  ( G =  map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L) }) as [L [H1 H2]].
  { clear - G ; induction G.
    - split with nil; split;reflexivity.
    - destruct IHG as [ L [ H1 H2 ] ].
      split with ((nil, a) :: L).
      split; simpl; [rewrite H1 | rewrite H2]; reflexivity. }
  replace ((vec r A ++ vec r B ++ T) :: G) with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r , T) :: L)) by (simpl; rewrite H2; reflexivity).
  apply hrr_plus_inv_gen.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hrr_mul_inv : forall G T A r0 r, HR_T_M ((vec r (r0 *S A) ++ T) :: G) -> HR_T_M ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
  intros G T A r0 r pi.
  assert ({ L & prod
                  ( G = map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (r0 *S A) ++ snd x) L)
                  ( G =  map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec r0 (fst x)) A ++ snd x) L) }) as [L [H1 H2]].
  { clear - G ; induction G.
    - split with nil; split;reflexivity.
    - destruct IHG as [ L [ H1 H2 ] ].
      split with ((nil, a) :: L).
      split; simpl; [rewrite H1 | rewrite H2]; reflexivity. }
  replace ((vec (mul_vec r0 r) A ++ T) :: G) with (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec r0 (fst x)) A ++ snd x) ((r , T) :: L)) by (simpl; rewrite H2; reflexivity).
  apply hrr_mul_inv_gen.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hrr_max_inv : forall G T A B r, HR_T_M ((vec r (A \/S B) ++ T) :: G) -> HR_T_M ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
Proof.
  intros G T A B r pi.
  assert ({ L & prod
                  ( G = map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A \/S B) ++ snd x) L)
                  (( G =  map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L) *
                   ( G = map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L))}) as [L [H1 [H2 H3]]].
  { clear - G ; induction G.
    - split with nil; repeat split;reflexivity.
    - destruct IHG as [ L [ H1 [H2 H3] ] ].
      split with ((nil, a) :: L).
      repeat split; simpl; [rewrite H1 | rewrite H2 | rewrite H3]; reflexivity. }
  apply hrr_ex_hseq with (G ++ (vec r B ++ T) :: (vec r A ++ T) :: nil) ; [ perm_Type_solve | ].
  change (hr_frag_T_M) with hr_frag_T_M.
  apply hrr_C_gen.
  apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r, T) :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r, T) :: L)).
  { simpl.
    rewrite <- H2; rewrite <- H3.
    perm_Type_solve. }
  apply hrr_max_inv_gen.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hrr_min_inv_l : forall G T A B r, HR_T_M ((vec r (A /\S B) ++ T) :: G) -> HR_T_M ((vec r A ++ T) :: G).
Proof.
Proof.
  intros G T A B r pi.
  assert ({ L & prod
                  ( G = map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L)
                  ( G =  map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L) }) as [L [H1 H2]].
  { clear - G ; induction G.
    - split with nil; split;reflexivity.
    - destruct IHG as [ L [ H1 H2 ] ].
      split with ((nil, a) :: L).
      split; simpl; [rewrite H1 | rewrite H2]; reflexivity. }
  replace ((vec r A ++ T) :: G) with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r , T) :: L)) by (simpl; rewrite H2; reflexivity).
  apply hrr_min_inv_gen_l with B.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hrr_min_inv_r : forall G T A B r, HR_T_M ((vec r (A /\S B) ++ T) :: G) -> HR_T_M ((vec r B ++ T) :: G).
Proof.
Proof.
  intros G T A B r pi.
  assert ({ L & prod
                  ( G = map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L)
                  ( G =  map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L) }) as [L [H1 H2]].
  { clear - G ; induction G.
    - split with nil; split;reflexivity.
    - destruct IHG as [ L [ H1 H2 ] ].
      split with ((nil, a) :: L).
      split; simpl; [rewrite H1 | rewrite H2]; reflexivity. }
  replace ((vec r B ++ T) :: G) with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r , T) :: L)) by (simpl; rewrite H2; reflexivity).
  apply hrr_min_inv_gen_r with A.
  simpl; rewrite <- H1.
  apply pi.
Qed.



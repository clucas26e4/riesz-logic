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
    
Lemma decomp_Allperm : forall M1 M2 T L A,
    Allperm (M1 ++ T :: M2)
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L) ->
    {' (L1, L2, p) : _ &
                     prod (L = L1 ++ p :: L2)
                          ((Allperm M1 (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L1)) *
                           (Allperm M2 (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L2)) *
                           (Permutation_Type T (vec (fst p) A ++ snd p)))}.
Proof.
  induction M1; intros M2 T L A H; destruct L; inversion H; subst.
  - split with (nil, L, p).
    repeat split; try reflexivity; try assumption.
    apply Forall2_Type_nil.
  - destruct (IHM1 M2 T L A X0) as [ [[L1 L2] p'] [HeqL [[H1 H2] H3]]].
    split with ((p :: L1) , L2 , p').
    repeat split; subst; try reflexivity; try assumption.
    apply Forall2_Type_cons; try assumption.
Qed.

Lemma decomp_Allperm_2 : forall M1 M2 M3 T1 T2 L A,
    Allperm (M1 ++ T1 :: M2 ++ T2 :: M3)
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L) ->
    {' (L1, L2, L3, p1, p2) : _ &
                     prod (L = L1 ++ p1 :: L2 ++ p2 :: L3)
                          ((Allperm M1 (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L1)) *
                           (Allperm M2 (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L2)) *
                           (Allperm M3 (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L3)) *
                           (Permutation_Type T1 (vec (fst p1) A ++ snd p1)) *
                           (Permutation_Type T2 (vec (fst p2) A ++ snd p2)))}.
Proof.
  intros M1 M2 M3 T1 T2 L A Hperm.
  destruct (decomp_Allperm M1 (M2 ++ T2 :: M3) T1 L A Hperm) as [ [[L1 L2] p'] [HeqL [[H1 H2] H3]]].
  destruct (decomp_Allperm M2 M3 T2 L2 A H2) as  [ [[L1' L2'] p''] [HeqL' [[H1' H2'] H3']]].
  split with (L1, L1', L2', p', p'').
  repeat split; subst; try assumption; try reflexivity.
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
    
Lemma hrr_plus_inv P : forall L A B,
    HR P (map (fun x => (vec (fst x) (A +S B) ++ snd x)) L) ->
    HR P (map (fun x => (vec (fst x) A ++ vec (fst x) B ++ snd x)) L).
Proof.
  intros L A B.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A +S B) ++ snd x) L) as G.
  assert ({ H & prod (Permutation_Type G H) (Allperm H (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A +S B) ++ snd x) L))}).
  { split with G; split; try reflexivity.
    rewrite <- HeqG.
    clear; induction G; try now constructor. }
  clear HeqG.
  intro pi; revert L X; induction pi; intros L [M [Hperm1 Hperm2]].
  - apply Permutation_Type_length_1_inv in Hperm1; rewrite Hperm1 in Hperm2.
    destruct L; simpl in Hperm2; try now inversion Hperm2.
    destruct L; simpl in Hperm2; try now inversion Hperm2.
    inversion Hperm2; destruct p; simpl in *.
    apply Permutation_Type_nil in X.
    destruct l0; destruct l1; try now inversion X.
    apply hrr_INIT.
  - destruct (in_Type_split T M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    apply hrr_W.
    apply IHpi.
    split with (M1 ++ M2); split.
    + rewrite Heq in Hperm1; apply Permutation_Type_cons_inv with T.
      transitivity (M1 ++ T :: M2); [apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + rewrite map_app; apply Forall2_Type_app; try assumption.
  - destruct (in_Type_split T M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    apply hrr_C; try assumption.
    change ((vec (fst p) A ++ vec (fst p) B ++ snd p)
              :: (vec (fst p) A ++ vec (fst p) B ++ snd p)
              :: map
              (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x)
              (L1 ++ L2))
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x)
           (p :: p :: L1 ++ L2)).
    apply IHpi.
    split with (T :: T :: M1 ++ M2); split.
    + apply Permutation_Type_cons; try reflexivity.
      rewrite Heq in Hperm1; perm_Type_solve.
    + simpl.
      do 2 (apply Forall2_Type_cons; try assumption).
      rewrite map_app; apply Forall2_Type_app; try assumption.
  - destruct (decomp_Permutation_Type_2 _ _ _ _ _ Hperm1) as [[[M1 M2] M3] H].
    destruct H as [H | H];
      rewrite H in Hperm2; rewrite H in Hperm1;
        destruct (decomp_Allperm_2 _ _ _ _ _ _ _ Hperm2) as [[ [[[L1 L2] L3] p ] p'] [ HeqL [[[[H1 H2] H3] H4] H5]]];
        destruct p as [p1 p2];
        destruct p' as [p1' p2'];
        remember ((p1 ++ p1'), (p2 ++ p2')) as p'';
        rewrite HeqL;
        (apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((p1, p2) :: (p1',p2') :: L1 ++ L2 ++ L3)) ; [ apply Permutation_Type_map; perm_Type_solve | ]);
        simpl in *;
        (apply hrr_S ; [ apply f | ]);
        (apply hrr_ex_seq with (vec (fst p'') A ++ vec (fst p'') B ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
        change ((vec (fst p'') A ++ vec (fst p'') B ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2 ++ L3))
          with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p'' :: L1 ++ L2 ++ L3));
        apply IHpi;
        split with ((T1 ++ T2) :: M1 ++ M2 ++ M3);
        (repeat split ;
         [ apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with T2; apply Permutation_Type_cons_inv with T1; perm_Type_solve |
           simpl; apply Forall2_Type_cons;
           [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)] ]).
  - destruct (in_Type_split (T1 ++ T2) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((T1 ++ T2) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in H3 as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hrr_ex_seq with ((vec r1 A ++ vec r1 B ++ D1) ++ (vec r2 A ++ vec r2 B ++ D2)).
    { transitivity (vec (r1 ++ r2) A ++ vec (r1 ++ r2) B ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm; perm_Type_solve | ].
      apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
    apply hrr_M; try assumption.
    + change ((vec r1 A ++ vec r1 B ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, D1) :: L1 ++ L2)).
      apply IHpi1.
      split with (T1 :: M1 ++ M2).
      rewrite Heq in Hperm1; split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (T1 ++ T2).
        etransitivity; [apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl; apply Forall2_Type_cons ; [ | rewrite map_app; apply Forall2_Type_app]; assumption.
    + change ((vec r2 A ++ vec r2 B ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r2, D2) :: L1 ++ L2)).
      apply IHpi2.
      split with (T2 :: M1 ++ M2).
      rewrite Heq in Hperm1; split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (T1 ++ T2).
        etransitivity; [apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl; apply Forall2_Type_cons ; [ | rewrite map_app; apply Forall2_Type_app]; assumption.
  - destruct (in_Type_split T M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    apply hrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hrr_ex_seq with (vec (mul_vec r r') A ++ vec (mul_vec r r') B ++ seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      repeat (apply Permutation_Type_app; try reflexivity). }
    change ((vec (mul_vec r r') A ++ vec (mul_vec r r') B ++ seq_mul r T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((mul_vec r r', seq_mul r T') :: L1 ++ L2)).
    apply IHpi.
    split with (seq_mul r T ::  M1 ++ M2); split.
    + apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with T.
      rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + simpl.
      apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
      rewrite <- seq_mul_vec_mul_vec; rewrite <- seq_mul_app.
      apply seq_mul_perm; assumption.
  - destruct (in_Type_split (vec s (covar n) ++ vec r (var n) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec s (covar n) ++ vec r (var n) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> (covar n)) as Hnc by now auto.
    assert (A +S B <> (var n)) as Hnv by now auto.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 A ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hrr_ID; try assumption.
    change ((vec r1 A ++ vec r1 B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, Db) :: L1 ++ L2)).
    apply IHpi.
    split with (T ::  M1 ++ M2); split.
    + apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec s (covar n) ++ vec r (var n) ++ T).
      rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + simpl.
      apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
      perm_Type_solve.
  - destruct (in_Type_split (vec r zero ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r zero ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> zero) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r zero ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_Z; try assumption.
    change ((vec r1 A ++ vec r1 B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, Db) :: L1 ++ L2)).
    apply IHpi.
    split with (T ::  M1 ++ M2); split.
    + apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec r zero ++ T).
      rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + simpl.
      apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
      perm_Type_solve.
  - destruct (in_Type_split (vec r (A0 +S B0) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r (A0 +S B0) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    case (term_eq_dec (A +S B) (A0 +S B0)).
    + intros H; inversion H; subst.
      destruct (perm_decomp_vec_eq _ _ _ _ _ H3) as [ [[[[a1 b1] c1] T'] D'] [H1' [[[H2' H3'] H4'] H5']]].
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
      change ((vec a1 A0 ++ vec a1 B0 ++ vec r A0 ++ vec r B0 ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ vec (fst x) B0 ++ snd x) (L1 ++ L2))
        with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ vec (fst x) B0 ++ snd x) ((a1 , vec r A0 ++ vec r B0 ++ T') :: L1 ++ L2)).
      apply IHpi.
      split with ((vec r A0 ++ vec r B0 ++ T) ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec r (A0 +S B0) ++ T).
        etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
        transitivity (vec (b1 ++ c1) A0 ++ vec (b1 ++ c1) B0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve.      
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 A ++ vec r1 B ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hrr_plus; try assumption.
      apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)).
      { perm_Type_solve. }
      change ((vec r1 A ++ vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r A0 ++ vec r B0 ++ Db) :: L1 ++ L2)).
      apply IHpi.
      split with ((vec r A0 ++ vec r B0 ++ T) ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec r (A0 +S B0) ++ T).
        rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
        perm_Type_solve.
  - destruct (in_Type_split (vec r (r0 *S A0) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r (r0 *S A0) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> r0 *S A0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)).
    { perm_Type_solve. }
    change ((vec r1 A ++ vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec (mul_vec r0 r) A0 ++ Db) :: L1 ++ L2)).
    apply IHpi.
    split with ((vec (mul_vec r0 r) A0 ++ T) ::  M1 ++ M2); split.
    + apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec r (r0 *S A0) ++ T).
      rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + simpl.
      apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
      perm_Type_solve.
  - destruct (in_Type_split (vec r (A0 \/S B0) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r (A0 \/S B0) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> A0 \/S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
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
    change ((vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)) :: (vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r B0 ++ Db) :: (r1, vec r A0 ++ Db) :: L1 ++ L2)).
    apply IHpi.
    split with ((vec r B0 ++ T) :: (vec r A0 ++ T) ::  M1 ++ M2); split.
    + apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with (vec r (A0 \/S B0) ++ T).
      rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + simpl.
      apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | rewrite map_app; apply Forall2_Type_app; try assumption] ]; perm_Type_solve.
  - destruct (in_Type_split (vec r (A0 /\S B0) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r (A0 /\S B0) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> A0 /\S B0) as Hneq by now auto.
    destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hrr_min; try assumption.
    + apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      change ((vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r A0 ++ Db) :: L1 ++ L2)).
      apply IHpi1.
      split with ((vec r A0 ++ T) ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with (vec r (A0 /\S B0) ++ T).
        rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption]; perm_Type_solve.
    + apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)).
      { perm_Type_solve. }
      change ((vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r B0 ++ Db) :: L1 ++ L2)).
      apply IHpi2.
      split with ((vec r B0 ++ T) ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with (vec r (A0 /\S B0) ++ T).
        rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption]; perm_Type_solve.
  - destruct (in_Type_split T2 M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T2 :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p'] [HeqL [[H1 H2] H3]]].
    apply IHpi.
    split with (M1 ++ T1 :: M2); split.
    + transitivity (T1 :: M1 ++ M2) ; [ | perm_Type_solve ].
      apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with T2.
      rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + rewrite HeqL; rewrite map_app.
      apply Forall2_Type_app; try assumption.
      simpl; apply Forall2_Type_cons; try assumption.
      transitivity T2; assumption.    
  - apply IHpi.
    split with M.
    split; try assumption.
    transitivity H; assumption.
  - destruct (in_Type_split T M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    rewrite HeqL.
    apply hrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p :: L1 ++ L2)).
    { perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hrr_can with A0 r s; try assumption.
    apply hrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec r1 A ++ vec r1 B ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (L1 ++ L2))
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L1 ++ L2)).
    apply IHpi.
    split with ((vec s (-S A0) ++ vec r A0 ++ T) :: M1 ++ M2); split.
    + apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with T.
      rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + simpl.
      apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption]; perm_Type_solve.
Qed.


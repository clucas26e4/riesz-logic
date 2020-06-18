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
        


Require Import Rpos.
Require Import term.
Require Import semantic.
Require Import hseq.
Require Import hr.
Require Import invertibility.
Require Import M_elim.

Require Import CMorphisms.
Require Import List_Type_more.
Require Import Permutation_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Bool_more.
Require Import Lra.

Local Open Scope R_scope.

(* TODO MOVE *)
Lemma sum_vec_perm : forall vr vs,
    Permutation_Type vr vs ->
    sum_vec vr = sum_vec vs.
Proof.
  intros vr vs Hperm; induction Hperm; simpl; nra.
Qed.

Lemma perm_decomp_vec_eq_2 : forall T D r s r' s' A B,
    A <> B ->
    Permutation_Type (vec s' B ++ vec r' A ++ T) (vec s B ++ vec r A ++ D) ->
    {' (a1 , b1 , c1, a2 , b2, c2, T', D') : _ &
                     prod (Permutation_Type r  (a1 ++ b1))
                          ((Permutation_Type r'  (b1 ++ c1)) *
                           (Permutation_Type s  (a2 ++ b2)) *
                           (Permutation_Type s'  (b2 ++ c2)) *
                           (Permutation_Type T (vec a2 B ++ vec a1 A ++ T')) *
                           (Permutation_Type D (vec c2 B ++ vec c1 A ++ D')) *
                           (Permutation_Type T' D')) }.
Proof.
  intros T D r s r' s' A B Hneq Hperm.
  revert s r' r T D A B Hneq Hperm.
  induction s'; [ intros s ; induction s ; [ intros r'; induction r'; [ intros r; induction r | ] | ] | ].
  - intros T D A B Hneq Hperm.
    split with (nil, nil,nil,nil,nil,nil , T , D).
    repeat split; try perm_Type_solve.
  - intros T D A B Hneq Hperm.
    simpl in *.
    destruct (in_Type_split (a , A) T) as [[T1 T2] HeqT].
    { apply Permutation_Type_in_Type with ((a , A) :: vec r A ++ D); try perm_Type_solve.
      left; reflexivity. }
    subst.
    destruct (IHr (T1 ++ T2) D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
    { apply Permutation_Type_cons_inv with (a , A).
      perm_Type_solve. }
    split with ((a :: a1), b1,c1,a2,b2,c2, T' , D').
    repeat split; try perm_Type_solve.
  - intros r T D A B Hneq Hperm; simpl in *.
    case (in_Type_app_or (vec r A) D (a , A)).
    { apply Permutation_Type_in_Type with ((a , A) :: vec r' A ++ T); try perm_Type_solve.
      left; reflexivity. }
    + intros Hin.
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
      destruct X as [vr Hperm'].
      destruct (IHr' vr T D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a , A).
        change ((a , A) :: vec vr A ++ D) with (vec (a :: vr) A ++ D).
        etransitivity ; [ apply Hperm | ].
        apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
      split with (a1, a :: b1, c1, a2, b2, c2, T', D').
      repeat split; simpl; try perm_Type_solve.
    + intros Hin.
      apply in_Type_split in Hin as [[D1 D2] HeqD]; subst.
      destruct (IHr' r T (D1 ++ D2) A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a,  A).
        perm_Type_solve. }
      split with (a1, b1, a :: c1 , a2, b2, c2, T', D').
      simpl; repeat split; try perm_Type_solve.
  - intros r' r T D A B Hneq Hperm; simpl in *.
    assert (In_Type (a , B) T).
    { case (in_Type_app_or (vec r' A) T (a , B)); try (intro H; assumption).
      { apply Permutation_Type_in_Type with ((a, B) :: vec s B ++ vec r A ++ D); try perm_Type_solve.
        left; reflexivity. }
      intro H; exfalso; clear - H Hneq.
      induction r'; simpl in H; inversion H.
      + inversion H0; subst; now apply Hneq.
      + apply IHr'; try assumption. }
    apply in_Type_split in X as [[T1 T2] Heq]; subst.
    destruct (IHs r' r (T1 ++ T2) D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
    { apply Permutation_Type_cons_inv with (a , B).
      perm_Type_solve. }
    split with (a1, b1,c1,a :: a2,b2,c2, T' , D').
    repeat split; try perm_Type_solve.
  - intros s r' r T D A B Hneq Hperm; simpl in *.
    case (in_Type_app_or (vec s B) (vec r A ++ D) (a , B)).
    { apply Permutation_Type_in_Type with ((a, B) :: vec s' B ++ vec r' A ++ T); try perm_Type_solve.
      left; reflexivity. }
    + intros Hin.
      assert { s' & Permutation_Type s (a :: s')}.
      { clear - Hin.
        induction s.
        - inversion Hin.
        - simpl in Hin.
          destruct Hin as [Heq | Hin].
          + inversion Heq; split with s; simpl; reflexivity.
          + specialize (IHs Hin) as [s' Hperm].
            split with (a0 :: s').
            perm_Type_solve. }
      destruct X as [vs Hperm'].
      destruct (IHs' vs r' r T D A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a , B).
        change ((a , B) :: vec vs B ++ vec r A ++  D) with (vec (a :: vs) B ++ vec r A ++ D).
        etransitivity ; [ apply Hperm | ].
        apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
      split with (a1, b1, c1, a2, a::b2, c2, T', D').
      repeat split; simpl; try perm_Type_solve.
    + intros H.
      assert (In_Type (a , B) D) as Hin; [ | clear H].
      { case (in_Type_app_or (vec r A) D (a , B)); [ apply H | | ]; try (intros H0; assumption).
        intro H0; exfalso; clear - H0 Hneq.
        induction r; simpl in H0; inversion H0.
        - inversion H; subst; now apply Hneq.
        - apply IHr; try assumption. }
      apply in_Type_split in Hin as [[D1 D2] HeqD]; subst.
      destruct (IHs' s r' r T (D1 ++ D2) A B Hneq) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]].
      { apply Permutation_Type_cons_inv with (a,  B).
        perm_Type_solve. }
      split with (a1, b1, c1 , a2, b2, a :: c2, T', D').
      simpl; repeat split; try perm_Type_solve.
Qed.

Lemma perm_decomp_vec_neq_2 : forall T D r s r' s' n1 n2,
    n1 <> n2 ->
    Permutation_Type (vec s (covar n1) ++ vec r (var n1) ++ T) (vec s' (covar n2) ++ vec r' (var n2) ++ D) ->
    {' (T', D') : _ &
                          prod (Permutation_Type T (vec s' (covar n2) ++ vec r' (var n2) ++ T'))
                               ((Permutation_Type D (vec s (covar n1) ++ vec r (var n1) ++ D')) *
                                (Permutation_Type T' D'))}.
Proof.
  intros T D r s r' s'.
  revert s r' r T D.
  induction s'; [ intros s ; induction s ; [ intros r' ; induction r' ; [ intros r; induction r | ] | ] | ].
  - intros T D n1 n2 Hneq Hperm.
    split with (T , D).
    simpl in *; repeat split; perm_Type_solve.
  - intros T D n1 n2 Hneq Hperm.
    simpl in *.
    destruct (in_Type_split (a , var n1) D) as [[D1 D2] Heq].
    { apply Permutation_Type_in_Type with ((a, var n1) :: vec r (var n1) ++ T); try perm_Type_solve.
      left; reflexivity. }
    subst.
    destruct (IHr T (D1 ++ D2) n1 n2 Hneq) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , var n1).
      perm_Type_solve. }
    split with (T', D').
    repeat split; try perm_Type_solve.
  - intros r T D n1 n2 Hneq Hperm.
    simpl in *.
    destruct (in_Type_split (a , var n2) T) as [[T1 T2] Heq].
    { case (in_Type_app_or (vec r (var n1)) T (a , var n2)) ; [ apply Permutation_Type_in_Type with ((a, var n2) :: vec r' (var n2) ++ D); [ perm_Type_solve | left; reflexivity ] | | auto ].
      intros H; clear - H Hneq.
      exfalso.
      induction r; simpl in H; inversion H.
      - inversion H0.
        apply Hneq; apply H3.
      - apply IHr; apply X. }
    subst.
    destruct (IHr' r (T1 ++ T2) D n1 n2 Hneq) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , var n2); perm_Type_solve. }
    split with (T', D').
    repeat split; try perm_Type_solve.
  - intros r' r T D n1 n2 Hneq Hperm.
    simpl in *.
    destruct (in_Type_split (a , covar n1) D) as [[D1 D2] Heq].
    { case (in_Type_app_or (vec r' (var n2)) D (a , covar n1)) ; [ apply Permutation_Type_in_Type with ((a, covar n1) :: vec s (covar n1) ++ vec r (var n1) ++ T); [ perm_Type_solve | left; reflexivity ] | | auto ].
      intros H; clear - H Hneq.
      exfalso.
      induction r'; simpl in H; inversion H.
      - inversion H0.
      - apply IHr'; apply X. }
    subst.
    destruct (IHs r' r T (D1 ++ D2) n1 n2 Hneq) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , covar n1); perm_Type_solve. }
    split with (T', D').
    repeat split; try perm_Type_solve.
  - intros s r' r T D n1 n2 Hneq Hperm.
    simpl in *.
    destruct (in_Type_split (a , covar n2) T) as [[T1 T2] Heq].
    { case (in_Type_app_or (vec s (covar n1)) (vec r (var n1) ++ T) (a , covar n2)) ; [ apply Permutation_Type_in_Type with ((a, covar n2) :: vec s' (covar n2) ++ vec r' (var n2) ++ D); [ perm_Type_solve | left; reflexivity ] | | ].
      - intros H; clear - H Hneq.
        exfalso.
        induction s; simpl in H; inversion H.
        + inversion H0.
          apply Hneq; apply H3.
        + apply IHs; apply X.
      - intro H0 ;case (in_Type_app_or (vec r (var n1)) T (a , covar n2)) ; [ apply H0 | | auto ].
        intros H; clear - H Hneq.
        exfalso.
        induction r; simpl in H; inversion H.
        + inversion H0.
        + apply IHr; apply X. }
    subst.
    destruct (IHs' s r' r (T1 ++ T2) D n1 n2 Hneq) as [[T' D'] [H1' [H2' H3']]].
    { apply Permutation_Type_cons_inv with (a , covar n2); perm_Type_solve. }
    split with (T', D').
    repeat split; try perm_Type_solve.
Qed.

Lemma hrr_atomic_can_elim_gen : forall L n,
    Forall_Type (fun x => sum_vec (fst (fst (fst x))) - sum_vec (snd (fst (fst x))) = sum_vec (fst (snd (fst x))) - sum_vec (snd (snd (fst x)))) L ->
    HR_C_S_T (map (fun x => (vec (fst (fst (fst x))) (covar n) ++ vec (snd (fst (fst x))) (var n) ++ snd x)) L) ->
    HR_C_S_T (map (fun x => (vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x)) L).
Proof.
  intros L n H.
  remember (map (fun x => (vec (fst (fst (fst x))) (covar n) ++ vec (snd (fst (fst x))) (var n) ++ snd x)) L) as G.
  assert ({ H & prod (Permutation_Type G H) (Allperm H (map (fun x => (vec (fst (fst (fst x))) (covar n) ++ vec (snd (fst (fst x))) (var n) ++ snd x)) L))}).
  { split with G; split; try reflexivity.
    rewrite <- HeqG.
    clear; induction G; try now constructor. }
  clear HeqG.
  intro pi; revert L H X; induction pi; intros L Hsum [M [Hperm1 Hperm2]].
  - apply Permutation_Type_length_1_inv in Hperm1; rewrite Hperm1 in Hperm2.
    destruct L; simpl in Hperm2; try now inversion Hperm2.
    destruct L; simpl in Hperm2; try now inversion Hperm2.
    inversion Hperm2; destruct p; destruct p ; destruct p; destruct p0; simpl in *.
    apply Permutation_Type_nil in X.
    destruct l1; destruct l2; destruct l0; try now inversion X.
    apply hrr_ID.
    { inversion Hsum; simpl in *.
      nra. }
    apply hrr_INIT.
  - destruct (in_Type_split T M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T :: G); try assumption.
      left; reflexivity. }
    subst.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    apply hrr_W.
    apply IHpi.
    + rewrite HeqL in Hsum; apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2]; inversion Hsum2.
      apply Forall_Type_app; assumption.
    + split with (M1 ++ M2); split.
      * apply Permutation_Type_cons_inv with T.
        transitivity (M1 ++ T :: M2); [apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * rewrite map_app; apply Forall2_Type_app; try assumption.
  - destruct (in_Type_split T M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    apply hrr_C; try assumption.
    change ((vec (fst (snd (fst p))) (covar n) ++ vec (snd (snd (fst p))) (var n) ++ snd p)
              :: (vec (fst (snd (fst p))) (covar n) ++ vec (snd (snd (fst p))) (var n) ++ snd p)
              :: map
              (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x)
              (L1 ++ L2))
      with
        (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x)
           (p :: p :: L1 ++ L2)).
    apply IHpi.
    + subst.
      apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2]; inversion Hsum2.
      repeat (apply Forall_Type_cons); try apply Forall_Type_app; assumption.
    + split with (T :: T :: M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity.
        rewrite Heq in Hperm1; perm_Type_solve.
      * simpl.
        do 2 (apply Forall2_Type_cons; try assumption).
        rewrite map_app; apply Forall2_Type_app; try assumption.
  - destruct (decomp_Permutation_Type_2 _ _ _ _ _ Hperm1) as [[[M1 M2] M3] H].
    destruct H as [H | H];
      rewrite H in Hperm2; rewrite H in Hperm1;
        destruct (decomp_Allperm_2 _ _ _ _ _ _ _ Hperm2) as [[ [[[L1 L2] L3] p ] p'] [ HeqL [[[[H1 H2] H3] H4] H5]]];
        rewrite HeqL;
        (apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: p' :: L1 ++ L2 ++ L3)) ; [ apply Permutation_Type_map; perm_Type_solve | ]);
        destruct p as [[[p1 p2] [p3 p4]] p5];
        destruct p' as [[[p1' p2'] [p3' p4']] p5'];
        simpl in *;
        remember ((((p1 ++ p1'), (p2 ++ p2')) , ((p3 ++ p3') , (p4 ++ p4'))), (p5 ++ p5')) as p'';
        (apply hrr_S ; [ apply f | ]);
        (apply hrr_ex_seq with (vec (fst (snd (fst p''))) (covar n) ++ vec (snd (snd (fst p''))) (var n) ++snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
        change ((vec (fst (snd (fst p''))) (covar n) ++ vec (snd (snd (fst p''))) (var n) ++snd p'') :: map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (L1 ++ L2 ++ L3))
          with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p'' :: L1 ++ L2 ++ L3));
        (apply IHpi ;
         [ subst;
           apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2];
           inversion Hsum2;
           apply Forall_Type_app_inv in X as [X1 Hsum3];
           inversion Hsum3;
           repeat (try apply Forall_Type_cons; try apply Forall_Type_app);
           try assumption;
           simpl in *;
           rewrite ? sum_vec_app;
           nra | ]);
        split with ((T1 ++ T2) :: M1 ++ M2 ++ M3);
        (repeat split ;
         [ apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with T2; apply Permutation_Type_cons_inv with T1; perm_Type_solve |
           simpl; apply Forall2_Type_cons;
           [ rewrite Heqp'';simpl; rewrite ? vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)] ]).
  - inversion f.
  - destruct (in_Type_split T M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    apply hrr_T with r; try assumption.
    destruct p as ([[r1 r2] [s1 s2]] , T'); simpl in *.
    apply hrr_ex_seq with (vec (mul_vec r s1) (covar n) ++ vec (mul_vec r s2) (var n) ++ seq_mul r T').
    { rewrite <- ? seq_mul_vec_mul_vec.
      rewrite ? seq_mul_app.
      reflexivity. }
    change ((vec (mul_vec r s1) (covar n) ++ vec (mul_vec r s2) (var n) ++ seq_mul r T') :: map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (L1 ++ L2))
      with
        (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) ((((mul_vec r r1, mul_vec r r2) , (mul_vec r s1 , mul_vec r s2)), seq_mul r T') :: L1 ++ L2)).
    apply IHpi.
    + subst; apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2].
      inversion Hsum2; simpl in H0.
      apply Forall_Type_cons ; [ | apply Forall_Type_app]; try assumption; simpl.
      rewrite ? mul_vec_sum_vec; nra.
    + split with (seq_mul r T ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with T.
        rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
        rewrite <- ? seq_mul_vec_mul_vec; rewrite <- ? seq_mul_app.
        apply seq_mul_perm; assumption.
  - destruct (in_Type_split (vec s (covar n0) ++ vec r (var n0) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec s (covar n0) ++ vec r (var n0) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    case_eq (n =? n0); [intros Heqn; apply Nat.eqb_eq in Heqn | intros Hneqn; apply Nat.eqb_neq in Hneqn].
    + subst.
      destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
      destruct (perm_decomp_vec_eq_2 T T1 r1 s1 r s (var n0) (covar n0)) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]]; [ now auto | apply H3 | ].
      apply hrr_ex_seq with (vec (c2 ++ s1') (covar n0) ++ vec (c1 ++ r1') (var n0) ++ T').
      { rewrite ? vec_app.
        transitivity (vec s1' (covar n0) ++ vec r1' (var n0) ++ (vec c2 (covar n0) ++ vec c1 (var n0) ++ T')); try perm_Type_solve. }
      change ((vec (c2 ++ s1') (covar n0) ++ vec (c1 ++ r1') (var n0) ++ T')
                :: map
                (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (covar n0) ++ vec (snd (snd (fst x))) (var n0) ++ snd x)
                (L1 ++ L2))
        with
          (map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (covar n0) ++ vec (snd (snd (fst x))) (var n0) ++ snd x)
               ((((a2,a1),(c2 ++ s1', c1 ++ r1')), T')::L1 ++ L2)).
      apply IHpi.
      * apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2].
        inversion Hsum2; simpl in*.
        apply Forall_Type_cons ; [ | apply Forall_Type_app; try assumption].
        simpl; rewrite ? sum_vec_app.
        transitivity (sum_vec c2 + sum_vec s1 - (sum_vec c1 + sum_vec r1)); try nra.
        replace (sum_vec s1) with (sum_vec (a2 ++ b2)).
        2:{ apply sum_vec_perm; perm_Type_solve. }
        replace (sum_vec r1) with (sum_vec (a1 ++ b1)) by (apply sum_vec_perm; perm_Type_solve).
        rewrite ? sum_vec_app.
        replace (sum_vec r) with (sum_vec (b1 ++ c1)) in e by (apply sum_vec_perm; perm_Type_solve).
        replace (sum_vec s) with (sum_vec (b2 ++ c2)) in e by (apply sum_vec_perm; perm_Type_solve).
        rewrite ? sum_vec_app in e.
        nra.
      * split with (T :: M1 ++ M2).
        split.
        -- apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec s (covar n0) ++ vec r (var n0) ++ T).
           etransitivity; [ apply Hperm1 | ]; symmetry; apply Permutation_Type_middle.
        -- simpl; apply Forall2_Type_cons; [ | rewrite map_app;apply Forall2_Type_app; try assumption].
           perm_Type_solve.
    + destruct p as [[[s1 r1] [s1' r1']] T1]; simpl in *.
      subst.
      destruct (perm_decomp_vec_neq_2 T T1 r s r1 s1 n0 n (not_eq_sym Hneqn) H3) as [[T' D'] [H1' [H2' H3']]].
      apply hrr_ex_seq with (vec s (covar n0) ++ vec r (var n0) ++ vec s1' (covar n) ++ vec r1' (var n) ++ T').
      { perm_Type_solve. }
      apply hrr_ID; try assumption.
      change ((vec s1' (covar n) ++ vec r1' (var n) ++ T')
                :: map
                (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                   vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x)
                (L1 ++ L2))
        with
          (map
             (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) =>
                vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x)
             ((((s1,r1),(s1',r1')),T')::L1 ++ L2)).
      apply IHpi.
      * apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2].
        inversion Hsum2.
        apply Forall_Type_cons ; [ | apply Forall_Type_app; try assumption].
        simpl in *; nra.
      * split with (T :: M1 ++ M2).
        split.
        -- apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec s (covar n0) ++ vec r (var n0) ++ T).
           etransitivity; [ apply Hperm1 | ]; symmetry; apply Permutation_Type_middle.
        -- simpl; apply Forall2_Type_cons; [ | rewrite map_app;apply Forall2_Type_app; try assumption].
           perm_Type_solve.      
  - destruct (in_Type_split (vec r zero ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r zero ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (zero <> covar n) as Hnc by now auto.
    assert (zero <> var n) as Hnv by now auto.
    apply Permutation_Type_sym in H3.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r zero ++ vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc.
      repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity; [ apply Permutation_Type_app_comm | ].
      etransitivity ; [ | symmetry; apply H1'].
      apply Permutation_Type_app; perm_Type_solve. }
    apply hrr_Z; try assumption.
    change ((vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (L1 ++ L2))
      with
        (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) ((r1, Db) :: L1 ++ L2)).
    apply IHpi.
    + subst; apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2]; inversion Hsum2.
      apply Forall_Type_cons; [ | apply Forall_Type_app]; simpl in *; try assumption.
    + split with (T ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec r zero ++ T).
        rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
        perm_Type_solve.
  - destruct (in_Type_split (vec r (A +S B) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r (A +S B) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> covar n) as Hnc by now auto.
    assert (A +S B <> var n) as Hnv by now auto.
    apply Permutation_Type_sym in H3.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A +S B) ++ vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      perm_Type_solve. }
    apply hrr_plus; try assumption.
    apply hrr_ex_seq with (vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r A ++ vec r B ++ Db); [ perm_Type_solve | ].
    change ((vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r A ++ vec r B ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (L1 ++ L2))
      with
        (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) ((r1, vec r A ++ vec r B ++ Db) :: L1 ++ L2)).
    apply IHpi.
    + subst; apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2]; inversion Hsum2.
      apply Forall_Type_cons; [ | apply Forall_Type_app]; simpl in *; try assumption.
    + split with ((vec r A ++ vec r B ++ T) ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec r (A +S B) ++ T).
        rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
        perm_Type_solve.
  - destruct (in_Type_split (vec r (r0 *S A) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r (r0 *S A) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (r0 *S A <> covar n) as Hnc by now auto.
    assert (r0 *S A <> var n) as Hnv by now auto.
    apply Permutation_Type_sym in H3.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (r0 *S A) ++ vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      perm_Type_solve. }
    apply hrr_mul; try assumption.
    apply hrr_ex_seq with (vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec (mul_vec r0 r) A ++ Db).
    { perm_Type_solve. }
    change ((vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec (mul_vec r0 r) A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (L1 ++ L2))
      with
        (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) ((r1, vec (mul_vec r0 r) A ++ Db) :: L1 ++ L2)).
    apply IHpi.
    + subst; apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2]; inversion Hsum2.
      apply Forall_Type_cons; [ | apply Forall_Type_app]; simpl in *; try assumption.
    + split with ((vec (mul_vec r0 r) A ++ T) ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons_inv with (vec r (r0 *S A) ++ T).
        rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption].
        perm_Type_solve.
  - destruct (in_Type_split (vec r (A \/S B) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r (A \/S B) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> covar n) as Hnc by now auto.
    assert (A \/S B <> var n) as Hnv by now auto.
    apply Permutation_Type_sym in H3.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A \/S B) ++ vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      perm_Type_solve. }
    apply hrr_max; try assumption.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r A ++ Db).
    { perm_Type_solve. }
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r B ++  Db).
    { perm_Type_solve. }
    change ((vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r B ++ Db) :: (vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (L1 ++ L2))
      with
        (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) ((r1, vec r B ++ Db) :: (r1, vec r A ++ Db) :: L1 ++ L2)).
    apply IHpi.
    + subst; apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2]; inversion Hsum2.
      repeat (try apply Forall_Type_cons; try apply Forall_Type_app); simpl in *; try assumption.
    + split with ((vec r B ++ T) :: (vec r A ++ T) ::  M1 ++ M2); split.
      * apply Permutation_Type_cons; try reflexivity; apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with (vec r (A \/S B) ++ T).
        rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
        symmetry; apply Permutation_Type_middle.
      * simpl.
        apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | rewrite map_app; apply Forall2_Type_app; try assumption] ]; perm_Type_solve.
  - destruct (in_Type_split (vec r (A /\S B) ++ T) M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with ((vec r (A /\S B) ++ T) :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p] [HeqL [[H1 H2] H3]]].
    apply hrr_ex_hseq with (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (p :: L1 ++ L2)).
    { rewrite HeqL; perm_Type_solve. }
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> covar n) as Hnc by now auto.
    assert (A /\S B <> var n) as Hnv by now auto.
    apply Permutation_Type_sym in H3.
    destruct (perm_decomp_vec_ID_case _ _ _ _ _ _ _ Hnc Hnv H3) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hrr_ex_seq with (vec r (A /\S B) ++ vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ Db).
    { etransitivity ; [ apply Permutation_Type_app_comm | ]; rewrite <- ? app_assoc; repeat (try apply Permutation_Type_app; try reflexivity).
      etransitivity ; [ | symmetry; apply H1' ].
      etransitivity ; [ apply Permutation_Type_app_comm | ].
      perm_Type_solve. }
    apply hrr_min; try assumption.
    + apply hrr_ex_seq with (vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r A ++ Db).
      { perm_Type_solve. }
      change ((vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r A ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (L1 ++ L2))
        with
          (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) ((r1, vec r A ++ Db) :: L1 ++ L2)).
      apply IHpi1.
      * subst; apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2]; inversion Hsum2.
        repeat (try apply Forall_Type_cons; try apply Forall_Type_app); simpl in *; try assumption.
      * split with ((vec r A ++ T) ::  M1 ++ M2); split.
        -- apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with (vec r (A /\S B) ++ T).
           rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
           symmetry; apply Permutation_Type_middle.
        -- simpl.
           apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption]; perm_Type_solve.
    + apply hrr_ex_seq with (vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r B ++ Db).
      { perm_Type_solve. }
      change ((vec (fst (snd r1)) (covar n) ++ vec (snd (snd r1)) (var n) ++ vec r B ++ Db) :: map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) (L1 ++ L2))
        with
          (map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) ((r1, vec r B ++ Db) :: L1 ++ L2)).
      apply IHpi2.
      * subst; apply Forall_Type_app_inv in Hsum as [Hsum1 Hsum2]; inversion Hsum2.
        repeat (try apply Forall_Type_cons; try apply Forall_Type_app); simpl in *; try assumption.
      * split with ((vec r B ++ T) ::  M1 ++ M2); split.
        -- apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with (vec r (A /\S B) ++ T).
           rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
           symmetry; apply Permutation_Type_middle.
        -- simpl.
           apply Forall2_Type_cons; [ | rewrite map_app; apply Forall2_Type_app; try assumption]; perm_Type_solve.
  - destruct (in_Type_split T2 M) as [[M1 M2] Heq].
    { apply Permutation_Type_in_Type with (T2 :: G); try assumption.
      left; reflexivity. }
    rewrite Heq in Hperm2.
    destruct (decomp_Allperm _ _ _ _ _ Hperm2) as [ [[L1 L2] p'] [HeqL [[H1 H2] H3]]].
    apply IHpi; try assumption.
    split with (M1 ++ T1 :: M2); split.
    + transitivity (T1 :: M1 ++ M2) ; [ | perm_Type_solve ].
      apply Permutation_Type_cons; try reflexivity ; apply Permutation_Type_cons_inv with T2.
      rewrite Heq in Hperm1; etransitivity; [ apply Hperm1 | ].
      symmetry; apply Permutation_Type_middle.
    + rewrite HeqL; rewrite map_app.
      apply Forall2_Type_app; try assumption.
      simpl; apply Forall2_Type_cons; try assumption.
      transitivity T2; assumption.    
  - apply IHpi; try assumption.
    split with M.
    split; try assumption.
    transitivity H; assumption.
  - inversion f.
Qed.
  
Lemma hrr_atomic_can_elim : forall G T n r s,
    sum_vec r = sum_vec s ->
    HR_C_S_T ((vec s (covar n) ++ vec r (var n) ++ T) :: G) ->
    HR_C_S_T (T :: G).
Proof.
  intros G T n r s Heq pi.
  assert ({ L & prod
                  ( G = map (fun x  => vec (fst (fst (fst x))) (covar n) ++ vec (snd (fst (fst x))) (var n) ++ snd x) L)
                  (( G =  map (fun x  => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) L) *
                   (Forall_Type
                      (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => sum_vec (fst (fst (fst x))) - sum_vec (snd (fst (fst x))) = sum_vec (fst (snd (fst x))) - sum_vec (snd (snd (fst x))))  L))}) as [L [H1 [H2 H3]]].
  { clear - G ; induction G.
    - split with nil; repeat split; try reflexivity.
      apply Forall_Type_nil.
    - destruct IHG as [ L [ H1 [H2 H3]] ].
      split with ((((nil,nil),(nil,nil)), a) :: L).
      repeat split; simpl; [rewrite H1 | rewrite H2 | ]; try reflexivity.
      apply Forall_Type_cons; try assumption.
      simpl; nra. }
  rewrite H2.
  change (T :: map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) L) with
      (map (fun x : list Rpos * list Rpos * (list Rpos * list Rpos) * list (Rpos * term) => vec (fst (snd (fst x))) (covar n) ++ vec (snd (snd (fst x))) (var n) ++ snd x) ( (((s , r) , (nil, nil)) , T) :: L)).
  apply hrr_atomic_can_elim_gen.
  - simpl; apply Forall_Type_cons; try assumption; simpl; nra.
  - simpl; rewrite <- H1.
    apply pi.
Qed.

Lemma hrr_can_2 : forall G T A r s,
    sum_vec r = sum_vec s ->
    HR_C_S_T ((vec s (-S A) ++ vec r A ++ T) :: G) ->
    HR_C_S_T (T :: G).
Proof.
  intros G T A; revert G T; induction A; intros G T r' s' Heq pi.
  - apply hrr_atomic_can_elim with n r' s'; try assumption.
  - apply hrr_atomic_can_elim with n s' r'; try nra.
    eapply hrr_ex_seq ; [ | apply pi].
    perm_Type_solve.
  - apply hrr_M_elim.
    apply hrr_Z_inv with r'.
    apply hrr_Z_inv with s'.
    apply HR_le_frag with (hr_frag_C_S_T); auto.
    repeat split.
  - apply (IHA1 G T r' s' Heq).
    apply (IHA2 G (vec s' (-S A1) ++ vec r' A1 ++ T) r' s' Heq).
    apply hrr_M_elim.
    apply hrr_ex_seq with (vec r' A1 ++ vec r' A2 ++ vec s' (-S A2) ++ vec s' (-S A1) ++ T); [ perm_Type_solve | ].
    apply hrr_plus_inv.
    apply hrr_ex_seq with (vec s' (-S A1) ++ vec s' (-S A2) ++ vec r' (A1 +S A2) ++ T); [ perm_Type_solve | ].
    apply hrr_plus_inv.
    apply HR_le_frag with hr_frag_C_S_T; try assumption.
    repeat split.
  - apply (IHA G T (mul_vec r r') (mul_vec r s')).
    { rewrite ? mul_vec_sum_vec; nra. }
    apply hrr_M_elim.
    apply hrr_mul_inv.
    apply hrr_ex_seq with (vec (mul_vec r r') A ++ vec s' (r *S (-S A)) ++ T) ; [ perm_Type_solve | ].
    apply hrr_mul_inv.
    apply HR_le_frag with hr_frag_C_S_T; try (repeat split).
    eapply hrr_ex_seq ; [ | apply pi].
    perm_Type_solve.
  - apply hrr_C; try reflexivity.
    apply (IHA2 (T :: G) T r' s' Heq).
    eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply (IHA1 ((vec s' (-S A2) ++ vec r' A2 ++ T) :: G) T r' s' Heq).
    apply hrr_M_elim.
    apply hrr_min_inv_l with (-S A2).
    apply hrr_ex_seq with (vec r' A1 ++ vec s' (-S (A1 \/S A2)) ++ T); [perm_Type_solve | ].
    eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply hrr_min_inv_r with (-S A1).
    apply hrr_ex_seq with (vec r' A2 ++ vec s' (-S (A1 \/S A2)) ++ T); [perm_Type_solve | ].
    apply hrr_max_inv.
    apply HR_le_frag with hr_frag_C_S_T; try (repeat split).
    eapply hrr_ex_seq ; [ | apply pi].
    perm_Type_solve.
  - apply hrr_C; try reflexivity.
    apply (IHA2 (T :: G) T r' s' Heq).
    eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply (IHA1 ((vec s' (-S A2) ++ vec r' A2 ++ T) :: G) T r' s' Heq).
    apply hrr_M_elim.
    apply hrr_ex_seq with (vec r' A1 ++ vec s' (-S A1) ++ T); [ perm_Type_solve | ].
    apply hrr_min_inv_l with A2.
    apply hrr_ex_seq with (vec s' (-S A1) ++ vec r' (A1 /\S A2) ++ T); [perm_Type_solve | ].
    eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
    apply hrr_ex_seq with (vec r' A2 ++ vec s' (-S A2) ++ T); [ perm_Type_solve | ].
    apply hrr_min_inv_r with A1.
    apply hrr_ex_seq with (vec s' (-S A2) ++ vec r' (A1 /\S A2) ++ T); [perm_Type_solve | ].
    apply hrr_max_inv.
    apply HR_le_frag with hr_frag_C_S_T; try (repeat split).
    apply pi.
Qed.

Lemma hrr_can_elim : forall G,
    HR_full G ->
    HR_C_S_T_M G.
Proof.
  intros G pi; induction pi; try now constructor.
  - now apply hrr_T with r.
  - now apply hrr_ex_seq with T1.
  - now apply hrr_ex_hseq with G.
  - apply HR_le_frag with hr_frag_C_S_T; try repeat split.
    apply hrr_can_2 with A r s; try assumption.
    apply hrr_M_elim.
    apply IHpi.
Qed.

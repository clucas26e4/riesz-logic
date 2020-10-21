(** * Implementation of the Section 4.5 *)
Require Import Rpos.
Require Import term.
Require Import semantic.
Require Import hseq.
Require Import hmr.
Require Import hmr_perm_lemmas.
Require Import tech_lemmas.

Require Import CMorphisms.
Require Import List_Type_more.
Require Import Permutation_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Bool_more.
Require Import Lra.

(** * Generalized version of the invertibilty of the logical rules *)
(** L is a list of pair of a vector r_i and a sequent T_i.

map takes a function f and a list (l_0,...,l_n) and return the list (f (l_0),...,f (l_n).

(map (fun x => (vec (fst x) zero ++ snd x)) L) is thus the hypersequent (|- \vec{r_0}.0, T_0 | ... | |- \vec{r_n}.0, T_n) *)
Lemma hmrr_Z_inv_gen P : forall L,
    HMR P (map (fun x => (vec (fst x) zero ++ snd x)) L) ->
    HMR P (map (fun x => (snd x)) L).
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
    apply hmrr_INIT.
  - destruct L; try now inversion Hperm.
    simpl; apply hmrr_W.
    apply IHpi.
    simpl in Hperm; now inversion Hperm.
  - destruct L; try now inversion Hperm.
    simpl; apply hmrr_C.
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
    simpl; apply hmrr_S.
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
    apply hmrr_ex_seq with (D1 ++ D2).
    { perm_Type_solve. }
    apply hmrr_M; try assumption.
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
    apply hmrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hmrr_ex_seq with (seq_mul r T').
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
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ Db).
    { perm_Type_solve. }
    apply hmrr_ID; try assumption.
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
    apply hmrr_ex_seq with (vec c1 zero ++ T').
    { perm_Type_solve. }
    apply hmrr_Z.
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
    apply hmrr_ex_seq with (vec r (A +S B) ++ Db).
    { perm_Type_solve. }
    apply hmrr_plus; try assumption.
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
    apply hmrr_ex_seq with (vec r (r0 *S A) ++ Db).
    { perm_Type_solve. }
    apply hmrr_mul; try assumption.
    apply hmrr_ex_seq with (vec (mul_vec r0 r) A ++ Db).
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
    apply hmrr_ex_seq with (vec r (A \/S B) ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_max; try assumption.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r A ++ Db).
    { perm_Type_solve. }
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r B ++ Db).
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
    apply hmrr_ex_seq with (vec r (A /\S B) ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_min; try assumption.
    + apply hmrr_ex_seq with (vec r A ++ Db).
      { perm_Type_solve. }
      change ((vec r A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec r A ++ Db) :: L)).
      apply IHpi1.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
    + apply hmrr_ex_seq with (vec r B ++ Db).
      { perm_Type_solve. }
      change ((vec r B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec r B ++ Db) :: L)).
      apply IHpi2.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (zero <> coone) as Hnc by now auto.
    assert (zero <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ Db).
    { perm_Type_solve. }
    apply hmrr_one; try assumption.
    change (Db :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [r1 T1]; simpl in *.
    assert (zero <> coone) as Hnc by now auto.
    assert (zero <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ Db) ; [ perm_Type_solve | ].
    apply seq_diamond_perm_decomp in H1' as [D' H1'].
    apply seq_diamond_app_inv in H1' as [[Da' Db'] [HD' [HDa' HDb']]]; subst.
    apply seq_diamond_perm_decomp in H5' as [Db'' H5']; subst.
    apply hmrr_diamond; try assumption.
    destruct r1.
    2:{ symmetry in H4'; apply seq_diamond_perm_decomp in H4' as [D' H'].
        destruct D'; inversion H'. }
    change ((vec s coone ++ vec r one ++ Db'') :: nil)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((nil, vec s coone ++ vec r one ++ Db'') :: nil)).
    apply IHpi.
    apply Forall2_Type_cons ; [ | apply Forall2_Type_nil].
    simpl.
    apply Permutation_Type_app; try reflexivity.
    apply Permutation_Type_app; try reflexivity.
    simpl in X.
    apply seq_diamond_perm_inv.
    apply Permutation_Type_app_inv_l with (vec r one).
    apply Permutation_Type_app_inv_l with (vec s coone).
    transitivity T1; try assumption.
    etransitivity ; [ apply H2' | ].
    rewrite app_assoc.
    apply Permutation_Type_app; perm_Type_solve.    
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) zero ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hmrr_can with A r s; try assumption.
    apply hmrr_ex_seq with (vec s (-S A) ++ vec r A ++ T1).
    { perm_Type_solve. }
    change ((vec s (-S A) ++ vec r A ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => snd x) ((r1, vec s (-S A) ++ vec r A ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.
    
Lemma hmrr_plus_inv_gen P : forall L A B,
    HMR P (map (fun x => (vec (fst x) (A +S B) ++ snd x)) L) ->
    HMR P (map (fun x => (vec (fst x) A ++ vec (fst x) B ++ snd x)) L).
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
    apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_W.
    apply IHpi.
    assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_C.
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
      (apply hmrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((p1, p2) :: (p1',p2') :: L)) ; [ apply Permutation_Type_map; perm_Type_solve | ]).
    simpl in *;
      apply hmrr_S;
      (apply hmrr_ex_seq with (vec (fst p'') A ++ vec (fst p'') B ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (fst p'') A ++ vec (fst p'') B ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) (p'' :: L));
      apply IHpi;
      simpl; apply Forall2_Type_cons;
        [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hmrr_ex_seq with ((vec r1 A ++ vec r1 B ++ D1) ++ (vec r2 A ++ vec r2 B ++ D2)).
    { transitivity (vec (r1 ++ r2) A ++ vec (r1 ++ r2) B ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm; perm_Type_solve | ].
      apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
    apply hmrr_M; try assumption.
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
    apply hmrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hmrr_ex_seq with (vec (mul_vec r r') A ++ vec (mul_vec r r') B ++ seq_mul r T').
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
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 A ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hmrr_ID; try assumption.
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
    apply hmrr_ex_seq with (vec r zero ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_Z; try assumption.
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
      apply hmrr_ex_seq with (vec c1 (A0 +S B0) ++ vec (a1 ++ b1) A0 ++ vec (a1 ++ b1) B0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      apply hmrr_plus.
      apply hmrr_ex_seq with (vec a1 A0 ++ vec a1 B0 ++ (vec r A0 ++ vec r B0 ++ T')).
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
      apply hmrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 A ++ vec r1 B ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hmrr_plus; try assumption.
      apply hmrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)).
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
    apply hmrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_mul; try assumption.
    apply hmrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)).
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
    apply hmrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_max; try assumption.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)).
    { perm_Type_solve. }
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)).
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
    apply hmrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 A ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_min; try assumption.
    + apply hmrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      change ((vec r1 A ++ vec r1 B ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r A0 ++ Db) :: L)).
      apply IHpi1.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
    + apply hmrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)).
      { perm_Type_solve. }
      change ((vec r1 A ++ vec r1 B ++ (vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec r B0 ++ Db) :: L)).
      apply IHpi2.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> coone) as Hnc by now auto.
    assert (A +S B <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ vec r1 A ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hmrr_one; try assumption.
    change ((vec r1 A ++ vec r1 B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [r1 T1]; simpl in *.
    assert (A +S B <> coone) as Hnc by now auto.
    assert (A +S B <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply seq_diamond_perm_decomp in H1' as [D' H1'].
    apply seq_diamond_app_inv in H1' as [[Da' Db'] [HD' [HDa' HDb']]]; subst.
    apply seq_diamond_perm_decomp in H5' as [Db'' H5']; subst.
    destruct r1.
    2:{ symmetry in H4'; apply seq_diamond_perm_decomp in H4' as [D' H'].
        destruct D'; inversion H'. }
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ seq_diamond Db'') ; [ perm_Type_solve | ].
    apply hmrr_diamond; try assumption.
    change ((vec s coone ++ vec r one ++ Db'') :: nil)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((nil, vec s coone ++ vec r one ++ Db'') :: nil)).
    apply IHpi.
    apply Forall2_Type_cons ; [ | apply Forall2_Type_nil].
    simpl.
    apply Permutation_Type_app; try reflexivity.
    apply Permutation_Type_app; try reflexivity.
    simpl in X.
    apply seq_diamond_perm_inv.
    apply Permutation_Type_app_inv_l with (vec r one).
    apply Permutation_Type_app_inv_l with (vec s coone).
    transitivity T1; try assumption.
    etransitivity ; [ apply H2' | ].
    rewrite app_assoc.
    apply Permutation_Type_app; perm_Type_solve. 
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A +S B) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hmrr_can with A0 r s; try assumption.
    apply hmrr_ex_seq with (vec r1 A ++ vec r1 B ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec r1 A ++ vec r1 B ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ vec (fst x) B ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.
    
Lemma hmrr_mul_inv_gen P : forall L a A,
    HMR P (map (fun x => (vec (fst x) (a *S A) ++ snd x)) L) ->
    HMR P (map (fun x => (vec (mul_vec a (fst x)) A ++ snd x)) L).
Proof with try assumption.
  intros L a A.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (a *S A) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (a *S A) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; try now inversion X.
    apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_W.
    apply IHpi...
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_C.
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
      (apply hmrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((p1, p2) :: (p1',p2') :: L)) ; [ apply Permutation_Type_map; perm_Type_solve | ]);
      simpl in *;
      apply hmrr_S;
      (apply hmrr_ex_seq with (vec (mul_vec a (fst p'')) A ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? mul_vec_app; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (mul_vec a (fst p'')) A ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) (L))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) (p'' :: L));
      apply IHpi;
      simpl; apply Forall2_Type_cons;
         [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hmrr_ex_seq with ((vec (mul_vec a r1) A ++ D1) ++ (vec (mul_vec a r2) A ++ D2)).
    { transitivity (vec (mul_vec a (r1 ++ r2)) A ++ (D1 ++ D2)) ; [rewrite ? mul_vec_app; rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm; apply mul_vec_perm; perm_Type_solve | ].
      perm_Type_solve. }
    apply hmrr_M; try assumption.
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
    apply hmrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hmrr_ex_seq with (vec (mul_vec a (mul_vec r r')) A ++ seq_mul r T').
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
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec (mul_vec a r1) A  ++ Db).
    { perm_Type_solve. }
    apply hmrr_ID; try assumption.
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
    apply hmrr_ex_seq with (vec r zero ++ vec (mul_vec a r1) A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_Z; try assumption.
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
    apply hmrr_ex_seq with (vec r (A0 +S B) ++ vec (mul_vec a r1) A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_plus; try assumption.
    apply hmrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r A0 ++ vec r B ++ Db)).
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
      apply hmrr_ex_seq with (vec c1 (r0 *S A0) ++ vec (mul_vec r0 (a1 ++ b1)) A0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm; apply mul_vec_perm; symmetry; assumption).
        perm_Type_solve. }
      apply hmrr_mul.
      apply hmrr_ex_seq with (vec (mul_vec r0 a1) A0 ++ (vec (mul_vec r0 r) A0 ++ T')).
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
      apply hmrr_ex_seq with (vec r (r0 *S A0) ++ vec (mul_vec a r1) A ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hmrr_mul; try assumption.
      apply hmrr_ex_seq with (vec (mul_vec a r1) A ++ (vec (mul_vec r0 r) A0 ++ Db)).
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
    apply hmrr_ex_seq with (vec r (A0 \/S B) ++ vec (mul_vec a r1) A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_max; try assumption.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r A0 ++ Db)).
    { perm_Type_solve. }
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r B ++ Db)).
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
    apply hmrr_ex_seq with (vec r (A0 /\S B) ++ vec (mul_vec a r1) A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_min; try assumption.
    + apply hmrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      change ((vec (mul_vec a r1) A ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec r A0 ++ Db) :: L)).
      apply IHpi1.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
    + apply hmrr_ex_seq with (vec (mul_vec a r1) A ++ (vec r B ++ Db)).
      { perm_Type_solve. }
      change ((vec (mul_vec a r1) A ++ (vec r B ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
        with
          (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec r B ++ Db) :: L)).
      apply IHpi2.
      simpl.
      apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (a *S A <> coone) as Hnc by now auto.
    assert (a *S A <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ vec (mul_vec a r1) A ++ Db).
    { perm_Type_solve. }
    apply hmrr_one; try assumption.
    change ((vec (mul_vec a r1) A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [r1 T1]; simpl in *.
    assert (a *S A <> coone) as Hnc by now auto.
    assert (a *S A <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply seq_diamond_perm_decomp in H1' as [D' H1'].
    apply seq_diamond_app_inv in H1' as [[Da' Db'] [HD' [HDa' HDb']]]; subst.
    apply seq_diamond_perm_decomp in H5' as [Db'' H5']; subst.
    destruct r1.
    2:{ symmetry in H4'; apply seq_diamond_perm_decomp in H4' as [D' H'].
        destruct D'; inversion H'. }
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ seq_diamond Db'') ; [ perm_Type_solve | ].
    apply hmrr_diamond; try assumption.
    change ((vec s coone ++ vec r one ++ Db'') :: nil)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((nil, vec s coone ++ vec r one ++ Db'') :: nil)).
    apply IHpi.
    apply Forall2_Type_cons ; [ | apply Forall2_Type_nil].
    simpl.
    apply Permutation_Type_app; try reflexivity.
    apply Permutation_Type_app; try reflexivity.
    simpl in X.
    apply seq_diamond_perm_inv.
    apply Permutation_Type_app_inv_l with (vec r one).
    apply Permutation_Type_app_inv_l with (vec s coone).
    transitivity T1; try assumption.
    etransitivity ; [ apply H2' | ].
    rewrite app_assoc.
    apply Permutation_Type_app; perm_Type_solve. 
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (a *S A) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hmrr_can with A0 r s; try assumption.
    apply hmrr_ex_seq with (vec (mul_vec a r1) A ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec (mul_vec a r1) A ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (mul_vec a (fst x)) A ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.

Lemma hmrr_max_inv_gen :
  forall L A B,
    HMR_T_M (map (fun x => (vec (fst x) (A \/S B) ++ snd x)) L) ->
    HMR_T_M (map (fun x => (vec (fst x) A ++ snd x)) L ++ map (fun x => (vec (fst x) B ++ snd x)) L).
Proof.
  intros L A B.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A \/S B) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A \/S B) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L ; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; inversion X.
    simpl; apply hmrr_W; apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_W.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_app_comm | ].
    simpl; apply hmrr_W.
    eapply hmrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    apply IHpi.
    assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_C.
    change ((vec (fst p) A ++ snd p) :: (vec (fst p) A  ++ snd p) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ (vec (fst p) B ++ snd p) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p :: p :: L) ++ (vec (fst p) B ++ snd p) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L).
    eapply hmrr_ex_hseq; [ apply Permutation_Type_app_comm | ].
    simpl; apply hmrr_C.
    change ((vec (fst p) B ++ snd p)
              :: (vec (fst p) B ++ snd p)
              :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L ++
              (vec (fst p) A ++ snd p)
              :: (vec (fst p) A ++ snd p)
              :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x)
              L)
      with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (p :: p :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p :: p :: L)).
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_app_comm | ].
    apply IHpi.
    simpl.
    do 2 (apply Forall2_Type_cons; try assumption).
  - destruct L; [ | destruct L]; inversion Hperm; inversion X0; subst.
    destruct p as [p1 p2];
      destruct p0 as [p1' p2'];
      remember ((p1 ++ p1'), (p2 ++ p2')) as p'';
      (apply hmrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((p1, p2) :: (p1',p2') :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((p1, p2) :: (p1',p2') :: L)) ; [ apply Permutation_Type_app; apply Permutation_Type_map; perm_Type_solve | ]);
      simpl in *;
      apply hmrr_S;
      (apply hmrr_ex_seq with (vec (fst p'') A ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (fst p'') A ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (L) ++ (vec p1 B ++ p2) :: (vec p1' B ++ p2') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (L))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p'' :: L) ++ (vec p1 B ++ p2) :: (vec p1' B ++ p2') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (L));
      (eapply hmrr_ex_hseq ; [ apply Permutation_Type_app_comm | ]);
      simpl; apply hmrr_S;
        (apply hmrr_ex_seq with (vec (fst p'') B ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
        change ((vec (fst p'') B ++ snd p'')
                  :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (L) ++
                  (vec (fst p'') A ++ snd p'')
                  :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x)
                  (L))
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (p'' :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p'' :: L));
        (eapply hmrr_ex_hseq ; [ apply Permutation_Type_app_comm | ]);
        apply IHpi;
        simpl; apply Forall2_Type_cons;
          [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hmrr_ex_seq with ((vec r1 A ++ D1) ++ (vec r2 A ++ D2)).
    { transitivity (vec (r1 ++ r2) A ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm| ] ; perm_Type_solve. }
    assert (HMR_T_M ((vec r1 A ++ D1) :: (vec r1 B ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as pi11.
    { eapply hmrr_ex_hseq ; [ | apply (IHpi1 ((r1, D1) :: L))].
      { perm_Type_solve. }
      simpl.
      apply Forall2_Type_cons; [ | assumption].
      perm_Type_solve. }
    assert (HMR_T_M ((vec r2 A ++ D2) :: (vec r2 B ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as pi22.
    { eapply hmrr_ex_hseq ; [ | apply (IHpi2 ((r2, D2) :: L))].
      { perm_Type_solve. }
      simpl.
      apply Forall2_Type_cons; [ | assumption].
      perm_Type_solve. }
    assert (HMR_T_M ((vec r2 A ++ D2) :: (vec r1 B ++ D1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as pi21.
    { destruct r1 ; [ | destruct r2 ].
      - apply hmrr_W; apply hmrr_C.
        apply pi11.
      - eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
        apply hmrr_W; apply hmrr_C.
        apply pi22.
      - apply hmrr_C.
        change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M); apply hmrr_T_vec with (r0 :: r1); try now auto.
        apply hmrr_ex_hseq with ( (vec (r0 :: r1) B ++ D1) 
                                   :: (vec (r2 :: r3) A ++ D2)
                                   :: seq_mul_vec (r0 :: r1) (vec (r2 :: r3) A ++ D2)
                                   :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++
                                   map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L).
        { etransitivity ; [ apply Permutation_Type_swap | etransitivity ; [ | apply Permutation_Type_swap ]].
          apply Permutation_Type_skip.
          apply Permutation_Type_swap. }
        apply hmrr_C; change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M); apply hmrr_T_vec with (r2 :: r3); try now auto.
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_skip; etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
        apply hmrr_S.
        apply hmrr_ex_seq with (seq_mul_vec (r2 :: r3) (vec (r0 :: r1) A ++ D1) ++ seq_mul_vec (r0 :: r1) (vec (r2 :: r3) B ++ D2)).
        { etransitivity ; [ apply Permutation_Type_app; apply seq_mul_vec_app_r | ].
          etransitivity ; [ | apply Permutation_Type_app; symmetry; apply seq_mul_vec_app_r].
          etransitivity ; [ apply Permutation_Type_app; (apply Permutation_Type_app ; [ apply seq_mul_vec_vec | reflexivity ] ) | ].
          perm_Type_solve. }
        apply hmrr_M; try reflexivity.
        + change hmr_frag_T_M with (hmr_frag_add_T (hmr_frag_add_M hmr_frag_T_M)); apply hmrr_T_vec_inv.
          eapply hmrr_ex_hseq ; [ etransitivity ; [apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
          apply hmrr_W.
          apply pi11.
        + change hmr_frag_T_M with (hmr_frag_add_T (hmr_frag_add_M hmr_frag_T_M)); apply hmrr_T_vec_inv.
          eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
          apply hmrr_W.
          eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
          apply pi22. }
    assert (HMR_T_M ((vec r1 A ++ D1) :: (vec r2 B ++ D2) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as pi12.
    { destruct r1 ; [ | destruct r2 ].
      - eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
        apply hmrr_W; apply hmrr_C.
        apply pi11.
      - apply hmrr_W; apply hmrr_C.
        apply pi22.
      - apply hmrr_C.
        change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M); apply hmrr_T_vec with (r2 :: r3); try now auto.
        eapply hmrr_ex_hseq ; [ etransitivity ; [ apply Permutation_Type_swap | etransitivity ; [ apply Permutation_Type_skip; apply Permutation_Type_swap | apply Permutation_Type_swap ]] | ].
        apply hmrr_C; change (hmr_frag_T_M) with (hmr_frag_add_T hmr_frag_T_M); apply hmrr_T_vec with (r0 :: r1); try now auto.
        eapply hmrr_ex_hseq ; [ apply Permutation_Type_skip; etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
        apply hmrr_S.
        apply hmrr_ex_seq with (seq_mul_vec (r2 :: r3) (vec (r0 :: r1) B ++ D1) ++ seq_mul_vec (r0 :: r1) (vec (r2 :: r3) A ++ D2)).
        { etransitivity ; [ apply Permutation_Type_app; apply seq_mul_vec_app_r | ].
          etransitivity ; [ | apply Permutation_Type_app; symmetry; apply seq_mul_vec_app_r].
          etransitivity ; [ apply Permutation_Type_app; (apply Permutation_Type_app ; [ apply seq_mul_vec_vec | reflexivity ] ) | ].
          perm_Type_solve. }
        apply hmrr_M; try reflexivity.
        + change hmr_frag_T_M with (hmr_frag_add_T (hmr_frag_add_M hmr_frag_T_M)); apply hmrr_T_vec_inv.
          eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
          apply hmrr_W.
          eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
          apply pi11.
        + change hmr_frag_T_M with (hmr_frag_add_T (hmr_frag_add_M hmr_frag_T_M)); apply hmrr_T_vec_inv.
          eapply hmrr_ex_hseq ; [ etransitivity ; [apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
          apply hmrr_W.
          apply pi22. }
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_skip; apply Permutation_Type_middle | ].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with ((vec r1 B ++ D1) ++ (vec r2 B ++ D2)).
    { transitivity (vec (r1 ++ r2) B ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app ; [ apply vec_perm| ] ; perm_Type_solve. }
    apply hmrr_M; try reflexivity ; (eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]); apply hmrr_M; try reflexivity; try assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    rewrite seq_mul_app; rewrite seq_mul_vec_mul_vec.
    eapply hmrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hmrr_T with r; try assumption.
    rewrite seq_mul_app; rewrite seq_mul_vec_mul_vec.
    apply hmrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((mul_vec r r', seq_mul r T') :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((mul_vec r r', seq_mul r T') :: L)).
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
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hmrr_ID; try assumption.
    eapply hmrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hmrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hmrr_ID; try assumption.
    eapply hmrr_ex_hseq; [ |  apply (IHpi ((r1 , Db) :: L))].
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
    apply hmrr_ex_seq with (vec r zero ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hmrr_Z; try assumption.
    eapply hmrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hmrr_ex_seq with (vec r zero ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hmrr_Z; try assumption.
    eapply hmrr_ex_hseq; [ |  apply (IHpi ((r1 , Db) :: L))].
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
    apply hmrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hmrr_plus; try assumption.
    apply hmrr_ex_seq with (vec r1 A ++ (vec r A0 ++ vec r B0 ++ Db)) ; [ perm_Type_solve | ].
    eapply hmrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hmrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hmrr_plus; try assumption.
    apply hmrr_ex_seq with (vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)) ; [ perm_Type_solve | ].
    eapply hmrr_ex_hseq; [ |  apply (IHpi ((r1 , vec r A0 ++ vec r B0 ++ Db) :: L))].
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
    apply hmrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hmrr_mul; try assumption.
    apply hmrr_ex_seq with (vec r1 A ++ (vec (mul_vec r0 r) A0 ++ Db)) ; [ perm_Type_solve | ].
    eapply hmrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ].
    simpl.
    apply hmrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hmrr_mul; try assumption.
    apply hmrr_ex_seq with (vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)) ; [ perm_Type_solve | ].
    eapply hmrr_ex_hseq; [ |  apply (IHpi ((r1 , vec (mul_vec r0 r) A0 ++ Db) :: L))].
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
      apply hmrr_ex_seq with (vec c1 (A0 \/S B0) ++ vec (a1 ++ b1) A0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      apply hmrr_max.
      apply hmrr_W.
      apply hmrr_ex_seq with (vec a1 A0 ++ (vec r A0 ++ T')).
      { transitivity (vec a1 A0 ++ (vec (b1 ++ c1) A0 ++ T')); [ apply Permutation_Type_app ; [ reflexivity | ] ;try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve | ].
        rewrite ? vec_app.
        perm_Type_solve. }
      eapply hmrr_ex_hseq ; [ rewrite app_comm_cons; apply Permutation_Type_app_comm | ]; simpl.
      apply hmrr_ex_seq with (vec c1 (A0 \/S B0) ++ vec (a1 ++ b1) B0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      apply hmrr_max.
      eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hmrr_W.
      apply hmrr_ex_seq with (vec a1 B0 ++ (vec r B0 ++ T')).
      { transitivity (vec a1 B0 ++ (vec (b1 ++ c1) B0 ++ T')); [ apply Permutation_Type_app ; [ reflexivity | ] ;try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve | ].
        rewrite ? vec_app.
        perm_Type_solve. }
      eapply hmrr_ex_hseq ; [ etransitivity ; [ apply Permutation_Type_middle | symmetry; rewrite app_comm_cons; symmetry; apply Permutation_Type_app_comm ] | ].
      simpl; apply C_A_B.
      eapply hmrr_ex_hseq ; [ etransitivity ; [ apply Permutation_Type_skip; apply Permutation_Type_swap | apply Permutation_Type_swap ] | ].
      eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ].
      simpl; apply C_A_B.
      eapply hmrr_ex_hseq ; [ | apply (IHpi ((a1, vec r B0 ++ T') :: (a1, vec r A0 ++ T') :: L))].
      { simpl.
        do 2 (apply Permutation_Type_skip).
        etransitivity ; [ apply Permutation_Type_app_comm | ].
        simpl; do 2 (apply Permutation_Type_skip).
        apply Permutation_Type_app_comm. }
      simpl.
      apply Forall2_Type_cons; [ | apply Forall2_Type_cons ; [ | assumption]]; perm_Type_solve.    
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hmrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 A ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hmrr_max; try assumption.
      apply hmrr_ex_seq with (vec r1 A ++ (vec r B0 ++ Db)).
      { perm_Type_solve. }
      eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hmrr_ex_seq with (vec r1 A ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      rewrite 2 app_comm_cons.
      eapply hmrr_ex_hseq;  [ apply Permutation_Type_app_comm | ].
      simpl;apply hmrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 B ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hmrr_max; try assumption.
      apply hmrr_ex_seq with (vec r1 B ++ (vec r B0 ++ Db)).
      { perm_Type_solve. }
      eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hmrr_ex_seq with (vec r1 B ++ (vec r A0 ++ Db)).
      { perm_Type_solve. }
      eapply hmrr_ex_hseq ; [ | apply (IHpi ((r1, vec r B0 ++ Db) :: (r1 , vec r A0 ++ Db) :: L)) ].
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
    assert (HMR_T_M ((vec r1 A ++ vec r A0 ++ Db) :: (vec r1 B ++ vec r A0 ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as piAA.
    { eapply hmrr_ex_hseq ; [ | apply (IHpi1 ((r1 , vec r A0 ++ Db) :: L)) ].
      { simpl.
        apply Permutation_Type_skip.
        etransitivity; [ apply Permutation_Type_app_comm | ].
        simpl; apply Permutation_Type_skip.
        apply Permutation_Type_app_comm. }
      simpl.
      apply Forall2_Type_cons; [ |  assumption]; perm_Type_solve. }
    assert (HMR_T_M ((vec r1 A ++ vec r B0 ++ Db) :: (vec r1 B ++ vec r B0 ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as piBB.
    { eapply hmrr_ex_hseq ; [ | apply (IHpi2 ((r1 , vec r B0 ++ Db) :: L)) ].
      { simpl.
        apply Permutation_Type_skip.
        etransitivity; [ apply Permutation_Type_app_comm | ].
        simpl; apply Permutation_Type_skip.
        apply Permutation_Type_app_comm. }
      simpl.
      apply Forall2_Type_cons; [ |  assumption]; perm_Type_solve. }
    assert (HMR_T_M ((vec r1 A ++ vec r A0 ++ Db) :: (vec r1 B ++ vec r B0 ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as piAB.
    { apply hmrr_C.
      eapply hmrr_ex_hseq; [ etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
      apply hmrr_C.
      eapply hmrr_ex_hseq; [ etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
      apply hmrr_S.
      apply hmrr_ex_seq with ((vec r1 A ++ vec r B0 ++ Db) ++ (vec r1 B ++ vec r A0 ++ Db)).
      { rewrite <- ? app_assoc.
        apply Permutation_Type_app; try reflexivity.
        rewrite ? app_assoc; apply Permutation_Type_app; try reflexivity.
        etransitivity ; [ | apply Permutation_Type_app_comm].
        perm_Type_solve. }
      apply hmrr_M; try reflexivity; [ eapply hmrr_ex_hseq ;
                                      [ etransitivity ;
                                        [ apply Permutation_Type_swap |
                                          apply Permutation_Type_skip; apply Permutation_Type_swap ] |];
                                      apply hmrr_W |
                                      eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ];
                                      apply hmrr_W;
                                      eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap  | ] ]; try assumption. }
    assert (HMR_T_M ((vec r1 A ++ vec r B0 ++ Db) :: (vec r1 B ++ vec r A0 ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)) as piBA.
    { apply hmrr_C.
      eapply hmrr_ex_hseq; [ etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
      apply hmrr_C.
      eapply hmrr_ex_hseq; [ etransitivity ; [ apply Permutation_Type_swap | apply Permutation_Type_skip; apply Permutation_Type_swap ] | ].
      apply hmrr_S.
      apply hmrr_ex_seq with ((vec r1 A ++ vec r A0 ++ Db) ++ (vec r1 B ++ vec r B0 ++ Db)).
      { rewrite <- ? app_assoc.
        apply Permutation_Type_app; try reflexivity.
        rewrite ? app_assoc; apply Permutation_Type_app; try reflexivity.
        etransitivity ; [ | apply Permutation_Type_app_comm].
        perm_Type_solve. }
      apply hmrr_M; try reflexivity; [ eapply hmrr_ex_hseq ;
                                      [ etransitivity ;
                                        [ apply Permutation_Type_swap |
                                          apply Permutation_Type_skip; apply Permutation_Type_swap ] |];
                                      apply hmrr_W |
                                      eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ];
                                      apply hmrr_W;
                                      eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap  | ] ]; try assumption. }
    eapply hmrr_ex_hseq; [ apply Permutation_Type_skip; apply Permutation_Type_middle | ].
    apply hmrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 A ++ Db); [ perm_Type_solve | ].
    apply hmrr_min;
      (eapply hmrr_ex_seq with (vec r1 A ++ vec r _ ++ Db) ; [ rewrite ? app_assoc; apply Permutation_Type_app; try apply Permutation_Type_app_comm; try reflexivity | ]);
      (eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ]);
      (apply hmrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 B ++ Db); [ perm_Type_solve | ]);
      apply hmrr_min;
      (eapply hmrr_ex_seq with (vec r1 B ++ vec r _ ++ Db) ; [ rewrite ? app_assoc; apply Permutation_Type_app; try apply Permutation_Type_app_comm; try reflexivity | ]);
      (eapply hmrr_ex_hseq; [ apply Permutation_Type_swap | ]);
      assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> coone) as Hnc by now auto.
    assert (A \/S B <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hmrr_one; try assumption.
    apply hmrr_ex_hseq with ((vec r1 B ++ T1) :: (vec r1 A ++ Db) :: (map (fun x => vec (fst x) A ++ snd x) L) ++ (map (fun x => vec (fst x) B ++ snd x) L)).
    { etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_middle. }
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ vec r1 B ++ Db) ; [ perm_Type_solve | ].
    apply hmrr_one; try assumption.
    apply hmrr_ex_hseq with (map (fun x => vec (fst x) A ++ snd x) ((r1, Db) :: L) ++ map (fun x => vec (fst x) B ++ snd x) ((r1, Db) :: L) ).
    { simpl.
      etransitivity; [ | apply Permutation_Type_swap].
      apply Permutation_Type_skip; symmetry; apply Permutation_Type_middle. }
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [r1 T1]; simpl in *.
    assert (A \/S B <> coone) as Hnc by now auto.
    assert (A \/S B <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply seq_diamond_perm_decomp in H1' as [D' H1'].
    apply seq_diamond_app_inv in H1' as [[Da' Db'] [HD' [HDa' HDb']]]; subst.
    apply seq_diamond_perm_decomp in H5' as [Db'' H5']; subst.
    destruct r1.
    2:{ symmetry in H4'; apply seq_diamond_perm_decomp in H4' as [D' H'].
        destruct D'; inversion H'. }
    apply hmrr_W.
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ seq_diamond Db'') ; [ perm_Type_solve | ].
    apply hmrr_diamond; try assumption.
    apply hmrr_C.
    change ((vec s coone ++ vec r one ++ Db'') :: (vec s coone ++ vec r one ++ Db'') :: nil) with
        (map (fun x => vec (fst x) A ++ snd x) ((nil, vec s coone ++ vec r one ++ Db'') :: nil) ++ map (fun x => vec (fst x) B ++ snd x) ((nil, vec s coone ++ vec r one ++ Db'') :: nil)).
    apply IHpi.
    apply Forall2_Type_cons ; [ | apply Forall2_Type_nil].
    simpl.
    apply Permutation_Type_app; try reflexivity.
    apply Permutation_Type_app; try reflexivity.
    simpl in X.
    apply seq_diamond_perm_inv.
    apply Permutation_Type_app_inv_l with (vec r one).
    apply Permutation_Type_app_inv_l with (vec s coone).
    transitivity T1; try assumption.
    etransitivity ; [ apply H2' | ].
    rewrite app_assoc.
    apply Permutation_Type_app; perm_Type_solve. 
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.    
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A \/S B) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_app; apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hmrr_can with A0 r s; try assumption.
    apply hmrr_ex_seq with (vec r1 A ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    rewrite app_comm_cons.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_app_comm | ].
    simpl; apply hmrr_can with A0 r s; try assumption.
    apply hmrr_ex_seq with (vec r1 B ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    eapply hmrr_ex_hseq; [ | apply (IHpi ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L))].
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      reflexivity. }
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.
    
Lemma hmrr_min_inv_gen_l : forall L A B,
    HMR_T_M (map (fun x => (vec (fst x) (A /\S B) ++ snd x)) L) ->
    HMR_T_M (map (fun x => (vec (fst x) A ++ snd x)) L).
Proof.
  intros L A B.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; inversion X.
    apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_W.
    apply IHpi.
    assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_C.
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
      (apply hmrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((p1, p2) :: (p1',p2') :: L )) ; [ apply Permutation_Type_map; perm_Type_solve | ]);
      simpl in *;
      apply hmrr_S;
      (apply hmrr_ex_seq with (vec (fst p'') A ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (fst p'') A ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (L ))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) (p'' :: L ));
      apply IHpi;
      simpl; apply Forall2_Type_cons;
        [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hmrr_ex_seq with ((vec r1 A ++ D1) ++ (vec r2 A ++ D2)).
    { transitivity (vec (r1 ++ r2) A ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
    apply hmrr_M; try assumption.
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
    apply hmrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hmrr_ex_seq with (vec (mul_vec r r') A ++ seq_mul r T').
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
    destruct (perm_decomp_vec_neq_2 _  _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hmrr_ID; try assumption.
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
    apply hmrr_ex_seq with (vec r zero ++ vec r1 A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_Z; try assumption.
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
    apply hmrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_plus; try assumption.
    apply hmrr_ex_seq with (vec r1 A ++ (vec r A0 ++ vec r B0 ++ Db)).
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
    apply hmrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_mul; try assumption.
    apply hmrr_ex_seq with (vec r1 A ++ (vec (mul_vec r0 r) A0 ++ Db)).
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
    apply hmrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 A ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_max; try assumption.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r1 A ++ (vec r A0 ++ Db)).
    { perm_Type_solve. }
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r1 A ++ (vec r B0 ++ Db)).
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
      apply hmrr_ex_seq with (vec c1 (A0 /\S B0) ++ vec (a1 ++ b1) A0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      assert (HMR_T_M ((vec a1 A0 ++ (vec r A0  ++ T')) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) L)) as piA.
      { change ((vec a1 A0  ++ vec r A0  ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) L)
          with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) ((a1 , vec r A0 ++ T') :: L)).
        apply IHpi1.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        transitivity (vec (b1 ++ c1) A0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve. }
      assert (HMR_T_M ((vec a1 A0 ++ (vec r B0  ++ T')) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) L)) as piB.
      { change ((vec a1 A0  ++ vec r B0  ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) L)
          with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A0 ++ snd x) ((a1 , vec r B0 ++ T') :: L)).
        apply IHpi2.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        transitivity (vec (b1 ++ c1) B0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve. }
      apply hmrr_min.
      * apply hmrr_ex_seq with (vec a1 A0 ++ (vec r A0  ++ T')).
        { transitivity (vec a1 A0  ++ (vec (b1 ++ c1) A0 ++ T')); [ apply Permutation_Type_app; try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve | ].
          rewrite ? vec_app.
          perm_Type_solve. }
        apply piA.
      * rewrite vec_app.
        apply hmrr_ex_seq with (vec c1 B0 ++ vec b1 A0 ++ vec a1 A0 ++ T'); [ perm_Type_solve | ].
        apply mix_A_B.
        -- eapply hmrr_ex_seq ; [ | apply piA].
           rewrite ? app_assoc.
           apply Permutation_Type_app; try reflexivity.
           etransitivity; [ apply Permutation_Type_app_comm | ].
           apply Permutation_Type_app ; try reflexivity.
           rewrite <- vec_app.
           apply vec_perm.
           perm_Type_solve.
        -- eapply hmrr_ex_seq ; [ | apply piB].
           rewrite ? app_assoc.
           apply Permutation_Type_app; try reflexivity.
           etransitivity; [ apply Permutation_Type_app_comm | ].
           apply Permutation_Type_app ; try reflexivity.
           rewrite <- vec_app.
           apply vec_perm.
           perm_Type_solve.
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hmrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 A ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hmrr_min; try assumption.
      * apply hmrr_ex_seq with (vec r1 A ++ (vec r A0 ++ Db)).
        { perm_Type_solve. }
        change ((vec r1 A ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec r A0 ++ Db) :: L)).
        apply IHpi1.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        perm_Type_solve.
      * apply hmrr_ex_seq with (vec r1 A ++ (vec r B0 ++ Db)).
        { perm_Type_solve. }
        change ((vec r1 A ++ (vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec r B0 ++ Db) :: L)).
        apply IHpi2.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> coone) as Hnc by now auto.
    assert (A /\S B <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ vec r1 A ++ Db).
    { perm_Type_solve. }
    apply hmrr_one; try assumption.
    change ((vec r1 A ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> coone) as Hnc by now auto.
    assert (A /\S B <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply seq_diamond_perm_decomp in H1' as [D' H1'].
    apply seq_diamond_app_inv in H1' as [[Da' Db'] [HD' [HDa' HDb']]]; subst.
    apply seq_diamond_perm_decomp in H5' as [Db'' H5']; subst.
    destruct r1.
    2:{ symmetry in H4'; apply seq_diamond_perm_decomp in H4' as [D' H'].
        destruct D'; inversion H'. }
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ seq_diamond Db'') ; [ perm_Type_solve | ].
    apply hmrr_diamond; try assumption.
    change ((vec s coone ++ vec r one ++ Db'') :: nil)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((nil, vec s coone ++ vec r one ++ Db'') :: nil)).
    apply IHpi.
    apply Forall2_Type_cons ; [ | apply Forall2_Type_nil].
    simpl.
    apply Permutation_Type_app; try reflexivity.
    apply Permutation_Type_app; try reflexivity.
    simpl in X.
    apply seq_diamond_perm_inv.
    apply Permutation_Type_app_inv_l with (vec r one).
    apply Permutation_Type_app_inv_l with (vec s coone).
    transitivity T1; try assumption.
    etransitivity ; [ apply H2' | ].
    rewrite app_assoc.
    apply Permutation_Type_app; perm_Type_solve. 
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hmrr_can with A0 r s; try assumption.
    apply hmrr_ex_seq with (vec r1 A  ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec r1 A ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.
    
Lemma hmrr_min_inv_gen_r : forall L A B,
    HMR_T_M (map (fun x => (vec (fst x) (A /\S B) ++ snd x)) L) ->
    HMR_T_M (map (fun x => (vec (fst x) B ++ snd x)) L).
Proof.
  intros L A B.
  remember (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L) as G.
  assert (Allperm G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L)) by (rewrite <- HeqG; clear; induction G; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L ; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [r1 T1]; destruct r1; destruct T1; inversion X.
    apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_W.
    apply IHpi.
    assumption.
  - destruct L; inversion Hperm; subst.
    simpl.
    apply hmrr_C.
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
      (apply hmrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((p1, p2) :: (p1',p2') :: L )) ; [ apply Permutation_Type_map; perm_Type_solve | ]);
      simpl in *;
      apply hmrr_S;
      (apply hmrr_ex_seq with (vec (fst p'') B ++ snd p'') ; [ rewrite Heqp''; simpl; rewrite ? vec_app; perm_Type_solve | ]);
      change ((vec (fst p'') B ++ snd p'') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (L ))
        with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) (p'' :: L ));
      apply IHpi;
      simpl; apply Forall2_Type_cons;
        [ rewrite Heqp'';simpl; rewrite vec_app ; perm_Type_solve | rewrite ? map_app; repeat (try apply Forall2_Type_app; try assumption)].
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r T]; simpl in *.
    apply decomp_M_case in X as [[[[D1 D2] r1] r2] [H1' [[H2' H3] H4]]].
    apply hmrr_ex_seq with ((vec r1 B ++ D1) ++ (vec r2 B ++ D2)).
    { transitivity (vec (r1 ++ r2) B ++ (D1 ++ D2)) ; [rewrite ? vec_app; perm_Type_solve | ].
      apply Permutation_Type_app; [ apply vec_perm | ]; perm_Type_solve. }
    apply hmrr_M; try assumption.
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
    apply hmrr_T with r; try assumption.
    destruct p as (r' , T'); simpl in *.
    apply hmrr_ex_seq with (vec (mul_vec r r') B ++ seq_mul r T').
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
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s (covar n) ++ vec r (var n) ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hmrr_ID; try assumption.
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
    apply hmrr_ex_seq with (vec r zero ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_Z; try assumption.
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
    apply hmrr_ex_seq with (vec r (A0 +S B0) ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_plus; try assumption.
    apply hmrr_ex_seq with (vec r1 B ++ (vec r A0 ++ vec r B0 ++ Db)).
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
    apply hmrr_ex_seq with (vec r (r0 *S A0) ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_mul; try assumption.
    apply hmrr_ex_seq with (vec r1 B ++ (vec (mul_vec r0 r) A0 ++ Db)).
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
    apply hmrr_ex_seq with (vec r (A0 \/S B0) ++ vec r1 B ++ Db).
    { etransitivity; [ apply Permutation_Type_app_comm | ].
      rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
      perm_Type_solve. }
    apply hmrr_max; try assumption.
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r1 B ++ (vec r A0 ++ Db)).
    { perm_Type_solve. }
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hmrr_ex_seq with (vec r1 B ++ (vec r B0 ++ Db)).
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
      apply hmrr_ex_seq with (vec c1 (A0 /\S B0) ++ vec (a1 ++ b1) B0 ++ T').
      { etransitivity ; [apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc.
        apply Permutation_Type_app; try (apply vec_perm;symmetry; assumption).
        perm_Type_solve. }
      assert (HMR_T_M ((vec a1 B0 ++ (vec r B0  ++ T')) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) L)) as piB.
      { change ((vec a1 B0  ++ vec r B0  ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) L)
          with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) ((a1 , vec r B0 ++ T') :: L)).
        apply IHpi2.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        transitivity (vec (b1 ++ c1) B0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve. }
      assert (HMR_T_M ((vec a1 B0 ++ (vec r A0  ++ T')) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) L)) as piA.
      { change ((vec a1 B0  ++ vec r A0  ++ T') :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) L)
          with ( map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B0 ++ snd x) ((a1 , vec r A0 ++ T') :: L)).
        apply IHpi1.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        transitivity (vec (b1 ++ c1) A0 ++ T).
        { repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
        etransitivity ; [ | apply Permutation_Type_app ; [ reflexivity | do 2 (try apply Permutation_Type_app; try (apply vec_perm; symmetry; apply H2')); reflexivity] ].
        perm_Type_solve. }
      apply hmrr_min.
      * rewrite vec_app.
        apply hmrr_ex_seq with (vec c1 A0 ++ vec b1 B0 ++ vec a1 B0 ++ T'); [ perm_Type_solve | ].
        apply mix_A_B.
        -- eapply hmrr_ex_seq ; [ | apply piB].
           rewrite ? app_assoc.
           apply Permutation_Type_app; try reflexivity.
           etransitivity; [ apply Permutation_Type_app_comm | ].
           apply Permutation_Type_app ; try reflexivity.
           rewrite <- vec_app.
           apply vec_perm.
           perm_Type_solve.
        -- eapply hmrr_ex_seq ; [ | apply piA].
           rewrite ? app_assoc.
           apply Permutation_Type_app; try reflexivity.
           etransitivity; [ apply Permutation_Type_app_comm | ].
           apply Permutation_Type_app ; try reflexivity.
           rewrite <- vec_app.
           apply vec_perm.
           perm_Type_solve.
      * apply hmrr_ex_seq with (vec a1 B0 ++ (vec r B0  ++ T')).
        { transitivity (vec a1 B0  ++ (vec (b1 ++ c1) B0 ++ T')); [ apply Permutation_Type_app; try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve | ].
          rewrite ? vec_app.
          perm_Type_solve. }
        apply piB.
    + intros Hneq.
      destruct (perm_decomp_vec_neq _ _ _ _ _ _ Hneq X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
      apply hmrr_ex_seq with (vec r (A0 /\S B0) ++ vec r1 B ++ Db).
      { etransitivity; [ apply Permutation_Type_app_comm | ].
        rewrite <- ? app_assoc; repeat (apply Permutation_Type_app; try reflexivity).
        perm_Type_solve. }
      apply hmrr_min; try assumption.
      * apply hmrr_ex_seq with (vec r1 B ++ (vec r A0 ++ Db)).
        { perm_Type_solve. }
        change ((vec r1 B ++ (vec r A0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec r A0 ++ Db) :: L)).
        apply IHpi1.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        perm_Type_solve.
      * apply hmrr_ex_seq with (vec r1 B ++ (vec r B0 ++ Db)).
        { perm_Type_solve. }
        change ((vec r1 B ++ (vec r B0 ++ Db)) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
          with
            (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec r B0 ++ Db) :: L)).
        apply IHpi2.
        simpl.
        apply Forall2_Type_cons; [ | assumption].
        perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> coone) as Hnc by now auto.
    assert (A /\S B <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ vec r1 B ++ Db).
    { perm_Type_solve. }
    apply hmrr_one; try assumption.
    change ((vec r1 B ++ Db) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, Db) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption].
    perm_Type_solve.
  - destruct L; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [r1 T1]; simpl in *.
    assert (A /\S B <> coone) as Hnc by now auto.
    assert (A /\S B <> one) as Hnv by now auto.
    destruct (perm_decomp_vec_neq_2 _ _ _ _ _ _ _ _ Hnc Hnv X) as [ [[[Ta Tb] Da ] Db] [H1' [[[H2' H3'] H4'] H5']]].
    apply seq_diamond_perm_decomp in H1' as [D' H1'].
    apply seq_diamond_app_inv in H1' as [[Da' Db'] [HD' [HDa' HDb']]]; subst.
    apply seq_diamond_perm_decomp in H5' as [Db'' H5']; subst.
    destruct r1.
    2:{ symmetry in H4'; apply seq_diamond_perm_decomp in H4' as [D' H'].
        destruct D'; inversion H'. }
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ seq_diamond Db'') ; [ perm_Type_solve | ].
    apply hmrr_diamond; try assumption.
    change ((vec s coone ++ vec r one ++ Db'') :: nil)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((nil, vec s coone ++ vec r one ++ Db'') :: nil)).
    apply IHpi.
    apply Forall2_Type_cons ; [ | apply Forall2_Type_nil].
    simpl.
    apply Permutation_Type_app; try reflexivity.
    apply Permutation_Type_app; try reflexivity.
    simpl in X.
    apply seq_diamond_perm_inv.
    apply Permutation_Type_app_inv_l with (vec r one).
    apply Permutation_Type_app_inv_l with (vec s coone).
    transitivity T1; try assumption.
    etransitivity ; [ apply H2' | ].
    rewrite app_assoc.
    apply Permutation_Type_app; perm_Type_solve. 
  - destruct L; inversion Hperm; subst.
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    transitivity T2; assumption.
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) (A /\S B) ++ snd x) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - destruct L; inversion Hperm; subst.
    simpl.
    destruct p as [r1 T1]; simpl in *.
    apply hmrr_can with A0 r s; try assumption.
    apply hmrr_ex_seq with (vec r1 B  ++ (vec s (-S A0) ++ vec r A0 ++ T1)).
    { perm_Type_solve. }
    change ((vec r1 B ++ vec s (-S A0) ++ vec r A0 ++ T1) :: map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) L)
      with
        (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r1, vec s (-S A0) ++ vec r A0 ++ T1) :: L)).
    apply IHpi.
    simpl.
    apply Forall2_Type_cons; [ | assumption]; perm_Type_solve.
Qed.

Lemma hmrr_diamond_inv_gen : forall L,
    HMR_T_M (map (fun x => (vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ seq_diamond (snd x))) L) ->
    HMR_T_M (map (fun x => (vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x)) L).
Proof.
  intros L.
  remember (map (fun x => (vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ seq_diamond (snd x))) L) as G.
  assert (Allperm G (map (fun x => (vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ seq_diamond (snd x))) L)) by (rewrite <- HeqG; clear; induction G; simpl; try now constructor).
  clear HeqG.
  intro pi; revert L X; induction pi; intros L Hperm.
  - destruct L ; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    apply Permutation_Type_nil in X.
    destruct p as [[s r] T]; destruct r; destruct s; destruct T; inversion X.
    apply hmrr_INIT.
  - destruct L; inversion Hperm; subst.
    simpl; apply hmrr_W.
    apply IHpi; try assumption.
  - destruct L; inversion Hperm; subst.
    simpl; apply hmrr_C.
    change ((vec (fst (fst p)) coone ++ vec (snd (fst p)) one ++ snd p)
              :: (vec (fst (fst p)) coone ++ vec (snd (fst p)) one ++ snd p)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (p :: p :: L)).
    apply IHpi.
    apply Forall2_Type_cons ; [ | apply Forall2_Type_cons]; try assumption.
  - destruct L ; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[s1 r1] T1'].
    destruct p0 as [[s2 r2] T2'].
    simpl in *.
    apply hmrr_S.
    apply hmrr_ex_seq with (vec (s1 ++ s2) coone ++ vec (r1 ++ r2) one ++ T1' ++ T2').
    { rewrite ? vec_app.
      perm_Type_solve. }
    change ((vec (s1 ++ s2) coone ++ vec (r1 ++ r2) one ++ T1' ++ T2')
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with
        (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s1 ++ s2, r1 ++ r2) , T1' ++ T2') :: L)).
    apply IHpi.
    apply Forall2_Type_cons; try assumption.
    simpl.
    rewrite ? vec_app; rewrite seq_diamond_app.
    perm_Type_solve.
  - destruct L; inversion Hperm; subst.
    destruct p as [[s r] T].
    apply decomp_M_case_2 in X as [[[[[[D1 D2] s1] s2] r1] r2] [H1 [[[H2 H3] H4] H5]]]; simpl in *.
    apply seq_diamond_perm_decomp in H3 as [D H3].
    apply seq_diamond_app_inv in H3 as [[D1' D2'] [Heq1 [Heq2 Heq3]]]; subst.
    apply hmrr_ex_seq with ((vec s1 coone ++ vec r1 one ++ D1') ++ (vec s2 coone ++ vec r2 one ++ D2')).
    { transitivity (vec (s1 ++ s2) coone ++ vec (r1 ++ r2) one ++ D1' ++ D2').
      - rewrite ? vec_app.
        perm_Type_solve.
      - repeat apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve.
        apply seq_diamond_perm_inv.
        apply Permutation_Type_app_inv_l with (vec r one).
        apply Permutation_Type_app_inv_l with (vec s coone).
        inversion Hperm; subst.
        etransitivity ; [ | apply X].
        transitivity (vec (s1 ++ s2) coone ++ vec (r1 ++ r2) one ++ (seq_diamond (D1' ++ D2'))).
        + repeat apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve.
        + etransitivity ; [ | apply Permutation_Type_app ; symmetry; [ apply H4 | apply H5]].
          rewrite ? vec_app; rewrite seq_diamond_app.
          perm_Type_solve. }
    apply hmrr_M; try assumption.
    + change ((vec s1 coone ++ vec r1 one ++ D1')
                :: map
                (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                   vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
        with
          (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s1,r1),D1')::L)).
      apply IHpi1; simpl; apply Forall2_Type_cons; assumption.
    + change ((vec s2 coone ++ vec r2 one ++ D2')
                :: map
                (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                   vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
        with
          (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s2,r2),D2')::L)).
      apply IHpi2; simpl; apply Forall2_Type_cons; assumption.
  - destruct L; inversion Hperm; subst.
    destruct p as [r1 T1]; simpl in *.
    apply hmrr_T with r; try assumption.
    rewrite ? seq_mul_app; rewrite ? seq_mul_vec_mul_vec.
    change ((vec (mul_vec r (fst r1)) coone ++ vec (mul_vec r (snd r1)) one ++ seq_mul r T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with
        (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((mul_vec r (fst r1), mul_vec r (snd r1)), seq_mul r T1) :: L)).
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    etransitivity ; [ apply seq_mul_perm; apply X | ].
    rewrite ? seq_mul_app; rewrite ? seq_mul_vec_mul_vec.
    rewrite seq_diamond_seq_mul.
    reflexivity.
  - destruct L; inversion Hperm; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct s.
    2:{ exfalso.
        assert (~ In (r0, covar n) (vec s1 coone ++ vec r1 one ++ seq_diamond T1)) as H.
        - intros Hin.
          apply in_app_or in Hin.
          case Hin ; [ | intros Hin2; apply in_app_or in Hin2; case Hin2].
          + clear.
            induction s1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHs1.
              apply H.
          + clear.
            induction r1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHr1.
              apply H.
          + apply seq_diamond_only_diamond.
            intros B; intros H; inversion H.
        - apply H.
          apply Permutation_Type_in with (vec (r0 :: s) (covar n) ++ vec r (var n) ++ T); try assumption.
          simpl; left.
          reflexivity. }
    destruct r.
    2:{ exfalso.
        assert (~ In (r, var n) (vec s1 coone ++ vec r1 one ++ seq_diamond T1)) as H.
        - intros Hin.
          apply in_app_or in Hin.
          case Hin ; [ | intros Hin2; apply in_app_or in Hin2; case Hin2].
          + clear.
            induction s1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHs1.
              apply H.
          + clear.
            induction r1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHr1.
              apply H.
          + apply seq_diamond_only_diamond.
            intros B; intros H; inversion H.
        - apply H.
          apply Permutation_Type_in with (vec (r :: r0) (var n) ++ T); try assumption.
          simpl; left.
          reflexivity. }
    simpl in *.
    change ((vec s1 coone ++ vec r1 one ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s1,r1),T1)::L)).
    apply IHpi.
    apply Forall2_Type_cons; try assumption.
  - destruct L; inversion Hperm; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct r.
    2:{ exfalso.
        assert (~ In (r, zero) (vec s1 coone ++ vec r1 one ++ seq_diamond T1)) as H.
        - intros Hin.
          apply in_app_or in Hin.
          case Hin ; [ | intros Hin2; apply in_app_or in Hin2; case Hin2].
          + clear.
            induction s1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHs1.
              apply H.
          + clear.
            induction r1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHr1.
              apply H.
          + apply seq_diamond_only_diamond.
            intros B; intros H; inversion H.
        - apply H.
          apply Permutation_Type_in with (vec (r :: r0) zero ++ T); try assumption.
          simpl; left.
          reflexivity. }
    simpl in *.
    change ((vec s1 coone ++ vec r1 one ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s1,r1),T1)::L)).
    apply IHpi.
    apply Forall2_Type_cons; try assumption.
  - destruct L; inversion Hperm; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct r.
    2:{ exfalso.
        assert (~ In (r, A +S B) (vec s1 coone ++ vec r1 one ++ seq_diamond T1)) as H.
        - intros Hin.
          apply in_app_or in Hin.
          case Hin ; [ | intros Hin2; apply in_app_or in Hin2; case Hin2].
          + clear.
            induction s1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHs1.
              apply H.
          + clear.
            induction r1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHr1.
              apply H.
          + apply seq_diamond_only_diamond.
            intros B0; intros H; inversion H.
        - apply H.
          apply Permutation_Type_in with (vec (r :: r0) (A +S B) ++ T); try assumption.
          simpl; left.
          reflexivity. }
    simpl in *.
    change ((vec s1 coone ++ vec r1 one ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s1,r1),T1)::L)).
    apply IHpi.
    apply Forall2_Type_cons; try assumption.
  - destruct L; inversion Hperm; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct r.
    2:{ exfalso.
        assert (~ In (r, r0 *S A) (vec s1 coone ++ vec r1 one ++ seq_diamond T1)) as H.
        - intros Hin.
          apply in_app_or in Hin.
          case Hin ; [ | intros Hin2; apply in_app_or in Hin2; case Hin2].
          + clear.
            induction s1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHs1.
              apply H.
          + clear.
            induction r1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHr1.
              apply H.
          + apply seq_diamond_only_diamond.
            intros B; intros H; inversion H.
        - apply H.
          apply Permutation_Type_in with (vec (r :: r2) (r0 *S A) ++ T); try assumption.
          simpl; left.
          reflexivity. }
    simpl in *.
    change ((vec s1 coone ++ vec r1 one ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s1,r1),T1)::L)).
    apply IHpi.
    apply Forall2_Type_cons; try assumption.
  - destruct L; inversion Hperm; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct r.
    2:{ exfalso.
        assert (~ In (r, (A \/S B)) (vec s1 coone ++ vec r1 one ++ seq_diamond T1)) as H.
        - intros Hin.
          apply in_app_or in Hin.
          case Hin ; [ | intros Hin2; apply in_app_or in Hin2; case Hin2].
          + clear.
            induction s1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHs1.
              apply H.
          + clear.
            induction r1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHr1.
              apply H.
          + apply seq_diamond_only_diamond.
            intros B0; intros H; inversion H.
        - apply H.
          apply Permutation_Type_in with (vec (r :: r0) (A \/S B) ++ T); try assumption.
          simpl; left.
          reflexivity. }
    simpl in *.
    apply hmrr_C.
    change ((vec s1 coone ++ vec r1 one ++ T1) :: (vec s1 coone ++ vec r1 one ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s1,r1),T1)::((s1,r1),T1)::L)).
    apply IHpi.
    apply Forall2_Type_cons; try apply Forall2_Type_cons; try assumption.    
  - destruct L; inversion Hperm; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct r.
    2:{ exfalso.
        assert (~ In (r, (A /\S B)) (vec s1 coone ++ vec r1 one ++ seq_diamond T1)) as H.
        - intros Hin.
          apply in_app_or in Hin.
          case Hin ; [ | intros Hin2; apply in_app_or in Hin2; case Hin2].
          + clear.
            induction s1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHs1.
              apply H.
          + clear.
            induction r1;intros Hin; inversion Hin.
            * inversion H.
            * apply IHr1.
              apply H.
          + apply seq_diamond_only_diamond.
            intros B0; intros H; inversion H.
        - apply H.
          apply Permutation_Type_in with (vec (r :: r0) (A /\S B) ++ T); try assumption.
          simpl; left.
          reflexivity. }
    simpl in *.
    change ((vec s1 coone ++ vec r1 one ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s1,r1),T1)::L)).
    apply IHpi1.
    apply Forall2_Type_cons; try assumption.
  - destruct L; inversion Hperm; subst.
    destruct p as [[s1 r1] T1]; simpl in *.
    destruct (perm_decomp_vec_eq_2 T (seq_diamond T1) r1 s1 r s one coone) as [[[[[[[[a1 b1] c1] a2] b2] c2] T'] D'] [H1' [[[[[H2' H3'] H4'] H5'] H6']]]]; [ now auto | apply X | ].
    destruct c2.
    2:{ exfalso.
        refine (seq_diamond_only_diamond T1 coone r2 _ _).
        - intros B Heq; inversion Heq.
        - apply In_Type_to_In.
          apply Permutation_Type_in_Type with (vec (r2 :: c2) coone ++ vec c1 one ++ D'); try perm_Type_solve.
          left; reflexivity. }
    destruct c1.
    2:{ exfalso.
        refine (seq_diamond_only_diamond T1 one r2 _ _).
        - intros B Heq; inversion Heq.
        - apply In_Type_to_In.
          apply Permutation_Type_in_Type with (vec (r2 :: c1) one ++ D'); try perm_Type_solve.
          left; reflexivity. }
    simpl in *; rewrite app_nil_r in *.
    apply hmrr_ex_seq with (vec s coone ++ vec r one ++ vec a2 coone ++ vec a1 one ++ T1).
    { transitivity (vec (a2 ++ s) coone ++ vec (a1 ++ r) one ++ T1); [ | repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve) ].
      rewrite ? vec_app.
      perm_Type_solve. }
    apply hmrr_one; try assumption.
    change ((vec a2 coone ++ vec a1 one ++ T1)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with
        (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((a2,a1), T1)::L)).
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    perm_Type_solve.    
  - destruct L ; [ | destruct L]; inversion Hperm; try inversion X0; subst.
    destruct p as [[s' r'] T']; simpl in *.
    assert (Permutation_Type s s') as Hperms.
    { clear - X.
      revert X; revert s'; induction s; intros s' Hperm.
      - simpl in *.
        destruct s'; try reflexivity.
        exfalso.
        assert (~ In (r0, coone) (vec r one ++ seq_diamond T)) as H.
        + intros Hin; apply in_app_or in Hin; case Hin.
          * intros H; clear - H.
            induction r; inversion H; try inversion H0.
            apply IHr; try assumption.
          * apply seq_diamond_only_diamond.
            intros B Heq; inversion Heq.
        + apply H.
          apply Permutation_Type_in with (vec (r0 :: s') coone ++ vec r' one ++ seq_diamond T'); try perm_Type_solve.
          left; reflexivity.
      - destruct (in_Type_split a s') as [[s1' s2'] H].
        + assert (In_Type (a , coone) (vec s' coone)).
          * destruct (in_Type_app_or (vec s' coone) (vec r' one ++ seq_diamond T') (a , coone)); try assumption.
            -- apply Permutation_Type_in_Type with (vec (a :: s) coone ++ vec r one ++ seq_diamond T); try perm_Type_solve; left; reflexivity.
            -- clear - i.
               exfalso.
               induction r'.
               ++ apply In_Type_to_In in i; refine (seq_diamond_only_diamond _ _ _ _ i).
                  intros B H; inversion H.
               ++ destruct i; try inversion e.
                  apply IHr'; apply i.
          * clear - X.
            induction s'; inversion X.
            -- inversion H; subst; left; reflexivity.
            -- right; apply IHs'; apply X0.
        + subst.
          transitivity (a :: s1' ++ s2'); try perm_Type_solve.
          apply Permutation_Type_skip.
          apply IHs.
          apply Permutation_Type_cons_inv with (a , coone); rewrite ? vec_app in Hperm; simpl in *.
          etransitivity ; [ apply Hperm | ].
          rewrite app_comm_cons.
          rewrite ? app_assoc.
          do 2 (try apply Permutation_Type_app; try reflexivity).
          rewrite vec_app.
          perm_Type_solve. }
    assert (Permutation_Type r r') as Hpermr.
    { clear - X Hperms.
      revert X; revert r'; induction r; intros r' Hperm.
      - simpl in *.
        destruct r'; try reflexivity.
        exfalso.
        assert (~ In (r, one) (vec s coone ++ seq_diamond T)) as H.
        + intros Hin; apply in_app_or in Hin; case Hin.
          * intros H; clear - H.
            induction s; inversion H; try inversion H0.
            apply IHs; try assumption.
          * apply seq_diamond_only_diamond.
            intros B Heq; inversion Heq.
        + apply H.
          apply Permutation_Type_in with (vec s' coone ++ vec (r :: r') one ++ seq_diamond T'); try perm_Type_solve.
          apply in_or_app; right.
          left; reflexivity.
      - destruct (in_Type_split a r') as [[r1' r2'] H].
        + assert (In_Type (a , one) (vec r' one)).
          * destruct (in_Type_app_or (vec s' coone) (vec r' one ++ seq_diamond T') (a , one)).
            -- apply Permutation_Type_in_Type with (vec s coone ++ vec (a :: r) one ++ seq_diamond T); try perm_Type_solve.
               apply in_Type_or_app; right; left; reflexivity.
            -- clear - i.
               exfalso.
               induction s'; inversion i; try inversion H.
               apply IHs'; apply X.
            -- apply in_Type_app_or in i.
               destruct i; try assumption.
               exfalso.
               apply In_Type_to_In in i.
               refine (seq_diamond_only_diamond _ _ _ _ i).
               intros B H; inversion H.
          * clear - X.
            induction r'; inversion X.
            -- inversion H; subst; left; reflexivity.
            -- right; apply IHr'; apply X0.
        + subst.
          transitivity (a :: r1' ++ r2'); try perm_Type_solve.
          apply Permutation_Type_skip.
          apply IHr.
          apply Permutation_Type_cons_inv with (a , one); rewrite ? vec_app in Hperm; simpl in *.
          rewrite vec_app.
          etransitivity ; [ apply Permutation_Type_middle |  ].
          etransitivity ; [ apply Hperm | ].
          perm_Type_solve. }
    assert (Permutation_Type T T') as HpermT.
    { clear - X Hperms Hpermr.
      apply seq_diamond_perm_inv.
      apply Permutation_Type_app_inv_l with (vec r one).
      apply Permutation_Type_app_inv_l with (vec s coone).
      etransitivity ; [ apply X | ].
      repeat (try apply Permutation_Type_app; try apply vec_perm; try perm_Type_solve). }
    eapply hmrr_ex_seq; [ | apply pi].
    repeat (try apply Permutation_Type_app; try apply vec_perm; try apply seq_diamond_perm; try perm_Type_solve).
  - destruct L; inversion Hperm; subst.
    destruct p0 as [[s r] T]; simpl in *.
    change ((vec s coone ++ vec r one ++ T)
              :: map
              (fun x : list Rpos * list Rpos * list (Rpos * term) =>
                 vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) L)
      with
        (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s,r), T) :: L)).
    apply IHpi.
    simpl; apply Forall2_Type_cons; try assumption.
    perm_Type_solve.
  - destruct (Permutation_Type_Forall2 _ H G (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ seq_diamond (snd x)) L) (Permutation_Type_sym p) Hperm).
    destruct (Permutation_Type_map_inv _ _ _ (Permutation_Type_sym p0)) as [L' Heq Hperm1].
    eapply hmrr_ex_hseq ; [ apply Permutation_Type_map; symmetry; apply Hperm1 | ].
    apply IHpi.
    rewrite Heq in f; apply f.
  - inversion f.
Qed.

(** ** The regular rules are invertibles, those lemmas are instances of the previous ones *)
          
Lemma hmrr_Z_inv : forall G T r,  HMR_T_M ((vec r zero ++ T) :: G) -> HMR_T_M (T :: G).
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
  apply hmrr_Z_inv_gen.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hmrr_plus_inv : forall G T A B r, HMR_T_M ((vec r (A +S B) ++ T) :: G) -> HMR_T_M ((vec r A ++ vec r B ++ T) :: G).
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
  apply hmrr_plus_inv_gen.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hmrr_mul_inv : forall G T A r0 r, HMR_T_M ((vec r (r0 *S A) ++ T) :: G) -> HMR_T_M ((vec (mul_vec r0 r) A ++ T) :: G).
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
  apply hmrr_mul_inv_gen.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hmrr_max_inv : forall G T A B r, HMR_T_M ((vec r (A \/S B) ++ T) :: G) -> HMR_T_M ((vec r B ++ T) :: (vec r A ++ T) :: G).
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
  apply hmrr_ex_hseq with (G ++ (vec r B ++ T) :: (vec r A ++ T) :: nil) ; [ perm_Type_solve | ].
  apply hmrr_C_gen.
  apply hmrr_ex_hseq with (map (fun x : list Rpos * list (Rpos * term) => vec (fst x) A ++ snd x) ((r, T) :: L) ++ map (fun x : list Rpos * list (Rpos * term) => vec (fst x) B ++ snd x) ((r, T) :: L)).
  { simpl.
    rewrite <- H2; rewrite <- H3.
    perm_Type_solve. }
  apply hmrr_max_inv_gen.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hmrr_min_inv_l : forall G T A B r, HMR_T_M ((vec r (A /\S B) ++ T) :: G) -> HMR_T_M ((vec r A ++ T) :: G).
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
  apply hmrr_min_inv_gen_l with B.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hmrr_min_inv_r : forall G T A B r, HMR_T_M ((vec r (A /\S B) ++ T) :: G) -> HMR_T_M ((vec r B ++ T) :: G).
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
  apply hmrr_min_inv_gen_r with A.
  simpl; rewrite <- H1.
  apply pi.
Qed.

Lemma hmrr_diamond_inv : forall T r s, HMR_T_M ((vec s coone ++ vec r one ++ seq_diamond T) :: nil) -> HMR_T_M ((vec s coone ++ vec r one ++ T) :: nil).
Proof.
  intros T r s pi.
  change ((vec s coone ++ vec r one ++ T) :: nil)
    with
      (map (fun x => vec (fst (fst x)) coone ++ vec (snd (fst x)) one ++ snd x) (((s,r),T) :: nil)).
  apply hmrr_diamond_inv_gen.
  apply pi.
Qed.

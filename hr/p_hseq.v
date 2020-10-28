Require Import Rpos.
Require Import term.
Require Import semantic.
Require Import FOL_R.
Require Import hseq.

Require Import lt_nat2.

Require Import CMorphisms.
Require Import List_more.
Require Import Bool_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Lra.
Require Import Lia.
Require Import wf_prod.

Local Open Scope R_scope.

Ltac sem_is_pos_decomp val a :=
  let H := fresh "H" in
  let HeqH := fresh "HeqH" in
  assert {H & R_order_dec (FOL_R_term_sem val a) = H} as [H HeqH] by (split with (R_order_dec (FOL_R_term_sem val a)); reflexivity); destruct H as [H | H | H];
  rewrite ? HeqH; revert H HeqH.


(** * Definitions *)
                                                
Definition p_sequent : Set := list (FOL_R_term * term).

Definition p_seq_is_atomic (T : p_sequent) := Forall_Type (fun x => match x with (a , A) => is_atom A end) T.

Fixpoint eval_p_sequent (val : nat -> R) (T : p_sequent) : sequent :=
  match T with
  | nil => nil
  | (a , A) :: T => match R_order_dec (FOL_R_term_sem val a) with
                    | R_is_gt _ H => (existT (fun x => 0 <? x = true) (FOL_R_term_sem val a) H, A) :: (eval_p_sequent val T)
                    | R_is_lt _ H => (existT (fun x => 0 <? x = true) (-(FOL_R_term_sem val a)) H, -S A) :: (eval_p_sequent val T)
                    | R_is_null _ H => eval_p_sequent val T
                    end
  end.

Fixpoint to_p_sequent (T : sequent) : p_sequent :=
  match T with
  | nil => nil
  | (a, A) :: T => (FOL_R_cst (projT1 a), A) :: (to_p_sequent T)
  end.
  
Definition Permutation_Type_p_seq val (T1 T2 : p_sequent) := Permutation_Type (eval_p_sequent val T1) (eval_p_sequent val T2).

Definition p_hypersequent : Set := list p_sequent.

Definition p_hseq_is_atomic G := Forall_Type p_seq_is_atomic G.

Definition Permutation_Type_p_hseq val (G1 G2 : p_hypersequent) := Permutation_Type (map (eval_p_sequent val) G1) (map (eval_p_sequent val) G2).

Fixpoint to_p_hypersequent (G : hypersequent) : p_hypersequent :=
  match G with
  | nil => nil
  | T :: G => (to_p_sequent T) :: (to_p_hypersequent G)
  end. 

(** ** Complexity *)
Fixpoint HR_complexity_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (a, A) :: T => ((HR_complexity_term A) + (HR_complexity_p_seq T))%nat
  end.

Fixpoint HR_complexity_p_hseq G :=
  match G with
  | nil => (0%nat, 0%nat)
  | T :: G => if HR_complexity_p_seq T =? fst (HR_complexity_p_hseq G) then (fst (HR_complexity_p_hseq G), S (snd (HR_complexity_p_hseq G)))
              else if (HR_complexity_p_seq T <? fst (HR_complexity_p_hseq G))%nat then (fst (HR_complexity_p_hseq G) , snd (HR_complexity_p_hseq G))
                   else (HR_complexity_p_seq T, 1%nat)
  end.

(** ** Max variable appearing in a term of a hypersequent *)
Fixpoint max_var_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (r, A) :: T => Nat.max (max_var_term A) (max_var_p_seq T)
  end.

Fixpoint max_var_p_hseq G :=
  match G with
  | nil => 0%nat
  | T :: G => Nat.max (max_var_p_seq T) (max_var_p_hseq G)
  end.

(** ** Min variable appearing in a weight of a hypersequent *)
Fixpoint max_var_weight_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (r, A) :: T => Nat.max (max_var_FOL_R_term r) (max_var_weight_p_seq T)
  end.

Fixpoint max_var_weight_p_hseq (G : p_hypersequent) :=
  match G with
  | nil => 0%nat
  | T :: G => Nat.max (max_var_weight_p_seq T) (max_var_weight_p_hseq G)
  end.

(** ** Substitution *)
Fixpoint subs_p_seq (D : p_sequent) n t :=
  match D with
  | nil => nil
  | (r, A) :: D => (r , subs A n t) :: (subs_p_seq D n t)
  end.

(** ** Definitions and properties of \vec{r}.A *)

Fixpoint vec (l : list FOL_R_term) (A : term) :=
  match l with
  | nil => nil
  | r :: l => (r , A) :: (vec l A)
  end.

Fixpoint sum_vec (l : list FOL_R_term) :=
  match l with
  | nil => FOL_R_cst 0
  | r :: l => r +R (sum_vec l)
  end.

Fixpoint copy_p_seq n (T : p_sequent) :=
  match n with
  | 0 => nil
  | S n => (copy_p_seq n T) ++ T
  end.

Fixpoint mul_vec r (l : list FOL_R_term) :=
  match l with
  | nil => nil
  | r0 :: l => (FOL_R_mul r r0) :: (mul_vec r l)
  end.

Fixpoint vec_mul_vec l1 l2 :=
  match l1 with
  | nil => nil
  | r :: l1 => (mul_vec r l2) ++ (vec_mul_vec l1 l2)
  end.

(** ** Sum of the weights *)
Fixpoint sum_weight_p_seq_var n (T : p_sequent) :=
  match T with
  | nil => FOL_R_cst 0
  | ((r , var n0) :: T) => if n =? n0 then r +R (sum_weight_p_seq_var n T) else sum_weight_p_seq_var n T
  | ( _ :: T) => sum_weight_p_seq_var n T
  end.
Fixpoint sum_weight_p_seq_covar n (T : p_sequent) :=
  match T with
  | nil => FOL_R_cst 0
  | ((r , covar n0) :: T) => if n =? n0 then r +R (sum_weight_p_seq_covar n T) else sum_weight_p_seq_covar n T
  | ( _ :: T) => sum_weight_p_seq_covar n T
  end.
Fixpoint p_sum_weight_var n G :=
  match G with
  | nil => FOL_R_cst 0
  | T :: G => (sum_weight_p_seq_var n T) +R (p_sum_weight_var n G)
  end.
Fixpoint p_sum_weight_covar n G :=
  match G with
  | nil => FOL_R_cst 0
  | T :: G => (sum_weight_p_seq_covar n T) +R (p_sum_weight_covar n G)
  end.

(** ** well defined hypersequent with regard to a valuation (i.e. all the weights of the hypersequent are strictly positive with this valuation) *)
Inductive p_seq_well_defined (val : nat -> R) : p_sequent -> Type :=
| p_seq_nil_well_defined : p_seq_well_defined val nil
| p_seq_cons_well_defined : forall r A T, (0 <? FOL_R_term_sem val r = true) -> p_seq_well_defined val T -> p_seq_well_defined val ((r, A) :: T).

Inductive p_hseq_well_defined (val : nat -> R) : p_hypersequent -> Type :=
| p_hseq_nil_well_defined : p_hseq_well_defined val nil
| p_hseq_cons_well_defined : forall T G, p_seq_well_defined val T -> p_hseq_well_defined val G -> p_hseq_well_defined val (T :: G).

(** * Properties *)
(** ** vec *)
Lemma vec_app : forall vr1 vr2 A, vec (vr1 ++ vr2) A = vec vr1 A ++ vec vr2 A.
Proof.
  induction vr1; intros vr2 A; simpl; try rewrite IHvr1; try reflexivity.
Qed.

Lemma sum_vec_app : forall vr1 vr2 val, FOL_R_pred_sem val ((sum_vec (vr1 ++ vr2)) =R ((sum_vec vr1) +R (sum_vec vr2))).
Proof.
  induction vr1; intros vr2 val.
  - rewrite app_nil_l; simpl; nra.
  - simpl.
    rewrite IHvr1.
    destruct a; simpl; nra.
Qed.

Lemma mul_vec_sum_vec : forall r vr val, FOL_R_pred_sem val (sum_vec (mul_vec r vr) =R r *R (sum_vec vr)).
Proof.
  intro r; induction vr; intros val.
  - simpl; nra.
  - simpl.
    rewrite IHvr.
    simpl; nra.
Qed.

Lemma sum_vec_vec_mul_vec : forall vr vs val, FOL_R_pred_sem val (sum_vec (vec_mul_vec vr vs) =R (sum_vec vr) *R (sum_vec vs)).
Proof.
  induction vr; intros vs val.
  - simpl; nra.
  - unfold vec_mul_vec; fold vec_mul_vec.
    unfold sum_vec; fold sum_vec.
    simpl; rewrite sum_vec_app.
    simpl; rewrite mul_vec_sum_vec.
    rewrite IHvr.
    simpl; nra.
Qed.

Lemma vec_mul_vec_nil_r : forall vr, vec_mul_vec vr nil = nil.
Proof with try reflexivity.
  induction vr...
  simpl; rewrite IHvr...
Qed.

Lemma vec_mul_vec_cons_r : forall vr1 vr2 r val, Permutation_Type_FOL_R_term val (vec_mul_vec vr1 (r :: vr2)) (mul_vec r vr1 ++ vec_mul_vec vr1 vr2).
Proof.
  unfold Permutation_Type_FOL_R_term.
  induction vr1; intros vr2 r val; simpl; try reflexivity.
  replace (FOL_R_term_sem val a * FOL_R_term_sem val r) with (FOL_R_term_sem val r * FOL_R_term_sem val a) by (simpl; nra).
  apply Permutation_Type_skip.
  rewrite ? map_app; rewrite app_assoc.
  etransitivity ; [ | apply Permutation_Type_app ; [ apply Permutation_Type_app_comm | reflexivity ] ].
  rewrite <- app_assoc; apply Permutation_Type_app; try reflexivity.
  rewrite <- map_app; apply IHvr1.
Qed.

Lemma vec_mul_vec_comm : forall vr1 vr2 val, Permutation_Type_FOL_R_term val (vec_mul_vec vr1 vr2) (vec_mul_vec vr2 vr1).
Proof.
  unfold Permutation_Type_FOL_R_term.
  induction vr1; intros vr2 val.
  - simpl; rewrite vec_mul_vec_nil_r; reflexivity.
  - simpl.
    etransitivity ; [ | symmetry; apply vec_mul_vec_cons_r ].
    rewrite ? map_app; apply Permutation_Type_app; try reflexivity.
    apply IHvr1.
Qed.

Lemma mul_vec_app : forall vr vs r, mul_vec r (vr ++ vs) = mul_vec r vr ++ mul_vec r vs.
Proof.
  induction vr; intros vs r; simpl; try rewrite IHvr; try reflexivity.
Qed.

Lemma mul_vec_perm : forall vr vs r val, Permutation_Type_FOL_R_term val vr vs ->  Permutation_Type_FOL_R_term val (mul_vec r vr) (mul_vec r vs).
Proof.
  unfold Permutation_Type_FOL_R_term.
  intros vr vs r val Hperm.
  remember (map (FOL_R_term_sem val) vr) as lr; remember (map (FOL_R_term_sem val) vs) as ls.
  revert vr vs Heqlr Heqls; induction Hperm; intros vr vs Heqlr Heqls.
  - symmetry in Heqlr; apply map_eq_nil in Heqlr; symmetry in Heqls; apply map_eq_nil in Heqls; subst.
    reflexivity.
  - destruct vr; destruct vs; inversion Heqlr; inversion Heqls; subst.
    simpl; rewrite H2; apply Permutation_Type_skip.
    apply IHHperm; reflexivity.
  - destruct vr; [ | destruct vr]; (destruct vs; [ | destruct vs]); inversion Heqlr; inversion Heqls; subst.
    simpl; rewrite H3; rewrite H4.
    replace (map (FOL_R_term_sem val) (mul_vec r vs)) with (map (FOL_R_term_sem val) (mul_vec r vr)); [ apply Permutation_Type_swap | ].
    clear - H5.
    revert vs H5; induction vr; intros vs H5.
    + destruct vs; try now inversion H5.
    + destruct vs; inversion H5; subst.
      simpl; rewrite H0.
      now rewrite IHvr with vs.
  - subst.
    apply Permutation_Type_map_inv in Hperm2 as [vr' Heq' Hperm']; subst.    
    etransitivity; [apply IHHperm1 | apply IHHperm2]; auto.
Qed.
(*
Lemma mul_vec_mul_vec_comm : forall vr r s val, FOL_R_pred_sem (mul_vec r (mul_vec s vr) =? mul_vec s (mul_vec r vr)).
Proof.
  induction vr; intros r s; simpl; try rewrite IHvr; try reflexivity.
  replace (time_pos r (time_pos s a)) with (time_pos s (time_pos r a)); try reflexivity.
  destruct s; destruct r; destruct a; apply Rpos_eq; simpl; nra.
Qed.

Lemma vec_mul_vec_mul_vec_comm : forall vr vs r, vec_mul_vec vr (mul_vec r vs) =  mul_vec r (vec_mul_vec vr vs).
Proof.
  induction vr; intros vs r; try reflexivity.
  simpl.
  rewrite mul_vec_app.
  rewrite IHvr.
  rewrite mul_vec_mul_vec_comm.
  reflexivity.
Qed.
*)
Lemma vec_perm : forall vr1 vr2 A val,
    Permutation_Type_FOL_R_term val vr1 vr2 -> Permutation_Type_p_seq val (vec vr1 A) (vec vr2 A).
Proof.
  unfold Permutation_Type_FOL_R_term; unfold Permutation_Type_p_seq.
  intros vr1 vr2 A val Hperm.
  remember (map (FOL_R_term_sem val) vr1) as l1; remember (map (FOL_R_term_sem val) vr2) as l2.
  revert vr1 vr2 Heql1 Heql2; induction Hperm; intros vr1 vr2 Heql1 Heql2.
  - destruct vr1; destruct vr2; inversion Heql1; now inversion Heql2.
  - destruct vr1; destruct vr2; inversion Heql1; inversion Heql2; subst.
    simpl; rewrite H2.
    sem_is_pos_decomp val f0; intros;
      try apply Permutation_Type_skip;
      now apply IHHperm.
  - destruct vr1; [ | destruct vr1]; (destruct vr2; [ | destruct vr2]); inversion Heql1; inversion Heql2; simpl; subst.
    rewrite H3; rewrite H4.
    replace (eval_p_sequent val (vec vr1 A)) with (eval_p_sequent val (vec vr2 A)) ; [ sem_is_pos_decomp val f1; sem_is_pos_decomp val f2 ;intros; now try apply Permutation_Type_swap | ].
    clear - H5.
    revert vr2 H5; induction vr1; intros vr2 H5; destruct vr2; inversion H5; subst; try reflexivity.
    simpl; rewrite H0; now rewrite IHvr1.
  - subst.
    apply Permutation_Type_map_inv in Hperm2 as [vr' Heq' Hperm']; subst.    
    etransitivity; [apply IHHperm1 | apply IHHperm2]; auto.
Qed.

Lemma sum_mul_vec : forall val l r, FOL_R_pred_sem val (sum_vec (mul_vec r l) =R FOL_R_mul r (sum_vec l)).
Proof.
  intros val; induction l; intros r.
  - simpl; nra.
  - specialize (IHl r).
    simpl in *.
    rewrite IHl.
    nra.
Qed.

Lemma sum_vec_perm : forall val vr vs,
    Permutation_Type vr vs ->
    FOL_R_pred_sem val (sum_vec vr =R sum_vec vs).
Proof.
  intros val vr vs Hperm; induction Hperm; simpl in *; nra.
Qed.

Lemma mul_vec_length : forall r vr,
    length (mul_vec r vr) = length vr.
Proof.
  intros r; induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.
(*
Lemma perm_decomp_vec_eq_2 : forall val T D r s r' s' A B,
    A <> B ->
    Permutation_Type_p_seq val (vec s' B ++ vec r' A ++ T) (vec s B ++ vec r A ++ D) ->
    {' (a1 , b1 , c1, a2 , b2, c2, T', D') : _ &
                     prod (Permutation_Type_FOL_R_term val r  (a1 ++ b1))
                          ((Permutation_Type_FOL_R_term val r'  (b1 ++ c1)) *
                           (Permutation_Type_FOL_R_term val s  (a2 ++ b2)) *
                           (Permutation_Type_FOL_R_term val s'  (b2 ++ c2)) *
                           (Permutation_Type_p_seq val T (vec a2 B ++ vec a1 A ++ T')) *
                           (Permutation_Type_p_seq val D (vec c2 B ++ vec c1 A ++ D')) *
                           (Permutation_Type_p_seq val T' D')) }.
Proof.
  unfold Permutation_Type_FOL_R_term; unfold Permutation_Type_p_seq.
  intros val T D r s r' s' A B Hneq Hperm.
  revert s r' r T D A B Hneq Hperm.
  induction s'; [ intros s ; induction s ; [ intros r'; induction r'; [ intros r; induction r | ] | ] | ].
  - intros T D A B Hneq Hperm.
    split with (nil, nil,nil,nil,nil,nil , T , D).
    repeat split; simpl in *; try perm_Type_solve.
  - intros T D A B Hneq Hperm.
    simpl in *.
    destruct (in_Type_split (FOL_R_term_sem val a , A) (eval_p_sequent val T)) as [[T1 T2] HeqT].
    { apply Permutation_Type_in_Type with ((FOL_R_term_sem val a , A) :: eval_p_sequent val (vec r A ++ D)); try perm_Type_solve.
      left; reflexivity. }
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
Qed. *)

(** ** Sequent *)

Lemma eval_p_sequent_cons : forall val r H A T,
    (existT _ (FOL_R_term_sem val r) H, A) :: eval_p_sequent val T = eval_p_sequent val ((r, A) :: T).
Proof.
  intros val r H A T.
  simpl in *.
  sem_is_pos_decomp val r; intros e He;
    [ | exfalso; clear - H e; apply R_blt_lt in H; apply R_blt_lt in e; lra
      | exfalso; clear - H e; apply R_blt_lt in H; lra].
  replace H with e by apply UIP_bool.
  reflexivity.
Qed.

Lemma Permutation_Type_eval_p_sequent : forall val T D,
    Permutation_Type T D ->
    Permutation_Type (eval_p_sequent val T) (eval_p_sequent val D).
Proof.
  intros val T D Hperm; induction Hperm; auto.
  - destruct x as [a A]; simpl.
    sem_is_pos_decomp val a; intros e He; try apply Permutation_Type_skip; assumption.
  - destruct x as [a A]; destruct y as [b B]; simpl.
    sem_is_pos_decomp val a; sem_is_pos_decomp val b; intros eb Heb ea Hea; try reflexivity; try apply Permutation_Type_swap.
  - etransitivity; [ apply IHHperm1 | apply IHHperm2 ].
Qed.
                                    
Lemma Permutation_Type_perm_eval_inv : forall val l T,
    Permutation_Type l (eval_p_sequent val T) ->
    { D & l = eval_p_sequent val D}.
Proof.
  intros val l T Hperm.
  remember (eval_p_sequent val T).
  revert T Heqs; induction Hperm; intros T Heqs.
  - split with nil; reflexivity.
  - induction T; try now inversion Heqs.
    destruct a as [a A]; simpl in Heqs.
    revert Heqs; sem_is_pos_decomp val a; intros e He Heqs;
      inversion Heqs; subst.
    + specialize (IHHperm T eq_refl) as [D Heq].
      split with ((a , A) :: D); simpl; rewrite He; rewrite Heq; try reflexivity.
    + specialize (IHHperm T eq_refl) as [D Heq].
      split with ((a , A) :: D); simpl; rewrite He; rewrite Heq; try reflexivity.
    + apply IHT.
      apply Heqs.
  - remember (length T).
    revert T Heqs Heqn.
    induction n; intros T Heqs Heqn.
    { destruct T; inversion Heqs; inversion Heqn. }
    destruct T ; [ | destruct T]; try now inversion Heqn.
    + exfalso.
      destruct p as [a A].
      simpl in Heqs.
      sem_is_pos_decomp val a; intros e He; rewrite He in Heqs; inversion Heqs.
    + destruct p as [a A]; destruct p0 as [b B]; simpl in Heqs.
      sem_is_pos_decomp val a; intros ea Hea; rewrite Hea in Heqs;
        sem_is_pos_decomp val b; intros eb Heb; rewrite Heb in Heqs;
          try (inversion Heqs; subst;
               split with ((b , B) :: (a , A) :: T);
               simpl; rewrite Hea; rewrite Heb; reflexivity);
          try (apply (IHn ((a, A) :: T));
               [simpl; rewrite Hea; apply Heqs |
                simpl in *; lia]);
          try (apply (IHn ((b, B) :: T));
               [simpl; rewrite Heb; apply Heqs |
                simpl in *; lia]).
  - specialize (IHHperm2 T Heqs) as [D Heq].
    apply IHHperm1 with D.
    apply Heq.
Qed.

Fixpoint seq_mul (r : FOL_R_term) (T : p_sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (FOL_R_mul r a, A) :: (seq_mul r T)
  end.
(*
Lemma seq_mul_One : forall val T, Forall2_Type (fun x y => FOL_R_pred_sem val (x =R y)) (seq_mul (FOL_R_cst 1) T) T.
  induction T; try reflexivity.
  destruct a as (a , A).
  unfold seq_mul; fold seq_mul.
  replace (time_pos One a) with a by (apply Rpos_eq; destruct a; simpl; nra).
  rewrite IHT; reflexivity.
Qed. *)
  
Lemma seq_mul_app : forall T1 T2 r, seq_mul r (T1 ++ T2) = seq_mul r T1 ++ seq_mul r T2.
Proof.
  induction T1; intros T2 r; try reflexivity.
  destruct a as (a , A).
  simpl; rewrite IHT1.
  reflexivity.
Qed.
(*
Lemma seq_mul_twice : forall T r1 r2,
    seq_mul r1 (seq_mul r2 T) = seq_mul (time_pos r1 r2) T.
Proof.
  induction T as [ | [a A] T]; intros r1 r2; simpl; try reflexivity.
  rewrite IHT.
  replace (time_pos r1 (time_pos r2 a)) with (time_pos (time_pos r1 r2) a) by (apply Rpos_eq;destruct r1; destruct r2; destruct a; simpl; nra).
  reflexivity.
Qed.*)

Fixpoint seq_mul_vec vr T :=
  match vr with
  | nil => nil
  | r :: vr => (seq_mul r T) ++ (seq_mul_vec vr T)
  end.

Lemma seq_mul_vec_nil_r : forall vr,
    seq_mul_vec vr nil = nil.
Proof.
  induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.

Lemma seq_mul_vec_app_l : forall T vr1 vr2,
    seq_mul_vec (vr1 ++ vr2) T = seq_mul_vec vr1 T ++ seq_mul_vec vr2 T.
Proof.
  intros T; induction vr1; intros vr2; try reflexivity.
  simpl.
  rewrite IHvr1.
  rewrite app_assoc; reflexivity.
Qed.
(*
Lemma seq_mul_vec_app_r : forall T1 T2 vr,
    Permutation_Type (seq_mul_vec vr (T1 ++ T2)) (seq_mul_vec vr T1 ++ seq_mul_vec vr T2).
Proof.
  intros T1 T2; induction vr; try reflexivity.
  simpl.
  rewrite seq_mul_app.
  perm_Type_solve.
Qed.


Lemma seq_mul_vec_perm_r : forall vr T1 T2,
    Permutation_Type T1 T2 ->
    Permutation_Type (seq_mul_vec vr T1) (seq_mul_vec vr T2).
Proof.
  intros vr T1 T2 Hperm; induction Hperm; try perm_Type_solve.
  - rewrite cons_is_app.
    etransitivity ; [ apply seq_mul_vec_app_r | ].
    rewrite (cons_is_app _ l').
    etransitivity ; [ | symmetry; apply seq_mul_vec_app_r].
    perm_Type_solve.
  - rewrite (cons_is_app _ (x :: l)).
    etransitivity ; [ apply seq_mul_vec_app_r | ].
    rewrite (cons_is_app _ l).
    etransitivity ; [ apply Permutation_Type_app; try apply seq_mul_vec_app_r; reflexivity | ].
    rewrite (cons_is_app _ (y :: l)).
    etransitivity ; [ | symmetry ; apply seq_mul_vec_app_r ].
    rewrite (cons_is_app _ l).
    etransitivity ; [ | symmetry; apply Permutation_Type_app; try apply seq_mul_vec_app_r; reflexivity ].
    perm_Type_solve.
Qed.

Lemma seq_mul_vec_perm_l : forall vr1 vr2 T,
    Permutation_Type vr1 vr2 ->
    Permutation_Type (seq_mul_vec vr1 T) (seq_mul_vec vr2 T).
Proof.
  intros vr1 vr2 T Hperm; induction Hperm; try perm_Type_solve.
Qed.
    
Lemma seq_mul_p_seq_mul_vec: forall T vr r,
    seq_mul r (seq_mul_vec vr T) = seq_mul_vec vr (seq_mul r T).
Proof.
  intros T vr; revert T; induction vr; intros T r; try reflexivity.
  simpl. rewrite seq_mul_app; rewrite IHvr; rewrite 2 seq_mul_twice.
  replace (time_pos r a) with (time_pos a r) by (apply Rpos_eq; destruct r; destruct a; simpl; nra).
  reflexivity.
Qed.

Lemma seq_mul_p_seq_mul_vec_2: forall T vr r,
    seq_mul r (seq_mul_vec vr T) = seq_mul_vec (mul_vec r vr) T.
Proof.
  intros T vr; revert T; induction vr; intros T r; try reflexivity.
  simpl. rewrite seq_mul_app; rewrite IHvr; rewrite seq_mul_twice.
  reflexivity.
Qed.
  
Lemma seq_mul_vec_twice : forall T vr1 vr2,
    Permutation_Type (seq_mul_vec vr1 (seq_mul_vec vr2 T)) (seq_mul_vec (vec_mul_vec vr1 vr2) T).
Proof.
  intros T vr1; revert T; induction vr1; intros T vr2; try reflexivity.
  simpl.
  rewrite seq_mul_p_seq_mul_vec_2; rewrite seq_mul_vec_app_l.
  specialize (IHvr1 T vr2).
  perm_Type_solve.
Qed.

Lemma seq_mul_vec_twice_comm : forall T vr1 vr2,
    Permutation_Type (seq_mul_vec vr1 (seq_mul_vec vr2 T)) (seq_mul_vec vr2 (seq_mul_vec vr1 T)).
Proof.
  intros T vr1; revert T; induction vr1; intros T vr2.
  - simpl; rewrite seq_mul_vec_nil_r.
    reflexivity.
  -  simpl.
     etransitivity ; [ | symmetry; apply seq_mul_vec_app_r].
     apply Permutation_Type_app.
     + rewrite seq_mul_p_seq_mul_vec.
       reflexivity.
     + apply IHvr1.
Qed.

Lemma seq_mul_vec_vec : forall A vr1 vr2,
    Permutation_Type (seq_mul_vec vr1 (vec vr2 A)) (seq_mul_vec vr2 (vec vr1 A)).
Proof.
  intros A vr1; revert A; induction vr1; intros A vr2.
  - simpl; rewrite seq_mul_vec_nil_r.
    reflexivity.
  -  simpl.
     change ((a, A) :: vec vr1 A) with ((vec (a :: nil) A) ++ vec vr1 A).
     etransitivity ; [ | symmetry; apply seq_mul_vec_app_r].
     apply Permutation_Type_app.
     + clear.
       induction vr2; simpl; try reflexivity.
       replace (time_pos a a0) with (time_pos a0 a) by (apply Rpos_eq; destruct a; destruct a0; simpl; nra).
       apply Permutation_Type_skip.
       apply IHvr2.
     + apply IHvr1.
Qed.

Lemma seq_mul_vec_mul_vec : forall A r vr,
    seq_mul r (vec vr A) = vec (mul_vec r vr) A.
Proof.
  intros A r vr; induction vr; simpl; try rewrite IHvr; try reflexivity.
Qed.

Lemma seq_mul_vec_vec_mul_vec : forall vr vs A,
    seq_mul_vec vr (vec vs A) = vec (vec_mul_vec vr vs) A.
Proof.
  induction vr; intros vs A.
  - reflexivity.
  - simpl.
    rewrite vec_app.
    rewrite IHvr.
    rewrite seq_mul_vec_mul_vec.
    reflexivity.
Qed.

    
Lemma seq_mul_perm : forall T1 T2 r,
    Permutation_Type T1 T2 ->
    Permutation_Type (seq_mul r T1) (seq_mul r T2).
Proof.
  intros T1 T2 r Hperm; induction Hperm; try destruct x; try destruct y; try now constructor.
  transitivity (seq_mul r l'); assumption.
Qed.

(** ** Substitution *)

Lemma subs_p_seq_app : forall D D' n t, subs_p_seq (D ++ D') n t = subs_p_seq D n t ++ subs_p_seq D' n t.
Proof.
  induction D; intros D' n t; simpl; try rewrite IHD; try destruct a; try reflexivity.
Qed.

Lemma subs_p_seq_vec : forall D n t A r, subs_p_seq ((vec r A) ++ D) n t = vec r (subs A n t) ++ subs_p_seq D n t.
Proof.
  intros D n t A; induction r;simpl; try rewrite IHr; try reflexivity.
Qed.

Lemma subs_p_seq_ex : forall T1 T2 n t, Permutation_Type T1 T2 -> Permutation_Type (subs_p_seq T1 n t) (subs_p_seq T2 n t).
Proof.
  intros T1 T2 n t Hperm; induction Hperm; try destruct x; try destruct y; simpl; try now constructor.
  transitivity (subs_p_seq l' n t); assumption.
Qed.

Fixpoint subs_p_hseq (G : hypersequent) n t :=
  match G with
  | nil => nil
  | D :: G => (subs_p_seq D n t) :: (subs_p_hseq G n t)
  end.

Lemma subs_p_hseq_ex : forall G1 G2 n t, Permutation_Type G1 G2 -> Permutation_Type (subs_p_hseq G1 n t) (subs_p_hseq G2 n t).
Proof.
  intros G1 G2 n t Hperm; induction Hperm; try destruct x; try destruct y; simpl; try now constructor.
  transitivity (subs_p_hseq l' n t); assumption.
Qed.

(** ** Atomic *)

Lemma copy_p_seq_atomic : forall n T, seq_is_atomic T -> seq_is_atomic (copy_p_seq n T).
Proof.
  induction n; intros T Hat; simpl; [ apply Forall_Type_nil | ].
  apply Forall_Type_app; auto.
  apply IHn; assumption.
Qed.

Lemma seq_atomic_app : forall T1 T2,
    seq_is_atomic T1 ->
    seq_is_atomic T2 ->
    seq_is_atomic (T1 ++ T2).
Proof.
  intros T1 T2 Hat1.
  induction Hat1; intros Hat2.
  - apply Hat2.
  - simpl; apply Forall_Type_cons; try assumption.
    apply IHHat1.
    apply Hat2.
Qed.

Lemma seq_atomic_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    seq_is_atomic T1 ->
    seq_is_atomic T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; intro Hat.
  - apply Forall_Type_nil.
  - inversion Hat; subst; apply Forall_Type_cons; [ | apply IHHperm]; assumption.
  - inversion Hat; inversion X0; subst.
    apply Forall_Type_cons ; [ | apply Forall_Type_cons ]; assumption.
  - apply IHHperm2; apply IHHperm1; apply Hat.
Qed.

Lemma hseq_atomic_perm : forall G H,
    Permutation_Type G H ->
    hseq_is_atomic G ->
    hseq_is_atomic H.
Proof.
  intros G H Hperm; induction Hperm; intro Hat.
  - apply Forall_Type_nil.
  - inversion Hat; subst; apply Forall_Type_cons; [ | apply IHHperm]; assumption.
  - inversion Hat; inversion X0; subst.
    apply Forall_Type_cons ; [ | apply Forall_Type_cons ]; assumption.
  - apply IHHperm2; apply IHHperm1; apply Hat.
Qed.

Lemma seq_atomic_app_inv_l : forall T1 T2,
    seq_is_atomic (T1 ++ T2) ->
    seq_is_atomic T1.
Proof.
  intros T1; induction T1; intros T2 Hat; try now constructor.
  simpl in Hat; inversion Hat; subst.
  apply Forall_Type_cons; try assumption.
  apply IHT1 with T2; apply X0.
Qed.

Lemma seq_atomic_app_inv_r : forall T1 T2,
    seq_is_atomic (T1 ++ T2) ->
    seq_is_atomic T2.
Proof.
  intros T1; induction T1; intros T2 Hat; try assumption.
  simpl in Hat; inversion Hat; subst.
  apply IHT1; assumption.
Qed.

Lemma seq_atomic_mul : forall T r,
    seq_is_atomic T ->
    seq_is_atomic (seq_mul r T).
Proof.
  intros T r Hat; induction Hat; try destruct x; simpl; try now constructor.
Qed.
*)
(** ** sum_weight_p_seq_(co)var *)

Lemma sum_weight_p_seq_var_lt_max_var : forall val n T1,
    (max_var_p_seq T1 < n)%nat ->
    FOL_R_term_sem val (sum_weight_p_seq_var n T1) = 0.
Proof.
  intros val n; induction T1; intros Hlt; auto.
  destruct a as [a A].
  destruct A; simpl in *; try (apply IHT1; simpl ; lia).
  replace (n =? n0) with false by (symmetry; apply Nat.eqb_neq; lia).
  apply IHT1.
  lia.
Qed.

Lemma sum_weight_p_seq_covar_lt_max_var : forall val n T1,
    (max_var_p_seq T1 < n)%nat ->
    FOL_R_term_sem val (sum_weight_p_seq_covar n T1) = 0.
Proof.
  intros val n; induction T1; intros Hlt; auto.
  destruct a as [a A].
  destruct A; simpl in *; try (apply IHT1 ; lia).
  replace (n =? n0) with false by (symmetry; apply Nat.eqb_neq; lia).
  apply IHT1.
  lia.
Qed. 
    
Lemma sum_weight_p_seq_var_app : forall val n T1 T2,
    FOL_R_pred_sem val (sum_weight_p_seq_var n (T1 ++ T2) =R sum_weight_p_seq_var n T1 +R sum_weight_p_seq_var n T2).
Proof.
  intros val n T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; try case (n =? n0); simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_covar_app : forall val n T1 T2,
    FOL_R_pred_sem val (sum_weight_p_seq_covar n (T1 ++ T2) =R sum_weight_p_seq_covar n T1 +R sum_weight_p_seq_covar n T2).
Proof.
  intros val n T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; try case (n =? n0); simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_var_mul : forall val n T r,
    FOL_R_pred_sem val (sum_weight_p_seq_var n (seq_mul r T) =R r *R sum_weight_p_seq_var n T).
Proof.
  intros val n T r; induction T; simpl in *; try nra.
  destruct a as [a A]; simpl.
  destruct A; try case (n =? n0); destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_covar_mul : forall val n T r,
    FOL_R_pred_sem val (sum_weight_p_seq_covar n (seq_mul r T) =R r *R sum_weight_p_seq_covar n T).
Proof.
  intros val n T r; induction T; simpl in *; try nra.
  destruct a as [a A]; simpl.
  destruct A; try case (n =? n0); destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_p_seq_var_vec_var_eq : forall val n r,
    FOL_R_pred_sem val (sum_weight_p_seq_var n (vec r (var n)) =R sum_vec r).
Proof.
  intros val n; induction r; simpl in *; try (rewrite Nat.eqb_refl; simpl; rewrite IHr); reflexivity.
Qed.

Lemma sum_weight_p_seq_covar_vec_covar_eq : forall val n r,
    FOL_R_pred_sem val (sum_weight_p_seq_covar n (vec r (covar n)) =R sum_vec r).
Proof.
  intros val n; induction r; simpl; try (rewrite Nat.eqb_refl; simpl; rewrite IHr); nra.
Qed.

Lemma sum_weight_p_seq_var_vec_neq : forall val n A r,
    var n <> A ->
    FOL_R_term_sem val (sum_weight_p_seq_var n (vec r A)) = 0.
Proof.
  intros val n A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; try (case_eq (n =? n0) ; [ intros H; exfalso; apply Nat.eqb_eq in H; now subst | ]); auto.
Qed.

Lemma sum_weight_p_seq_covar_vec_neq : forall val n A r,
    covar n <> A ->
    FOL_R_term_sem val (sum_weight_p_seq_covar n (vec r A)) = 0.
Proof.
  intros val n A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; try (case_eq (n =? n0) ; [ intros H; exfalso; apply Nat.eqb_eq in H; now subst | ]); auto.
Qed.
(*
Lemma sum_weight_p_seq_var_eval : forall val n T1 T2,
    eval_p_sequent val T1 = eval_p_sequent val T2 ->
    FOL_R_pred_sem val (sum_weight_p_seq_var n T1 =R sum_weight_p_seq_var n T2).
Proof.
  intros val n; induction T1; induction T2; intros Heq; simpl in *; try reflexivity.
  - destruct a as [a A].
    sem_is_pos_decomp val a; intros e He; simpl in Heq; rewrite He in *; try now inversion Heq.
    destruct A; try case (n =? n0); simpl; try rewrite e; specialize (IHT2 Heq); lra.
  - destruct a as [a A].
    sem_is_pos_decomp val a; intros e He;
      rewrite He in Heq; inversion Heq; subst.
    specialize (IHT1 nil H0).
    destruct A; try case (n =? n0); simpl in *; rewrite IHT1; try rewrite e; lra.
    
  -
    specialize (IHT1 T2 H2).
    destruct a as [a A]; destruct p as [b B].
    simpl in *.
    destruct A; destruct B; inversion H1; subst; try case (n =? n1); simpl; try nra.
Qed.

Lemma sum_weight_p_seq_var_perm : forall val n T1 T2,
    Permutation_Type_p_seq val T1 T2 ->
    FOL_R_pred_sem val (sum_weight_p_seq_var n T1 =R sum_weight_p_seq_var n T2).
Proof.
  unfold Permutation_Type_p_seq.
  intros val n T1 T2 Hperm.
  remember (eval_p_sequent val T1); remember (eval_p_sequent val T2).
  revert T1 T2 Heql Heql0; induction Hperm; intros T1 T2 Heql Heql0; subst.
  - destruct T1; destruct T2; inversion Heql; inversion Heql0; reflexivity.
  - destruct T1; destruct T2; inversion Heql; inversion Heql0; subst.
    destruct p; destruct p0; inversion H2; subst.
    simpl in *.
    destruct t0; try case (n =? n0); simpl; rewrite (IHHperm T1 T2); try rewrite H0; reflexivity.
  - destruct T1; [ | destruct T1]; (destruct T2 ; [ | destruct T2]); inversion Heql; inversion Heql0; subst.
    apply sum_weight_p_seq_var_eval with _ n _ _ in H5.
    destruct p; destruct p0; destruct p1; destruct p2; inversion H3; inversion H4; subst.
    simpl in *.
    destruct t1; destruct t2; try case (n =? n0); try case (n =? n1); simpl; try nra.
  - simpl in *.
    destruct (Permutation_Type_perm_eval_inv _ _ _ Hperm2) as [T3 Heq]; subst.
    etransitivity ; [ apply IHHperm1 | apply IHHperm2 ]; reflexivity.
Qed.

Lemma sum_weight_p_seq_covar_eval : forall val n T1 T2,
    eval_p_sequent val T1 = eval_p_sequent val T2 ->
    FOL_R_pred_sem val (sum_weight_p_seq_covar n T1 =R sum_weight_p_seq_covar n T2).
Proof.
  intros val n; induction T1; intros T2 Heq; simpl in *; destruct T2; inversion Heq; subst; try reflexivity.
  specialize (IHT1 T2 H2).
  destruct a as [a A]; destruct p as [b B].
  simpl in *.
  destruct A; destruct B; inversion H1; subst; try case (n =? n1); simpl; try nra.
Qed.

Lemma sum_weight_p_seq_covar_perm : forall val n T1 T2,
    Permutation_Type_p_seq val T1 T2 ->
    FOL_R_pred_sem val (sum_weight_p_seq_covar n T1 =R sum_weight_p_seq_covar n T2).
Proof.
  unfold Permutation_Type_p_seq.
  intros val n T1 T2 Hperm.
  remember (eval_p_sequent val T1); remember (eval_p_sequent val T2).
  revert T1 T2 Heql Heql0; induction Hperm; intros T1 T2 Heql Heql0; subst.
  - destruct T1; destruct T2; inversion Heql; inversion Heql0; reflexivity.
  - destruct T1; destruct T2; inversion Heql; inversion Heql0; subst.
    destruct p; destruct p0; inversion H2; subst.
    simpl in *.
    destruct t0; try case (n =? n0); simpl; rewrite (IHHperm T1 T2); try rewrite H0; reflexivity.
  - destruct T1; [ | destruct T1]; (destruct T2 ; [ | destruct T2]); inversion Heql; inversion Heql0; subst.
    apply sum_weight_p_seq_covar_eval with _ n _ _ in H5.
    destruct p; destruct p0; destruct p1; destruct p2; inversion H3; inversion H4; subst.
    simpl in *.
    destruct t1; destruct t2; try case (n =? n0); try case (n =? n1); simpl; try nra.
  - simpl in *.
    destruct (Permutation_Type_perm_eval_inv _ _ _ Hperm2) as [T3 Heq]; subst.
    etransitivity ; [ apply IHHperm1 | apply IHHperm2 ]; reflexivity.
Qed.

Lemma p_sum_weight_var_lt_max_var : forall val n G,
    (max_var_p_hseq G < n)%nat ->
    FOL_R_term_sem val (p_sum_weight_var n G) = 0.
Proof.
  intros val n; induction G; intros Hlt; auto.
  simpl in *.
  rewrite IHG; try lia.
  rewrite sum_weight_p_seq_var_lt_max_var; try lia.
  lra.
Qed.

Lemma p_sum_weight_covar_lt_max_var : forall val n G,
    (max_var_p_hseq G < n)%nat ->
    FOL_R_term_sem val (p_sum_weight_covar n G) = 0.
Proof.
  intros val n; induction G; intros Hlt; auto.
  simpl in *.
  rewrite IHG; try lia.
  rewrite sum_weight_p_seq_covar_lt_max_var; try lia.
  lra.
Qed. 

Lemma p_sum_weight_var_eval : forall val n G H,
    map (eval_p_sequent val) G = map (eval_p_sequent val) H ->
    FOL_R_pred_sem val (p_sum_weight_var n G =R p_sum_weight_var n H).
Proof.
  intros val n.
  induction G; intros H Heq; destruct H; inversion Heq; subst; simpl; try nra.
  rewrite (IHG H); try assumption.
  apply sum_weight_p_seq_var_eval with _ n _ _ in H1.
  rewrite H1; reflexivity.
Qed.

Lemma p_sum_weight_var_perm : forall val n G H,
    Permutation_Type_p_hseq val G H ->
    FOL_R_pred_sem val (p_sum_weight_var n G =R p_sum_weight_var n H).
Proof.
  unfold Permutation_Type_p_hseq.
  intros val n G H Hperm.
  remember (map (eval_p_sequent val) G); remember (map (eval_p_sequent val) H).
  revert G H Heql Heql0; induction Hperm; intros G H Heql Heql0; simpl in *.
  - destruct G; destruct H; inversion Heql; inversion Heql0; reflexivity.
  - destruct G; destruct H; inversion Heql; inversion Heql0; subst.
    simpl.
    apply sum_weight_p_seq_var_eval with _ n _ _ in H3.
    rewrite H3.
    rewrite (IHHperm G H); reflexivity.
  - destruct G; [ | destruct G]; (destruct H; [ | destruct H]); inversion Heql; inversion Heql0; subst.
    simpl; apply sum_weight_p_seq_var_eval with _ n _ _ in H4; apply sum_weight_p_seq_var_eval with _ n _ _ in H5; rewrite H4; rewrite H5.
    apply p_sum_weight_var_eval with _ n _ _ in H6.
    rewrite H6; nra.
  - subst.
    apply Permutation_Type_map_inv in Hperm2 as [vr' Heq' Hperm']; subst.    
    etransitivity; [apply IHHperm1 | apply IHHperm2]; auto.    
Qed. 

Lemma p_sum_weight_covar_eval : forall val n G H,
    map (eval_p_sequent val) G = map (eval_p_sequent val) H ->
    FOL_R_pred_sem val (p_sum_weight_covar n G =R p_sum_weight_covar n H).
Proof.
  intros val n.
  induction G; intros H Heq; destruct H; inversion Heq; subst; simpl; try nra.
  rewrite (IHG H); try assumption.
  apply sum_weight_p_seq_covar_eval with _ n _ _ in H1.
  rewrite H1; reflexivity.
Qed.

Lemma p_sum_weight_covar_perm : forall val n G H,
    Permutation_Type_p_hseq val G H ->
    FOL_R_pred_sem val (p_sum_weight_covar n G =R p_sum_weight_covar n H).
Proof.
  unfold Permutation_Type_p_hseq.
  intros val n G H Hperm.
  remember (map (eval_p_sequent val) G); remember (map (eval_p_sequent val) H).
  revert G H Heql Heql0; induction Hperm; intros G H Heql Heql0; simpl in *.
  - destruct G; destruct H; inversion Heql; inversion Heql0; reflexivity.
  - destruct G; destruct H; inversion Heql; inversion Heql0; subst.
    simpl.
    apply sum_weight_p_seq_covar_eval with _ n _ _ in H3.
    rewrite H3.
    rewrite (IHHperm G H); reflexivity.
  - destruct G; [ | destruct G]; (destruct H; [ | destruct H]); inversion Heql; inversion Heql0; subst.
    simpl; apply sum_weight_p_seq_covar_eval with _ n _ _ in H4; apply sum_weight_p_seq_covar_eval with _ n _ _ in H5; rewrite H4; rewrite H5.
    apply p_sum_weight_covar_eval with _ n _ _ in H6.
    rewrite H6; nra.
  - subst.
    apply Permutation_Type_map_inv in Hperm2 as [vr' Heq' Hperm']; subst.    
    etransitivity; [apply IHHperm1 | apply IHHperm2]; auto.    
Qed.
*)
(*
Lemma seq_decomp_atomic :
  forall T n,
    {' (r,s,D) : _ &
                    prod (sum_vec r = sum_weight_p_seq_var n T)
                         ((sum_vec s = sum_weight_p_seq_covar n T) *
                          (Permutation_Type T (vec s (covar n) ++ vec r (var n) ++ D))) }.
Proof.
  induction T; intros n.
  - split with (nil, nil, nil).
    repeat split; try reflexivity.
  - destruct (IHT n) as [[[r s] D] [Hr [Hs Hperm]]].
    destruct a as [a A].
    destruct A; try (esplit with (r , s, (a , _) :: D); repeat split; try assumption;
                     rewrite ? app_assoc; etransitivity ; [ | apply Permutation_Type_middle]; apply Permutation_Type_skip; rewrite <- app_assoc; now apply Hperm).
    + case_eq (n =? n0); intros Heq.
      * split with (a :: r, s, D).
        repeat split.
        -- simpl; rewrite Hr.
           rewrite Heq; reflexivity.
        -- apply Hs.
        -- simpl; apply Nat.eqb_eq in Heq; subst.
           perm_Type_solve.
      * split with (r , s , (a, var n0) :: D).
        repeat split.
        -- simpl; rewrite Hr.
           rewrite Heq; reflexivity.
        -- apply Hs.
        -- simpl; perm_Type_solve.
    + case_eq (n =? n0); intros Heq.
      * split with (r, a :: s, D).
        repeat split.
        -- apply Hr.
        -- simpl; rewrite Hs.
           rewrite Heq; reflexivity.
        -- simpl; apply Nat.eqb_eq in Heq; subst.
           perm_Type_solve.
      * split with (r , s , (a, covar n0) :: D).
        repeat split.
        -- apply Hr.
        -- simpl; rewrite Hs.
           rewrite Heq; reflexivity.
        -- simpl; perm_Type_solve.
Qed.
           
Lemma seq_atomic_decomp_decr :
  forall T,
    seq_is_atomic T ->
    {' (n, r,s,D) : _ &
                    prod (sum_vec r = sum_weight_p_seq_var n T)
                         ((sum_vec s = sum_weight_p_seq_covar n T) *
                          (Permutation_Type T (vec s (covar n) ++ vec r (var n) ++ D)) *
                          ((length D < length T)%nat)) } + { T = nil }.
Proof.
  destruct T; intros Hat.
  - right; reflexivity.
  - left.
    destruct p as (a , A).
    inversion Hat; subst.
    destruct A; try now inversion X.
    + destruct (seq_decomp_atomic T n) as [[[r s] D] [Hr [Hs Hperm]]].
      split with (n, a :: r, s , D).
      repeat split.
      * simpl.
        rewrite Nat.eqb_refl.
        rewrite Hr; reflexivity.
      * apply Hs.
      * perm_Type_solve.
      * simpl.
        apply Permutation_Type_length in Hperm.
        rewrite Hperm.
        rewrite ? app_length.
        lia.
    + destruct (seq_decomp_atomic T n) as [[[r s] D] [Hr [Hs Hperm]]].
      split with (n, r, a :: s , D).
      repeat split.
      * apply Hr.
      * simpl.
        rewrite Nat.eqb_refl.
        rewrite Hs; reflexivity.
      * perm_Type_solve.
      * simpl.
        apply Permutation_Type_length in Hperm.
        rewrite Hperm.
        rewrite ? app_length.
        lia.
Qed.
*)
Lemma p_seq_non_atomic_perm :
  forall T,
    (p_seq_is_atomic T -> False) ->
    {' (A , D) : _ &
                 Permutation_Type T (A :: D) &
                 ~ (is_atom (snd A)) }.
Proof.
  induction T; intros Hnat; [exfalso; apply Hnat; apply Forall_Type_nil | ].
  destruct a as [a A].
  destruct A.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_Type_cons; auto.
      apply I. }
    split with (A, ((a, var n) :: D)); auto.
    perm_Type_solve.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_Type_cons; auto.
      apply I. }
    split with (A, ((a, covar n) :: D)); auto.
    perm_Type_solve.
  - split with ((a, zero), T); auto.
  - split with ((a, A1 +S A2), T); auto.
  - split with ((a, r *S A), T); auto.
  - split with ((a, A1 \/S A2), T); auto.
  - split with ((a, A1 /\S A2), T); auto.
Qed.

Lemma p_seq_atomic_seq_atomic : forall val T,
    p_seq_is_atomic T ->
    seq_is_atomic (eval_p_sequent val T).
Proof.
  intros val T; induction T; intros Hall.
  - apply Forall_Type_nil.
  - destruct a as [a A].
    simpl in Hall |- *.
    inversion Hall; subst.
    sem_is_pos_decomp val a; intros; simpl; try apply Forall_Type_cons; try apply IHT; auto.
    destruct A; inversion X; auto.
Qed.

Lemma p_hseq_atomic_hseq_atomic : forall val G,
    p_hseq_is_atomic G ->
    hseq_is_atomic (map (eval_p_sequent val) G).
Proof.
  intros val; induction G; intros Hat; try apply Forall_Type_nil.
  simpl; inversion Hat; subst; apply Forall_Type_cons; [ apply p_seq_atomic_seq_atomic | apply IHG]; auto.
Qed.

(** Complexity related theorem *)

Lemma complexity_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    HR_complexity_p_seq T1 = HR_complexity_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; try destruct x; try destruct y; simpl; lia.
Qed.

Lemma complexity_p_hseq_perm : forall G1 G2,
    Permutation_Type G1 G2 ->
    HR_complexity_p_hseq G1 = HR_complexity_p_hseq G2.
Proof.
  intros G1 G2 Hperm; induction Hperm.
  - reflexivity.
  - simpl.
    rewrite IHHperm.
    case (HR_complexity_p_seq x =? fst (HR_complexity_p_hseq l'));
      case (HR_complexity_p_seq x <? fst (HR_complexity_p_hseq l'))%nat; reflexivity.
  - simpl.
    case_eq (HR_complexity_p_seq x =? fst (HR_complexity_p_hseq l)); intros H1;
      case_eq (HR_complexity_p_seq y =? fst (HR_complexity_p_hseq l)); intros H2;
        case_eq (HR_complexity_p_seq x <? fst (HR_complexity_p_hseq l))%nat; intros H3;
          case_eq (HR_complexity_p_seq y <? fst (HR_complexity_p_hseq l))%nat; intros H4;
            case_eq (HR_complexity_p_seq x =? HR_complexity_p_seq y); intros H5;
              case_eq (HR_complexity_p_seq x <? HR_complexity_p_seq y)%nat; intros H6;
                case_eq (HR_complexity_p_seq y <? HR_complexity_p_seq x)%nat; intros H7;
                  repeat (simpl; try rewrite H1; try rewrite H2; try rewrite H3; try rewrite H4; try rewrite H5; try (rewrite Nat.eqb_sym in H5; rewrite H5); try rewrite H6; try rewrite H7);
                  try reflexivity;
                  (apply Nat.eqb_eq in H1 + apply Nat.eqb_neq in H1);
                  (apply Nat.eqb_eq in H2 + apply Nat.eqb_neq in H2);
                  (apply Nat.ltb_lt in H3 + apply Nat.ltb_nlt in H3);
                  (apply Nat.ltb_lt in H4 + apply Nat.ltb_nlt in H4);
                  (apply Nat.eqb_eq in H5 + apply Nat.eqb_neq in H5);
                  (apply Nat.ltb_lt in H6 + apply Nat.ltb_nlt in H6);
                  (apply Nat.ltb_lt in H7 + apply Nat.ltb_nlt in H7);
                  try lia.
    rewrite H5; reflexivity.
  - transitivity (HR_complexity_p_hseq l'); assumption.
Qed.

Lemma complexity_p_hseq_perm_fst : forall G,
    G <> nil ->
    {' (T, H) : _ &
                Permutation_Type G (T :: H) &
                HR_complexity_p_seq T = fst (HR_complexity_p_hseq G) }.
  induction G; intros H; [ exfalso; apply H; reflexivity | clear H ].
  simpl.
  case_eq (HR_complexity_p_seq a =? fst (HR_complexity_p_hseq G)); intros H1.
  - split with (a, G); try reflexivity.
    apply Nat.eqb_eq in H1; rewrite H1; reflexivity.
  - case_eq (HR_complexity_p_seq a <? fst (HR_complexity_p_hseq G))%nat; intros H2.
    + destruct G; [ inversion H2 | ].
      destruct IHG as [[T H] Hperm Heq].
      { intros H; inversion H. }
      split with (T, (a :: H)).
      * transitivity (a :: T :: H); perm_Type_solve.
      * rewrite (complexity_p_hseq_perm _ _ Hperm).
        rewrite (complexity_p_hseq_perm _ _ Hperm) in Heq.
        rewrite Heq; reflexivity.
    + split with (a, G); reflexivity.
Qed.

Lemma complexity_p_hseq_perm_fst_p_seq : forall T1 T2 G,
    Permutation_Type T1 T2 ->
    HR_complexity_p_hseq (T1 :: G) = HR_complexity_p_hseq (T2 :: G).
Proof.
  intros T1 T2 G Hperm.
  simpl.
  rewrite (complexity_p_seq_perm _ _ Hperm).
  reflexivity.
Qed.

Lemma complexity_p_seq_app : forall T1 T2,
    HR_complexity_p_seq (T1 ++ T2) = (HR_complexity_p_seq T1 + HR_complexity_p_seq T2)%nat.
Proof.
  induction T1; intros T2; simpl; try rewrite IHT1; try destruct a; lia.
Qed.

Lemma complexity_p_seq_vec : forall r A,
    HR_complexity_p_seq (vec r A) = (length r * HR_complexity_term A)%nat.
Proof.
  induction r; intros A; simpl; try rewrite IHr; lia.
Qed.

Lemma p_seq_is_atomic_complexity_0 :
  forall T,
    p_seq_is_atomic T ->
    HR_complexity_p_seq T = 0%nat.
Proof.
  induction T; intros Hat;
    inversion Hat; simpl; try destruct a; try rewrite IHT; try rewrite is_atom_complexity_0;
      auto.
Qed.

Lemma p_seq_is_atomic_complexity_0_inv :
  forall T,
    HR_complexity_p_seq T = 0%nat ->
    p_seq_is_atomic T.
Proof.
  induction T; intros Heq; [ apply Forall_Type_nil |] .
  destruct a as [a A]; simpl in *.
  apply Forall_Type_cons ; [ apply is_atom_complexity_0_inv  | apply IHT]; lia.
Qed.

Lemma p_hseq_is_atomic_complexity_0 :
  forall G,
    p_hseq_is_atomic G ->
    fst (HR_complexity_p_hseq G) = 0%nat.
Proof.
  induction G; intros Hat; [ reflexivity | ].
  inversion Hat; subst; specialize (IHG X0).
  simpl.
  rewrite p_seq_is_atomic_complexity_0 ; [ | apply X].
  rewrite IHG; reflexivity.
Qed.

Lemma p_hseq_is_atomic_complexity_0_inv :
  forall G,
    fst (HR_complexity_p_hseq G) = 0%nat ->
    p_hseq_is_atomic G.
Proof.
  induction G; intros Heq; [ apply Forall_Type_nil | ].
  simpl in *.
  case_eq (HR_complexity_p_seq a =? fst (HR_complexity_p_hseq G)); intros H; rewrite H in Heq; simpl in Heq ; [ apply Nat.eqb_eq in H | apply Nat.eqb_neq in H ].
  { apply Forall_Type_cons; [ apply p_seq_is_atomic_complexity_0_inv | apply IHG ]; lia. }
  exfalso.
  case_eq (HR_complexity_p_seq a <? fst (HR_complexity_p_hseq G))%nat; intros H2; rewrite H2 in Heq; [apply Nat.ltb_lt in H2 | apply Nat.ltb_nlt in H2]; simpl in *; lia.
Qed.

Lemma hrr_Z_decrease_complexity : forall G T r,
    r <> nil ->
    HR_complexity_p_seq (vec r zero ++ T) = fst (HR_complexity_p_hseq ((vec r zero ++ T) :: G)) ->
    HR_complexity_p_hseq (T :: G) <2 HR_complexity_p_hseq ((vec r zero ++ T) :: G).
Proof.
  intros G T r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq T =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r zero ++ T) =? fst (HR_complexity_p_hseq G)); intros H2.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H2.
    rewrite complexity_p_seq_app in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r zero ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq T <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite complexity_p_seq_app in H2; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq T <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r zero ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite complexity_p_seq_app in H4; lia.
    + apply fst_lt2.
      rewrite complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      simpl; lia.
Qed.
    
Lemma hrr_plus_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_complexity_p_seq (vec r (A +S B) ++ T) = fst (HR_complexity_p_hseq ((vec r (A +S B) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec r A ++ vec r B ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec r A ++ vec r B ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (A +S B) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite 2 complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (A +S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq (vec r A ++ vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq (vec r A ++ vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r (A +S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_p_seq_vec; simpl; lia.
Qed.

Lemma hrr_mul_decrease_complexity : forall G T A r0 r,
    r <> nil ->
    HR_complexity_p_seq (vec r (r0 *S A) ++ T) = fst (HR_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G).
Proof.
  intros G T A r0 r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (r0 *S A) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    rewrite mul_vec_length in H1.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (r0 *S A) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      rewrite mul_vec_length in H1.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      rewrite mul_vec_length in *; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq (vec (mul_vec (FOL_R_cst (projT1 r0)) r) A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r (r0 *S A) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_p_seq_vec; rewrite mul_vec_length in *; simpl; lia.
Qed.

Lemma hrr_min_r_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec r A ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec r A ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite ? complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq (vec r A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq (vec r A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_p_seq_vec; simpl; lia.
Qed.

Lemma hrr_min_l_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec r B ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec r B ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
    + exfalso.
      apply Nat.eqb_neq in H2; apply H2; apply Heq.
    + apply fst_lt2.
      apply Nat.ltb_nlt in H4; apply Nat.eqb_neq in H2; lia.
    + exfalso.
      apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4.
      rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; lia.
    + apply fst_lt2.
      rewrite ? complexity_p_seq_app; destruct r; [ exfalso; apply Hnnil; reflexivity | ].
      rewrite ? complexity_p_seq_vec; simpl; lia.
Qed.

Lemma hrr_max_decrease_complexity : forall G T A B r,
    r <> nil ->
    HR_complexity_p_seq (vec r (A \/S B) ++ T) = fst (HR_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G)) ->
    HR_complexity_p_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) <2 HR_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_complexity_p_seq (vec r A ++ T) =? fst (HR_complexity_p_hseq G)); intros H1; case_eq (HR_complexity_p_seq (vec r (A \/S B) ++ T) =? fst (HR_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_complexity_p_seq (vec r (A \/S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + simpl.
      case_eq (HR_complexity_p_seq (vec r B ++ T) =? fst (HR_complexity_p_hseq G)); intros H4.
      * apply fst_lt2.
        apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
        lia.
      * case_eq (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H5.
        -- apply fst_lt2.
           apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
           lia.
        -- apply fst_lt2.
           rewrite ? complexity_p_seq_app; rewrite ? complexity_p_seq_vec; destruct r; [ exfalso; apply Hnnil; reflexivity | ]; simpl; lia.        
  - replace (HR_complexity_p_seq (vec r A ++ T) <? fst (HR_complexity_p_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_neq in H1; apply Nat.eqb_eq in H2.
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    simpl.
    replace (HR_complexity_p_seq (vec r B ++ T) =? fst (HR_complexity_p_hseq G)) with false.
    2:{ symmetry.
        apply Nat.eqb_neq; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    replace (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    apply snd_lt2; lia.
  - simpl in Heq.
    rewrite H2 in Heq.
    assert ((HR_complexity_p_seq (vec r (A \/S B) ++ T) <? fst (HR_complexity_p_hseq G))%nat = false) as H3.
    { apply Nat.ltb_nlt; apply Nat.eqb_neq in H2.
      intros H; apply Nat.ltb_lt in H.
      rewrite H in Heq.
      simpl in Heq.
      apply H2; apply Heq. }
    rewrite H3; clear Heq.
    case_eq (HR_complexity_p_seq (vec r A ++ T) <? fst (HR_complexity_p_hseq G))%nat; intros H4; simpl.
    + case (HR_complexity_p_seq (vec r B ++ T) =? fst (HR_complexity_p_hseq G));
        [ | case (HR_complexity_p_seq (vec r B ++ T) <? fst (HR_complexity_p_hseq G))%nat];
        apply fst_lt2; apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4;
          rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *;
            (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
    + case (HR_complexity_p_seq (vec r B ++ T) =? HR_complexity_p_seq (vec r A ++ T));
        [ | case (HR_complexity_p_seq (vec r B ++ T) <? HR_complexity_p_seq (vec r A ++ T))%nat];
      apply fst_lt2;
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *;
          (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
Qed.

(** ** max_(co)var *)

Lemma max_var_seq_le_p_seq : forall val T,
    (max_var_seq (eval_p_sequent val T) <= max_var_p_seq T)%nat.
Proof.
  intros val; induction T; simpl; auto.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros e He; simpl; try lia.
  clear - IHT.
  induction A; simpl; try lia.
Qed.

Lemma max_var_hseq_le_p_hseq : forall val G,
    (max_var_hseq (map (eval_p_sequent val) G) <= max_var_p_hseq G)%nat.
Proof.
  intros val; induction G; simpl; auto.
  assert (H := max_var_seq_le_p_seq val a).
  lia.
Qed.

(** ** well defined *)
Lemma p_seq_well_defined_perm : forall val T D,
    Permutation_Type T D ->
    p_seq_well_defined val T ->
    p_seq_well_defined val D.
Proof.
  intros val T D Hperm.
  induction Hperm; intros Hwd; inversion Hwd; subst; (try constructor); auto.
  inversion H2; subst.
  apply p_seq_cons_well_defined; [ | apply p_seq_cons_well_defined ]; auto.
Qed.

Lemma p_hseq_well_defined_perm : forall val G H,
    Permutation_Type G H ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val H.
Proof.
  intros val G H Hperm.
  induction Hperm; intros Hwd; inversion Hwd; subst; try (constructor; now auto); auto.
  inversion H2; subst.
  apply p_hseq_cons_well_defined; [ | apply p_hseq_cons_well_defined ]; auto.
Qed.

(** ** to_p_hypersequent *)

Lemma to_p_sequent_well_defined : forall val T,
    p_seq_well_defined val (to_p_sequent T).
Proof.
  intros val; induction T; [ apply p_seq_nil_well_defined | ].
  destruct a as [[a Ha] A]; simpl.
  apply p_seq_cons_well_defined; assumption.
Qed.

Lemma to_p_hypersequent_well_defined : forall val G,
    p_hseq_well_defined val (to_p_hypersequent G).
Proof.
  intros val; induction G; [ apply p_hseq_nil_well_defined | ].
  apply p_hseq_cons_well_defined; [ apply to_p_sequent_well_defined | assumption ].
Qed.

Lemma eval_p_sequent_to_p_sequent : forall val T,
    eval_p_sequent val (to_p_sequent T) = T.
Proof.
  intros val; induction T; try reflexivity.
  destruct a as [[a Ha] A]; simpl.
  assert {H & R_order_dec a = H} as [e He] by (split with (R_order_dec a); reflexivity); destruct e as [e | e | e];
    rewrite ? He;
    [ | exfalso; clear - e Ha; simpl in *; apply R_blt_lt in Ha; apply R_blt_lt in e; nra
      | exfalso; clear - e Ha; simpl in *; apply R_blt_lt in Ha; nra].
  replace e with Ha by (apply UIP_bool).
  rewrite IHT; reflexivity.
Qed.

Lemma eval_p_hypersequent_to_p_hypersequent : forall val G,
    map (eval_p_sequent val) (to_p_hypersequent G) = G.
Proof.
  intros val; induction G; try reflexivity.
  simpl.
  rewrite eval_p_sequent_to_p_sequent; rewrite IHG.
  reflexivity.
Qed.

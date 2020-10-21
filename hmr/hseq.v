(** * Definition of hypersquents and sequents *)
Require Import Rpos.
Require Import term.
Require Import semantic.

Require Import CMorphisms.
Require Import List_more.
Require Import List_Type_more.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Lra.
Require Import Lia.

Local Open Scope R_scope.


(** * Definitions *)
                                                
Definition sequent : Set := list (Rpos * term).

Definition hypersequent : Set := list sequent.

Definition seq_diamond (T : sequent) := map (fun x => (fst x, <S> (snd x))) T.

(** Property stating whether or not a (hyper)sequent is atomic or basic *)
                                            
Definition seq_is_atomic (T : sequent) := Forall_Type (fun x => match x with (a , A) => is_atom A end) T.

Definition seq_is_basic (T : sequent) := Forall_Type (fun x => match x with (a , A) => is_basic A end) T. 

Definition hseq_is_atomic G := Forall_Type seq_is_atomic G.

Definition hseq_is_basic G := Forall_Type seq_is_basic G.

(** ** Substitution *)
Fixpoint subs_seq (D : sequent) n t :=
  match D with
  | nil => nil
  | (r, A) :: D => (r , subs A n t) :: (subs_seq D n t)
  end.

Fixpoint subs_hseq (G : hypersequent) n t :=
  match G with
  | nil => nil
  | D :: G => (subs_seq D n t) :: (subs_hseq G n t)
  end.

(** ** Definitions of \vec{r}.A and variants *)
(** return \vec{l}.A *)
Fixpoint vec (l : list Rpos) (A : term) :=
  match l with
  | nil => nil
  | r :: l => (r , A) :: (vec l A)
  end.

(** return \sum\vec{l} *)
Fixpoint sum_vec (l : list Rpos) :=
  match l with
  | nil => 0%R
  | r :: l => Rplus (projT1 r) (sum_vec l)
  end.

(** return (r\vec{l}) *)
Fixpoint mul_vec r (l : list Rpos) :=
  match l with
  | nil => nil
  | r0 :: l => (time_pos r r0) :: (mul_vec r l)
  end.

(** return (\vec{l1}\vec{l2}) *)
Fixpoint vec_mul_vec l1 l2 :=
  match l1 with
  | nil => nil
  | r :: l1 => (mul_vec r l2) ++ (vec_mul_vec l1 l2)
  end.

(** return T,...,T n-times *)
Fixpoint copy_seq n (T : sequent) :=
  match n with
  | 0 => nil
  | S n => (copy_seq n T) ++ T
  end.

(** return r.T *)
Fixpoint seq_mul (r : Rpos) (T : sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (time_pos r a, A) :: (seq_mul r T)
  end.

(** return \vec{vr}.T *)
Fixpoint seq_mul_vec vr T :=
  match vr with
  | nil => nil
  | r :: vr => (seq_mul r T) ++ (seq_mul_vec vr T)
  end.

(** ** Sum of the weights *)
(** sum_weight_seq_var n T return the sum of the weights of the formula (var n) that appears in the sequent T. *)
Fixpoint sum_weight_seq_var n (T : sequent) :=
  match T with
  | nil => 0
  | ((r , var n0) :: T) => if n =? n0 then (projT1 r) + sum_weight_seq_var n T else sum_weight_seq_var n T
  | ( _ :: T) => sum_weight_seq_var n T
  end.

(** sum_weight_seq_covar n T return the sum of the weights of the formula (covar n) that appears in the sequent T. *)
Fixpoint sum_weight_seq_covar n (T : sequent) :=
  match T with
  | nil => 0
  | ((r , covar n0) :: T) => if n =? n0 then (projT1 r) + sum_weight_seq_covar n T else sum_weight_seq_covar n T
  | ( _ :: T) => sum_weight_seq_covar n T
  end.

(** sum_weight_seq_one T return the sum of the weights of the formula one that appears in the sequent T. *)
Fixpoint sum_weight_seq_one (T : sequent) :=
  match T with
  | nil => 0
  | ((r , one) :: T) => (projT1 r) + sum_weight_seq_one T
  | ( _ :: T) => sum_weight_seq_one T
  end.
(** sum_weight_seq_coone T return the sum of the weights of the formula coone that appears in the sequent T. *)
Fixpoint sum_weight_seq_coone (T : sequent) :=
  match T with
  | nil => 0
  | ((r , coone) :: T) => (projT1 r) + sum_weight_seq_coone T
  | ( _ :: T) => sum_weight_seq_coone T
  end.

(** sum_weight_var n G return the sum of the weights of the formula (var n) that appears in the hypersequent G. *)
Fixpoint sum_weight_var n G :=
  match G with
  | nil => 0
  | T :: G => sum_weight_seq_var n T + sum_weight_var n G
  end.
(** sum_weight_covar n G return the sum of the weights of the formula (covar n) that appears in the hypersequent G.*)
Fixpoint sum_weight_covar n G :=
  match G with
  | nil => 0
  | T :: G => sum_weight_seq_covar n T + sum_weight_covar n G
  end.
(** sum_weight_one G return the sum of the weights of the formula one that appears in the hypersequent G. *)
Fixpoint sum_weight_one G :=
  match G with
  | nil => 0
  | T :: G => sum_weight_seq_one T + sum_weight_one G
  end.
(** sum_weight_coone G return the sum of the weights of the formula coone that appears in the hypersequent G. *)
Fixpoint sum_weight_coone G :=
  match G with
  | nil => 0
  | T :: G => sum_weight_seq_coone T + sum_weight_coone G
  end.

(** keep only the diamonds formulas and (co)ones but remove the diamond operator *)
Fixpoint only_diamond_seq (T : sequent) :=
  match T with
  | nil => nil
  | (a , <S> A) :: T => (a , A) :: only_diamond_seq T
  | (a , one) :: T => (a , one) :: only_diamond_seq T
  | (a , coone) :: T => (a , coone) :: only_diamond_seq T
  | _ :: T => only_diamond_seq T
  end.

Fixpoint only_diamond_hseq G :=
  match G with
  | nil => nil
  | T :: G => only_diamond_seq T :: only_diamond_hseq G
  end.

(** * Properties *)
(** ** vec *)

Lemma sum_vec_le_0 : forall r, (0 <= sum_vec r)%R.
  induction r; [ | destruct a as [a Ha]; simpl;  apply (R_blt_lt 0 a) in Ha]; simpl; try nra.
Qed.
    
Lemma sum_vec_non_nil : forall r, r <> nil -> (0 <? sum_vec r)%R = true.
  induction r; intros Hnnil; [auto | ].
  simpl.
  apply R_blt_lt.
  destruct a as [a Ha].
  clear Hnnil; simpl.
  apply R_blt_lt in Ha.
  assert (Hle := (sum_vec_le_0 r)).
  nra.
Qed.

Lemma vec_app : forall vr1 vr2 A, vec (vr1 ++ vr2) A = vec vr1 A ++ vec vr2 A.
Proof.
  induction vr1; intros vr2 A; simpl; try rewrite IHvr1; try reflexivity.
Qed.

Lemma sum_vec_app : forall vr1 vr2, sum_vec (vr1 ++ vr2) = (sum_vec vr1) + (sum_vec vr2).
Proof.
  induction vr1; intros vr2.
  - rewrite app_nil_l; simpl; nra.
  - simpl.
    rewrite IHvr1.
    destruct a; simpl; nra.
Qed.

Lemma mul_vec_sum_vec : forall r vr, sum_vec (mul_vec r vr) = (projT1 r) * (sum_vec vr).
Proof.
  intro r; induction vr.
  - simpl; nra.
  - simpl.
    rewrite IHvr.
    destruct r; destruct a; simpl; nra.
Qed.

Lemma sum_vec_vec_mul_vec : forall vr vs, sum_vec (vec_mul_vec vr vs) = (sum_vec vr) * (sum_vec vs).
Proof.
  induction vr; intro vs.
  - simpl; nra.
  - unfold vec_mul_vec; fold vec_mul_vec.
    unfold sum_vec; fold sum_vec.
    rewrite sum_vec_app.
    rewrite mul_vec_sum_vec.
    rewrite IHvr.
    destruct a;  simpl; nra.
Qed.

Lemma vec_mul_vec_nil_r : forall vr, vec_mul_vec vr nil = nil.
Proof with try reflexivity.
  induction vr...
  simpl; rewrite IHvr...
Qed.

Lemma vec_mul_vec_cons_r : forall vr1 vr2 r, Permutation_Type (vec_mul_vec vr1 (r :: vr2)) (mul_vec r vr1 ++ vec_mul_vec vr1 vr2).
Proof.
  induction vr1; intros vr2 r; simpl; try reflexivity.
  replace (time_pos a r) with (time_pos r a) by (clear; destruct r; destruct a; apply Rpos_eq; simpl; nra).
  apply Permutation_Type_skip.
  rewrite app_assoc.
  etransitivity ; [ | apply Permutation_Type_app ; [ apply Permutation_Type_app_comm | reflexivity ] ].
  rewrite <- app_assoc; apply Permutation_Type_app; try reflexivity.
  apply IHvr1.
Qed.

Lemma vec_mul_vec_comm : forall vr1 vr2, Permutation_Type (vec_mul_vec vr1 vr2) (vec_mul_vec vr2 vr1).
Proof.
  induction vr1; intros vr2.
  - simpl; rewrite vec_mul_vec_nil_r; reflexivity.
  - simpl.
    etransitivity ; [ | symmetry; apply vec_mul_vec_cons_r ].
    apply Permutation_Type_app; try reflexivity.
    apply IHvr1.
Qed.

Lemma mul_vec_app : forall vr vs r, mul_vec r (vr ++ vs) = mul_vec r vr ++ mul_vec r vs.
Proof.
  induction vr; intros vs r; simpl; try rewrite IHvr; try reflexivity.
Qed.

Lemma mul_vec_perm : forall vr vs r, Permutation_Type vr vs ->  Permutation_Type (mul_vec r vr) (mul_vec r vs).
Proof.
  intros vr vs r Hperm; induction Hperm; try now constructor.
  transitivity (mul_vec r l'); try assumption.
Qed.

Lemma mul_vec_mul_vec_comm : forall vr r s, mul_vec r (mul_vec s vr) = mul_vec s (mul_vec r vr).
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

Lemma vec_perm : forall vr1 vr2 A,
    Permutation_Type vr1 vr2 -> Permutation_Type (vec vr1 A) (vec vr2 A).
Proof.
  intros vr1 vr2 A Hperm; induction Hperm; try now constructor.
  transitivity (vec l' A); try assumption.
Qed.

Lemma sum_vec_perm : forall vr vs,
    Permutation_Type vr vs ->
    sum_vec vr = sum_vec vs.
Proof.
  intros vr vs Hperm; induction Hperm; simpl; nra.
Qed.

(** ** Sequent *)

Lemma vec_diamond : forall r A, vec r (<S> A) = seq_diamond (vec r A).
Proof.
  intros r A; induction r; simpl; try rewrite IHr; try reflexivity.
Qed.

Lemma seq_diamond_app : forall T1 T2, seq_diamond (T1 ++ T2) = seq_diamond T1 ++ seq_diamond T2.
Proof.
  induction T1; intros T2; simpl; try rewrite IHT1; try reflexivity.
Qed.

Lemma seq_mul_One : forall T, seq_mul One T = T.
  induction T; try reflexivity.
  destruct a as (a , A).
  unfold seq_mul; fold seq_mul.
  replace (time_pos One a) with a by (apply Rpos_eq; destruct a; simpl; nra).
  rewrite IHT; reflexivity.
Qed.
  
Lemma seq_mul_app : forall T1 T2 r, seq_mul r (T1 ++ T2) = seq_mul r T1 ++ seq_mul r T2.
Proof.
  induction T1; intros T2 r; try reflexivity.
  destruct a as (a , A).
  simpl; rewrite IHT1.
  reflexivity.
Qed.

Lemma seq_mul_twice : forall T r1 r2,
    seq_mul r1 (seq_mul r2 T) = seq_mul (time_pos r1 r2) T.
Proof.
  induction T as [ | [a A] T]; intros r1 r2; simpl; try reflexivity.
  rewrite IHT.
  replace (time_pos r1 (time_pos r2 a)) with (time_pos (time_pos r1 r2) a) by (apply Rpos_eq;destruct r1; destruct r2; destruct a; simpl; nra).
  reflexivity.
Qed.

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
    
Lemma seq_mul_seq_mul_vec: forall T vr r,
    seq_mul r (seq_mul_vec vr T) = seq_mul_vec vr (seq_mul r T).
Proof.
  intros T vr; revert T; induction vr; intros T r; try reflexivity.
  simpl. rewrite seq_mul_app; rewrite IHvr; rewrite 2 seq_mul_twice.
  replace (time_pos r a) with (time_pos a r) by (apply Rpos_eq; destruct r; destruct a; simpl; nra).
  reflexivity.
Qed.

Lemma seq_mul_seq_mul_vec_2: forall T vr r,
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
  rewrite seq_mul_seq_mul_vec_2; rewrite seq_mul_vec_app_l.
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
     + rewrite seq_mul_seq_mul_vec.
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

Lemma seq_diamond_perm_decomp : forall T D,
    Permutation_Type (seq_diamond T) D ->
    { D' & D = seq_diamond D'}.
Proof.
  intros T D Hperm; remember (seq_diamond T) as T'.
  revert T HeqT'; induction Hperm; intros T HeqT'.
  - split with nil; reflexivity.
  - destruct T; inversion HeqT'.
    destruct (IHHperm T H1) as [D' Heq].
    split with (p :: D').
    simpl; rewrite Heq; reflexivity.
  - destruct T; [ | destruct T]; inversion HeqT'.
    split with (p0 :: p :: T); reflexivity.
  - destruct (IHHperm1 T HeqT') as [D HeqD].
    apply IHHperm2 with D.
    apply HeqD.
Qed.

Lemma seq_diamond_app_inv : forall T T1 T2,
    T1 ++ T2 = (seq_diamond T) ->
    {' (D1, D2) : _ &
                  prod (T = D1 ++ D2)
                       ((T1 = seq_diamond D1) *
                        (T2 = seq_diamond D2)) }.
Proof.
  intros T T1 T2 Heq.
  revert T Heq; induction T1; intros T Heq.
  - split with (nil, T); repeat split; try reflexivity.
    apply Heq.
  - destruct T; inversion Heq; subst.
    destruct (IHT1 _ H1) as [[D1 D2] [H1' [H2' H3']]].
    split with (p :: D1, D2).
    repeat split; simpl; try rewrite H1'; try rewrite H2'; try rewrite H3'; reflexivity.
Qed.

Lemma seq_diamond_inj : forall T D,
    seq_diamond T = seq_diamond D ->
    T = D.
Proof.
  induction T; intros D Heq; destruct D; inversion Heq; subst; simpl; try rewrite (IHT _ H2); try reflexivity.
  destruct a; destruct p; simpl in *; now subst.
Qed.

Lemma seq_diamond_perm_inv : forall T D,
    Permutation_Type (seq_diamond T) (seq_diamond D) ->
    Permutation_Type T D.
Proof.
  intros T D Hperm.
  remember (seq_diamond T) as T'; remember (seq_diamond D) as D'.
  revert T D HeqT' HeqD'.
  induction Hperm; intros T D HeqT' HeqD'.
  - destruct T; destruct D; inversion HeqT'; inversion HeqD'; reflexivity.
  - destruct T; destruct D; inversion HeqT'; inversion HeqD'; subst.
    destruct p; destruct p0; inversion H2; subst.
    apply Permutation_Type_skip; apply IHHperm; reflexivity.
  - destruct T ; [ | destruct T] ; (destruct D; [ | destruct D]); inversion HeqT'; inversion HeqD'; subst.
    destruct p; destruct p0; destruct p1; destruct p2; inversion H3; inversion H4; subst.
    apply seq_diamond_inj in H5; rewrite H5; apply Permutation_Type_swap.
  - subst.
    apply seq_diamond_perm_decomp in Hperm1 as [T' Heq']; subst.
    transitivity T'; [ apply IHHperm1 | apply IHHperm2]; reflexivity.
Qed.

Lemma seq_diamond_perm : forall T D,
    Permutation_Type T D ->
    Permutation_Type (seq_diamond T) (seq_diamond D).
Proof.
  intros T D Hperm; induction Hperm; try now constructor.
  transitivity (seq_diamond l'); assumption.
Qed.

Lemma seq_diamond_seq_mul : forall T r,
    seq_mul r (seq_diamond T) = seq_diamond (seq_mul r T).
Proof.
  induction T; intros r; try destruct a; simpl; try rewrite IHT; reflexivity.
Qed.

Lemma seq_diamond_seq_mul_vec : forall T r,
    seq_mul_vec r (seq_diamond T) = seq_diamond (seq_mul_vec r T).
Proof.
  intros T r; revert T; induction r; intros T; try reflexivity.
  simpl.
  rewrite seq_diamond_app; rewrite IHr; rewrite seq_diamond_seq_mul; reflexivity.
Qed.

Lemma seq_diamond_only_diamond : forall T A r,
    (forall B, A <> <S> B) ->
    ~ (In (r,A) (seq_diamond T)).
Proof.
  induction T; intros A r H.
  - auto.
  - intro Hin; simpl in Hin.
    destruct Hin.
    + inversion H0.
      apply (H (snd a)).
      symmetry; apply H3.
    + apply (IHT A r H).
      apply H0.
Qed.

Lemma copy_seq_plus : forall T n1 n2, copy_seq (n1 + n2) T = copy_seq n1 T ++ copy_seq n2 T.
Proof.
  intros T; intros n1; induction n2; simpl.
  - rewrite app_nil_r; rewrite Nat.add_0_r; reflexivity.
  - rewrite Nat.add_succ_r; simpl.
    rewrite IHn2.
    rewrite app_assoc; reflexivity.
Qed.

Lemma copy_seq_perm : forall T1 T2 n,
    Permutation_Type T1 T2 ->
    Permutation_Type (copy_seq n T1) (copy_seq n T2).
Proof.
  intros T1 T2; induction n; try reflexivity.
  intros Hperm.
  simpl; specialize (IHn Hperm).
  apply Permutation_Type_app; assumption.
Qed.

Lemma copy_seq_app : forall T1 T2 n,
    Permutation_Type (copy_seq n (T1 ++ T2)) (copy_seq n T1 ++ copy_seq n T2).
Proof.
  intros T1 T2; induction n; simpl; perm_Type_solve.
Qed.

Lemma copy_seq_nil : forall n, copy_seq n nil = nil.
Proof.
  induction n; simpl; try rewrite IHn; reflexivity.
Qed.

Lemma copy_seq_twice : forall T n1 n2, copy_seq n1 (copy_seq n2 T) = copy_seq (n1 * n2) T.
Proof.
  intros T; induction n1; intros n2; try reflexivity.
  simpl.
  rewrite IHn1; rewrite <- copy_seq_plus.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

(** ** Substitution *)

Lemma subs_seq_app : forall D D' n t, subs_seq (D ++ D') n t = subs_seq D n t ++ subs_seq D' n t.
Proof.
  induction D; intros D' n t; simpl; try rewrite IHD; try destruct a; try reflexivity.
Qed.

Lemma subs_seq_vec : forall D n t A r, subs_seq ((vec r A) ++ D) n t = vec r (subs A n t) ++ subs_seq D n t.
Proof.
  intros D n t A; induction r;simpl; try rewrite IHr; try reflexivity.
Qed.

Lemma subs_seq_ex : forall T1 T2 n t, Permutation_Type T1 T2 -> Permutation_Type (subs_seq T1 n t) (subs_seq T2 n t).
Proof.
  intros T1 T2 n t Hperm; induction Hperm; try destruct x; try destruct y; simpl; try now constructor.
  transitivity (subs_seq l' n t); assumption.
Qed.

Lemma subs_hseq_ex : forall G1 G2 n t, Permutation_Type G1 G2 -> Permutation_Type (subs_hseq G1 n t) (subs_hseq G2 n t).
Proof.
  intros G1 G2 n t Hperm; induction Hperm; try destruct x; try destruct y; simpl; try now constructor.
  transitivity (subs_hseq l' n t); assumption.
Qed.

Lemma subs_seq_diamond : forall T n t, subs_seq (seq_diamond T) n t = seq_diamond (subs_seq T n t).
Proof.
  induction T; intros n t; simpl; try (destruct a ; rewrite IHT); try reflexivity.
Qed.

(** ** Diamond properties *)
Lemma only_diamond_seq_app :
  forall T1 T2,
    only_diamond_seq (T1 ++ T2) = only_diamond_seq T1 ++ only_diamond_seq T2.
Proof.
  induction T1; intros T2; simpl; try (rewrite IHT1; destruct a; destruct t); reflexivity.
Qed.

Lemma only_diamond_seq_mul :
  forall T r,
    seq_mul r (only_diamond_seq T) = only_diamond_seq (seq_mul r T).
Proof.
  induction T; intros r; simpl; try (destruct a; destruct t; simpl; rewrite IHT); try reflexivity.
Qed.

Lemma only_diamond_seq_copy :
  forall T n,
    copy_seq n (only_diamond_seq T) = only_diamond_seq (copy_seq n T).
Proof.
  intros T; induction n; simpl; try rewrite only_diamond_seq_app; try rewrite IHn; reflexivity.
Qed.

Lemma only_diamond_seq_vec_var :
  forall n r,
    only_diamond_seq (vec r (var n)) = nil.
Proof.
  intros n; induction r; simpl; auto.
Qed.

Lemma only_diamond_seq_vec_covar :
  forall n r,
    only_diamond_seq (vec r (covar n)) = nil.
Proof.
  intros n; induction r; simpl; auto.
Qed.

Lemma only_diamond_seq_vec_one :
  forall r,
    only_diamond_seq (vec r one) = vec r one.
Proof.
  induction r; simpl; try rewrite IHr; reflexivity.
Qed.

Lemma only_diamond_seq_vec_coone :
  forall r,
    only_diamond_seq (vec r coone) = vec r coone.
Proof.
  induction r; simpl; try rewrite IHr; reflexivity.
Qed.

Lemma only_diamond_seq_only_diamond :
  forall T,
    only_diamond_seq (seq_diamond T) = T.
Proof.
  induction T; try destruct a; simpl; try rewrite IHT; reflexivity.
Qed.

Lemma only_diamond_seq_perm :
  forall T1 T2,
    Permutation_Type T1 T2 ->
    Permutation_Type (only_diamond_seq T1) (only_diamond_seq T2).
Proof.
  intros T1 T2 Hperm.
  induction Hperm.
  - apply Permutation_Type_nil_nil.
  - destruct x; destruct t; simpl; try apply Permutation_Type_cons; try apply IHHperm; reflexivity.
  - destruct x; destruct y; destruct t; destruct t0; simpl; try apply Permutation_Type_swap; try apply Permutation_Type_cons; reflexivity.
  - apply Permutation_Type_trans with (only_diamond_seq l'); assumption.
Qed.

(** ** sum_weight_seq_(co)var *)

Lemma sum_weight_seq_var_pos : forall n T,
    0 <= sum_weight_seq_var n T.
Proof.
  intros n; induction T; simpl; try nra.
  destruct a as [a A].
  destruct a as [a Ha].
  destruct A; try nra.
  case (n =? n0); simpl; apply R_blt_lt in Ha; nra.
Qed.

Lemma sum_weight_seq_covar_pos : forall n T,
    0 <= sum_weight_seq_covar n T.
Proof.
  intros n; induction T; simpl; try nra.
  destruct a as [a A].
  destruct a as [a Ha].
  destruct A; try nra.
  case (n =? n0); simpl; apply R_blt_lt in Ha; nra.
Qed.

Lemma sum_weight_seq_var_app : forall n T1 T2,
    sum_weight_seq_var n (T1 ++ T2) = sum_weight_seq_var n T1 + sum_weight_seq_var n T2.
Proof.
  intros n T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; try case (n =? n0); simpl; try nra.
Qed.

Lemma sum_weight_seq_covar_app : forall n T1 T2,
    sum_weight_seq_covar n (T1 ++ T2) = sum_weight_seq_covar n T1 + sum_weight_seq_covar n T2.
Proof.
  intros n T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; try case (n =? n0); simpl; try nra.
Qed.

Lemma sum_weight_seq_var_mul : forall n T r,
    sum_weight_seq_var n (seq_mul r T) = (projT1 r) * sum_weight_seq_var n T.
Proof.
  intros n T r; induction T; simpl; try nra.
  destruct a as [a A]; simpl.
  destruct A; try case (n =? n0); destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_seq_covar_mul : forall n T r,
    sum_weight_seq_covar n (seq_mul r T) = (projT1 r) * sum_weight_seq_covar n T.
Proof.
  intros n T r; induction T; simpl; try nra.
  destruct a as [a A]; simpl.
  destruct A; try case (n =? n0); destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_seq_var_copy : forall n T r,
    sum_weight_seq_var n (copy_seq r T) = (INR r) * sum_weight_seq_var n T.
Proof.
  intros n T r; induction r; simpl in *; try nra.
  rewrite sum_weight_seq_var_app; rewrite IHr.
  change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)).
  rewrite S_INR; nra.
Qed.

Lemma sum_weight_seq_covar_copy : forall n T r,
    sum_weight_seq_covar n (copy_seq r T) = (INR r) * sum_weight_seq_covar n T.
Proof.
  intros n T r; induction r; simpl in *; try nra.
  rewrite sum_weight_seq_covar_app; rewrite IHr.
  change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)).
  rewrite S_INR; nra.
Qed.

Lemma sum_weight_seq_var_vec_var_eq : forall n r,
    sum_weight_seq_var n (vec r (var n)) = sum_vec r.
Proof.
  intros n; induction r; simpl; try (rewrite Nat.eqb_refl; rewrite IHr); reflexivity.
Qed.

Lemma sum_weight_seq_covar_vec_covar_eq : forall n r,
    sum_weight_seq_covar n (vec r (covar n)) = sum_vec r.
Proof.
  intros n; induction r; simpl; try (rewrite Nat.eqb_refl; rewrite IHr); nra.
Qed.

Lemma sum_weight_seq_var_vec_neq : forall n A r,
    var n <> A ->
    sum_weight_seq_var n (vec r A) = 0.
Proof.
  intros n A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; try (case_eq (n =? n0) ; [ intros H; exfalso; apply Nat.eqb_eq in H; now subst | ]); auto.
Qed.

Lemma sum_weight_seq_covar_vec_neq : forall n A r,
    covar n <> A ->
    sum_weight_seq_covar n (vec r A) = 0.
Proof.
  intros n A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; try (case_eq (n =? n0) ; [ intros H; exfalso; apply Nat.eqb_eq in H; now subst | ]); auto.
Qed.

Lemma sum_weight_seq_var_perm : forall n T1 T2,
    Permutation_Type T1 T2 ->
    sum_weight_seq_var n T1 = sum_weight_seq_var n T2.
Proof.
  intros n T1 T2 Hperm; induction Hperm; simpl; try destruct x as [a A]; try destruct y as [b B]; try destruct A; try destruct B; try case (n =? n0); try case (n =? n1); try nra.
Qed.

Lemma sum_weight_seq_covar_perm : forall n T1 T2,
    Permutation_Type T1 T2 ->
    sum_weight_seq_covar n T1 = sum_weight_seq_covar n T2.
Proof.
  intros n T1 T2 Hperm; induction Hperm; simpl; try destruct x as [a A]; try destruct y as [b B]; try destruct A; try destruct B; try case (n =? n0); try case (n =? n1); try nra.
Qed.

Lemma sum_weight_var_perm : forall n G H,
    Permutation_Type G H ->
    sum_weight_var n G = sum_weight_var n H.
Proof.
  intros n G H Hperm; induction Hperm; simpl; nra.
Qed.

Lemma sum_weight_covar_perm : forall n G H,
    Permutation_Type G H ->
    sum_weight_covar n G = sum_weight_covar n H.
Proof.
  intros n G H Hperm; induction Hperm; simpl; nra.
Qed.

Lemma seq_decomp_basic :
  forall T n,
    {' (r,s,D) : _ &
                    prod (sum_vec r = sum_weight_seq_var n T)
                         ((sum_vec s = sum_weight_seq_covar n T) *
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
           
Lemma seq_basic_decomp_decr :
  forall T,
    seq_is_basic T ->
    {' (n, r,s,D) : _ &
                    prod (sum_vec r = sum_weight_seq_var n T)
                         ((sum_vec s = sum_weight_seq_covar n T) *
                          (Permutation_Type T (vec s (covar n) ++ vec r (var n) ++ D)) *
                          ((length D < length T)%nat)) } + { forall n, prod (sum_weight_seq_var n T = 0) (sum_weight_seq_covar n T = 0) }.
Proof.
  induction T; intros Hat.
  - right.
    intros n; split; reflexivity.
  - inversion Hat; subst.
    specialize (IHT X0).
    destruct a as [a A].
    destruct A; (try now inversion X); 
      destruct IHT as [[[[[nv r] s] D] H] | H].
    + left.
      clear r s D H.
      destruct (seq_decomp_basic T n) as [[[r s] D] [Hr [Hs Hperm]]].
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
    + left.
      split with (n, a :: nil, nil, T); specialize (H n) as [Hvar Hcovar].
      repeat split.
      * simpl; rewrite Hvar.
        rewrite Nat.eqb_refl.
        reflexivity.
      * simpl; rewrite Hcovar; reflexivity.
      * auto.
      * simpl; lia.
    + left.
      clear r s D H.
      destruct (seq_decomp_basic T n) as [[[r s] D] [Hr [Hs Hperm]]].
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
    + left.
      split with (n, nil , a :: nil, T); specialize (H n) as [Hvar Hcovar].
      repeat split.
      * simpl; rewrite Hvar; reflexivity.
      * simpl; rewrite Hcovar.
        rewrite Nat.eqb_refl.
        reflexivity.
      * auto.
      * simpl; lia.
    + left; split with (nv,r,s,((a, one) :: D)).
      repeat split; destruct H as [Hvar [[Hcovar Hperm] Hlen]].
      * simpl; rewrite Hvar; reflexivity.
      * simpl; rewrite Hcovar; reflexivity.
      * perm_Type_solve.
      * simpl; lia.
    + right.
      intros n; specialize (H n) as [Hvar Hcovar].
      split; simpl; assumption.
    + left; split with (nv,r,s,((a, coone) :: D)).
      repeat split; destruct H as [Hvar [[Hcovar Hperm] Hlen]].
      * simpl; rewrite Hvar; reflexivity.
      * simpl; rewrite Hcovar; reflexivity.
      * perm_Type_solve.
      * simpl; lia.
    + right.
      intros n; specialize (H n) as [Hvar Hcovar].
      split; simpl; assumption.
    + left; split with (nv,r,s,((a, <S> A) :: D)).
      repeat split; destruct H as [Hvar [[Hcovar Hperm] Hlen]].
      * simpl; rewrite Hvar; reflexivity.
      * simpl; rewrite Hcovar; reflexivity.
      * perm_Type_solve.
      * simpl; lia.
    + right.
      intros n; specialize (H n) as [Hvar Hcovar].
      split; simpl; assumption.
Qed.

Lemma sum_weight_seq_var_seq_diamond :
  forall n T,
    sum_weight_seq_var n (seq_diamond T) = 0.
Proof.
  intros n; induction T; auto.
Qed.

Lemma sum_weight_seq_covar_seq_diamond :
  forall n T,
    sum_weight_seq_covar n (seq_diamond T) = 0.
Proof.
  intros n; induction T; auto.
Qed.

(** ** sum_weight_seq_(co)one *)

Lemma sum_weight_seq_one_app : forall T1 T2,
    sum_weight_seq_one (T1 ++ T2) = sum_weight_seq_one T1 + sum_weight_seq_one T2.
Proof.
  intros T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; simpl; try nra.
Qed.

Lemma sum_weight_seq_coone_app : forall T1 T2,
    sum_weight_seq_coone (T1 ++ T2) = sum_weight_seq_coone T1 + sum_weight_seq_coone T2.
Proof.
  intros T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; simpl; try nra.
Qed.

Lemma sum_weight_seq_one_mul : forall T r,
    sum_weight_seq_one (seq_mul r T) = (projT1 r) * sum_weight_seq_one T.
Proof.
  intros T r; induction T; simpl; try nra.
  destruct a as [a A]; simpl.
  destruct A; destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_seq_coone_mul : forall T r,
    sum_weight_seq_coone (seq_mul r T) = (projT1 r) * sum_weight_seq_coone T.
Proof.
  intros T r; induction T; simpl; try nra.
  destruct a as [a A]; simpl.
  destruct A; destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_seq_one_copy : forall T r,
    sum_weight_seq_one (copy_seq r T) = (INR r) * sum_weight_seq_one T.
Proof.
  intros T r; induction r; simpl in *; try nra.
  rewrite sum_weight_seq_one_app; rewrite IHr.
  change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)).
  rewrite S_INR; nra.
Qed.

Lemma sum_weight_seq_coone_copy : forall T r,
    sum_weight_seq_coone (copy_seq r T) = (INR r) * sum_weight_seq_coone T.
Proof.
  intros T r; induction r; simpl in *; try nra.
  rewrite sum_weight_seq_coone_app; rewrite IHr.
  change (match r with
          | 0%nat => 1
          | S _ => INR r + 1
          end) with (INR (S r)).
  rewrite S_INR; nra.
Qed.

Lemma sum_weight_seq_one_vec_one_eq : forall r,
    sum_weight_seq_one (vec r (one)) = sum_vec r.
Proof.
  intros; induction r; simpl; try (rewrite IHr); reflexivity.
Qed.

Lemma sum_weight_seq_coone_vec_coone_eq : forall r,
    sum_weight_seq_coone (vec r (coone)) = sum_vec r.
Proof.
  intros; induction r; simpl; try (rewrite IHr); nra.
Qed.

Lemma sum_weight_seq_one_vec_neq : forall A r,
    one <> A ->
    sum_weight_seq_one (vec r A) = 0.
Proof.
  intros A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A ; now subst; auto.
Qed.

Lemma sum_weight_seq_coone_vec_neq : forall A r,
    coone <> A ->
    sum_weight_seq_coone (vec r A) = 0.
Proof.
  intros A; induction r; intros Hneq; simpl; try reflexivity.
  destruct A; now subst; auto.
Qed.

Lemma sum_weight_seq_one_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    sum_weight_seq_one T1 = sum_weight_seq_one T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; simpl; try destruct x as [a A]; try destruct y as [b B]; try destruct A; try destruct B; try nra.
Qed.

Lemma sum_weight_seq_coone_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    sum_weight_seq_coone T1 = sum_weight_seq_coone T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; simpl; try destruct x as [a A]; try destruct y as [b B]; try destruct A; try destruct B; try nra.
Qed.

Lemma sum_weight_one_perm : forall G H,
    Permutation_Type G H ->
    sum_weight_one G = sum_weight_one H.
Proof.
  intros G H Hperm; induction Hperm; simpl; nra.
Qed.

Lemma sum_weight_coone_perm : forall G H,
    Permutation_Type G H ->
    sum_weight_coone G = sum_weight_coone H.
Proof.
  intros G H Hperm; induction Hperm; simpl; nra.
Qed.

Lemma sum_weight_seq_one_seq_diamond :
  forall T,
    sum_weight_seq_one (seq_diamond T) = 0.
Proof.
  induction T; auto.
Qed.

Lemma sum_weight_seq_coone_seq_diamond :
  forall T,
    sum_weight_seq_coone (seq_diamond T) = 0.
Proof.
  induction T; auto.
Qed.

(** ** atomic and basic *)
Lemma copy_seq_atomic : forall n T, seq_is_atomic T -> seq_is_atomic (copy_seq n T).
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

Lemma seq_basic_app : forall T1 T2,
    seq_is_basic T1 ->
    seq_is_basic T2 ->
    seq_is_basic (T1 ++ T2).
Proof.
  induction T1; intros T2 H1 H2; try assumption.
  simpl.
  inversion H1; subst; apply Forall_Type_cons; try assumption.
  apply IHT1; assumption.
Qed.

Lemma seq_basic_mul : forall T r,
    seq_is_basic T ->
    seq_is_basic (seq_mul r T).
Proof.
  induction T; intros r Hb; try assumption.
  inversion Hb; subst; destruct a; simpl; apply Forall_Type_cons; try apply IHT; assumption.
Qed.

Lemma seq_basic_app_inv_l : forall T1 T2,
    seq_is_basic (T1 ++ T2) ->
    seq_is_basic T1.
Proof.
  induction T1; intros T2 Hb; [apply Forall_Type_nil | ].
  simpl; inversion Hb; subst.
  apply Forall_Type_cons; [ | apply IHT1 with T2]; assumption.
Qed.

Lemma seq_basic_app_inv_r : forall T1 T2,
    seq_is_basic (T1 ++ T2) ->
    seq_is_basic T2.
Proof.
  induction T1; intros T2 Hb; [assumption | ].
  simpl; inversion Hb; subst.
  apply IHT1; apply X0.
Qed.

Lemma seq_basic_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    seq_is_basic T1 ->
    seq_is_basic T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; intro Hat.
  - apply Forall_Type_nil.
  - inversion Hat; subst; apply Forall_Type_cons; [ | apply IHHperm]; assumption.
  - inversion Hat; inversion X0; subst.
    apply Forall_Type_cons ; [ | apply Forall_Type_cons ]; assumption.
  - apply IHHperm2; apply IHHperm1; apply Hat.
Qed.

Lemma hseq_basic_perm : forall G H,
    Permutation_Type G H ->
    hseq_is_basic G ->
    hseq_is_basic H.
Proof.
  intros G H Hperm; induction Hperm; intro Hat.
  - apply Forall_Type_nil.
  - inversion Hat; subst; apply Forall_Type_cons; [ | apply IHHperm]; assumption.
  - inversion Hat; inversion X0; subst.
    apply Forall_Type_cons ; [ | apply Forall_Type_cons ]; assumption.
  - apply IHHperm2; apply IHHperm1; apply Hat.
Qed.

Lemma copy_seq_basic : forall T n,
    seq_is_basic T ->
    seq_is_basic (copy_seq n T).
Proof.
  intros T; induction n; intros Hb; simpl ; [ | apply seq_basic_app].
  - apply Forall_Type_nil.
  - apply IHn; apply Hb.
  - apply Hb.
Qed.

Lemma seq_basic_no_atom : forall T, seq_is_basic T ->
                                    (forall n : nat, (sum_weight_seq_var n T = 0) * (sum_weight_seq_covar n T = 0)) ->
                                    {' (r, s, D) : _ & Permutation_Type T (vec s coone ++ vec r one ++ seq_diamond D) }.
Proof.
  induction T; intros Hb Hna.
  - split with (nil, nil, nil).
    apply Permutation_Type_nil_nil.
  - inversion Hb; subst.
    destruct (IHT X0) as [[[r s] D] Hperm].
    + intros n.
      assert (Hvpos := sum_weight_seq_var_pos n T).
      assert (Hcvpos := sum_weight_seq_covar_pos n T).
      destruct a as [[a Ha] A].
      clear IHT Hb.
      specialize (Hna n) as [Hvna Hcvna].
      split; simpl in *;
        destruct A; try (case_eq (n =? n0); intros Hnn0; rewrite Hnn0 in *);
                         apply R_blt_lt in Ha;
                         try nra.
    + destruct a as [a A].
      destruct A; try now inversion X.
      * exfalso; clear IHT Hb.
        specialize (Hna n) as [Hna _]; simpl in Hna.
        rewrite Nat.eqb_refl in Hna.
        destruct a as [a Ha].
        simpl in *; apply R_blt_lt in Ha.
        assert (Hpos := sum_weight_seq_var_pos n T).
        nra.
      * exfalso; clear IHT Hb.
        specialize (Hna n) as [_ Hna]; simpl in Hna.
        rewrite Nat.eqb_refl in Hna.
        destruct a as [a Ha].
        simpl in *; apply R_blt_lt in Ha.
        assert (Hpos := sum_weight_seq_covar_pos n T).
        nra.
      * split with (a :: r, s, D); simpl.
        perm_Type_solve.
      * split with (r, a :: s, D); simpl.
        perm_Type_solve.
      * split with (r , s, ((a , A) :: D)).
        perm_Type_solve.
Qed.

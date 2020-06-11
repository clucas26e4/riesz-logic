Require Import Rpos.
Require Import term.
Require Import semantic.

Require Import CMorphisms.
Require Import List.
Require Import Permutation_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Lra.

Local Open Scope R_scope.

(* MOVE ?*)
Fixpoint vec (l : list Rpos) (A : term) :=
  match l with
  | nil => nil
  | r :: l => (r , A) :: (vec l A)
  end.

Fixpoint sum_vec (l : list Rpos) :=
  match l with
  | nil => 0%R
  | r :: l => Rplus (projT1 r) (sum_vec l)
  end.

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

Fixpoint mul_vec r (l : list Rpos) :=
  match l with
  | nil => nil
  | r0 :: l => (time_pos r r0) :: (mul_vec r l)
  end.

Fixpoint vec_mul_vec l1 l2 :=
  match l1 with
  | nil => nil
  | r :: l1 => (mul_vec r l2) ++ (vec_mul_vec l1 l2)
  end.

(** * Definition of hr *)

(** ** Sequent *)
                                                
Definition sequent : Set := list (Rpos * term).

Global Instance Permutation_Type_app_sequent :
 Proper (@Permutation_Type sequent ==> @Permutation_Type sequent ==> @Permutation_Type sequent) (@app sequent) | 10.
Proof.
  repeat intro; now apply Permutation_Type_app.
Qed.

Fixpoint seq_mul (r : Rpos) (T : sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (time_pos r a, A) :: (seq_mul r T)
  end.

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

Lemma seq_mul_vec_app_r : forall T1 T2 vr,
    Permutation_Type (seq_mul_vec vr (T1 ++ T2)) (seq_mul_vec vr T1 ++ seq_mul_vec vr T2).
Proof.
  intros T1 T2; induction vr; try reflexivity.
  simpl.
  rewrite seq_mul_app.
  perm_Type_solve.
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

(** ** Hypersequent *)

Definition hypersequent : Set := list sequent.

(** *** Substitution *)
Fixpoint subs_seq (D : sequent) n t :=
  match D with
  | nil => nil
  | (r, A) :: D => (r , subs A n t) :: (subs_seq D n t)
  end.

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

Fixpoint subs_hseq (G : hypersequent) n t :=
  match G with
  | nil => nil
  | D :: G => (subs_seq D n t) :: (subs_hseq G n t)
  end.

Lemma subs_hseq_ex : forall G1 G2 n t, Permutation_Type G1 G2 -> Permutation_Type (subs_hseq G1 n t) (subs_hseq G2 n t).
Proof.
  intros G1 G2 n t Hperm; induction Hperm; try destruct x; try destruct y; simpl; try now constructor.
  transitivity (subs_hseq l' n t); assumption.
Qed.

(** ** HR *)

Inductive HR b : hypersequent -> Type :=
| INIT : HR b (nil :: nil)
| W : forall G T, HR b G -> HR b (T :: G)
| C : forall G T, HR b (T :: T :: G) -> HR b (T :: G)
| S : forall G T1 T2, HR b ((T1 ++ T2) :: G) -> HR b (T1 :: T2 :: G)
| M : forall G T1 T2, HR b (T1 :: G) -> HR b (T2 :: G) -> HR b ((T1 ++ T2) :: G)
| TR : forall G T r, HR b (seq_mul r T :: G) -> HR b (T :: G)
| ID : forall G T n r s, sum_vec r = sum_vec s -> HR b (T :: G) -> HR b ((vec s (covar n) ++ vec r (var n) ++ T) :: G)
| Z : forall G T r, HR b (T :: G) -> HR b ((vec r zero ++ T) :: G)

| plus : forall G T A B r, HR b ((vec r A ++ vec r B ++ T) :: G) -> HR b ((vec r (A +S B) ++ T) :: G)
| mul : forall G T A r0 r, HR b ((vec (mul_vec r0 r) A ++ T) :: G) -> HR b ((vec r (r0 *S A) ++ T) :: G)
| max : forall G T A B r, HR b ((vec r B ++ T) :: (vec r A ++ T) :: G) -> HR b ((vec r (A \/S B) ++ T) :: G)
| min : forall G T A  B r, HR b ((vec r A ++ T) :: G) -> HR b ((vec r B ++ T) :: G) -> HR b ((vec r (A /\S B) ++ T) :: G)
| ex_seq : forall G T1 T2, Permutation_Type T1 T2 -> HR b (T1 :: G) -> HR b (T2 :: G)
| ex_hseq : forall G H, Permutation_Type G H -> HR b G -> HR b H
| can {f : b = true} : forall G T A r s, sum_vec r = sum_vec s -> HR b ((vec s (-S A) ++ vec r A ++ T) :: G) -> HR b (T :: G).

(* Some basic properties *)

Lemma HR_not_empty b : forall G, HR b G -> G <> nil.
Proof.
  intros G pi; induction pi; (try now auto).
  intros Heq; apply IHpi; apply Permutation_Type_nil.
  symmetry; now rewrite <- Heq.
Qed.


Lemma HR_no_can_can : forall G, HR false G -> HR true G.
Proof.
  intros G pi.
  induction pi; try now constructor.
  - apply TR with r; apply IHpi.
  - apply ex_seq with T1; assumption.
  - apply ex_hseq with G; assumption.
Qed.

Lemma W_gen b : forall G H, HR b G -> HR b (H ++ G).
Proof.
  intros G H; revert G; induction H; intros G pi.
  - auto.
  - simpl; apply W; apply IHlist; apply pi.
Qed.


(* Proof of lemmas of subsection 3.3 *)

Lemma ID_gen b : forall G T A r s, sum_vec r = sum_vec s -> HR b (T :: G) -> HR b ((vec s (-S A) ++ vec r A ++ T) :: G).
Proof.
  intros G T A; revert G T.
  induction A;intros G T r0 s Heq pi; unfold minus; fold minus.
  - apply ID; assumption.
  - apply ex_seq with (vec r0 (covar n) ++ vec s (var n) ++ T); [ perm_Type_solve | ].
    apply ID; try symmetry; assumption.
  - apply Z; apply Z; apply pi.
  - apply plus.
    apply ex_seq with (vec r0 (A1 +S A2) ++ vec s (-S A1) ++ vec s (-S A2) ++ T); [ perm_Type_solve | ].
    apply plus.
    eapply ex_seq.
    2:{ eapply IHA1; [ apply Heq | ].
        eapply ex_seq.
        2:{ eapply IHA2; [ apply Heq | apply pi ]. }
        perm_Type_solve. }
    perm_Type_solve.
  - apply mul.
    eapply ex_seq with (vec r0 (r *S A) ++ vec (mul_vec r s) (-S A) ++ T) ; [ perm_Type_solve | ].
    apply mul.
    apply ex_seq with (vec (mul_vec r s) (-S A) ++ vec (mul_vec r r0) A ++ T); [ perm_Type_solve | ].
    apply IHA ; [ | apply pi].
    (* TODO MOVING *)
    assert (forall l r, sum_vec (mul_vec r l) =  Rmult (projT1 r) (sum_vec l)) as sum_mul_vec.
    { clear.
      induction l; intros [r Hr].
      - simpl; nra.
      - remember (existT (fun r0 : R => (0 <? r0)%R = true) r Hr) as t.
        unfold mul_vec; fold (mul_vec t l).
        unfold sum_vec; fold (sum_vec (mul_vec t l)); fold (sum_vec l).
        rewrite IHl.
        rewrite Heqt.
        destruct a.
        simpl.
        nra. }
    rewrite ? sum_mul_vec.
    destruct r as [r Hr].
    simpl.
    apply R_blt_lt in Hr.
    nra.
  - apply min.
    + apply ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A1) ++ T); [perm_Type_solve | ].
      apply max.
      apply W.
      eapply ex_seq; [ | apply IHA1; [ apply Heq | apply pi] ].
      perm_Type_solve.
    + apply ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A2) ++ T); [perm_Type_solve | ].
      apply max.
      apply ex_hseq with ((vec r0 A1 ++ vec s (-S A2) ++ T) :: (vec r0 A2 ++ vec s (-S A2) ++ T) :: G) ; [ perm_Type_solve | ]. 
      apply W.
      eapply ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      perm_Type_solve.
  - apply ex_seq with (vec r0 (A1 /\S A2) ++ vec s (-S A1 \/S -S A2) ++ T); [ perm_Type_solve | ].
    apply min.
    + apply ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A1) ++ T); [perm_Type_solve | ].
      apply max.
      apply W.
      apply IHA1; [ apply Heq | apply pi].
    + apply ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A2) ++ T); [perm_Type_solve | ].
      apply max.
      apply ex_hseq with ((vec s (-S A1) ++ vec r0 A2 ++ T) :: (vec s (-S A2) ++ vec r0 A2 ++ T) :: G) ; [ perm_Type_solve | ]. 
      apply W.
      eapply ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      perm_Type_solve.
Qed.

Lemma subs_proof b : forall G n t,
    HR b G ->
    HR b (subs_hseq G n t).
Proof with try assumption; try reflexivity.
  intros G n t pi.
  induction pi;unfold subs_hseq in *; fold subs_hseq in *; try rewrite ? subs_seq_vec in *; try rewrite subs_seq_app in *; unfold subs in *; fold subs in *; try now constructor.
  - replace (subs_seq (seq_mul r T) n t) with (seq_mul r (subs_seq T n t)) in IHpi by (clear; induction T; try destruct a; simpl; try rewrite IHT; try reflexivity).
    apply TR with r...
  - case (n =? n0).
    + apply ID_gen...
    + apply ID...
  - eapply ex_seq; [ apply subs_seq_ex ; apply p | ]...
  - eapply ex_hseq; [ apply subs_hseq_ex; apply p | ]...
  - rewrite eq_subs_minus in IHpi.
    apply can with (subs A n t) r s...
Qed.    

Lemma plus_can_inv : forall G T A B r, HR true ((vec r (A +S B) ++ T) :: G) -> HR true ((vec r A ++ vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply can with (A +S B) r r; try reflexivity.
  apply ex_seq with ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) ++ (vec r (A +S B) ++ T)); [ perm_Type_solve | ].
  apply M; [ | apply pi].
  apply ex_hseq with (G ++ ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) :: nil)); [ perm_Type_solve | ].
  apply W_gen.
  unfold minus; fold (-S A); fold (-S B).
  apply plus.
  apply ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B); [ perm_Type_solve | ].
  apply ID_gen; try reflexivity.
  replace (vec r (-S B) ++ vec r B) with (vec r (-S B) ++ vec r B ++ nil) by (now rewrite app_nil_r).
  apply ID_gen; [ reflexivity | apply INIT ].
Qed.

Lemma Z_can_inv : forall G T r, HR true ((vec r zero ++ T) :: G) -> HR true (T :: G).
Proof.
  intros G T r pi.
  apply can with zero r r; try reflexivity.
  apply Z.
  apply pi.
Qed.
  
Lemma mul_can_inv : forall G T A r0 r, HR true ((vec r (r0 *S A) ++ T) :: G) -> HR true ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
  intros G T A r0 r pi.
  apply can with (r0 *S A) r r; try reflexivity.
  apply ex_seq with ((vec r (-S (r0 *S A)) ++ vec (mul_vec r0 r) A) ++ (vec r (r0 *S A) ++ T)); [ perm_Type_solve | ].
  apply M; [ | apply pi ].
  apply ex_hseq with (G ++ ((vec r (-S (r0 *S A)) ++ vec (mul_vec r0 r) A) :: nil)); [ perm_Type_solve | ].
  apply W_gen.
  unfold minus; fold minus.
  apply mul.
  replace (vec (mul_vec r0 r) (-S A) ++ vec (mul_vec r0 r) A) with (vec (mul_vec r0 r) (-S A) ++ vec (mul_vec r0 r) A ++ nil) by (now rewrite app_nil_r).
  apply ID_gen ; [ reflexivity | ].
  apply INIT.
Qed.

Lemma max_can_inv : forall G T A B r, HR true ((vec r (A \/S B) ++ T) :: G) -> HR true ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply can with (A \/S B) r r; try reflexivity.
  apply ex_seq with ( (vec r (-S (A \/S B)) ++ vec r B) ++ (vec r (A \/S B) ++ T)); [perm_Type_solve | ].
  apply M.
  2:{ eapply ex_hseq; [ | apply W; apply pi ].
      apply Permutation_Type_swap. }
  apply ex_hseq with ((vec r A ++ T) :: (vec r (-S (A \/S B)) ++ vec r B) :: G); [ apply Permutation_Type_swap | ].
  apply can with (A \/S B) r r ; try reflexivity.
  apply ex_seq with ( (vec r (-S (A \/S B)) ++ vec r A) ++ (vec r (A \/S B) ++ T)); [perm_Type_solve | ].
  apply M.
  2:{ eapply ex_hseq; [ | apply W; apply pi].
      apply Permutation_Type_swap. }
  unfold minus; fold minus.
  apply min.
  - apply ex_hseq with (( (vec r (-S A /\S -S B) ++ vec r B) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ perm_Type_solve | ].
    apply W_gen.
    replace (vec r (-S A) ++ vec r A) with (vec r (-S A) ++ vec r A ++ nil) by (now rewrite app_nil_r).
    apply ID_gen; [reflexivity | apply INIT].
  - eapply ex_hseq ; [ apply Permutation_Type_swap | ].
    apply min.
    + apply S.
      apply ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B ++ nil) ; [ perm_Type_solve | ].
      apply ID_gen; [ reflexivity | apply ID_gen ; [ reflexivity | ] ].
      apply ex_hseq with (G ++ (nil :: nil)); [ perm_Type_solve | ].
      apply W_gen; apply INIT.
    + rewrite <-(app_nil_r (vec r B)).
      apply ID_gen; [ reflexivity | ].
      eapply ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ (nil :: nil)); [ | apply W_gen; apply INIT ].
      perm_Type_solve.
Qed.

Lemma min_can_inv_l : forall G T A  B r, HR true ((vec r (A /\S B) ++ T) :: G) -> HR true ((vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply can with (A /\S B) r r; try reflexivity.
  apply ex_seq with ((vec r (-S (A /\S B)) ++ vec r A) ++ (vec r (A /\S B) ++ T)); [ perm_Type_solve | ].
  apply M ; [ | apply pi].
  unfold minus; fold minus.
  apply max.
  apply ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ perm_Type_solve | ].
  apply W_gen.
  rewrite <-(app_nil_r (vec r A)).
  apply ID_gen; [ reflexivity | apply INIT].
Qed.

Lemma min_can_inv_r : forall G T A  B r, HR true ((vec r (A /\S B) ++ T) :: G) -> HR true ((vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply can with (A /\S B) r r; try reflexivity.
  apply ex_seq with ((vec r (-S (A /\S B)) ++ vec r B) ++ (vec r (A /\S B) ++ T)); [ perm_Type_solve | ].
  apply M ; [ | apply pi].
  unfold minus; fold minus.
  apply max.
  apply ex_hseq with (((vec r (-S A) ++ vec r B) :: G) ++ ((vec r (-S B) ++ vec r B) :: nil)); [ perm_Type_solve | ].
  apply W_gen.
  rewrite <-(app_nil_r (vec r B)).
  apply ID_gen; [ reflexivity | apply INIT].
Qed.

Lemma TR_vec b : forall G T vr,
    vr <> nil ->
    HR b (seq_mul_vec vr T :: G) ->
    HR b (T :: G).
Proof.
  intros G T vr; revert G T; induction vr; intros G T Hnnil pi.
  - exfalso; auto.
  - simpl in *.
    destruct vr.
    + apply TR with a.
      simpl in pi; rewrite app_nil_r in pi; apply pi.
    + apply C.
      apply TR with a.
      eapply ex_hseq ; [ apply Permutation_Type_swap | ].
      refine (IHvr (seq_mul a T :: G) T _ _) ; [ now auto | ].
      eapply ex_hseq ; [ apply Permutation_Type_swap | ].
      apply S.
      apply pi.
Qed.

Lemma TR_vec_inv b : forall G T vr,
    HR b (T :: G) ->
    HR b (seq_mul_vec vr T :: G).
Proof with try assumption.
  intros G T vr; revert G T; induction vr; intros G T pi.
  - apply ex_hseq with (G ++ (nil :: nil)) ; [ perm_Type_solve | ].
    apply W_gen.
    apply INIT.
  - simpl.
    apply M.
    + apply TR with (inv_pos a).
      rewrite seq_mul_twice.
      replace (time_pos (inv_pos a) a) with One by (apply Rpos_eq; destruct a; simpl;apply R_blt_lt in e;apply Rinv_l_sym; nra).
      rewrite seq_mul_One.
      apply pi.
    + apply IHvr.
      apply pi.
Qed.

Lemma mix_A_B b : forall G T A B vr vs,
    HR b (((vec vs A) ++ (vec vr A) ++ T) :: G) ->
    HR b (((vec vs B) ++ (vec vr B) ++ T) :: G) ->
    HR b (((vec vs B) ++ (vec vr A) ++ T) :: G).
Proof.
  intros G T A B vr vs piA piB.
  destruct vr as [| r vr]; [ | destruct vs as [ | s vs ]]; try assumption.
  apply C.
  apply TR_vec with (r :: vr) ; [now auto | ].
  eapply ex_hseq ; [ apply Permutation_Type_swap | ].
  apply TR_vec with (s :: vs) ; [ now auto | ].
  apply S.
  apply ex_seq with ((seq_mul_vec (r :: vr) ((vec (s :: vs) A) ++ (vec (r :: vr) A) ++ T)) ++ (seq_mul_vec (s :: vs) ((vec (s :: vs) B) ++ (vec (r :: vr) B) ++ T))).
  2:{ apply M.
      - apply TR_vec_inv.
        apply piA.
      - apply TR_vec_inv.
        apply piB. }
  transitivity ((seq_mul_vec (r :: vr) (vec (s :: vs) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B ++ vec (r :: vr) B ++ T)).
  - apply Permutation_Type_app; try reflexivity.
    transitivity (seq_mul_vec (r :: vr) (vec (s :: vs) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A ++ T)).
    + apply seq_mul_vec_app_r.
    + apply Permutation_Type_app; try reflexivity.
      apply seq_mul_vec_app_r.
  - transitivity ((seq_mul_vec (r :: vr) (vec (s :: vs) A) ++
                               seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++
                                                                                                   ( seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B) ++ seq_mul_vec (s :: vs) T)).
    + apply Permutation_Type_app; try reflexivity.
      transitivity (seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B ++ T)).
      * apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        apply seq_mul_vec_app_r.
    + transitivity ((seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (s :: vs) T) ++ seq_mul_vec (r :: vr) (vec (s :: vs) B ++ vec (r :: vr) A ++ T)).
      * transitivity ((seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (s :: vs) T) ++ (seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ (seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T))).
        -- transitivity ((seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) B) ++ seq_mul_vec (s :: vs) T).
           ++ do 2 (apply Permutation_Type_app; try reflexivity).
              apply seq_mul_vec_vec.
           ++ transitivity ((seq_mul_vec (s :: vs) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A) ++ seq_mul_vec (r :: vr) T) ++ seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) T).
              ** do 3 (apply Permutation_Type_app; try reflexivity).
                 apply seq_mul_vec_vec.
              ** remember (seq_mul_vec (s :: vs) (vec (r :: vr) A)) as srA.
                 remember (seq_mul_vec (r :: vr) (vec (r :: vr) A)) as rrA.
                 remember (seq_mul_vec (s :: vs) (vec (s :: vs) B)) as ssB.
                 remember (seq_mul_vec (r :: vr) (vec (s :: vs) B)) as rsB.
                 perm_Type_solve.                 
        -- apply Permutation_Type_app; try reflexivity.
           transitivity (seq_mul_vec (r :: vr) (vec (s :: vs) B) ++ seq_mul_vec (r :: vr) (vec (r :: vr) A ++ T)).
           ++ apply Permutation_Type_app; try reflexivity.
              symmetry; apply seq_mul_vec_app_r.
           ++ symmetry; apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        transitivity (seq_mul_vec (s :: vs) (vec (s :: vs) B) ++ seq_mul_vec (s :: vs) (vec (r :: vr) A ++ T)).
        -- apply Permutation_Type_app; try reflexivity.
           symmetry; apply seq_mul_vec_app_r.
        -- symmetry; apply seq_mul_vec_app_r.
Qed.

Lemma W_A_B b : forall G T A B vr vs,
    HR b (((vec vs B) ++ (vec vr A) ++ T) ::((vec vs B) ++ (vec vr B) ++ T) ::((vec vs A) ++ (vec vr A) ++ T) :: G) ->
    HR b (((vec vs B) ++ (vec vr B) ++ T) ::((vec vs A) ++ (vec vr A) ++ T) :: G).
Proof.
  intros G T A B vr vs pi.
  destruct vr as [ | r vr]; [ | destruct vs as [ | s vs]].
  - simpl in *.
    apply C.
    apply pi.
  - simpl in *.
    eapply ex_hseq ; [ apply Permutation_Type_swap | ].
    apply C.
    eapply ex_hseq ; [ | apply pi].
    apply Permutation_Type_skip.
    apply Permutation_Type_swap.
  - remember (s :: vs) as vs'; remember (r :: vr) as vr'.
    apply C.
    apply TR_vec with vs' ; [ rewrite Heqvs'; now auto | ].
    apply ex_hseq with ((vec vs' A ++ vec vr' A ++ T) :: (vec vs' B ++ vec vr' B ++ T) :: (seq_mul_vec vs' (vec vs' B ++ vec vr' B ++ T)) :: G).
    { etransitivity ; [ | apply Permutation_Type_swap ].
      etransitivity; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_swap. }
    apply C.
    apply TR_vec with vr'; [ rewrite Heqvr' ; now auto | ].
    eapply ex_hseq.
    { apply Permutation_Type_skip.
      etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_swap. }
    apply S.
    apply ex_seq with (seq_mul_vec (vr' ++ vs') (vec vs' B ++ vec vr' A ++ T)).
    2:{ apply TR_vec_inv.
        eapply ex_hseq ; [ apply Permutation_Type_skip; apply Permutation_Type_swap | apply pi]. }
    rewrite seq_mul_vec_app_l.
    symmetry.
    transitivity ((seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B ++ vec vr' B ++ T)).
    + apply Permutation_Type_app; try reflexivity.
      transitivity (seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A ++ T)).
      * apply seq_mul_vec_app_r.
      * apply Permutation_Type_app; try reflexivity.
        apply seq_mul_vec_app_r.
    + transitivity ((seq_mul_vec vr' (vec vs' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ ( seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B) ++ seq_mul_vec vs' T)).
      * apply Permutation_Type_app; try reflexivity.
        transitivity (seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B ++ T)).
        -- apply seq_mul_vec_app_r.
        -- apply Permutation_Type_app; try reflexivity.
           apply seq_mul_vec_app_r.
      * transitivity ((seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B ++ vec vr' A ++ T)).
        -- transitivity ((seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ (seq_mul_vec vs' (vec vs' B) ++ (seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vs' T))).
           ++ transitivity ((seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' B) ++ seq_mul_vec vs' T).
              ** do 2 (apply Permutation_Type_app; try reflexivity).
                 apply seq_mul_vec_vec.
              ** transitivity ((seq_mul_vec vs' (vec vr' A) ++ seq_mul_vec vr' (vec vr' A) ++ seq_mul_vec vr' T) ++ seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vs' T).
                 --- do 3 (apply Permutation_Type_app; try reflexivity).
                     apply seq_mul_vec_vec.
                 --- remember (seq_mul_vec vs' (vec vr' A)) as srA.
                     remember (seq_mul_vec vr' (vec vr' A)) as rrA.
                     remember (seq_mul_vec vs' (vec vs' B)) as ssB.
                     remember (seq_mul_vec vr' (vec vs' B)) as rsB.
                     perm_Type_solve.                 
           ++ apply Permutation_Type_app; try reflexivity.
              transitivity (seq_mul_vec vs' (vec vs' B) ++ seq_mul_vec vs' (vec vr' A ++ T)).
              ** apply Permutation_Type_app; try reflexivity.
                 symmetry; apply seq_mul_vec_app_r.
              ** symmetry; apply seq_mul_vec_app_r.
        -- apply Permutation_Type_app; try reflexivity.
           transitivity (seq_mul_vec vr' (vec vs' B) ++ seq_mul_vec vr' (vec vr' A ++ T)).
           ++ apply Permutation_Type_app; try reflexivity.
              symmetry; apply seq_mul_vec_app_r.
           ++ symmetry; apply seq_mul_vec_app_r.
Qed.

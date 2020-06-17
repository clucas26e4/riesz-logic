Require Import Rpos.
Require Import term.
Require Import semantic.
Require Import hseq.

Require Import CMorphisms.
Require Import List.
Require Import Permutation_Type.
Require Import Permutation_Type_more.
Require Import Permutation_Type_solve.
Require Import Bool_more.
Require Import Lra.

Local Open Scope R_scope.

Record hr_frag := mk_hr_frag {
                      hr_C : bool;
                      hr_S : bool;
                      hr_T : bool;
                      hr_M : bool;
                      hr_CAN : bool }.

Definition le_hr_frag P Q :=
  prod (Bool.leb (hr_C P) (hr_C Q))
       (prod (Bool.leb (hr_S P) (hr_S Q))
             (prod (Bool.leb (hr_T P) (hr_T Q))
                   (prod (Bool.leb (hr_M P) (hr_M Q))
                         (Bool.leb (hr_CAN P) (hr_CAN Q))))).

Lemma le_hr_frag_trans : forall P Q R,
  le_hr_frag P Q -> le_hr_frag Q R -> le_hr_frag P R.
Proof.
intros P Q R H1 H2.
destruct H1 as (Hc1 & Hs1 & Ht1 & Hm1 & Hcan1).
destruct H2 as (Hc2 & Hs2 & Ht2 & Hm2 & Hcan2).
repeat (split; [eapply leb_trans; try eassumption | ]).
eapply leb_trans; eassumption.
Qed.

Instance le_hr_frag_po : PreOrder le_hr_frag.
Proof.
split.
- repeat split; apply leb_refl.
- intros P Q R.
  apply le_hr_frag_trans.
Qed.

Definition hr_frag_add_C P := mk_hr_frag true (hr_S P) (hr_T P) (hr_M P) (hr_CAN P).
Definition hr_frag_rm_C P := mk_hr_frag false (hr_S P) (hr_T P) (hr_M P) (hr_CAN P).
Definition hr_frag_add_S P := mk_hr_frag (hr_C P) true (hr_T P) (hr_M P) (hr_CAN P).
Definition hr_frag_rm_S P := mk_hr_frag (hr_C P) false (hr_T P) (hr_M P) (hr_CAN P).
Definition hr_frag_add_T P := mk_hr_frag (hr_C P) (hr_S P) true (hr_M P) (hr_CAN P).
Definition hr_frag_rm_T P := mk_hr_frag (hr_C P) (hr_S P) false (hr_M P) (hr_CAN P).
Definition hr_frag_add_M P := mk_hr_frag (hr_C P) (hr_S P) (hr_T P) true (hr_CAN P).
Definition hr_frag_rm_M P := mk_hr_frag (hr_C P) (hr_S P) (hr_T P) false (hr_CAN P).
Definition hr_frag_add_CAN P := mk_hr_frag (hr_C P) (hr_S P) (hr_T P) (hr_M P) true.
Definition hr_frag_rm_CAN P := mk_hr_frag (hr_C P) (hr_S P) (hr_T P) (hr_M P) false.

Lemma add_C_le_frag : forall P, le_hr_frag P (hr_frag_add_C P).
Proof.
  intros P.
  repeat (split; try apply leb_refl; try apply leb_true).
Qed.
Lemma add_S_le_frag : forall P, le_hr_frag P (hr_frag_add_S P).
Proof.
  intros P.
  repeat (split; try apply leb_refl; try apply leb_true).
Qed.
Lemma add_T_le_frag : forall P, le_hr_frag P (hr_frag_add_T P).
Proof.
  intros P.
  repeat (split; try apply leb_refl; try apply leb_true).
Qed.
Lemma add_M_le_frag : forall P, le_hr_frag P (hr_frag_add_M P).
Proof.
  intros P.
  repeat (split; try apply leb_refl; try apply leb_true).
Qed.
Lemma add_CAN_le_frag : forall P, le_hr_frag P (hr_frag_add_CAN P).
Proof.
  intros P.
  repeat (split; try apply leb_refl; try apply leb_true).
Qed.
Lemma rm_C_le_frag : forall P, le_hr_frag (hr_frag_rm_C P) P.
Proof.
  intros P.
  repeat (split; try apply leb_refl).
Qed.
Lemma rm_S_le_frag : forall P, le_hr_frag (hr_frag_rm_S P) P.
Proof.
  intros P.
  repeat (split; try apply leb_refl).
Qed.
Lemma rm_T_le_frag : forall P, le_hr_frag (hr_frag_rm_T P) P.
Proof.
  intros P.
  repeat (split; try apply leb_refl).
Qed.
Lemma rm_M_le_frag : forall P, le_hr_frag (hr_frag_rm_M P) P.
Proof.
  intros P.
  repeat (split; try apply leb_refl).
Qed.
Lemma rm_CAN_le_frag : forall P, le_hr_frag (hr_frag_rm_CAN P) P.
Proof.
  intros P.
  repeat (split; try apply leb_refl).
Qed.

Definition hr_frag_M_can := (mk_hr_frag false false false true true).
Definition hr_frag_S_M_can := (mk_hr_frag false true false true true).
Definition hr_frag_full := (mk_hr_frag true true true true true).
Definition hr_frag_C_S_T_M := (mk_hr_frag true true true true false).
Definition hr_frag_C_S_T := (mk_hr_frag true true true false false).


(** * Definition of hr *)
(** ** HR *)

Inductive HR P : hypersequent -> Type :=
| hrr_INIT : HR P (nil :: nil)
| hrr_W : forall G T, HR P G -> HR P (T :: G)
| hrr_C {f : hr_C P = true} : forall G T, HR P (T :: T :: G) -> HR P (T :: G)
| hrr_S  {f : hr_S P = true} : forall G T1 T2, HR P ((T1 ++ T2) :: G) -> HR P (T1 :: T2 :: G)
| hrr_M {f : hr_M P = true} : forall G T1 T2, HR P (T1 :: G) -> HR P (T2 :: G) -> HR P ((T1 ++ T2) :: G)
| hrr_T {f : hr_T P = true} : forall G T r, HR P (seq_mul r T :: G) -> HR P (T :: G)
| hrr_ID : forall G T n r s, sum_vec r = sum_vec s -> HR P (T :: G) -> HR P ((vec s (covar n) ++ vec r (var n) ++ T) :: G)
| hrr_Z : forall G T r, HR P (T :: G) -> HR P ((vec r zero ++ T) :: G)

| hrr_plus : forall G T A B r, HR P ((vec r A ++ vec r B ++ T) :: G) -> HR P ((vec r (A +S B) ++ T) :: G)
| hrr_mul : forall G T A r0 r, HR P ((vec (mul_vec r0 r) A ++ T) :: G) -> HR P ((vec r (r0 *S A) ++ T) :: G)
| hrr_max : forall G T A B r, HR P ((vec r B ++ T) :: (vec r A ++ T) :: G) -> HR P ((vec r (A \/S B) ++ T) :: G)
| hrr_min : forall G T A B r, HR P ((vec r A ++ T) :: G) -> HR P ((vec r B ++ T) :: G) -> HR P ((vec r (A /\S B) ++ T) :: G)
| hrr_ex_seq : forall G T1 T2, Permutation_Type T1 T2 -> HR P (T1 :: G) -> HR P (T2 :: G)
| hrr_ex_hseq : forall G H, Permutation_Type G H -> HR P G -> HR P H
| hrr_can {f : hr_CAN P = true} : forall G T A r s, sum_vec r = sum_vec s -> HR P ((vec s (-S A) ++ vec r A ++ T) :: G) -> HR P (T :: G).

(* HR with only can and M *)
Definition HR_M_can := HR hr_frag_M_can.
(* HR with only can, S and M *)
Definition HR_S_M_can := HR hr_frag_S_M_can.
(* HR with every rule *)
Definition HR_full := HR hr_frag_full.
(* HR without the CAN rule *)
Definition HR_C_S_T_M := HR hr_frag_C_S_T_M.
(* HR with neither the CAN rule nor the M rule *)
Definition HR_C_S_T := HR hr_frag_C_S_T.

(* Some basic properties *)

Lemma HR_not_empty P : forall G, HR P G -> G <> nil.
Proof.
  intros G pi; induction pi; (try now auto).
  intros Heq; apply IHpi; apply Permutation_Type_nil.
  symmetry; now rewrite <- Heq.
Qed.


Lemma HR_le_frag : forall P Q,
    le_hr_frag P Q ->
    forall G, HR P G -> HR Q G.
Proof.
  intros P Q Hle G pi.
  induction pi;  destruct P as [HCP HSP HTP HMP HCANP]; destruct Q as [HCQ HSQ HTQ HMQ HCANQ]; destruct Hle as [HleC [HleS [HleT [HleM HleCAN]]]]; simpl in *; subst; try (now constructor).
  - apply hrr_T with r; assumption.
  - apply hrr_ex_seq with T1; assumption.
  - apply hrr_ex_hseq with G; assumption.
  - apply hrr_can with A r s; try assumption; try reflexivity.
Qed.

Lemma hrr_W_gen P : forall G H, HR P G -> HR P (H ++ G).
Proof.
  intros G H; revert G; induction H; intros G pi.
  - auto.
  - simpl; apply hrr_W; apply IHlist; apply pi.
Qed.

(* Proof of lemmas of subsection 3.3 *)

Lemma hrr_ID_gen P : forall G T A r s, sum_vec r = sum_vec s -> HR P (T :: G) -> HR P ((vec s (-S A) ++ vec r A ++ T) :: G).
Proof.
  intros G T A; revert G T.
  induction A;intros G T r0 s Heq pi; unfold minus; fold minus.
  - apply hrr_ID; assumption.
  - apply hrr_ex_seq with (vec r0 (covar n) ++ vec s (var n) ++ T); [ perm_Type_solve | ].
    apply hrr_ID; try symmetry; assumption.
  - apply hrr_Z; apply hrr_Z; apply pi.
  - apply hrr_plus.
    apply hrr_ex_seq with (vec r0 (A1 +S A2) ++ vec s (-S A1) ++ vec s (-S A2) ++ T); [ perm_Type_solve | ].
    apply hrr_plus.
    eapply hrr_ex_seq.
    2:{ eapply IHA1; [ apply Heq | ].
        eapply hrr_ex_seq.
        2:{ eapply IHA2; [ apply Heq | apply pi ]. }
        perm_Type_solve. }
    perm_Type_solve.
  - apply hrr_mul.
    eapply hrr_ex_seq with (vec r0 (r *S A) ++ vec (mul_vec r s) (-S A) ++ T) ; [ perm_Type_solve | ].
    apply hrr_mul.
    apply hrr_ex_seq with (vec (mul_vec r s) (-S A) ++ vec (mul_vec r r0) A ++ T); [ perm_Type_solve | ].
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
  - apply hrr_min.
    + apply hrr_ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A1) ++ T); [perm_Type_solve | ].
      apply hrr_max.
      apply hrr_W.
      eapply hrr_ex_seq; [ | apply IHA1; [ apply Heq | apply pi] ].
      perm_Type_solve.
    + apply hrr_ex_seq with (vec r0 (A1 \/S A2) ++ vec s (-S A2) ++ T); [perm_Type_solve | ].
      apply hrr_max.
      apply hrr_ex_hseq with ((vec r0 A1 ++ vec s (-S A2) ++ T) :: (vec r0 A2 ++ vec s (-S A2) ++ T) :: G) ; [ perm_Type_solve | ]. 
      apply hrr_W.
      eapply hrr_ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      perm_Type_solve.
  - apply hrr_ex_seq with (vec r0 (A1 /\S A2) ++ vec s (-S A1 \/S -S A2) ++ T); [ perm_Type_solve | ].
    apply hrr_min.
    + apply hrr_ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A1) ++ T); [perm_Type_solve | ].
      apply hrr_max.
      apply hrr_W.
      apply IHA1; [ apply Heq | apply pi].
    + apply hrr_ex_seq with (vec s (-S A1 \/S -S A2) ++ vec r0 (A2) ++ T); [perm_Type_solve | ].
      apply hrr_max.
      apply hrr_ex_hseq with ((vec s (-S A1) ++ vec r0 A2 ++ T) :: (vec s (-S A2) ++ vec r0 A2 ++ T) :: G) ; [ perm_Type_solve | ]. 
      apply hrr_W.
      eapply hrr_ex_seq; [ | apply IHA2; [ apply Heq | apply pi] ].
      perm_Type_solve.
Qed.

Lemma subs_proof P : forall G n t,
    HR P G ->
    HR P (subs_hseq G n t).
Proof with try assumption; try reflexivity.
  intros G n t pi.
  induction pi;unfold subs_hseq in *; fold subs_hseq in *; try rewrite ? subs_seq_vec in *; try rewrite subs_seq_app in *; unfold subs in *; fold subs in *; try now constructor.
  - replace (subs_seq (seq_mul r T) n t) with (seq_mul r (subs_seq T n t)) in IHpi by (clear; induction T; try destruct a; simpl; try rewrite IHT; try reflexivity).
    apply hrr_T with r...
  - case (n =? n0).
    + apply hrr_ID_gen...
    + apply hrr_ID...
  - eapply hrr_ex_seq; [ apply subs_seq_ex ; apply p | ]...
  - eapply hrr_ex_hseq; [ apply subs_hseq_ex; apply p | ]...
  - rewrite eq_subs_minus in IHpi.
    apply hrr_can with (subs A n t) r s...
Qed.    

Lemma hrr_plus_can_inv P : forall G T A B r, HR P ((vec r (A +S B) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec r A ++ vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hrr_can with (A +S B) r r; try reflexivity.
  apply hrr_ex_seq with ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) ++ (vec r (A +S B) ++ T)); [ perm_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P) ; [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  apply hrr_ex_hseq with (G ++ ((vec r (-S (A +S B)) ++ vec r A ++ vec r B) :: nil)); [ perm_Type_solve | ].
  apply hrr_W_gen.
  unfold minus; fold (-S A); fold (-S B).
  apply hrr_plus.
  apply hrr_ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B); [ perm_Type_solve | ].
  apply hrr_ID_gen; try reflexivity.
  replace (vec r (-S B) ++ vec r B) with (vec r (-S B) ++ vec r B ++ nil) by (now rewrite app_nil_r).
  apply hrr_ID_gen; [ reflexivity | apply hrr_INIT ].
Qed.

Lemma hrr_Z_can_inv P : forall G T r, HR P ((vec r zero ++ T) :: G) -> HR (hr_frag_add_CAN P) (T :: G).
Proof.
  intros G T r pi.
  apply hrr_can with zero r r; try reflexivity.
  apply hrr_Z.
  apply HR_le_frag with P; try assumption.
  apply add_CAN_le_frag.
Qed.
  
Lemma hrr_mul_can_inv P : forall G T A r0 r, HR P ((vec r (r0 *S A) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec (mul_vec r0 r) A ++ T) :: G).
Proof.
  intros G T A r0 r pi.
  apply hrr_can with (r0 *S A) r r; try reflexivity.
  apply hrr_ex_seq with ((vec r (-S (r0 *S A)) ++ vec (mul_vec r0 r) A) ++ (vec r (r0 *S A) ++ T)); [ perm_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  apply hrr_ex_hseq with (G ++ ((vec r (-S (r0 *S A)) ++ vec (mul_vec r0 r) A) :: nil)); [ perm_Type_solve | ].
  apply hrr_W_gen.
  unfold minus; fold minus.
  apply hrr_mul.
  replace (vec (mul_vec r0 r) (-S A) ++ vec (mul_vec r0 r) A) with (vec (mul_vec r0 r) (-S A) ++ vec (mul_vec r0 r) A ++ nil) by (now rewrite app_nil_r).
  apply hrr_ID_gen ; [ reflexivity | ].
  apply hrr_INIT.
Qed.

Lemma hrr_max_can_inv P : forall G T A B r, HR P ((vec r (A \/S B) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M (hr_frag_add_S P))) ((vec r B ++ T) :: (vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hrr_can with (A \/S B) r r; try reflexivity.
  apply hrr_ex_seq with ( (vec r (-S (A \/S B)) ++ vec r B) ++ (vec r (A \/S B) ++ T)); [perm_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hrr_W.
      apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M (hr_frag_add_S P)); [ (apply le_hr_frag_trans with (hr_frag_add_S P) ; [ apply add_S_le_frag | apply add_M_le_frag]) | apply add_CAN_le_frag]. }
  apply hrr_ex_hseq with ((vec r A ++ T) :: (vec r (-S (A \/S B)) ++ vec r B) :: G); [ apply Permutation_Type_swap | ].
  apply hrr_can with (A \/S B) r r ; try reflexivity.
  apply hrr_ex_seq with ( (vec r (-S (A \/S B)) ++ vec r A) ++ (vec r (A \/S B) ++ T)); [perm_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ eapply hrr_ex_hseq; [ apply Permutation_Type_swap | ].
      apply hrr_W.
      apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M (hr_frag_add_S P)); [ (apply le_hr_frag_trans with (hr_frag_add_S P) ; [ apply add_S_le_frag | apply add_M_le_frag]) | apply add_CAN_le_frag]. }
  unfold minus; fold minus.
  apply hrr_min.
  - apply hrr_ex_hseq with (( (vec r (-S A /\S -S B) ++ vec r B) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ perm_Type_solve | ].
    apply hrr_W_gen.
    replace (vec r (-S A) ++ vec r A) with (vec r (-S A) ++ vec r A ++ nil) by (now rewrite app_nil_r).
    apply hrr_ID_gen; [reflexivity | apply hrr_INIT].
  - eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_min.
    + apply hrr_S; try reflexivity.
      apply hrr_ex_seq with (vec r (-S A) ++ vec r A ++ vec r (-S B) ++ vec r B ++ nil) ; [ perm_Type_solve | ].
      apply hrr_ID_gen; [ reflexivity | apply hrr_ID_gen ; [ reflexivity | ] ].
      apply hrr_ex_hseq with (G ++ (nil :: nil)); [ perm_Type_solve | ].
      apply hrr_W_gen; apply hrr_INIT.
    + rewrite <-(app_nil_r (vec r B)).
      apply hrr_ID_gen; [ reflexivity | ].
      eapply hrr_ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ (nil :: nil)); [ | apply hrr_W_gen; apply hrr_INIT ].
      perm_Type_solve.
Qed.

Lemma hrr_min_can_inv_l P : forall G T A  B r, HR P ((vec r (A /\S B) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec r A ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hrr_can with (A /\S B) r r; try reflexivity.
  apply hrr_ex_seq with ((vec r (-S (A /\S B)) ++ vec r A) ++ (vec r (A /\S B) ++ T)); [ perm_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  unfold minus; fold minus.
  apply hrr_max.
  apply hrr_ex_hseq with (((vec r (-S B) ++ vec r A) :: G) ++ ((vec r (-S A) ++ vec r A) :: nil)); [ perm_Type_solve | ].
  apply hrr_W_gen.
  rewrite <-(app_nil_r (vec r A)).
  apply hrr_ID_gen; [ reflexivity | apply hrr_INIT].
Qed.

Lemma hrr_min_can_inv_r P : forall G T A  B r, HR P ((vec r (A /\S B) ++ T) :: G) -> HR (hr_frag_add_CAN (hr_frag_add_M P)) ((vec r B ++ T) :: G).
Proof.
  intros G T A B r pi.
  apply hrr_can with (A /\S B) r r; try reflexivity.
  apply hrr_ex_seq with ((vec r (-S (A /\S B)) ++ vec r B) ++ (vec r (A /\S B) ++ T)); [ perm_Type_solve | ].
  apply hrr_M; try reflexivity.
  2:{ apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_CAN_le_frag]. }
  unfold minus; fold minus.
  apply hrr_max.
  apply hrr_ex_hseq with (((vec r (-S A) ++ vec r B) :: G) ++ ((vec r (-S B) ++ vec r B) :: nil)); [ perm_Type_solve | ].
  apply hrr_W_gen.
  rewrite <-(app_nil_r (vec r B)).
  apply hrr_ID_gen; [ reflexivity | apply hrr_INIT].
Qed.

Lemma hrr_T_vec P : forall G T vr,
    vr <> nil ->
    HR P (seq_mul_vec vr T :: G) ->
    HR (hr_frag_add_S (hr_frag_add_T (hr_frag_add_C P))) (T :: G).
Proof.
  intros G T vr; revert P G T; induction vr; intros P G T Hnnil pi.
  - exfalso; auto.
  - simpl in *.
    destruct vr.
    + apply hrr_T with a; try reflexivity.
      simpl in pi; rewrite app_nil_r in pi.
      apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_S (hr_frag_add_T P)) ; [ | apply add_C_le_frag ].
      apply le_hr_frag_trans with (hr_frag_add_T P) ; [ | apply add_S_le_frag ].
      apply add_T_le_frag.
    + apply hrr_C; try reflexivity.
      apply hrr_T with a; try reflexivity.
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      refine (IHvr (hr_frag_add_S P) (seq_mul a T :: G) T _ _) ; [ now auto | ].
      eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
      apply hrr_S; try reflexivity.
      apply HR_le_frag with P; try assumption.
      apply add_S_le_frag.
Qed.

Lemma hrr_T_vec_inv P : forall G T vr,
    HR P (T :: G) ->
    HR (hr_frag_add_T (hr_frag_add_M P)) (seq_mul_vec vr T :: G).
Proof with try assumption.
  intros G T vr; revert G T; induction vr; intros G T pi.
  - apply hrr_ex_hseq with (G ++ (nil :: nil)) ; [ perm_Type_solve | ].
    apply hrr_W_gen.
    apply hrr_INIT.
  - simpl.
    apply hrr_M; try reflexivity.
    + apply hrr_T with (inv_pos a); try reflexivity.
      rewrite seq_mul_twice.
      replace (time_pos (inv_pos a) a) with One by (apply Rpos_eq; destruct a; simpl;apply R_blt_lt in e;apply Rinv_l_sym; nra).
      rewrite seq_mul_One.
      apply HR_le_frag with P; try assumption.
      apply le_hr_frag_trans with (hr_frag_add_M P); [ apply add_M_le_frag | apply add_T_le_frag ].
    + apply IHvr.
      apply pi.
Qed.

Lemma mix_A_B : forall G T A B vr vs,
    HR_C_S_T_M (((vec vs A) ++ (vec vr A) ++ T) :: G) ->
    HR_C_S_T_M (((vec vs B) ++ (vec vr B) ++ T) :: G) ->
    HR_C_S_T_M (((vec vs B) ++ (vec vr A) ++ T) :: G).
Proof.
  intros G T A B vr vs piA piB.
  destruct vr as [| r vr]; [ | destruct vs as [ | s vs ]]; try assumption.
  apply hrr_C; try reflexivity.
  change (hr_frag_C_S_T_M) with (hr_frag_add_S (hr_frag_add_T (hr_frag_add_C hr_frag_C_S_T_M))).
  apply hrr_T_vec with (r :: vr) ; [now auto | ].
  eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
  change (hr_frag_C_S_T_M) with (hr_frag_add_S (hr_frag_add_T (hr_frag_add_C hr_frag_C_S_T_M))).
  apply hrr_T_vec with (s :: vs) ; [ now auto | ].
  apply hrr_S; try reflexivity.
  apply hrr_ex_seq with ((seq_mul_vec (r :: vr) ((vec (s :: vs) A) ++ (vec (r :: vr) A) ++ T)) ++ (seq_mul_vec (s :: vs) ((vec (s :: vs) B) ++ (vec (r :: vr) B) ++ T))).
  2:{ apply hrr_M; try reflexivity.
      - change (hr_frag_C_S_T_M) with (hr_frag_add_S (hr_frag_add_T (hr_frag_add_C hr_frag_C_S_T_M))).
        apply hrr_T_vec_inv.
        apply piA.
      - change (hr_frag_C_S_T_M) with (hr_frag_add_S (hr_frag_add_T (hr_frag_add_C hr_frag_C_S_T_M))).
        apply hrr_T_vec_inv.
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

Lemma W_A_B : forall G T A B vr vs,
    HR_C_S_T_M (((vec vs B) ++ (vec vr A) ++ T) ::((vec vs B) ++ (vec vr B) ++ T) ::((vec vs A) ++ (vec vr A) ++ T) :: G) ->
    HR_C_S_T_M (((vec vs B) ++ (vec vr B) ++ T) ::((vec vs A) ++ (vec vr A) ++ T) :: G).
Proof.
  intros G T A B vr vs pi.
  destruct vr as [ | r vr]; [ | destruct vs as [ | s vs]].
  - simpl in *.
    apply hrr_C; try reflexivity.
    apply pi.
  - simpl in *.
    eapply hrr_ex_hseq ; [ apply Permutation_Type_swap | ].
    apply hrr_C; try reflexivity.
    eapply hrr_ex_hseq ; [ | apply pi].
    apply Permutation_Type_skip.
    apply Permutation_Type_swap.
  - remember (s :: vs) as vs'; remember (r :: vr) as vr'.
    apply hrr_C; try reflexivity.
    change hr_frag_C_S_T_M with (hr_frag_add_S (hr_frag_add_T (hr_frag_add_C hr_frag_C_S_T_M))).
    apply hrr_T_vec with vs' ; [ rewrite Heqvs'; now auto | ].
    apply hrr_ex_hseq with ((vec vs' A ++ vec vr' A ++ T) :: (vec vs' B ++ vec vr' B ++ T) :: (seq_mul_vec vs' (vec vs' B ++ vec vr' B ++ T)) :: G).
    { etransitivity ; [ | apply Permutation_Type_swap ].
      etransitivity; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_swap. }
    apply hrr_C; try reflexivity.
    change hr_frag_C_S_T_M with (hr_frag_add_S (hr_frag_add_T (hr_frag_add_C hr_frag_C_S_T_M))).
    apply hrr_T_vec with vr'; [ rewrite Heqvr' ; now auto | ].
    eapply hrr_ex_hseq.
    { apply Permutation_Type_skip.
      etransitivity ; [ apply Permutation_Type_swap | ].
      apply Permutation_Type_skip.
      apply Permutation_Type_swap. }
    apply hrr_S; try reflexivity.
    apply hrr_ex_seq with (seq_mul_vec (vr' ++ vs') (vec vs' B ++ vec vr' A ++ T)).
    2:{ change hr_frag_C_S_T_M with (hr_frag_add_T (hr_frag_add_M hr_frag_C_S_T_M)).
        apply hrr_T_vec_inv.
        eapply hrr_ex_hseq ; [ apply Permutation_Type_skip; apply Permutation_Type_swap | apply pi]. }
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

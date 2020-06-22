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

Lemma hrr_mul_vec : forall L,
    HR_C_S_T (map (fun x => snd x) L) ->
    HR_C_S_T (map (fun x => seq_mul (fst x) (snd x)) L).
Proof.
  intros L pi.
  remember (map (fun x => snd x) L) as G.
  revert L HeqG; induction pi; intros L HeqG.
  - destruct L; [ | destruct L]; try now inversion HeqG.
    destruct p as [r T]; destruct T; try now inversion HeqG.
    apply hrr_INIT.
  - destruct L; try now inversion HeqG.
    simpl; apply hrr_W.
    apply IHpi.
    simpl in HeqG; inversion HeqG.
    reflexivity.
  - destruct L; try now inversion HeqG.
    simpl; apply hrr_C; try reflexivity.
    change (seq_mul (fst p) (snd p)
                    :: seq_mul (fst p) (snd p) :: map (fun x : Rpos * sequent => seq_mul (fst x) (snd x)) L)
      with
        (map (fun x : Rpos * sequent => seq_mul (fst x) (snd x)) (p :: p :: L)).
    apply IHpi.
    simpl in HeqG; inversion HeqG.
    reflexivity.

Lemma hrr_M_2 : forall G T1 T2,
    HR_C_S_T (T1 :: G) ->
    HR_C_S_T (T2 :: G) ->
    HR_C_S_T ((T1 ++ T2) :: G).
Proof.
Admitted.

Lemma hrr_M_elim : forall G,
    HR_C_S_T_M G ->
    HR_C_S_T G.
Proof.
  intros G pi; induction pi; try now constructor.
  - apply hrr_M_2; assumption.
  - now apply hrr_T with r.
  - now apply hrr_ex_seq with T1.
  - now apply hrr_ex_hseq with G.
Qed.

(** * Implementation of Section 3.10 *)
Require Import Rpos.
Require Import riesz_logic_List_more.
Require Import FOL_R.
Require Import lt_nat_tuples.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import RL.hr.p_hseq.
Require Import RL.hr.hr.
Require Import RL.hr.lambda_prop_tools.
Require Import RL.hr.invertibility.
Require Import RL.hr.can_elim.
Require Import RL.hr.M_elim.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.

Local Open Scope R_scope.

(* begin hide *)
(* Preliminary work necessary for the decidability result *)
Fixpoint pos_indexes (L : list R) :=
  match L with
  | nil => nil
  | r :: L => if (0 <? r) then 0%nat :: map S (pos_indexes L) else map S (pos_indexes L)
  end.

Lemma pos_indexes_nth : forall L i,
    In_inf i (pos_indexes L) ->
    0 < nth i L 0.
Proof.
  induction L; intros i Hin; simpl in Hin; try now exfalso.
  case_eq (0 <? a); intros H; rewrite H in Hin.
  - destruct i.
    + apply R_blt_lt in H; apply H.
    + simpl; apply IHL.
      apply In_inf_map_S_inv.
      inversion Hin; [ exfalso; inversion H0 | ].
      apply X.
  - destruct i.
    + exfalso.
      apply not_0_In_inf_map_S with (pos_indexes L).
      apply Hin.
    + apply IHL; apply In_inf_map_S_inv; apply Hin.
Qed.

Lemma pos_indexes_Forall_inf : forall L,
    Forall_inf (fun n : nat => (n < length L)%nat) (pos_indexes L).
Proof.
  induction L; [ apply Forall_inf_nil | ].
  simpl.
  case_eq (0 <? a); intros _.
  - apply Forall_inf_cons.
    + lia.
    + apply Forall_inf_lt_map_S.
      apply IHL.
  - apply Forall_inf_lt_map_S; apply IHL.
Qed.

Lemma pos_indexes_not_In_inf : forall L i,
    (i < length L)%nat ->
    (In_inf i (pos_indexes L) -> False) ->
    (nth i L 0 <= 0).
Proof.
  induction L; intros i Hlen H; try now inversion Hlen.
  simpl in H.
  case_eq (0 <? a); intros Hlt; rewrite Hlt in H.
  - destruct i; [ exfalso; apply H; left; lia | ].
    simpl.
    apply IHL; [ simpl in Hlen; lia | ].
    intros Hin.
    apply H.
    right.
    apply in_inf_map.
    apply Hin.
  - destruct i; [ simpl; apply R_blt_nlt in Hlt; lra | ].
    simpl.
    apply IHL; [simpl in Hlen; lia | ].
    intros Hin.
    apply H.
    apply in_inf_map; apply Hin.
Qed.

Lemma pos_indexes_order : forall L,
    forall i j : nat,
      (j < length (pos_indexes L))%nat ->
      (i < j)%nat -> (nth i (pos_indexes L) 0 < nth j (pos_indexes L) 0)%nat.
Proof.
  induction L; intros i j Hlen Hlt ; [ now inversion Hlen | ].
  simpl.
  case_eq (0 <? a); intros H.
  - simpl in Hlen; rewrite H in Hlen.
    simpl in Hlen.
    destruct j; [inversion Hlt | ].
    destruct i; simpl.
    + rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
      rewrite map_nth.
      lia.
    + rewrite nth_indep with _ _ _ _ 1%nat ; [ | lia].
      rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
      rewrite ? map_nth.
      apply lt_n_S.
      rewrite map_length in Hlen.
      apply IHL; lia.
  - simpl in Hlen; rewrite H in Hlen.
    rewrite nth_indep with _ _ _ _ 1%nat ; [ | lia].
    rewrite nth_indep with _ _ j _ 1%nat ; [ | lia].
    rewrite ? map_nth.
    apply lt_n_S.
    rewrite map_length in Hlen.
    apply IHL; lia.
Qed.

Fixpoint p_sum_weight_var_with_coeff n G L :=
  match G, L with
  | _, nil => FOL_R_cst 0
  | nil, _ => FOL_R_cst 0
  | T :: G , r :: L => (r *R sum_weight_p_seq_var n T) +R p_sum_weight_var_with_coeff n G L
  end.

Lemma p_sum_weight_var_with_coeff_lt_max_var : forall n G L val,
    (max_var_p_hseq G < n)%nat ->
    FOL_R_term_sem val (p_sum_weight_var_with_coeff n G L) = 0.
Proof.
  intros n; induction G; intros L val Hlt; destruct L; auto.
  simpl in *.
  rewrite sum_weight_p_seq_var_lt_max_var; try lia.
  rewrite IHG; try lia.
  lra.
Qed.

Lemma p_sum_weight_var_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    p_sum_weight_var_with_coeff n (G1 ++ G2) L = p_sum_weight_var_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma p_sum_weight_var_with_coeff_app2 : forall val n G1 G2 L1 L2,
    (length L1 = length G1) ->
    FOL_R_pred_sem val (p_sum_weight_var_with_coeff n (G1 ++ G2) (L1 ++ L2) =R p_sum_weight_var_with_coeff n G1 L1 +R p_sum_weight_var_with_coeff n G2 L2).
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  lra.
Qed.

Lemma p_sum_weight_var_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    p_sum_weight_var_with_coeff n G (L1 ++ L2) = p_sum_weight_var_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Fixpoint p_sum_weight_covar_with_coeff n G L :=
  match G, L with
  | _, nil => FOL_R_cst 0
  | nil, _ => FOL_R_cst 0
  | T :: G , r :: L => (r *R sum_weight_p_seq_covar n T) +R p_sum_weight_covar_with_coeff n G L
  end.

Lemma p_sum_weight_covar_with_coeff_lt_max_covar : forall n G L val,
    (max_var_p_hseq G < n)%nat ->
    FOL_R_term_sem val (p_sum_weight_covar_with_coeff n G L) = 0.
Proof.
  intros n; induction G; intros L val Hlt; destruct L; auto.
  simpl in *.
  rewrite sum_weight_p_seq_covar_lt_max_var; try lia.
  rewrite IHG; try lia.
  lra.
Qed.

Lemma p_sum_weight_covar_with_coeff_app1 : forall n G1 G2 L,
    (length L <= length G1)%nat ->
    p_sum_weight_covar_with_coeff n (G1 ++ G2) L = p_sum_weight_covar_with_coeff n G1 L.
Proof.
  intros n; induction G1; intros G2 L Hlen; destruct L; try (now inversion Hlen); [destruct G2 | ]; auto.
  simpl; rewrite IHG1; auto.
  simpl in Hlen; lia.
Qed.

Lemma p_sum_weight_covar_with_coeff_app2 : forall val n G1 G2 L1 L2,
    (length L1 = length G1) ->
    FOL_R_pred_sem val (p_sum_weight_covar_with_coeff n (G1 ++ G2) (L1 ++ L2) =R p_sum_weight_covar_with_coeff n G1 L1 +R p_sum_weight_covar_with_coeff n G2 L2).
Proof.
  intros n; induction G1; intros G2 L1 L2 Hlen; destruct L1; try (now inversion Hlen); [destruct L2 ; destruct G2 | ]; simpl; try lra.
  simpl in *; rewrite IHG1; auto.
  lra.
Qed.

Lemma p_sum_weight_covar_with_coeff_app3 : forall n G L1 L2,
    (length G <= length L1)%nat ->
    p_sum_weight_covar_with_coeff n G (L1 ++ L2) = p_sum_weight_covar_with_coeff n G L1.
Proof.
  intros n; induction G; intros L1 L2 Hlen; destruct L1; try (now inversion Hlen); [now destruct L2 | ].
  simpl; rewrite IHG; auto.
  simpl in Hlen; lia.
Qed.

Lemma FOL_R_term_sem_eval_p_sequent : forall val n T,
    FOL_R_term_sem val (sum_weight_p_seq_var n T) - FOL_R_term_sem val (sum_weight_p_seq_covar n T) = sum_weight_seq_var n (eval_p_sequent val T) - sum_weight_seq_covar n (eval_p_sequent val T) .
Proof.
  intros val n; induction T; simpl; try reflexivity.
  destruct a as [a A].
  sem_is_pos_decomp val a; intros e He; simpl;
    destruct A; simpl; try case (n =? n0); simpl; try rewrite IHT; try lra.
Qed.

Lemma FOL_R_term_sem_eval_p_hseq : forall val n G L,
    FOL_R_term_sem val (p_sum_weight_var_with_coeff n G L) - FOL_R_term_sem val (p_sum_weight_covar_with_coeff n G L) = sum_weight_var_with_coeff n (map (eval_p_sequent val) G) (map (FOL_R_term_sem val) L) - sum_weight_covar_with_coeff n (map (eval_p_sequent val) G) (map (FOL_R_term_sem val) L).
Proof.
  intros val n; induction G; intros [ | r L]; simpl; try reflexivity.
  specialize (IHG L).
  transitivity
    (FOL_R_term_sem val r * (FOL_R_term_sem val (sum_weight_p_seq_var n a) - FOL_R_term_sem val (sum_weight_p_seq_covar n a)) +
     (FOL_R_term_sem val (p_sum_weight_var_with_coeff n G L) - FOL_R_term_sem val (p_sum_weight_covar_with_coeff n G L))); try lra.
  rewrite IHG; rewrite FOL_R_term_sem_eval_p_sequent.
  lra.
Qed.

Lemma FOL_R_term_sem_upd_val_vec_lt : forall val a vx vr,
    Forall_inf (fun x => max_var_FOL_R_term a < x)%nat vx ->
    FOL_R_term_sem (upd_val_vec val vx vr) a = FOL_R_term_sem val a.
Proof.
  intros val; induction a; intros vx vr Hall.
  - simpl.
    apply upd_val_vec_not_in.
    intros Hin.
    apply (Forall_inf_forall Hall) in Hin.
    simpl in Hin; lia.
  - reflexivity.
  - simpl; rewrite IHa1; [ rewrite IHa2 | ]; try reflexivity; refine (Forall_inf_arrow _ _ Hall);
      intros a Hlt; simpl in Hlt; lia.
  - simpl; rewrite IHa1; [ rewrite IHa2 | ]; try reflexivity; refine (Forall_inf_arrow _ _ Hall);
      intros a Hlt; simpl in Hlt; lia.
Qed.

Lemma eval_p_seq_upd_val_vec_lt : forall val T vx vr,
    Forall_inf (fun x => max_var_weight_p_seq T < x)%nat vx ->
    eval_p_sequent (upd_val_vec val vx vr) T = eval_p_sequent val T.
Proof.
  intros val; induction T; intros vx vr Hall; simpl; try reflexivity.
  destruct a as [a A].
  rewrite ? FOL_R_term_sem_upd_val_vec_lt ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  rewrite IHT ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  reflexivity.
Qed.
  
Lemma eval_p_hseq_upd_val_vec_lt : forall val G vx vr,
    Forall_inf (fun x => max_var_weight_p_hseq G < x)%nat vx ->
    map (eval_p_sequent (upd_val_vec val vx vr)) G = map (eval_p_sequent val) G.
Proof.
  intros val; induction G; intros vx vr Hall; simpl; try reflexivity.
  rewrite eval_p_seq_upd_val_vec_lt ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  rewrite IHG ; [ | refine (Forall_inf_arrow _ _ Hall); intros a' Hlt'; simpl in Hlt'; lia].
  reflexivity.
Qed.

Lemma sum_weight_with_coeff_eval_eq : forall val n G L,
    sum_weight_var_with_coeff n (map (eval_p_sequent val) G) L - sum_weight_covar_with_coeff n (map (eval_p_sequent val) G) L = FOL_R_term_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) L) (p_sum_weight_var_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length L)))) - FOL_R_term_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length L)) L) (p_sum_weight_covar_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length L)))).
Proof.
  intros val n G L.
  rewrite FOL_R_term_sem_eval_p_hseq.
  rewrite map_val_seq_var.
  rewrite eval_p_hseq_upd_val_vec_lt; try reflexivity.
  apply forall_Forall_inf.
  intros x Hin.
  case_eq (max_var_weight_p_hseq G <? x)%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H]; auto.
  exfalso.
  apply not_In_inf_seq with (S (max_var_weight_p_hseq G)) (length L) x; try lia.
  apply Hin.
Qed.  

(* return a list of all non empty subsets of [0..n] *)
Fixpoint make_subsets n :=
  match n with
  | 0%nat => nil
  | S n => (n :: nil) :: (map (cons n) (make_subsets n)) ++ make_subsets n
  end.

Lemma cond_is_in_make_subsets : forall n l,
    l <> nil ->
    (forall i, nth i l 0 < n)%nat ->
    (forall i j, (j < length l)%nat -> (i < j)%nat -> (nth i l 0 > nth j l 0)%nat) ->
    In_inf l (make_subsets n).
Proof.
  induction n; intros l Hnnil Hle Hlt.
  - specialize (Hle 0%nat).
    exfalso; destruct l; inversion Hle.
  - destruct l; [exfalso; apply Hnnil; reflexivity | ].
    case_eq (n0 =? n); intros Heq.
    + apply Nat.eqb_eq in Heq; subst.
      destruct l.
      * left; reflexivity.
      * right.
        apply in_inf_or_app; left.
        apply in_inf_map_cons.
        apply IHn.
        -- intros H'; inversion H'.
        -- intros i.
           case_eq (i <? length (n0 :: l))%nat; intros H.
           ++ specialize (Hlt 0%nat (S i)).
              simpl in Hlt.
              change (match i with
                      | 0 => n0
                      | S m => nth m l 0
                      end)%nat with (nth i (n0 :: l) 0)%nat in Hlt.
              apply Nat.ltb_lt in H; simpl in H.
              lia.
           ++ apply Nat.ltb_nlt in H.
              rewrite nth_overflow ; destruct n; try lia.
              exfalso.
              specialize (Hlt 0 1)%nat.
              simpl in Hlt; lia.
        -- intros i j Hlen' Hlt'.
           assert (H' := Hlt (S i) (S j)).
           change (nth (S i) (S n :: n0 :: l) 0%nat) with (nth i (n0 :: l) 0%nat) in *.
           change (nth (S j) (S n :: n0 :: l) 0)%nat with (nth j (n0 :: l) 0%nat) in *.
           apply H'; simpl in *; lia.
    + right; apply in_inf_or_app; right.
      apply IHn.
      -- intros H'; inversion H'.
      -- intros i.
         destruct i; [ specialize (Hle 0%nat); apply Nat.eqb_neq in Heq; simpl in *; lia | ].
         case_eq (S i <? length (n0 :: l))%nat; intros H; [ apply Nat.ltb_lt in H | apply Nat.ltb_nlt in H].
         ++ specialize (Hle i).
            specialize (Hlt i (S i)).
            lia.
         ++ rewrite nth_overflow; destruct n; try lia.
            destruct n0; inversion Heq.
            specialize (Hle 0)%nat.
            simpl in Hle; lia.
      -- intros i j Hlen' Hlt'.
         specialize (Hle j); specialize (Hlt i j).
         apply Hlt; lia.
Qed.

Lemma cond_is_in_make_subsets_inv : forall n l,
    In_inf l (make_subsets n) ->
    (l <> nil) * (forall i, nth i l 0 < n)%nat * (forall i j, (j < length l)%nat -> (i < j)%nat -> (nth i l 0 > nth j l 0)%nat).
Proof.
  induction n; intros l; [ intros Hin | intros [Heq | Hin]].
  - inversion Hin.
  - destruct l; [ | destruct l]; inversion Heq; subst.
    repeat split.
    + intros H; inversion H.
    + intros i; destruct i; [ | destruct i]; simpl; lia.
    + intros i j Hlen Hlt.
      destruct j ; [inversion Hlt | ].
      destruct j; try now inversion Hlen.
  - destruct (in_inf_app_or _ _ _ Hin).
    + destruct (in_inf_map_cons_inv _ _ _ _ i) as [l' [Heq Hin']]; subst.
      destruct (IHn l' Hin') as [[Hnnil Hlen] Hlt].
      clear i Hin.
      repeat split.
      * intros H; inversion H.
      * intros i.
        destruct i.
        -- simpl; lia.
        -- specialize (Hlen i).
           simpl.
           lia.
      * intros i j Hlen' Hlt'.
        destruct j; try now inversion Hlt'.
        change (nth (S j) (S n :: l') 0)%nat with (nth j l' 0)%nat.
        destruct i.
        -- simpl.
           specialize (Hlen j).
           lia.
        -- change (nth (S i) (S n :: l') 0)%nat with (nth i l' 0)%nat.
           apply Hlt; simpl in *; lia.
    + specialize (IHn l i).
      clear Hin i.
      destruct IHn as [[Hnil Hlen] Hlt].
      repeat split; auto.
      intro i; specialize (Hlen i); lia.
Qed.    
    
(* return the complementary list of v *)
Fixpoint complementary (v : list nat) n :=
  match v with
  | nil => seq 0%nat n
  | i :: v => remove (Nat.eq_dec) i (complementary v n)
  end.

Lemma In_inf_complementary : forall v n i,
    In_inf i v ->
    In_inf i (complementary v n) ->
    False.
Proof.
  induction v; intros n i Hin1 Hin2; [ inversion Hin1 | ].
  simpl in Hin2.
  case_eq (i =? a); intros H.
  - apply Nat.eqb_eq in H; subst.
    apply In_inf_remove_not in Hin2.
    apply Hin2.
  - inversion Hin1; [ apply Nat.eqb_neq in H; lia | ].
    apply IHv with n i; auto.
    apply In_inf_remove_In_inf in Hin2.
    apply Hin2.
Qed.

Lemma In_inf_complementary_inv : forall v n i,
    (i < n)%nat ->
    (In_inf i (complementary v n) -> False) ->
    In_inf i v.
Proof.
  induction v; intros n i Hlt H.
  - exfalso; apply H.
    replace i with (i + 0)%nat by lia.
    apply In_inf_seq.
    apply Hlt.
  - simpl in *.
    case_eq (a =? i); intros Heq.
    + left.
      apply Nat.eqb_eq in Heq; auto.
    + right.
      apply IHv with n; auto.
      intros Hin.
      apply H.
      apply In_inf_remove_In_inf_inv.
      apply Nat.eqb_neq in Heq; split; auto.    
Qed.

Lemma In_inf_complementary2 : forall v n i,
    In_inf i (complementary v n) ->
    In_inf i v ->
    False.
Proof.
  induction v; intros n i Hin1 Hin2; [ inversion Hin2 | ].
  simpl in Hin1.
  case_eq (i =? a); intros H.
  - apply Nat.eqb_eq in H; subst.
    apply In_inf_remove_not in Hin1.
    apply Hin1.
  - inversion Hin2; [ apply Nat.eqb_neq in H; lia | ].
    apply IHv with n i; auto.
    apply In_inf_remove_In_inf in Hin1.
    apply Hin1.
Qed.

Lemma In_inf_complementary2_inv : forall v n i,
    (i < n)%nat ->
    (In_inf i v -> False) ->
    In_inf i (complementary v n).
Proof.
  induction v; intros n i Hlt H.
  - replace i with (i + 0)%nat by lia.
    apply In_inf_seq.
    apply Hlt.
  - simpl in *.
    case_eq (a =? i); intros Heq.
    + exfalso; apply H; left; apply Nat.eqb_eq; apply Heq.
    + apply In_inf_remove_In_inf_inv.
      apply Nat.eqb_neq in Heq; split; auto.    
Qed.

Lemma complementary_partition : forall v n i,
    (i < n)%nat ->
    (In_inf i v) + (In_inf i (complementary v n)).
Proof.
  intros v n i Hlt.
  assert (Hin := in_inf_dec Nat.eq_dec i v).
  inversion Hin.
  - left; apply X.
  - right.
    apply In_inf_complementary2_inv; auto.
Qed.  
  
Lemma In_inf_complementary_lt : forall L n i,
    In_inf i (complementary L n) ->
    (i < n)%nat.
Proof.
  induction L; intros n i Hin.
  - simpl complementary in Hin.
    replace n with (0 + n)%nat by lia.
    apply In_inf_seq_lt.
    apply Hin.
  - simpl in Hin.
    apply In_inf_remove_In_inf in Hin as [Hneq Hin].
    apply IHL; auto.
Qed.

(* end hide *)

(** return the conjunction /\(beta_{k + i} = 0) for all i \in v *)
Fixpoint FOL_R_all_zero k (v : list nat) :=
  match v with
  | nil => FOL_R_true
  | n :: v => FOL_R_and (FOL_R_atoms (FOL_R_eq (FOL_R_var (k + n)) (FOL_R_cst 0))) (FOL_R_all_zero k v)
  end.

Lemma cond_FOL_R_all_zero_formula_sem : forall k v val,
    (forall n, In_inf n v -> val (k + n)%nat = 0) ->
    FOL_R_formula_sem val (FOL_R_all_zero k v).
Proof.
  intros k; induction v; intros val H; [apply I | ].
  split.
  - apply H.
    apply in_inf_eq.
  - apply IHv.
    intros n Hin.
    apply H.
    apply in_inf_cons; apply Hin.
Qed.
    
Lemma cond_FOL_R_all_zero_formula_sem_inv : forall k v val,
    FOL_R_formula_sem val (FOL_R_all_zero k v) ->
    forall n, In_inf n v -> val (k + n)%nat = 0.
Proof.
  intros k; induction v; intros val Hf n Hin; inversion Hin; subst.
  - destruct Hf as [Heq _]; apply Heq.
  - destruct Hf as [_ Hf].
    apply IHv; assumption.
Qed.

(** return the conjunction /\(0\leq\beta_{k + i} /\ \beta_{k + i} = 0) for all in \in v *)
Fixpoint FOL_R_all_gtz k (v : list nat ) :=
  match v with
  | nil => FOL_R_true
  | n :: v => FOL_R_and (FOL_R_and (FOL_R_neg (FOL_R_atoms (FOL_R_eq (FOL_R_var (k + n)) (FOL_R_cst 0)))) (FOL_R_atoms (FOL_R_le (FOL_R_cst 0) (FOL_R_var (k + n))))) (FOL_R_all_gtz k v)
  end.

Lemma cond_FOL_R_all_gtz_formula_sem : forall k v val,
    (forall n, In_inf n v -> 0 < val (k + n)%nat) ->
    FOL_R_formula_sem val (FOL_R_all_gtz k v).
Proof.
  intros k; induction v; intros val H; [apply I | ].
  split.
  - specialize (H a (in_inf_eq a v)).
    split; simpl; lra.
  - apply IHv.
    intros n Hin.
    apply H.
    apply in_inf_cons; apply Hin.
Qed.
    
Lemma cond_FOL_R_all_gtz_formula_sem_inv : forall k v val,
    FOL_R_formula_sem val (FOL_R_all_gtz k v) ->
    forall n, In_inf n v -> 0 < val (k + n)%nat.
Proof.
  intros k; induction v; intros val Hf n Hin; inversion Hin; subst.
  - destruct Hf as [[Hneq Hle] _].
    simpl in *; lra.
  - destruct Hf as [_ Hf].
    apply IHv; assumption.
Qed.

(** return the conjunction /\(\sum_i^m \beta_{(max_var_weight G) + i} \sum\vec R_{i,j} = \sum_i^m \beta_{(max_var_weight G) + i} \sum\vec S_{i,j} *)
Fixpoint FOL_R_all_atoms_eq G k:=
  match k with
  | 0%nat => FOL_R_atoms (FOL_R_eq (p_sum_weight_var_with_coeff 0%nat G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) (p_sum_weight_covar_with_coeff 0%nat G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))))
  | S k => FOL_R_and (FOL_R_atoms (FOL_R_eq (p_sum_weight_var_with_coeff (S k) G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))) (p_sum_weight_covar_with_coeff (S k) G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))))) (FOL_R_all_atoms_eq G k)
  end.


Lemma cond_FOL_R_all_atoms_eq_formula_sem : forall G k val,
    (forall n, (n <= k)%nat -> FOL_R_pred_sem val (p_sum_weight_var_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))) =R p_sum_weight_covar_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))))) ->
    FOL_R_formula_sem val (FOL_R_all_atoms_eq G k).
Proof.
  intros G; induction k; intros val H.
  - simpl.
    specialize (H 0%nat (Nat.le_refl 0%nat)).
    apply H.
  - simpl.
    split.
    + specialize (H (S k) (Nat.le_refl (S k))).
      apply H.
    + apply IHk.
      intros n Hle.
      apply H.
      lia.
Qed.
    
Lemma cond_FOL_R_all_atoms_eq_formula_sem_inv : forall G k val,
    FOL_R_formula_sem val (FOL_R_all_atoms_eq G k) ->
    forall n, (n <= k)%nat -> FOL_R_pred_sem val (p_sum_weight_var_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G))) =R p_sum_weight_covar_with_coeff n G (map FOL_R_var (seq (S (max_var_weight_p_hseq G)) (length G)))).
Proof.
  intros G; induction k; intros val Hf n Hle.
  - simpl in Hf.
    destruct n; inversion Hle.
    apply Hf.
  - destruct Hf as [Hf1 Hf2].
    case_eq (n =? S k)%nat; intros Heq.
    + simpl in Hf1 |- *.
      apply Nat.eqb_eq in Heq; rewrite Heq.
      apply Hf1.
    + apply IHk ; try assumption.
      apply Nat.eqb_neq in Heq.
      lia.
Qed.

(** return the formula corresponding to \phi_{G,v} *)
Definition FOL_R_phi G v := FOL_R_and (FOL_R_all_zero (S (max_var_weight_p_hseq G)) (complementary v (length G))) (FOL_R_and (FOL_R_all_gtz (S (max_var_weight_p_hseq G)) v) (FOL_R_all_atoms_eq G (max_var_p_hseq G))).

(** return the formula corresponding to \exists \beta_1,....,\beta_n \phi_{G,v} *)
Definition FOL_R_exists_phi G v :=
  exists_vec (seq (S (max_var_weight_p_hseq G)) (length G)) (FOL_R_phi G v).

Lemma cond_FOL_R_exists_phi_formula_sem : forall G v val,
    { vr & prod (length vr = length G) (FOL_R_formula_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (FOL_R_phi G v)) } ->
    FOL_R_formula_sem val (FOL_R_exists_phi G v).
Proof.
  intros G v val [vr [Hlen Hf]].
  apply cond_FOL_R_exists_vec_formula_sem.
  split with vr.
  split; auto.
  rewrite seq_length.
  rewrite Hlen; reflexivity.
Qed.  
    
Lemma cond_FOL_R_exists_phi_formula_sem_inv : forall G v val,
    FOL_R_formula_sem val (FOL_R_exists_phi G v) ->
    { vr & prod (length vr = length G) (FOL_R_formula_sem (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (FOL_R_phi G v)) }.
Proof.
  intros G v val Hf.
  apply cond_FOL_R_exists_vec_formula_sem_inv in Hf as [vr [Hlen Hf]].
  split with vr.
  split; auto.
  rewrite seq_length in Hlen; rewrite Hlen; reflexivity.
Qed.

(** return the whole formula for the atomic case *)
Fixpoint FOL_R_atomic_case_aux G V :=
  match V with
  | nil => FOL_R_false
  | v :: V => FOL_R_or (FOL_R_exists_phi G v) (FOL_R_atomic_case_aux G V)
  end.

Lemma cond_FOL_R_atomic_case_aux_formula_sem : forall G V val,
    { v : _ & In_inf v V & FOL_R_formula_sem val (FOL_R_exists_phi G v)} ->
    FOL_R_formula_sem val (FOL_R_atomic_case_aux G V).
Proof.
  intros G; induction V; intros val [v Hin Hf]; inversion Hin; subst.
  - left.
    apply Hf.
  - right.
    apply IHV.
    split with v; assumption.
Qed.

Lemma cond_FOL_R_atomic_case_aux_formula_sem_inv : forall G V val,
    FOL_R_formula_sem val (FOL_R_atomic_case_aux G V) ->
    { v : _ & In_inf v V & FOL_R_formula_sem val (FOL_R_exists_phi G v)}.
Proof.
  intros G V; induction V; intros val Hf; inversion Hf.
  - split with a; auto.
    apply in_inf_eq.
  - destruct (IHV val X) as [v Hin Hf'].
    split with v; try assumption.
    now apply in_inf_cons.
Qed.

Definition FOL_R_atomic_case G  :=
  FOL_R_atomic_case_aux G (make_subsets (length G)).

(** there exists a formula \phi_G such that \phi_G(\vec r) has a proof if and only if G[\vec r /\vec x] has a proof *) 
Lemma HR_FOL_R_equiv : forall G,
    { f & forall val, p_hseq_well_defined val G ->
                      prod
                        (HR_full (map (eval_p_sequent val) G) -> FOL_R_formula_sem val f)
                        (FOL_R_formula_sem val f -> HR_full (map (eval_p_sequent val) G)) }.
Proof.
  enough (forall G,
             { f & forall val, p_hseq_well_defined val G ->
                               prod
                                (HR_T (map (eval_p_sequent val) G) -> FOL_R_formula_sem val f)
                                (FOL_R_formula_sem val f -> HR_full (map (eval_p_sequent val) G)) }).
  { intros G.
    specialize (X G) as [f H].
    split with f.
    intros val H'.
    destruct (H val) as [H1 H2]; try assumption.
    split.
    - intros pi.
      apply H1.
      apply hrr_M_elim.
      apply hrr_can_elim.
      apply pi.
    - apply H2. }
  intros G; remember (HR_complexity_p_hseq G) as a.
  revert G Heqa.
  apply (lt_nat2_wf_rect a); clear a.
  intros n Hind.
  intros G Heqn.
  destruct n as [n m].
  destruct n.
  - split with (FOL_R_atomic_case G).
    intros val H.
    split.
    + intros pi.
      unfold FOL_R_atomic_case.
      apply cond_FOL_R_atomic_case_aux_formula_sem.
      apply HR_le_frag with _ (hr_frag_T_M) _ in pi ; [ | repeat split; auto].
      assert (hseq_is_atomic (map (eval_p_sequent val) G)) as Hat.
      { apply p_hseq_atomic_hseq_atomic.
        apply p_hseq_is_atomic_complexity_0_inv.
        rewrite <- Heqn; reflexivity. }
      destruct (lambda_prop _ Hat pi) as [L [Hlen [[Hex Hall] Hsum]]].
      split with (rev (pos_indexes L)).
      { apply cond_is_in_make_subsets.
        - apply rev_not_nil.
          clear - Hex.
          induction L; [inversion Hex | ].
          inversion Hex; subst.
          + apply R_blt_lt in H0.
            simpl; rewrite H0.
            intros H; inversion H.
          + case_eq (0 <? a); intros H; [ simpl; rewrite H; intros H'; inversion H' | ].
            simpl; rewrite H.
            intros H'; apply map_eq_nil in H'.
            apply IHL; assumption.
        - intros i.
          apply rev_nth_all_lt.
          clear i.
          intros i.
          case_eq (i <? length (pos_indexes L))%nat.
          + intros Hlt; apply Nat.ltb_lt in Hlt.
            apply Forall_inf_nth; try assumption.
            rewrite map_length in Hlen.
            rewrite <- Hlen.
            apply pos_indexes_Forall_inf.
          + intros Hlt; apply Nat.ltb_nlt in Hlt; rewrite nth_overflow; destruct G; simpl; try lia.
            apply HR_not_empty in pi.
            exfalso; auto.            
        - intros i j Hlen' Hlt'.
          apply rev_reverse_order_lt; try lia.
          apply pos_indexes_order. }
      apply cond_FOL_R_exists_phi_formula_sem.
      split with L.
      split; [ rewrite map_length in Hlen; apply Hlen | ].
      repeat split.
      * apply cond_FOL_R_all_zero_formula_sem.
        intros n Hin.
        rewrite map_length in Hlen; rewrite <- Hlen.
        rewrite upd_val_vec_eq.
        enough (nth n L (val (S (max_var_weight_p_hseq G) + n)%nat) <= 0).
        { apply Forall_inf_nth with _ _ _ n (val ((S (max_var_weight_p_hseq G)) + n)%nat) in Hall; [ lra | ].
          apply In_inf_complementary_lt with (rev (pos_indexes L)).
          change (list (prod Rpos term)) with sequent in Hin.
          rewrite <- Hlen in Hin.
          apply Hin. }
        rewrite nth_indep with _ _ _ _ 0.
        2:{ apply In_inf_complementary_lt with (rev (pos_indexes L)).
            change (list (prod Rpos term)) with sequent in Hin.
            rewrite <- Hlen in Hin.
            apply Hin. }
        apply pos_indexes_not_In_inf.
        -- apply In_inf_complementary_lt with (rev (pos_indexes L)).
           change (list (prod Rpos term)) with sequent in Hin.
           rewrite <- Hlen in Hin.
           apply Hin.
        -- intros H'.
           apply In_inf_complementary in Hin; auto.
           apply In_inf_rev.
           apply H'.
      * apply cond_FOL_R_all_gtz_formula_sem.
        intros n Hin.
        change (list (prod Rpos term)) with sequent.
        rewrite map_length in Hlen; rewrite <- Hlen.
        rewrite upd_val_vec_eq.
        assert (n < length L)%nat as Hlt.
        { apply (@Forall_inf_forall _ (fun x => x < length L)%nat) with (pos_indexes L); [ apply pos_indexes_Forall_inf | ].
          apply In_inf_rev_inv.
          apply Hin. }
        rewrite nth_indep with _ _ _ _ 0; auto.
        apply pos_indexes_nth.
        apply In_inf_rev_inv.
        apply Hin.        
      * apply cond_FOL_R_all_atoms_eq_formula_sem.
        intros n Hlen'.
        rewrite map_length in Hlen; rewrite <- Hlen.
        simpl.
        specialize (Hsum n).
        rewrite sum_weight_with_coeff_eq_var_covar in Hsum.
        rewrite (sum_weight_with_coeff_eval_eq val n G L) in Hsum.
        lra.
    + intros f.
      unfold FOL_R_atomic_case in f.
      apply cond_FOL_R_atomic_case_aux_formula_sem_inv in f as [v Hin f].
      apply cond_FOL_R_exists_phi_formula_sem_inv in f as [vr [Hlen f]].
      destruct f as [f1 [f2 f3]].
      apply HR_le_frag with hr_frag_T_M ; [repeat split; auto | ].
      apply lambda_prop_inv.
      { apply p_hseq_atomic_hseq_atomic.
        apply p_hseq_is_atomic_complexity_0_inv.
        rewrite <- Heqn; reflexivity. }
      split with (map (upd_val_vec val (seq (S (max_var_weight_p_hseq G)) (length G)) vr) (seq (S (max_var_weight_p_hseq G)) (length G))).
      repeat split.
      * rewrite ? map_length.
        rewrite seq_length.
        reflexivity.
      * clear f1 f3.
        apply cond_is_in_make_subsets_inv in Hin as [[Hnnil Hle] Hlt].
        destruct v ; [ exfalso; apply Hnnil; auto | ].
        apply nth_Exists_inf with n 0.
        { rewrite map_length; rewrite seq_length.
          apply (Hle 0%nat). }
        rewrite <- Hlen.
        rewrite map_upd_val_vec_eq.
        apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ n in f2.
        2:{ left; auto. }
        rewrite <- Hlen in f2.
        rewrite upd_val_vec_eq in f2.
        rewrite nth_indep with _ _ _ _ (val ((S (max_var_weight_p_hseq G)) + n)%nat) ; [ apply f2 | ].
        rewrite Hlen.
        apply (Hle 0%nat).
      * clear f3.
        rewrite <- Hlen.
        rewrite map_upd_val_vec_eq.
        apply nth_Forall_inf.
        intros i a' Hlt.
        destruct (complementary_partition v (length vr) i); auto.
        -- apply cond_FOL_R_all_gtz_formula_sem_inv with _ _ _ i in f2; auto.
           rewrite <- Hlen in f2; rewrite upd_val_vec_eq in f2.
           rewrite nth_indep with _ _ _ _ 0; auto.
           apply Rlt_le.
           rewrite nth_indep with _ _ _ _ (val ((S (max_var_weight_p_hseq G)) + i)%nat) ; [ apply f2 | apply Hlt].
        -- rewrite Hlen in i0.
           apply cond_FOL_R_all_zero_formula_sem_inv with _ _ _ i in f1; auto.
           rewrite <- Hlen in f1.
           rewrite upd_val_vec_eq in f1.
           rewrite nth_indep with _ _ _ _ (val ((S (max_var_weight_p_hseq G)) + i)%nat); auto.
           lra.
      * clear f1 f2.
        intros n.
        case_eq (n <=? max_var_p_hseq G)%nat; intros Hle.
        -- apply cond_FOL_R_all_atoms_eq_formula_sem_inv with _ _ _ n in f3 ; [ | apply Nat.leb_le in Hle; auto].
           rewrite sum_weight_with_coeff_eq_var_covar.
           rewrite (sum_weight_with_coeff_eval_eq val n G _).
           simpl in f3 |- *.
           rewrite <- Hlen.
           rewrite map_upd_val_vec_eq.
           rewrite Hlen.
           lra.
        -- apply Nat.leb_nle in Hle.
           clear - Hle.
           rewrite sum_weight_with_coeff_eq_var_covar.
           assert (H := max_var_hseq_le_p_hseq val G).
           rewrite sum_weight_var_with_coeff_lt_max_var; [ | lia ].
           rewrite sum_weight_covar_with_coeff_lt_max_var; [ | lia ].
           lra.
  - destruct complexity_p_hseq_perm_fst with G as [[T H] Hperm Heqc].
    { destruct G; [ | intro H; inversion H].
      inversion Heqn. }
    destruct p_seq_non_atomic_perm with T as [[A D] Hperm' Hnat].
    { intros Hat.
      apply p_seq_is_atomic_complexity_0 in Hat.
      rewrite <- Heqn in Heqc; rewrite Heqc in Hat.
      inversion Hat. }
    destruct A as [r A]; simpl in Hnat.
    destruct A; try (exfalso; now apply Hnat).
    + destruct Hind with (HR_complexity_p_hseq (D :: H)) (D :: H) as [f H'].
      * rewrite Heqn.
        rewrite (complexity_p_hseq_perm _ _ Hperm).
        change (p_sequent) with (list (prod FOL_R_term term)).
        rewrite (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change ((r , zero) :: D) with (vec (r :: nil) zero ++ D).
        apply hrr_Z_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change (list (prod FOL_R_term term)) with p_sequent.
        rewrite <- (complexity_p_hseq_perm _ _ Hperm).
        rewrite <- (complexity_p_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * split with f.
        intros val Hwd.
        assert (Hwd' := p_hseq_well_defined_perm _ _ _ Hperm Hwd).
        inversion Hwd'; subst.
        assert (Hwd'' := p_seq_well_defined_perm _ _ _ Hperm' X).
        inversion Hwd''; subst.
        destruct (H' val) as [H0 H0'].
        { apply Forall_inf_cons; assumption. }
        split.
        -- intros pi.
           apply H0.
           apply hrr_M_elim.
           simpl.
           apply hrr_Z_inv with ((existT _ (FOL_R_term_sem val r) H1) :: nil).
           simpl.
           rewrite eval_p_sequent_cons.
           eapply hrr_ex_seq ; [ apply Permutation_Type_eval_p_sequent; apply Hperm' | eapply hrr_ex_hseq ; [ rewrite <- map_cons; apply Permutation_Type_map; apply Hperm | ]].
           eapply HR_le_frag ; [ | apply pi].
           repeat split; auto.
        -- intros  Hf.
           eapply hrr_ex_hseq ; [ symmetry; apply Permutation_Type_map; apply Hperm | simpl; eapply hrr_ex_seq ; [ symmetry; apply Permutation_Type_eval_p_sequent; apply Hperm' | ]].
           simpl in *.
           sem_is_pos_decomp val r; intros e He ;
             [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
               | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
           change ((existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e, zero) :: eval_p_sequent val D) with (hseq.vec (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e :: nil) zero ++ eval_p_sequent val D).
           apply hrr_Z.
           apply H0'.
           apply Hf.
    + destruct Hind with (HR_complexity_p_hseq ((vec (r :: nil) A1 ++ vec (r :: nil) A2 ++ D) :: H)) ((vec (r :: nil) A1 ++ vec (r :: nil) A2 ++ D) :: H) as [f H'].
      * rewrite Heqn.
        rewrite (complexity_p_hseq_perm _ _ Hperm).
        change p_sequent with (list (prod FOL_R_term term)).
        rewrite (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change ((r , A1 +S A2) :: D) with (vec (r :: nil) (A1 +S A2) ++ D).
        apply hrr_plus_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change (list (prod FOL_R_term term)) with p_sequent.
        rewrite <- (complexity_p_hseq_perm _ _ Hperm).
        rewrite <- (complexity_p_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * split with f.
        intros val Hwd.
        assert (Hwd' := p_hseq_well_defined_perm _ _ _ Hperm Hwd).
        inversion Hwd'; subst.
        assert (Hwd'' := p_seq_well_defined_perm _ _ _ Hperm' X).
        inversion Hwd''; subst.
        destruct (H' val) as [H0 H0'].
        { simpl; apply Forall_inf_cons; [ apply Forall_inf_cons; [ | apply Forall_inf_cons] | ]; assumption. }
        split.
        -- intros pi.
           apply H0.
           apply hrr_M_elim.
           simpl in *.
           sem_is_pos_decomp val r; intros e He ;
             [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
               | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
           set (R := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e)).
           change ((R, A1) :: (R , A2) :: eval_p_sequent val D) with (hseq.vec (R :: nil) A1 ++ hseq.vec (R :: nil) A2 ++ eval_p_sequent val D).
           apply hrr_plus_inv.
           simpl.
           unfold R.
           rewrite eval_p_sequent_cons.
           eapply hrr_ex_seq ; [ apply Permutation_Type_eval_p_sequent; apply Hperm' | eapply hrr_ex_hseq ; [ rewrite <- map_cons; apply Permutation_Type_map; apply Hperm | ]].
           eapply HR_le_frag ; [ | apply pi].
           repeat split; auto.
        -- intros  Hf.
           eapply hrr_ex_hseq ; [ symmetry; apply Permutation_Type_map; apply Hperm | simpl; eapply hrr_ex_seq ; [ symmetry; apply Permutation_Type_eval_p_sequent; apply Hperm' | ]].
           simpl in *.
           sem_is_pos_decomp val r; intros e He ;
             [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
               | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
           change ((existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e, A1 +S A2) :: eval_p_sequent val D) with (hseq.vec (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e :: nil) (A1 +S A2) ++ eval_p_sequent val D).
           apply hrr_plus.
           simpl; rewrite 2 eval_p_sequent_cons.
           apply H0'.
           apply Hf.
    + destruct Hind with (HR_complexity_p_hseq ((vec (mul_vec (FOL_R_cst (projT1 r0)) (r :: nil)) A ++ D) :: H)) ((vec (mul_vec (FOL_R_cst (projT1 r0)) (r :: nil)) A ++ D) :: H) as [f H'].
      * rewrite Heqn.
        rewrite (complexity_p_hseq_perm _ _ Hperm).
        change p_sequent with (list (prod FOL_R_term term)).
        rewrite (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change ((r , r0 *S A) :: D) with (vec (r :: nil) (r0 *S A) ++ D).
        apply hrr_mul_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change (list (prod FOL_R_term term)) with p_sequent.
        rewrite <- (complexity_p_hseq_perm _ _ Hperm).
        rewrite <- (complexity_p_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * split with f.
        intros val Hwd.
        assert (Hwd' := p_hseq_well_defined_perm _ _ _ Hperm Hwd).
        inversion Hwd'; subst.
        assert (Hwd'' := p_seq_well_defined_perm _ _ _ Hperm' X).
        inversion Hwd''; subst.
        destruct (H' val) as [H0 H0'].
        { simpl; apply Forall_inf_cons; [ apply Forall_inf_cons | ]; try assumption.
          simpl in *.
          apply R_blt_lt; apply R_blt_lt in H1.
          destruct r0 as [r0 Hr0]; clear - H1 Hr0; simpl; apply R_blt_lt in Hr0.
          nra. }
        split.
        -- intros pi.
           apply H0.
           apply hrr_M_elim.
           simpl in *.
           assert {H & R_order_dec (projT1 r0 * FOL_R_term_sem val r) = H} as [e He] by (split with (R_order_dec (projT1 r0 * FOL_R_term_sem val r)); reflexivity); destruct e as [e | e | e];
             rewrite ? He;
             [ | exfalso; destruct r0 as [r0 Hr0]; clear - e H1 Hr0; simpl in *; apply R_blt_lt in Hr0; apply R_blt_lt in H1; apply R_blt_lt in e; nra
               | exfalso; destruct r0 as [r0 Hr0]; clear - e H1 Hr0; simpl in *; apply R_blt_lt in Hr0; apply R_blt_lt in H1; nra].
           replace ((existT (fun x : R => (0 <? x) = true) (projT1 r0 * FOL_R_term_sem val r) e, A) :: eval_p_sequent val D) with (hseq.vec (hseq.mul_vec r0 (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) H1 :: nil)) A ++ eval_p_sequent val D).
           2:{ simpl.
               replace (time_pos r0 (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) H1)) with (existT (fun x : R => (0 <? x) = true) (projT1 r0 * FOL_R_term_sem val r) e) by (destruct r0; apply Rpos_eq; simpl; nra).
               reflexivity. }
           apply hrr_mul_inv.
           simpl; rewrite eval_p_sequent_cons.
           eapply hrr_ex_seq ; [ apply Permutation_Type_eval_p_sequent; apply Hperm' | eapply hrr_ex_hseq ; [ rewrite <- map_cons; apply Permutation_Type_map; apply Hperm | ]].
           eapply HR_le_frag ; [ | apply pi].
           repeat split; auto.
        -- intros  Hf.
           eapply hrr_ex_hseq ; [ symmetry; apply Permutation_Type_map; apply Hperm | simpl; eapply hrr_ex_seq ; [ symmetry; apply Permutation_Type_eval_p_sequent; apply Hperm' | ]].
           simpl in *.
           sem_is_pos_decomp val r; intros e He ;
             [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
               | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
           change ((existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e, r0 *S A) :: eval_p_sequent val D) with (hseq.vec (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e :: nil) (r0 *S A) ++ eval_p_sequent val D).
           apply hrr_mul.
           replace (hseq.vec
                      (hseq.mul_vec r0 (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e :: nil)) A ++ eval_p_sequent val D)
             with (eval_p_sequent val (vec (mul_vec (FOL_R_cst (projT1 r0)) (r :: nil)) A ++ D));
             [ apply H0'; apply Hf | ].
           simpl in *.
           assert {H & R_order_dec (projT1 r0 * FOL_R_term_sem val r) = H} as [e' He'] by (split with (R_order_dec (projT1 r0 * FOL_R_term_sem val r)); reflexivity); destruct e' as [e' | e' | e'];
             rewrite ? He';
             [ | exfalso; destruct r0 as [r0 Hr0]; clear - e' H1 Hr0; simpl in *; apply R_blt_lt in Hr0; apply R_blt_lt in H1; apply R_blt_lt in e'; nra
               | exfalso; destruct r0 as [r0 Hr0]; clear - e' H1 Hr0; simpl in *; apply R_blt_lt in Hr0; apply R_blt_lt in H1; nra].
           replace (existT (fun x : R => (0 <? x) = true) (projT1 r0 * FOL_R_term_sem val r) e') with (time_pos r0 (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e)) by (destruct r0; apply Rpos_eq; simpl; nra).
           reflexivity.           
    + destruct Hind with (HR_complexity_p_hseq ((vec (r :: nil) A2 ++ D) :: (vec (r :: nil) A1 ++ D) :: H)) ((vec (r :: nil) A2 ++ D) :: (vec (r :: nil) A1 ++ D) :: H) as [f H'].
      * rewrite Heqn.
        rewrite (complexity_p_hseq_perm _ _ Hperm).
        change p_sequent with (list (prod FOL_R_term term)).
        rewrite (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change ((r , A1 \/S A2) :: D) with (vec (r :: nil) (A1 \/S A2) ++ D).
        apply hrr_max_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change (list (prod FOL_R_term term)) with p_sequent.
        rewrite <- (complexity_p_hseq_perm _ _ Hperm).
        rewrite <- (complexity_p_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * split with f.
        intros val Hwd.
        assert (Hwd' := p_hseq_well_defined_perm _ _ _ Hperm Hwd).
        inversion Hwd'; subst.
        assert (Hwd'' := p_seq_well_defined_perm _ _ _ Hperm' X).
        inversion Hwd''; subst.
        destruct (H' val) as [H0 H0'].
        { simpl; apply Forall_inf_cons; [ apply Forall_inf_cons | apply Forall_inf_cons ; [ apply Forall_inf_cons | ] ]; assumption. }
        split.
        -- intros pi.
           apply H0.
           apply hrr_M_elim.
           simpl in *.
           sem_is_pos_decomp val r; intros e He ;
             [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
               | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
           set (R := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e)).
           change ((R, A1) :: eval_p_sequent val D) with (hseq.vec (R :: nil) A1 ++ eval_p_sequent val D).
           change ((R, A2) :: eval_p_sequent val D) with (hseq.vec (R :: nil) A2 ++ eval_p_sequent val D).
           apply hrr_max_inv.
           simpl.
           unfold R.
           rewrite eval_p_sequent_cons.
           eapply hrr_ex_seq ; [ apply Permutation_Type_eval_p_sequent; apply Hperm' | eapply hrr_ex_hseq ; [ rewrite <- map_cons; apply Permutation_Type_map; apply Hperm | ]].
           eapply HR_le_frag ; [ | apply pi].
           repeat split; auto.
        -- intros  Hf.
           eapply hrr_ex_hseq ; [ symmetry; apply Permutation_Type_map; apply Hperm | simpl; eapply hrr_ex_seq ; [ symmetry; apply Permutation_Type_eval_p_sequent; apply Hperm' | ]].
           simpl in *.
           sem_is_pos_decomp val r; intros e He ;
             [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
               | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
           change ((existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e, A1 \/S A2) :: eval_p_sequent val D) with (hseq.vec (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e :: nil) (A1 \/S A2) ++ eval_p_sequent val D).
           apply hrr_max.
           simpl; rewrite 2 eval_p_sequent_cons.
           apply H0'.
           apply Hf.
    + destruct Hind with (HR_complexity_p_hseq ((vec (r :: nil) A1 ++ D) :: H)) ((vec (r :: nil) A1 ++ D) :: H) as [f H1'].
      * rewrite Heqn.
        rewrite (complexity_p_hseq_perm _ _ Hperm).
        change p_sequent with (list (prod FOL_R_term term)).
        rewrite (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change ((r , A1 /\S A2) :: D) with (vec (r :: nil) (A1 /\S A2) ++ D).
        apply hrr_min_r_decrease_complexity; [ intros H'; inversion H' | ].
        unfold vec; unfold app; rewrite <- (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
        change (list (prod FOL_R_term term)) with p_sequent.
        rewrite <- (complexity_p_hseq_perm _ _ Hperm).
        rewrite <- (complexity_p_seq_perm _ _ Hperm').
        apply Heqc.
      * reflexivity.
      * destruct Hind with (HR_complexity_p_hseq ((vec (r :: nil) A2 ++ D) :: H)) ((vec (r :: nil) A2 ++ D) :: H) as [f2 H2'].
        -- rewrite Heqn.
           rewrite (complexity_p_hseq_perm _ _ Hperm).
           change p_sequent with (list (prod FOL_R_term term)).
           rewrite (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
           change ((r , A1 /\S A2) :: D) with (vec (r :: nil) (A1 /\S A2) ++ D).
           apply hrr_min_l_decrease_complexity; [ intros H'; inversion H' | ].
           unfold vec; unfold app; rewrite <- (complexity_p_hseq_perm_fst_p_seq _ _ H Hperm').
           change (list (prod FOL_R_term term)) with p_sequent.
           rewrite <- (complexity_p_hseq_perm _ _ Hperm).
           rewrite <- (complexity_p_seq_perm _ _ Hperm').
           apply Heqc.
        -- reflexivity.
        -- split with (FOL_R_and f f2).
           intros val Hwd.
           assert (Hwd' := p_hseq_well_defined_perm _ _ _ Hperm Hwd).
           inversion Hwd'; subst.
           assert (Hwd'' := p_seq_well_defined_perm _ _ _ Hperm' X).
           inversion Hwd''; subst.
           destruct (H1' val) as [H10 H11].
           { simpl; apply Forall_inf_cons; [ apply Forall_inf_cons | ]; assumption. }
           destruct (H2' val) as [H20 H21].
           { simpl; apply Forall_inf_cons; [ apply Forall_inf_cons | ]; assumption. }
           split.
           ++ intros pi.
              split.
              ** apply H10.
                 apply hrr_M_elim.
                 simpl in *.
                 sem_is_pos_decomp val r; intros e He ;
                   [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
                     | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
                 set (R := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e)).
                 change ((R, A1) :: eval_p_sequent val D) with (hseq.vec (R :: nil) A1 ++ eval_p_sequent val D).
                 apply hrr_min_inv_l with A2.
                 simpl.
                 unfold R.
                 rewrite eval_p_sequent_cons.
                 eapply hrr_ex_seq ; [ apply Permutation_Type_eval_p_sequent; apply Hperm' | eapply hrr_ex_hseq ; [ rewrite <- map_cons; apply Permutation_Type_map; apply Hperm | ]].
                 eapply HR_le_frag ; [ | apply pi].
                 repeat split; auto.
              ** apply H20.
                 apply hrr_M_elim.
                 simpl in *.
                 sem_is_pos_decomp val r; intros e He ;
                   [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
                     | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
                 set (R := (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e)).
                 change ((R, A2) :: eval_p_sequent val D) with (hseq.vec (R :: nil) A2 ++ eval_p_sequent val D).
                 apply hrr_min_inv_r with A1.
                 simpl.
                 unfold R.
                 rewrite eval_p_sequent_cons.
                 eapply hrr_ex_seq ; [ apply Permutation_Type_eval_p_sequent; apply Hperm' | eapply hrr_ex_hseq ; [ rewrite <- map_cons; apply Permutation_Type_map; apply Hperm | ]].
                 eapply HR_le_frag ; [ | apply pi].
                 repeat split; auto.
           ++ intros  Hf.
              eapply hrr_ex_hseq ; [ symmetry; apply Permutation_Type_map; apply Hperm | simpl; eapply hrr_ex_seq ; [ symmetry; apply Permutation_Type_eval_p_sequent; apply Hperm' | ]].
              simpl in *.
              sem_is_pos_decomp val r; intros e He ;
                [ | exfalso; clear - e H1; apply R_blt_lt in H1; apply R_blt_lt in e; lra
                  | exfalso; clear - e H1; apply R_blt_lt in H1; lra].
              change ((existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e, A1 /\S A2) :: eval_p_sequent val D) with (hseq.vec (existT (fun x : R => (0 <? x) = true) (FOL_R_term_sem val r) e :: nil) (A1 /\S A2) ++ eval_p_sequent val D).
              apply hrr_min;
                simpl; rewrite eval_p_sequent_cons;
                  [ apply H11| apply H21];
                  apply Hf.
Qed.

Lemma p_HR_decidable : forall val G,
    p_hseq_well_defined val G ->
    (HR_full (map (eval_p_sequent val) G)) + (HR_full (map (eval_p_sequent val) G) -> False).
Proof.
  intros val G Hwd.
  destruct (HR_FOL_R_equiv G) as [f [H1 H2]]; [ apply Hwd | ].
  destruct (FOL_R_decidable f) with val.
  - left.
    apply H2; apply f0.
  - right.
    intros pi; apply f0; apply H1; apply pi.
Qed.

(** Theorem 3.17 *)
Lemma HR_decidable : forall G,
    (HR_full G) + (HR_full G -> False).
Proof.
  intros G.
  rewrite <- (eval_p_hypersequent_to_p_hypersequent) with (fun x => 0) _.
  apply p_HR_decidable.
  apply to_p_hypersequent_well_defined.
Qed.

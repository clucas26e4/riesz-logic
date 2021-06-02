Require Import Reals.

Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type.
Require Import RL.OLlibs.Permutation_Type_solve.
Require Import List.

Require Import RL.hmr.term.
Require Import RL.hmr.hseq.
Require Import RL.hmr.p_hseq.
Require Import RL.hmr.apply_logical_rule.
Require Import RL.hmr.lambda_prop_tools.
Require Import RL.hmr.hmr.
Require Import RL.hmr.semantic.
Require Import RL.hmr.can_elim.
Require Import RL.hmr.completeness.
Require Import RL.hmr.soundness.

Require Import RL.Utilities.riesz_logic_List_more.
Require Import RL.Utilities.riesz_logic_Nat_more.
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.polynomials.
Require Import RL.Utilities.pol_continuous.
Require Import RL.Utilities.Lim_seq_US.
Require Import RL.Utilities.R_complements.

Require Import Lra.
Require Import Lia.

Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rcomplements.
Local Open Scope R_scope.

(* begin hide *)
(* Preliminary tools and results used for the different versions of the lambda property,
   e.g, to deal with parametrized hypersequent *)

(* Multiply every sequent by a new variable *)
Fixpoint mul_p_hseq_new_var_aux G i :=
  match G with
  | nil => nil
  | T :: G => (seq_mul (Poly_var i) T) :: (mul_p_hseq_new_var_aux G (S i))
  end.
Definition mul_p_hseq_new_var G := mul_p_hseq_new_var_aux G (S (max_var_weight_p_hseq G)).

Definition val_add_vec val i L := upd_val_vec val (seq i (length L)) L.

Definition eval_p_hseq_with_coeff_aux G val L i := (map (eval_p_sequent (val_add_vec val i L)) (mul_p_hseq_new_var_aux G i)).

Definition eval_p_hseq_with_coeff G val L := eval_p_hseq_with_coeff_aux G val L (S (max_var_weight_p_hseq G)).

Lemma eval_mul_p_hseq_new_var_aux : forall G L n val i,
    length G = length L ->
    (max_var_weight_p_hseq G < i)%nat ->
    Forall_inf (fun x => prod (0 <= x) (x <= 1)) L ->
    sum_weight_var n (eval_p_hseq_with_coeff_aux G val L i) = sum_weight_var_with_coeff n (map (eval_p_sequent val) G) (map R_to_oRpos L).
Proof.
  unfold eval_p_hseq_with_coeff_aux; unfold val_add_vec.
  induction G; intros L n val i Hlen Hlt Hborned; simpl; destruct L; simpl; try reflexivity; try now inversion Hlen.
  inversion Hborned; subst.
  unfold R_to_oRpos; fold R_to_oRpos.
  case (R_order_dec r); intros H.
  2:{ clear - H H0.
      exfalso.
      apply R_blt_lt in H.
      destruct H0; lra. }
  - simpl in Hlen.
    apply eq_add_S in Hlen.
    assert (max_var_weight_p_hseq G < S i)%nat.
    { simpl in Hlt; lia. }
    specialize (IHG L n (upd_val val i r) (S i) Hlen H1 X).
    rewrite IHG; simpl.
    rewrite eval_p_hseq_upd_val_lt.
    2:{ destruct a; simpl in *; lia. }
    rewrite eval_p_sequent_upd_val_vec_lt_max_var.
    2:{ destruct a; [ simpl; apply Forall_inf_seq_gt; lia | ].
        rewrite max_var_weight_p_seq_seq_mul; simpl in *; try lia;
          [ | intros H2; inversion H2].
        destruct p; simpl in *; apply Forall_inf_seq_gt; lia. }
    rewrite sum_weight_var_eval_p_sequent_seq_mul.
    simpl.
    rewrite upd_val_eq.
    rewrite eval_p_sequent_upd_val_lt; try reflexivity.
    simpl in Hlt; lia.
  - simpl in Hlen.
    apply eq_add_S in Hlen.
    assert (max_var_weight_p_hseq G < S i)%nat.
    { simpl in Hlt; lia. }
    subst; specialize (IHG L n (upd_val val i 0) (S i) Hlen H1 X).
    rewrite IHG; simpl.
    rewrite eval_p_hseq_upd_val_lt.
    2:{ destruct a; simpl in *; lia. }
    rewrite eval_p_sequent_upd_val_vec_lt_max_var.
    2:{ destruct a; [ simpl; apply Forall_inf_seq_gt; lia | ].
        rewrite max_var_weight_p_seq_seq_mul; simpl in *; try lia;
          [ | intros H2; inversion H2].
        destruct p; simpl in *; apply Forall_inf_seq_gt; lia. }
    rewrite sum_weight_var_eval_p_sequent_seq_mul.
    simpl.
    rewrite upd_val_eq.
    rewrite eval_p_sequent_upd_val_lt; try nra.
    simpl in Hlt; lia.
Qed.

Lemma eval_mul_p_hseq_new_var : forall G L n val,
    length G = length L ->
    Forall_inf (fun x => prod (0 <= x) (x <= 1)) L ->
    sum_weight_var n (eval_p_hseq_with_coeff G val L) = sum_weight_var_with_coeff n (map (eval_p_sequent val) G) (map R_to_oRpos L).
Proof.
  intros; apply eval_mul_p_hseq_new_var_aux; try assumption; lia.
Qed.

Lemma eval_mul_p_hseq_new_one_aux : forall G L val i,
    length G = length L ->
    (max_var_weight_p_hseq G < i)%nat ->
    Forall_inf (fun x => prod (0 <= x) (x <= 1)) L ->
    sum_weight_one (eval_p_hseq_with_coeff_aux G val L i) = sum_weight_one_with_coeff (map (eval_p_sequent val) G) (map R_to_oRpos L).
Proof.
  unfold eval_p_hseq_with_coeff_aux; unfold val_add_vec.
  induction G; intros L val i Hlen Hlt Hborned; simpl; destruct L; simpl; try reflexivity; try now inversion Hlen.
  inversion Hborned; subst.
  unfold R_to_oRpos; fold R_to_oRpos.
  case (R_order_dec r); intros H.
  2:{ clear - H H0.
      exfalso.
      apply R_blt_lt in H.
      destruct H0; lra. }
  - simpl in Hlen.
    apply eq_add_S in Hlen.
    assert (max_var_weight_p_hseq G < S i)%nat.
    { simpl in Hlt; lia. }
    specialize (IHG L (upd_val val i r) (S i) Hlen H1 X).
    rewrite IHG; simpl.
    rewrite eval_p_hseq_upd_val_lt.
    2:{ destruct a; simpl in *; lia. }
    rewrite eval_p_sequent_upd_val_vec_lt_max_var.
    2:{ destruct a; [ simpl; apply Forall_inf_seq_gt; lia | ].
        rewrite max_var_weight_p_seq_seq_mul; simpl in *; try lia;
          [ | intros H2; inversion H2].
        destruct p; simpl in *; apply Forall_inf_seq_gt; lia. }
    rewrite sum_weight_one_eval_p_sequent_seq_mul.
    simpl.
    rewrite upd_val_eq.
    rewrite eval_p_sequent_upd_val_lt; try nra.
    simpl in Hlt; lia.
  - simpl in Hlen.
    apply eq_add_S in Hlen.
    assert (max_var_weight_p_hseq G < S i)%nat.
    { simpl in Hlt; lia. }
    subst; specialize (IHG L (upd_val val i 0) (S i) Hlen H1 X).
    rewrite IHG; simpl.
    rewrite eval_p_hseq_upd_val_lt.
    2:{ destruct a; simpl in *; lia. }
    rewrite eval_p_sequent_upd_val_vec_lt_max_var.
    2:{ destruct a; [ simpl; apply Forall_inf_seq_gt; lia | ].
        rewrite max_var_weight_p_seq_seq_mul; simpl in *; try lia;
          [ | intros H2; inversion H2].
        destruct p; simpl in *; apply Forall_inf_seq_gt; lia. }
    rewrite sum_weight_one_eval_p_sequent_seq_mul.
    simpl.
    rewrite upd_val_eq.
    rewrite eval_p_sequent_upd_val_lt; try nra.
    simpl in Hlt; lia.
Qed.

Lemma well_defined_mul_new_var_aux : forall G L val i,
    (max_var_weight_p_hseq G < i)%nat ->
    length G = length L ->
    p_hseq_well_defined val G ->
    Forall_inf (fun x => 0 <= x) L ->
    Forall_inf (p_seq_well_defined (val_add_vec val i L)) (mul_p_hseq_new_var_aux G i).
Proof.
  induction G; intros L val i Hvm Hlen Hwd Hall; try apply Forall_inf_nil.
  destruct L; try now inversion Hlen.
  inversion Hwd; subst; simpl.
  change (val_add_vec val i (r :: L)) with
      (val_add_vec (upd_val val i r) (S i) L).
  apply Forall_inf_cons.
  - apply p_seq_well_defined_seq_mul.
    + simpl; unfold val_add_vec.
      rewrite upd_val_vec_not_in.
      2:{ apply not_In_inf_seq; lia. }
      rewrite upd_val_eq.
      inversion Hall; subst; apply H0.
    + apply p_seq_well_defined_upd_val_vec.
      * apply forall_Forall_inf.
        intros x Hin.
        apply In_inf_nth with _ _ _ 0%nat in Hin as [j Hlt Heq].
        rewrite seq_length in Hlt.
        rewrite <- Heq.
        rewrite seq_nth; simpl in *; lia.
      * change (upd_val val i r) with (upd_val_vec val (i :: nil) (r :: nil)).
        apply p_seq_well_defined_upd_val_vec; try assumption.
        apply Forall_inf_cons; [ | apply Forall_inf_nil].
        simpl in *; lia.
  - apply IHG; simpl in *; try lia; [ | inversion Hall; subst; assumption].
    apply p_hseq_well_defined_upd_val; try assumption.
    simpl in *; lia.
Qed.

Lemma well_defined_mul_new_var : forall G L val,
    length G = length L ->
    p_hseq_well_defined val G ->
    Forall_inf (fun x => 0 <= x) L ->
    Forall_inf (p_seq_well_defined (val_add_vec val (S (max_var_weight_p_hseq G)) L)) (mul_p_hseq_new_var G).
Proof.
  unfold mul_p_hseq_new_var.
  intros; apply well_defined_mul_new_var_aux; try assumption.
  lia.
Qed.

Lemma eval_mul_p_hseq_new_one : forall G L val,
    length G = length L ->
    Forall_inf (fun x => prod (0 <= x) (x <= 1)) L ->
    sum_weight_one (eval_p_hseq_with_coeff G val L) = sum_weight_one_with_coeff (map (eval_p_sequent val) G) (map R_to_oRpos L).
Proof.
  intros; apply eval_mul_p_hseq_new_one_aux; try assumption; lia.
Qed.

Lemma modal_complexity_p_hseq_mul_new_var_aux : forall G i,
    modal_complexity_p_hseq G = modal_complexity_p_hseq (mul_p_hseq_new_var_aux G i).
Proof.
  induction G; intros i; try reflexivity.
  simpl.
  rewrite modal_complexity_seq_mul.
  rewrite IHG with (S i).
  reflexivity.
Qed.

Lemma modal_complexity_p_hseq_mul_new_var : forall G,
    modal_complexity_p_hseq G = modal_complexity_p_hseq (mul_p_hseq_new_var G).
Proof.
  intros G; unfold mul_p_hseq_new_var; apply modal_complexity_p_hseq_mul_new_var_aux.
Qed.
  
Fixpoint max_list_oRpos (L : list (option Rpos)) :=
  match L with
  | nil => 0
  | None :: L => max_list_oRpos L
  | Some r :: L => if (max_list_oRpos L <? projT1 r)
                   then projT1 r
                   else max_list_oRpos L
  end.

Lemma max_list_oRpos_pos :
  forall L,
    (Exists_inf (fun x => x <> None) L) ->
    0 < max_list_oRpos L.
Proof.
  induction L; intros Hex; inversion Hex; subst.
  - destruct a; [|contradiction ].
    destruct r.
    simpl.
    clear - e; apply R_blt_lt in e.
    case_eq (max_list_oRpos L <? x); intros; try assumption.
    apply R_blt_nlt in H.
    lra.
  - destruct a.
    + destruct r; simpl.
      clear Hex; apply R_blt_lt in e.
      specialize (IHL X).
      case_eq (max_list_oRpos L <? x); intros; try assumption.
    + apply IHL; apply X.
Qed.

Lemma max_list_oRpos_bpos :
  forall L,
    (Exists_inf (fun x => x <> None) L) ->
    (0 <? max_list_oRpos L) = true.
Proof.
  intros.
  apply R_blt_lt.
  apply max_list_oRpos_pos.
  apply X.
Qed.

Definition max_list_oRpos_Rpos (L : list (option Rpos)) (Hex : Exists_inf (fun x => x <> None) L) := existT (fun x => 0 <? x = true) (max_list_oRpos L) (max_list_oRpos_bpos L Hex).

Definition oRpos_div_Rpos (o : option Rpos) (r : Rpos) :=
  match o with
  | None => None
  | Some r' => Some (time_pos r' (inv_pos r))
  end.

Lemma list_oRpos_div_nth_Some :
  forall L r i r1,
    (i < length L)%nat ->
    nth i L None = Some r1 ->
    nth i (map (fun x => oRpos_div_Rpos x r) L) None = Some (time_pos r1 (inv_pos r)).
Proof.
  induction L; intros r i r1 Hlen Heq; try now inversion Hlen.
  destruct i.
  - destruct a; inversion Heq.
    simpl.
    reflexivity.
  - simpl in Hlen.
    apply lt_S_n in Hlen.
    simpl in Heq.
    specialize (IHL r i r1 Hlen Heq).
    destruct a; simpl; apply IHL.
Qed.

Lemma list_oRpos_div_nth_None :
  forall L r i,
    (i < length L)%nat ->
    nth i L None = None ->
    nth i (map (fun x => oRpos_div_Rpos x r) L) None = None.
Proof.
  induction L; intros r i Hlen Heq; try now inversion Hlen.
  destruct i.
  - destruct a; inversion Heq.
    simpl.
    reflexivity.
  - simpl in Hlen.
    apply lt_S_n in Hlen.
    simpl in Heq.
    specialize (IHL r i Hlen Heq).
    destruct a; simpl; apply IHL.
Qed.

Lemma list_oRpos_max_nth :
  forall (L :list (option Rpos)) (Hex : Exists_inf (fun x => x <> None) L),
    { i : _ &
          prod (i < length L)%nat
               ((nth i L None = Some (max_list_oRpos_Rpos L Hex))) }.
Proof.
  unfold max_list_oRpos_Rpos.
  intros L Hex.
  remember (max_list_oRpos_bpos L Hex) as H.
  clear HeqH Hex.
  induction L; [exfalso; apply R_blt_lt in H; simpl in *; lra | ].
  destruct a.
  2:{ simpl in H.
      specialize (IHL H) as [i [Hlen Heq]].
      split with (S i).
      repeat split; [ simpl; lia | apply Heq]. }
  simpl in H.
  case_eq (max_list_oRpos L <? projT1 r); intros H'.
  - split with 0%nat.
    repeat split; [ simpl; lia | ].
    simpl.
    f_equal.
    destruct r; simpl.
    apply Rpos_eq; simpl.
    simpl in H'; rewrite H'; reflexivity.
  - assert (H0 := H).
    rewrite H' in H0.
    specialize (IHL H0) as [i [Hlen Heq]].
    split with (S i).
    repeat split; [ simpl; lia | ].
    simpl.
    rewrite Heq.
    f_equal; apply Rpos_eq; simpl.
    rewrite H'; reflexivity.
Qed.

Lemma list_oRpos_div_max_exist_1 :
  forall (L : list (option Rpos)) (Hex : Exists_inf (fun x => x <> None) L),
    Exists_inf (fun x => x = Some One) (map (fun x => oRpos_div_Rpos x (max_list_oRpos_Rpos L Hex)) L).
Proof.
  intros L Hex.
  destruct (list_oRpos_max_nth L Hex) as [i [Hlen Heq]].
  apply exists_Exists_inf with (nth i (map (fun x => oRpos_div_Rpos x (max_list_oRpos_Rpos L Hex)) L) None).
  - apply nth_In_inf.
    rewrite map_length.
    apply Hlen.
  - rewrite list_oRpos_div_nth_Some with _ _ _ (max_list_oRpos_Rpos L Hex); try assumption.
    f_equal.
    apply inv_pos_r.
Qed.

Lemma list_oRpos_max_correct :
  forall (L : list (option Rpos)) rmax,
    max_list_oRpos L <= rmax ->
    Forall_inf (fun x => {r & x <> None -> prod (x = Some r) (projT1 r <= rmax)}) L.
Proof.
  induction L; intros rmax Hle; simpl in *; [apply Forall_inf_nil | apply Forall_inf_cons].
  - destruct a.
    + split with r.
      intros _; split; [ reflexivity | ].
      case_eq (max_list_oRpos L <? projT1 r); intros H; rewrite H in Hle; (apply R_blt_lt in H + apply R_blt_nlt in H); try lra.
    + split with One; intros H; contradiction.
  - apply IHL.
    destruct a; simpl in Hle; try assumption.
    case_eq (max_list_oRpos L <? projT1 r); intros H; rewrite H in Hle; (apply R_blt_lt in H + apply R_blt_nlt in H); try lra.
Qed.

Lemma list_oRpos_div_max_all_le_1 :
  forall (L : list (option Rpos)) (r : Rpos),
    max_list_oRpos L <= (projT1 r) ->
    Forall_inf (fun x => {r & x <> None -> prod (x = Some r) (projT1 r <= 1)}) (map (fun x => oRpos_div_Rpos x r) L).
Proof.
  intros L r Hle.
  assert (H := list_oRpos_max_correct L (projT1 r) Hle).
  revert r Hle H.
  induction L; intros r Hle Hall; [ apply Forall_inf_nil | ].
  simpl; apply Forall_inf_cons.
  - destruct a.
    2:{ split with One; intros; contradiction. }
    split with (time_pos r0 (inv_pos r)).
    intros _.
    inversion Hall; subst.
    destruct H0 as [r' f].
    assert (Some r0 <> None) as temp by (intros H; inversion H).
    specialize (f temp); clear temp.
    destruct f as [Htemp Hle'].
    inversion Htemp; subst.
    split.
    + reflexivity.
    + simpl.
      destruct r'; destruct r; simpl.
      simpl in *.
      apply R_blt_lt in e0.
      apply Rmult_le_reg_r with x0; try assumption.
      rewrite Rmult_assoc.
      rewrite Rinv_l.
      2:{ lra. }
      lra.
  - apply IHL; [ | inversion Hall; assumption].
    destruct a; simpl in Hle; try assumption.
    case_eq (max_list_oRpos L <? projT1 r0); intros H; rewrite H in Hle; (apply R_blt_lt in H + apply R_blt_nlt in H); simpl in *; lra.
Qed.

Lemma list_oRpos_div_sum_eq :
  forall (L : list (option Rpos)) r G n,
    sum_weight_var_with_coeff n G (map (fun x => oRpos_div_Rpos x r) L) = (sum_weight_var_with_coeff n G L) / (projT1 r).
Proof.
  intros L r G n.
  revert L; induction G; intros L; destruct L; simpl; try lra.
  specialize (IHG L).
  destruct o; simpl; try lra.
  destruct r0; destruct r; simpl in *; lra.
Qed.

Lemma list_oRpos_div_one_eq :
  forall (L : list (option Rpos)) r G ,
    sum_weight_one_with_coeff G (map (fun x => oRpos_div_Rpos x r) L) = (sum_weight_one_with_coeff G L) / (projT1 r).
Proof.
  intros L r G.
  revert L; induction G; intros L; destruct L; simpl; try lra.
  specialize (IHG L).
  destruct o; simpl; try lra.
  destruct r0; destruct r; simpl in *; lra.
Qed.

Lemma concat_with_coeff_div : forall G L r, concat_with_coeff_mul G (map (fun x : option Rpos => oRpos_div_Rpos x r) L) = hseq.seq_mul (inv_pos r) (concat_with_coeff_mul G L).
Proof.
  induction G; intros L r; destruct L; try reflexivity.
  specialize (IHG L r).
  destruct o; simpl; rewrite IHG; try reflexivity.
  rewrite hseq.seq_mul_app.
  f_equal.
  rewrite hseq.seq_mul_twice.
  f_equal.
  destruct r; destruct r0; apply Rpos_eq; simpl; nra.
Qed.

Lemma only_diamond_p_hseq_mul_p_hseq_new_var_aux : forall G i,
    only_diamond_p_hseq (mul_p_hseq_new_var_aux G i) = mul_p_hseq_new_var_aux (only_diamond_p_hseq G) i.
Proof.
  induction G; intros i; try reflexivity.
  simpl.
  rewrite (IHG (S i)).
  f_equal.
  symmetry; apply only_diamond_p_seq_mul.
Qed.

Lemma concat_with_coeff_mul_p_hseq_new_var_aux : forall G L i val,
    (max_var_weight_p_hseq G < i)%nat ->
    length G = length L ->
    concat (map (eval_p_sequent (val_add_vec val i (map oRpos_to_R L))) (mul_p_hseq_new_var_aux G i)) = concat_with_coeff_mul (map (eval_p_sequent val) G) L.
Proof.
  induction G; intros L i val Hlt Hlen; destruct L; try reflexivity; [ inversion Hlen | ].
  simpl in Hlen.
  apply eq_add_S in Hlen.
  destruct o.
  - simpl.
    rewrite eval_p_sequent_seq_mul_pos with _ _ r _.
    2:{ unfold val_add_vec.
        simpl; rewrite upd_val_vec_not_in; [ rewrite upd_val_eq; reflexivity | ].
        apply not_In_inf_seq; lia. }
    replace (eval_p_sequent (val_add_vec val i (projT1 r :: map oRpos_to_R L)) a)
      with (eval_p_sequent val a).
    2:{ symmetry; unfold val_add_vec; apply eval_p_sequent_upd_val_vec_lt_max_var.
        simpl in Hlt; apply Forall_inf_seq_gt; lia. }
    f_equal.
    change (val_add_vec val i (projT1 r :: map oRpos_to_R L)) with
        (val_add_vec (upd_val val i (projT1 r)) (S i) (map oRpos_to_R L)).
    rewrite (IHG L (S i) (upd_val val i (projT1 r))); simpl in *; try lia.
    f_equal.
    apply eval_p_hseq_upd_val_lt.
    lia.    
  - simpl.
    change (val_add_vec val i (0 :: map oRpos_to_R L)) with
        (val_add_vec (upd_val val i 0) (S i) (map oRpos_to_R L)).
    rewrite eval_p_sequent_seq_mul_0.
    2:{ unfold val_add_vec.
        simpl.
        rewrite upd_val_vec_not_in.
        - rewrite upd_val_eq; reflexivity.
        - apply not_In_inf_seq; lia. }
    rewrite (IHG L (S i) (upd_val val i 0)); simpl in *; try lia.
    f_equal.
    apply eval_p_hseq_upd_val_lt.
    lia.
Qed.
      
Lemma concat_with_coeff_mul_p_hseq_new_var_only_diamond : forall G L val,
    length G = length L ->
    concat (map (eval_p_sequent (val_add_vec val (S (max_var_weight_p_hseq G)) (map oRpos_to_R L))) (only_diamond_p_hseq (mul_p_hseq_new_var G))) = concat_with_coeff_mul (only_diamond_hseq (map (eval_p_sequent val) G)) L.
Proof.
  intros G L val Hlen.
  unfold mul_p_hseq_new_var.
  rewrite only_diamond_p_hseq_mul_p_hseq_new_var_aux.
  rewrite only_diamond_eval_p_hseq.
  apply concat_with_coeff_mul_p_hseq_new_var_aux.
  - assert (H:= max_var_weight_p_hseq_only_diamond G); lia.
  - replace (@length p_sequent (only_diamond_p_hseq G)) with (length G); try assumption.
    clear; induction G; simpl in *; try lia.
Qed.

Lemma sum_weight_one_mul_p_hseq_new_var_aux : forall G L val i,
    Forall_inf (fun x => 0 <= x) L ->
    (max_var_weight_p_hseq G < i)%nat ->
    length G = length L ->
    sum_weight_one_with_coeff (map (eval_p_sequent val) G) (map R_to_oRpos L) = eval_Poly (val_add_vec val i L) (p_sum_weight_one (mul_p_hseq_new_var_aux G i)).
Proof.
  induction G; intros L val i Hall Hlt Hlen; destruct L;
    simpl; try reflexivity; try now inversion Hlen.
  simpl in Hlen; apply eq_add_S in Hlen.
  unfold R_to_oRpos; fold R_to_oRpos.
  case (R_order_dec r); intros e; simpl.
  - rewrite sum_weight_one_p_seq_mul; simpl.
    unfold val_add_vec; simpl.
    rewrite upd_val_vec_not_in.
    2:{ apply not_In_inf_seq; lia. }
    rewrite upd_val_eq.
    do 2 f_equal.
    + rewrite p_sum_weight_one_seq_sem.
      rewrite eval_p_sequent_upd_val_vec_lt_max_var.
      2:{ simpl in *; apply Forall_inf_seq_gt; lia. }
      rewrite eval_p_sequent_upd_val_lt; [ | simpl in *; lia ].
      reflexivity.
    + replace (map (eval_p_sequent val) G) with
          (map (eval_p_sequent (upd_val val i r)) G).
      2:{ rewrite eval_p_hseq_upd_val_lt; [ | simpl in *; lia ].
          reflexivity. }
      apply (IHG L (upd_val val i r) (S i)); try (simpl in * ; lia).
      inversion Hall; assumption.
  - inversion Hall; subst.
    exfalso.
    apply R_blt_lt in e; nra.
  - subst.
    rewrite sum_weight_one_p_seq_mul; simpl.
    unfold val_add_vec; simpl.
    rewrite upd_val_vec_not_in.
    2:{ apply not_In_inf_seq; lia. }
    rewrite upd_val_eq.
    rewrite Rmult_0_l; rewrite Rplus_0_l.
    replace (map (eval_p_sequent val) G) with
        (map (eval_p_sequent (upd_val val i 0)) G).
    2:{ rewrite eval_p_hseq_upd_val_lt; [ | simpl in *; lia ].
        reflexivity. }
    apply (IHG L (upd_val val i 0) (S i)); try (simpl in * ; lia).
    inversion Hall; assumption.      
Qed.

Lemma sum_weight_one_mul_p_hseq_new_var : forall G L val,
    Forall_inf (fun x => 0 <= x) L ->
    length G = length L ->
    sum_weight_one_with_coeff (map (eval_p_sequent val) G) (map R_to_oRpos L) = eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_one (mul_p_hseq_new_var G)).
Proof.
  intros G L val Hall Hlen.
  unfold mul_p_hseq_new_var.
  apply sum_weight_one_mul_p_hseq_new_var_aux; try assumption.
  lia.  
Qed.
(* end hide *)

(** * Lambda property *)
(** Statement of the lambda property *)
Definition def_lambda_prop G :=
  { L &
    prod (length L = length G)
         ((Exists_inf (fun x => x <> None) L) *
          (forall n, sum_weight_var_with_coeff n G L = 0) *
          (0 <= sum_weight_one_with_coeff G L) *
          (HMR_T_M ((concat_with_coeff_mul (only_diamond_hseq G) L) :: nil)))}.

(** * Modal free case *)
(** ** Different formulations of the modal-free lambda property *)
(** Atomic lambda property *)
Definition def_lambda_prop_modal_free G :=
  { L &
    prod (length L = length G)
         ((Exists_inf (fun x => x <> None) L) *
          (forall n, sum_weight_var_with_coeff n G L = 0) *
          (0 <= sum_weight_one_with_coeff G L))}.

(** Atomic lambda property with where the t_i are in [0,1] and not only in R_{>0} *)
Definition def_lambda_prop_modal_free_one G :=
  { L &
    prod (length L = length G)
         ((Exists_inf (fun x => x = Some One) L) *
          (Forall_inf (fun x => {r & x <> None -> prod (x  = Some r) (projT1 r <= 1)}) L) *
          (forall n, sum_weight_var_with_coeff n G L = 0) *
          (0 <= sum_weight_one_with_coeff G L))}.

Definition p_def_lambda_prop_modal_free_one G val := 
  { L &
    prod (length L = length G)
         ((Exists_inf (fun x => x = 1) L) *
          (Forall_inf (fun x => prod (0 <= x) (x <= 1)) L) *
          (forall n, eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_var n (mul_p_hseq_new_var G)) = 0) *
          (0 <= eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_one (mul_p_hseq_new_var G))))}.

(** ** Proofs that those formulations are equivalent *)
Lemma def_lambda_prop_modal_free_one_implies_reg :
  forall G,
    def_lambda_prop_modal_free_one G ->
    def_lambda_prop_modal_free G.
Proof.
  intros G [L [Hlen [[[Hex Hall] Hsum] Hstep]]].
  split with L.
  repeat split; try assumption.
  clear - Hex.
  induction L; inversion Hex; subst.
  - left.
    intros H; inversion H.
  - specialize (IHL X).
    right; apply IHL.
Qed.

Lemma def_lambda_prop_modal_free_reg_implies_one :
  forall G,
    def_lambda_prop_modal_free G ->
    def_lambda_prop_modal_free_one G.
Proof.
  intros G [L [Hlen [[Hex Hsum] Hone]]].
  split with (map (fun x => oRpos_div_Rpos x (max_list_oRpos_Rpos L Hex)) L).
  repeat split.
  - rewrite map_length; apply Hlen.
  - apply list_oRpos_div_max_exist_1.
  - apply list_oRpos_div_max_all_le_1.
    apply Rle_refl.
  - intros n.
    rewrite list_oRpos_div_sum_eq.
    rewrite Hsum.
    lra.
  - rewrite list_oRpos_div_one_eq.
    remember (max_list_oRpos_Rpos L Hex).
    clear Heqs.
    destruct s as [s H]; simpl; apply R_blt_lt in H.
    rewrite <- Rmult_0_l with (/ s).
    apply Rmult_le_compat_r; try lra.
    apply Rlt_le.
    apply Rinv_0_lt_compat; apply H.
Qed.

Lemma def_lambda_prop_modal_free_one_reg_implies_p :
  forall G val,
    def_lambda_prop_modal_free_one (map (eval_p_sequent val) G) ->
    p_def_lambda_prop_modal_free_one G val.
Proof.
  intros G val [L [Hlen [[[Hex Hall] Hsum] Hone]]].
  split with (map oRpos_to_R L).
  repeat split.
  - rewrite map_length; rewrite map_length in Hlen; lia.
  - apply Exists_inf_exists in Hex as [x Hinx Heqx].
    apply (In_inf_nth _ _ None) in Hinx as [i Hlti Heqi].
    apply exists_Exists_inf with (nth i (map oRpos_to_R L) 0).
    + apply nth_In_inf.
      rewrite map_length; lia.
    + change 0 with (oRpos_to_R None).
      rewrite map_nth.
      rewrite Heqi; rewrite Heqx; reflexivity.
  - clear - Hall.
    induction L; [ apply Forall_inf_nil | ].
    inversion Hall; subst.
    specialize (IHL X).
    simpl; apply Forall_inf_cons; try assumption.
    destruct H0 as [r H0].
    destruct a; [ | simpl; split; lra].
    assert (Some r0 <> None) by now auto.
    specialize (H0 H); clear H.
    destruct H0 as [H0 H0'].
    inversion H0; subst.
    destruct r as [r Hr].
    simpl in *.
    split ; [ clear - Hr; apply R_blt_lt in Hr; lra | assumption ].
  - replace L with (map R_to_oRpos (map oRpos_to_R L)) in Hsum.
    2:{ rewrite map_map.
        rewrite map_ext with _ _ _ (fun x => x) _; [ | apply R_to_oRpos_oRpos_to_R].
        apply map_id. }
    intros n; specialize (Hsum n);
      rewrite <- eval_mul_p_hseq_new_var in Hsum.
    + unfold val_add_vec.
      rewrite p_sum_weight_var_sem.
      apply Hsum.
    + rewrite map_length; rewrite map_length in Hlen; lia.
    + clear - Hall.
      induction L; [ apply Forall_inf_nil | ].
      inversion Hall; subst.
      specialize (IHL X).
      simpl; apply Forall_inf_cons; try assumption.
      destruct H0 as [r H0].
      destruct a; [ | simpl; split; lra].
      assert (Some r0 <> None) by now auto.
      specialize (H0 H); clear H.
      destruct H0 as [H0 H0'].
      inversion H0; subst.
      destruct r as [r Hr].
      simpl in *.
      split ; [ clear - Hr; apply R_blt_lt in Hr; lra | assumption ].
  - replace L with (map R_to_oRpos (map oRpos_to_R L)) in Hone.
    2:{ rewrite map_map.
        rewrite map_ext with _ _ _ (fun x => x) _; [ | apply R_to_oRpos_oRpos_to_R].
        apply map_id. }
    rewrite <- eval_mul_p_hseq_new_one in Hone.
    + unfold val_add_vec.
      rewrite p_sum_weight_one_sem.
      apply Hone.
    + rewrite map_length; rewrite map_length in Hlen; lia.
    + clear - Hall.
      induction L; [ apply Forall_inf_nil | ].
      inversion Hall; subst.
      specialize (IHL X).
      simpl; apply Forall_inf_cons; try assumption.
      destruct H0 as [r H0].
      destruct a; [ | simpl; split; lra].
      assert (Some r0 <> None) by now auto.
      specialize (H0 H); clear H.
      destruct H0 as [H0 H0'].
      inversion H0; subst.
      destruct r as [r Hr].
      simpl in *.
      split ; [ clear - Hr; apply R_blt_lt in Hr; lra | assumption ].
Qed.

Lemma def_lambda_prop_modal_free_one_p_implies_reg :
  forall G val,
    p_def_lambda_prop_modal_free_one G val ->
    def_lambda_prop_modal_free_one (map (eval_p_sequent val) G).
Proof.
  intros G val [L [Hlen [[[Hex Hall] Hsum] Hone]]].
  split with (map R_to_oRpos L).
  repeat split.
  - rewrite ? map_length; lia.
  - apply Exists_inf_exists in Hex as [x Hinx Heqx].
    apply (In_inf_nth _ _ 0) in Hinx as [i Hlti Heqi].
    apply exists_Exists_inf with (nth i (map R_to_oRpos L) None).
    + apply nth_In_inf.
      rewrite map_length; lia.
    + replace None with (R_to_oRpos 0).
      2:{ clear.
          unfold R_to_oRpos.
          case (R_order_dec 0); intros e; try reflexivity; exfalso; apply R_blt_lt in e; lra. }
      rewrite map_nth.
      rewrite Heqi; rewrite Heqx.
      clear.
      unfold R_to_oRpos.
      case (R_order_dec 1); intros e; [ | exfalso; clear -e; apply R_blt_lt in e; lra | exfalso; lra ].
      f_equal.
      apply Rpos_eq; reflexivity.
  - clear - Hall.
    induction L; [ apply Forall_inf_nil | ].
    inversion Hall; subst.
    specialize (IHL X).
    simpl; apply Forall_inf_cons; try assumption.
    destruct H0 as [H0 H1].
    remember (R_to_oRpos a).
    revert Heqo.
    unfold R_to_oRpos.
    case (R_order_dec a); intros e; [ | exfalso; clear -e H0; apply R_blt_lt in e; lra | ]; intros Heqo;
      [ | split with One; intros H'; subst; contradiction].
    destruct o; inversion Heqo.
    split with s; subst.
    intros _; split; [f_equal; apply Rpos_eq; reflexivity | apply H1].
  - intros n; specialize (Hsum n);
      rewrite <- eval_mul_p_hseq_new_var.
    + rewrite p_sum_weight_var_sem in Hsum.
      apply Hsum.
    + lia.
    + apply Hall.
  - rewrite <- eval_mul_p_hseq_new_one.
    + rewrite p_sum_weight_one_sem in Hone.
      apply Hone.
    + lia.
    + apply Hall.
Qed.

Lemma lambda_prop_modal_free :
  forall G,
    hseq_is_basic G ->
    modal_complexity_hseq G = 0%nat ->
    HMR_T_M G ->
    def_lambda_prop_modal_free G.
Proof.
  intros G Hat Hmax pi.
  destruct (lambda_prop G Hat pi) as [L [Hlen [[[Hex Hsum] Hone] Hstep]]].
  split with L.
  repeat split; assumption.
Qed.

Lemma lambda_prop_modal_free_inv :
  forall G,
    hseq_is_basic G ->
    modal_complexity_hseq G = 0%nat ->
    def_lambda_prop_modal_free G ->
    HMR_T_M G.
Proof.
  intros G Hat Hmax [L [Hlen [[Hex Hsum] Hone]]].
  apply lambda_prop_inv; try assumption.
  split with L.
  repeat split; try assumption.
  destruct (concat_with_coeff_mul_only_diamond_no_diamond G L) as [[r s] [Hperm Hone']]; try assumption.
  eapply hmrr_ex_seq; [ symmetry; apply Hperm | ].
  rewrite <- (app_nil_r (hseq.vec r MRS_one)).
  apply hmrr_one; [ | apply hmrr_INIT].
  lra.
Qed.

(** * Modal case *)
(** ** Different formulations of the lambda property *)
Definition def_lambda_prop_one G :=
  { L &
    prod (length L = length G)
         ((Exists_inf (fun x => x = Some One) L) *
          (Forall_inf (fun x => {r & x <> None -> prod (x  = Some r) (projT1 r <= 1)}) L) *
          (forall n, sum_weight_var_with_coeff n G L = 0) *
          (0 <= sum_weight_one_with_coeff G L) *
          (HMR_T_M (concat_with_coeff_mul (only_diamond_hseq G) L :: nil)))}.

Definition p_def_lambda_prop_one G val := 
  { L &
    prod (length L = length G)
         ((Exists_inf (fun x => x = 1) L) *
          (Forall_inf (fun x => prod (0 <= x) (x <= 1)) L) *
          (forall n, eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_var n (mul_p_hseq_new_var G)) = 0) *
          (0 <= eval_Poly (val_add_vec val (S (max_var_weight_p_hseq G)) L) (p_sum_weight_one (mul_p_hseq_new_var G))) *
          (HMR_T_M ( concat (map (eval_p_sequent (val_add_vec val (S (max_var_weight_p_hseq G)) L)) (only_diamond_p_hseq (mul_p_hseq_new_var  G))) :: nil)))}.

(** ** Proofs that those formulations are equivalent *)
Lemma def_lambda_prop_one_implies_reg :
  forall G,
    def_lambda_prop_one G ->
    def_lambda_prop G.
Proof.
  intros G [L [Hlen [[[[Hex Hall] Hsum] Hone ]Hstep]]].
  split with L.
  repeat split; try assumption.
  clear - Hex.
  induction L; inversion Hex; subst.
  - left.
    intros H; inversion H.
  - specialize (IHL X).
    right; apply IHL.
Qed.

Lemma def_lambda_prop_reg_implies_one :
  forall G,
    def_lambda_prop G ->
    def_lambda_prop_one G.
Proof.
  intros G [L [Hlen [[[Hex Hsum] Hone] Hstep]]].
  split with (map (fun x => oRpos_div_Rpos x (max_list_oRpos_Rpos L Hex)) L).
  repeat split.
  - rewrite map_length; apply Hlen.
  - apply list_oRpos_div_max_exist_1.
  - apply list_oRpos_div_max_all_le_1.
    apply Rle_refl.
  - intros n.
    rewrite list_oRpos_div_sum_eq.
    rewrite Hsum.
    lra.
  - rewrite list_oRpos_div_one_eq.
    remember (max_list_oRpos_Rpos L Hex).
    clear Heqs.
    destruct s as [s H]; simpl; apply R_blt_lt in H.
    rewrite <- Rmult_0_l with (/ s).
    apply Rmult_le_compat_r; try lra.
    apply Rlt_le.
    apply Rinv_0_lt_compat; apply H.
  - rewrite concat_with_coeff_div.
    apply hmrr_T with (max_list_oRpos_Rpos L Hex); try reflexivity.
    rewrite hseq.seq_mul_twice.
    replace (time_pos (max_list_oRpos_Rpos L Hex) (inv_pos (max_list_oRpos_Rpos L Hex))) with One.
    { rewrite hseq.seq_mul_One; apply Hstep. }
    remember (max_list_oRpos_Rpos L Hex); clear.
    destruct s; apply Rpos_eq; simpl.
    apply R_blt_lt in e.
    apply Rinv_r_sym; lra.
Qed.

Lemma def_lambda_prop_one_reg_implies_p :
  forall G val,
    def_lambda_prop_one (map (eval_p_sequent val) G) ->
    p_def_lambda_prop_one G val.
Proof.
  intros G val [L [Hlen [[[[Hex Hall] Hsum] Hone] Hstep]]].
  split with (map oRpos_to_R L).
  repeat split.
  - rewrite map_length; rewrite map_length in Hlen; lia.
  - apply Exists_inf_exists in Hex as [x Hinx Heqx].
    apply (In_inf_nth _ _ None) in Hinx as [i Hlti Heqi].
    apply exists_Exists_inf with (nth i (map oRpos_to_R L) 0).
    + apply nth_In_inf.
      rewrite map_length; lia.
    + change 0 with (oRpos_to_R None).
      rewrite map_nth.
      rewrite Heqi; rewrite Heqx; reflexivity.
  - clear - Hall.
    induction L; [ apply Forall_inf_nil | ].
    inversion Hall; subst.
    specialize (IHL X).
    simpl; apply Forall_inf_cons; try assumption.
    destruct H0 as [r H0].
    destruct a; [ | simpl; split; lra].
    assert (Some r0 <> None) by now auto.
    specialize (H0 H); clear H.
    destruct H0 as [H0 H0'].
    inversion H0; subst.
    destruct r as [r Hr].
    simpl in *.
    split ; [ clear - Hr; apply R_blt_lt in Hr; lra | assumption ].
  - replace L with (map R_to_oRpos (map oRpos_to_R L)) in Hsum.
    2:{ rewrite map_map.
        rewrite map_ext with _ _ _ (fun x => x) _; [ | apply R_to_oRpos_oRpos_to_R].
        apply map_id. }
    intros n; specialize (Hsum n);
      rewrite <- eval_mul_p_hseq_new_var in Hsum.
    + unfold val_add_vec.
      rewrite p_sum_weight_var_sem.
      apply Hsum.
    + rewrite map_length; rewrite map_length in Hlen; lia.
    + clear - Hall.
      induction L; [ apply Forall_inf_nil | ].
      inversion Hall; subst.
      specialize (IHL X).
      simpl; apply Forall_inf_cons; try assumption.
      destruct H0 as [r H0].
      destruct a; [ | simpl; split; lra].
      assert (Some r0 <> None) by now auto.
      specialize (H0 H); clear H.
      destruct H0 as [H0 H0'].
      inversion H0; subst.
      destruct r as [r Hr].
      simpl in *.
      split ; [ clear - Hr; apply R_blt_lt in Hr; lra | assumption ].
  - replace L with (map R_to_oRpos (map oRpos_to_R L)) in Hone.
    2:{ rewrite map_map.
        rewrite map_ext with _ _ _ (fun x => x) _; [ | apply R_to_oRpos_oRpos_to_R].
        apply map_id. }
    rewrite <- eval_mul_p_hseq_new_one in Hone.
    + unfold val_add_vec.
      rewrite p_sum_weight_one_sem.
      apply Hone.
    + rewrite map_length; rewrite map_length in Hlen; lia.
    + clear - Hall.
      induction L; [ apply Forall_inf_nil | ].
      inversion Hall; subst.
      specialize (IHL X).
      simpl; apply Forall_inf_cons; try assumption.
      destruct H0 as [r H0].
      destruct a; [ | simpl; split; lra].
      assert (Some r0 <> None) by now auto.
      specialize (H0 H); clear H.
      destruct H0 as [H0 H0'].
      inversion H0; subst.
      destruct r as [r Hr].
      simpl in *.
      split ; [ clear - Hr; apply R_blt_lt in Hr; lra | assumption ].
  - rewrite concat_with_coeff_mul_p_hseq_new_var_only_diamond.
    2:{ rewrite map_length in Hlen; lia. }
    apply Hstep.
Qed.

Lemma def_lambda_prop_one_p_implies_reg :
  forall G val,
    p_def_lambda_prop_one G val ->
    def_lambda_prop_one (map (eval_p_sequent val) G).
Proof.
  intros G val [L [Hlen [[[[Hex Hall] Hsum] Hone] Hstep]]].
  split with (map R_to_oRpos L).
  repeat split.
  - rewrite ? map_length; lia.
  - apply Exists_inf_exists in Hex as [x Hinx Heqx].
    apply (In_inf_nth _ _ 0) in Hinx as [i Hlti Heqi].
    apply exists_Exists_inf with (nth i (map R_to_oRpos L) None).
    + apply nth_In_inf.
      rewrite map_length; lia.
    + replace None with (R_to_oRpos 0).
      2:{ clear.
          unfold R_to_oRpos.
          case (R_order_dec 0); intros e; try reflexivity; exfalso; apply R_blt_lt in e; lra. }
      rewrite map_nth.
      rewrite Heqi; rewrite Heqx.
      clear.
      unfold R_to_oRpos.
      case (R_order_dec 1); intros e; [ | exfalso; clear -e; apply R_blt_lt in e; lra | exfalso; lra ].
      f_equal.
      apply Rpos_eq; reflexivity.
  - clear - Hall.
    induction L; [ apply Forall_inf_nil | ].
    inversion Hall; subst.
    specialize (IHL X).
    simpl; apply Forall_inf_cons; try assumption.
    destruct H0 as [H0 H1].
    remember (R_to_oRpos a).
    revert Heqo.
    unfold R_to_oRpos.
    case (R_order_dec a); intros e; [ | exfalso; clear -e H0; apply R_blt_lt in e; lra | ]; intros Heqo;
      [ | split with One; intros H'; subst; contradiction].
    destruct o; inversion Heqo.
    split with s; subst.
    intros _; split; [f_equal; apply Rpos_eq; reflexivity | apply H1].
  - intros n; specialize (Hsum n);
      rewrite <- eval_mul_p_hseq_new_var.
    + rewrite p_sum_weight_var_sem in Hsum.
      apply Hsum.
    + lia.
    + apply Hall.
  - rewrite <- eval_mul_p_hseq_new_one.
    + rewrite p_sum_weight_one_sem in Hone.
      apply Hone.
    + lia.
    + apply Hall.
  - replace L with (map oRpos_to_R (map R_to_oRpos L)) in Hstep.
    2:{ clear - Hall.
        induction L; try reflexivity.
        inversion Hall; subst.
        destruct H0 as [Ha _].
        specialize (IHL X).
        simpl; rewrite IHL; f_equal.
        unfold R_to_oRpos.
        case (R_order_dec a); intros e; try (exfalso; try apply R_blt_lt in e; nra);
          simpl; nra. }
    rewrite concat_with_coeff_mul_p_hseq_new_var_only_diamond in Hstep; try assumption.
    rewrite map_length; lia.
Qed.

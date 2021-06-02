Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.polynomials.
Require Import RL.Utilities.riesz_logic_Nat_more.
Require Import RL.Utilities.Lim_seq_US.
Require Import RL.Utilities.pol_continuous.
Require Import RL.Utilities.R_complements.
Require Import riesz_logic_List_more.
Require Import RL.hr.term.
Require Import RL.hr.semantic.
Require Import RL.hr.hseq.
Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.

Require Import CMorphisms.
Require Import Lra.
Require Import Lia.
Require Import FunctionalExtensionality.

Require Import RL.OLlibs.List_more.
Require Import RL.OLlibs.List_Type.
Require Import RL.OLlibs.Permutation_Type_more.
Require Import RL.OLlibs.Permutation_Type_solve.
Require Import RL.OLlibs.wf_prod.

Local Open Scope R_scope.
(** * Definitions *)
                                                
Definition p_sequent : Type := list (Poly * term).

Definition p_seq_is_atomic (T : p_sequent) := Forall_inf (fun x => match x with (a , A) => is_atom A end) T.

Fixpoint eval_p_sequent (val : nat -> R) (T : p_sequent) : sequent :=
  match T with
  | nil => nil
  | (a , A) :: T => match R_order_dec (eval_Poly val a) with
                    | R_is_gt H => (existT (fun x => 0 <? x = true) (eval_Poly val a) H, A) :: (eval_p_sequent val T)
                    | R_is_lt H => (existT (fun x => 0 <? x = true) (-(eval_Poly val a)) H, -S A) :: (eval_p_sequent val T)
                    | R_is_null H => eval_p_sequent val T
                    end
  end.

Fixpoint to_p_sequent (T : sequent) : p_sequent :=
  match T with
  | nil => nil
  | (a, A) :: T => (Poly_cst (projT1 a), A) :: (to_p_sequent T)
  end.
  
Definition Permutation_Type_p_seq val (T1 T2 : p_sequent) := Permutation_Type (eval_p_sequent val T1) (eval_p_sequent val T2).

Definition p_hypersequent : Type := list p_sequent.

Definition p_hseq_is_atomic G := Forall_inf p_seq_is_atomic G.

Definition Permutation_Type_p_hseq val (G1 G2 : p_hypersequent) := Permutation_Type (map (eval_p_sequent val) G1) (map (eval_p_sequent val) G2).

Fixpoint to_p_hypersequent (G : hypersequent) : p_hypersequent :=
  match G with
  | nil => nil
  | T :: G => (to_p_sequent T) :: (to_p_hypersequent G)
  end. 

(** ** Complexity *)
Fixpoint HR_outer_complexity_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (a, A) :: T => ((RS_outer_complexity_term A) + (HR_outer_complexity_p_seq T))%nat
  end.

Fixpoint HR_outer_complexity_p_hseq G :=
  match G with
  | nil => (0%nat, 0%nat)
  | T :: G => if HR_outer_complexity_p_seq T =? fst (HR_outer_complexity_p_hseq G) then (fst (HR_outer_complexity_p_hseq G), S (snd (HR_outer_complexity_p_hseq G)))
              else if (HR_outer_complexity_p_seq T <? fst (HR_outer_complexity_p_hseq G))%nat then (fst (HR_outer_complexity_p_hseq G) , snd (HR_outer_complexity_p_hseq G))
                   else (HR_outer_complexity_p_seq T, 1%nat)
  end.

(** ** Max variable appearing in a weight of a hypersequent *)
Fixpoint max_var_weight_p_seq (T : p_sequent) :=
  match T with
  | nil => 0%nat
  | (r, A) :: T => Nat.max (max_var_Poly r) (max_var_weight_p_seq T)
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

Fixpoint vec (l : list Poly) (A : term) :=
  match l with
  | nil => nil
  | r :: l => (r , A) :: (vec l A)
  end.

Fixpoint sum_vec (l : list Poly) :=
  match l with
  | nil => Poly_cst 0
  | r :: l => r +R (sum_vec l)
  end.

Fixpoint copy_p_seq n (T : p_sequent) :=
  match n with
  | 0 => nil
  | S n => (copy_p_seq n T) ++ T
  end.

Fixpoint seq_mul (r : Poly) (T : p_sequent) :=
  match T with
  | nil => nil
  | ((a , A) :: T) => (Poly_mul r a, A) :: (seq_mul r T)
  end.

Fixpoint mul_vec r (l : list Poly) :=
  match l with
  | nil => nil
  | r0 :: l => (Poly_mul r r0) :: (mul_vec r l)
  end.

Fixpoint vec_mul_vec l1 l2 :=
  match l1 with
  | nil => nil
  | r :: l1 => (mul_vec r l2) ++ (vec_mul_vec l1 l2)
  end.

(** ** Sum of the weights *)
Fixpoint sum_weight_var_p_seq n (T : p_sequent) :=
  match T with
  | nil => Poly_cst 0
  | ((r , RS_var n0) :: T) => if (term.V_eq n n0) then r +R (sum_weight_var_p_seq n T) else sum_weight_var_p_seq n T
  | ((r , RS_covar n0) :: T) => if (term.V_eq n n0) then ((Poly_cst (-1)) *R r) +R (sum_weight_var_p_seq n T) else sum_weight_var_p_seq n T
  | ( _ :: T) => sum_weight_var_p_seq n T
  end.
Fixpoint p_sum_weight_var n G :=
  match G with
  | nil => Poly_cst 0
  | T :: G => (sum_weight_var_p_seq n T) +R (p_sum_weight_var n G)
  end.

(** ** well defined hypersequent with regard to a valuation (i.e. all the weights of the hypersequent are strictly positive with this valuation) *)
Definition p_seq_well_defined (val : nat -> R) (T : p_sequent) :=
  Forall_inf (fun x => (0 <= eval_Poly val (fst x))) T.

Definition p_hseq_well_defined (val : nat -> R) G : Type :=
  Forall_inf (p_seq_well_defined val) G.

(** * Properties *)
(** ** vec *)
Lemma vec_inj : forall vr vs A,
    vec vr A = vec vs A ->
    vr = vs.
Proof.
  induction vr; intros [ | s vs] A Heq; inversion Heq; subst; auto.
  rewrite IHvr with vs A; auto.
Qed.

Lemma in_inf_vec_eq_term : forall vr r A B, In_inf (r, A) (vec vr B) -> prod (A = B) (In_inf r vr).
Proof.
  induction vr; intros r A B Hin; inversion Hin; subst.
  - inversion H; split; auto.
    left; reflexivity.
  - destruct IHvr with r A B; auto.
    split; auto.
    right; assumption.
Qed.

Lemma Permutation_Type_vec : forall vr vs A,
    Permutation_Type vr vs ->
    Permutation_Type (vec vr A) (vec vs A).
Proof.
  intros vr vs A Hperm; induction Hperm; simpl; Permutation_Type_solve.
Qed.

Lemma Permutation_Type_vec_decomp : forall T vr A,
    Permutation_Type T (vec vr A) ->
    { vs & prod (T = vec vs A) (Permutation_Type vr vs)}.
Proof.
  intros T vr A Hperm.
  remember (vec vr A) as D.
  revert vr A HeqD.
  induction Hperm; intros vr A HeqD.
  - split with nil; repeat split; auto.
    destruct vr; auto.
    inversion HeqD.
  - destruct vr; inversion HeqD; subst.
    specialize (IHHperm vr A) as [vs [Heq Hperm']]; auto.
    split with (p :: vs).
    repeat split.
    + rewrite Heq; reflexivity.
    + apply Permutation_Type_skip; auto.
  - destruct vr; inversion HeqD.
    destruct vr; inversion H1; subst.
    split with (p0 :: p :: vr).
    repeat split; auto.
    apply Permutation_Type_swap.
  - destruct (IHHperm2 vr A HeqD) as [vs [Heq' Hperm']].
    destruct (IHHperm1 vs A Heq') as [vs' [Heq'' Hperm'']].
    split with vs'; repeat split; auto.
    Permutation_Type_solve.
Qed.

Lemma Permutation_Type_vec_inv : forall vr vs A,
    Permutation_Type (vec vr A) (vec vs A) ->
    Permutation_Type vr vs.
Proof.
  intros vr vs A Hperm.
  remember (vec vr A); remember (vec vs A).
  revert vr vs A Heql Heql0.
  induction Hperm; intros vr vs A Heql Heql0.
  - destruct vr; destruct vs; auto; inversion Heql; inversion Heql0.
  - destruct vr; destruct vs; inversion Heql; inversion Heql0; subst.
    inversion H2.
    apply Permutation_Type_skip.
    apply IHHperm with A; auto.
  - destruct vr; destruct vs; inversion Heql; inversion Heql0; subst.
    destruct vr; destruct vs; inversion H1; inversion H3; subst.
    rewrite vec_inj with vr vs A; auto.
    apply Permutation_Type_swap.
  - subst.
    destruct (Permutation_Type_vec_decomp _ _ _ Hperm2) as [vr' [ Heq Hperm]].
    subst.
    specialize (IHHperm2 vr' vs A (eq_refl _) (eq_refl _)).
    specialize (IHHperm1 vr vr' A (eq_refl _) (eq_refl _)).
    Permutation_Type_solve.    
Qed.

Lemma seq_mul_vec_eq_vec_mul_vec : forall r vr A,
    seq_mul r (vec vr A) = vec (mul_vec r vr) A.
Proof.
  intros r vr A; induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.

Lemma vec_length : forall vr A, length (vec vr A) = length vr.
Proof.
  induction vr; intros A; try specialize (IHvr A); simpl; lia.
Qed.

Lemma vec_app : forall vr1 vr2 A, vec (vr1 ++ vr2) A = vec vr1 A ++ vec vr2 A.
Proof.
  induction vr1; intros vr2 A; simpl; try rewrite IHvr1; try reflexivity.
Qed.

Lemma sum_vec_app : forall vr1 vr2 val, eval_Poly val (sum_vec (vr1 ++ vr2)) = eval_Poly val ((sum_vec vr1) +R (sum_vec vr2)).
Proof.
  induction vr1; intros vr2 val.
  - rewrite app_nil_l; simpl; nra.
  - simpl.
    rewrite IHvr1.
    destruct a; simpl; nra.
Qed.

Lemma Permutation_Type_mul_vec : forall r vr vs,
  Permutation_Type vr vs ->
  Permutation_Type (mul_vec r vr) (mul_vec r vs).
Proof.
  intros r vr vs Hperm; induction Hperm; simpl; Permutation_Type_solve.
Qed.

Lemma mul_vec_sum_vec : forall r vr val, eval_Poly val (sum_vec (mul_vec r vr)) = eval_Poly val (r *R (sum_vec vr)).
Proof.
  intro r; induction vr; intros val.
  - simpl; nra.
  - simpl.
    rewrite IHvr.
    simpl; nra.
Qed.

Lemma sum_vec_vec_mul_vec : forall vr vs val, eval_Poly val (sum_vec (vec_mul_vec vr vs)) = eval_Poly val ((sum_vec vr) *R (sum_vec vs)).
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

Lemma vec_mul_vec_cons_r : forall vr1 vr2 r val, Permutation_Type_Poly val (vec_mul_vec vr1 (r :: vr2)) (mul_vec r vr1 ++ vec_mul_vec vr1 vr2).
Proof.
  unfold Permutation_Type_Poly.
  induction vr1; intros vr2 r val; simpl; try reflexivity.
  replace (eval_Poly val a * eval_Poly val r) with (eval_Poly val r * eval_Poly val a) by (simpl; nra).
  apply Permutation_Type_skip.
  rewrite ? map_app; rewrite app_assoc.
  etransitivity ; [ | apply Permutation_Type_app ; [ apply Permutation_Type_app_comm | reflexivity ] ].
  rewrite <- app_assoc; apply Permutation_Type_app; try reflexivity.
  rewrite <- map_app; apply IHvr1.
Qed.

Lemma vec_mul_vec_comm : forall vr1 vr2 val, Permutation_Type_Poly val (vec_mul_vec vr1 vr2) (vec_mul_vec vr2 vr1).
Proof.
  unfold Permutation_Type_Poly.
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

Lemma mul_vec_perm : forall vr vs r val, Permutation_Type_Poly val vr vs ->  Permutation_Type_Poly val (mul_vec r vr) (mul_vec r vs).
Proof.
  unfold Permutation_Type_Poly.
  intros vr vs r val Hperm.
  remember (map (eval_Poly val) vr) as lr; remember (map (eval_Poly val) vs) as ls.
  revert vr vs Heqlr Heqls; induction Hperm; intros vr vs Heqlr Heqls.
  - symmetry in Heqlr; apply map_eq_nil in Heqlr; symmetry in Heqls; apply map_eq_nil in Heqls; subst.
    reflexivity.
  - destruct vr; destruct vs; inversion Heqlr; inversion Heqls; subst.
    simpl; rewrite H2; apply Permutation_Type_skip.
    apply IHHperm; reflexivity.
  - destruct vr; [ | destruct vr]; (destruct vs; [ | destruct vs]); inversion Heqlr; inversion Heqls; subst.
    simpl; rewrite H3; rewrite H4.
    replace (map (eval_Poly val) (mul_vec r vs)) with (map (eval_Poly val) (mul_vec r vr)); [ apply Permutation_Type_swap | ].
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

Lemma vec_perm : forall vr1 vr2 A val,
    Permutation_Type_Poly val vr1 vr2 -> Permutation_Type_p_seq val (vec vr1 A) (vec vr2 A).
Proof.
  unfold Permutation_Type_Poly; unfold Permutation_Type_p_seq.
  intros vr1 vr2 A val Hperm.
  remember (map (eval_Poly val) vr1) as l1; remember (map (eval_Poly val) vr2) as l2.
  revert vr1 vr2 Heql1 Heql2; induction Hperm; intros vr1 vr2 Heql1 Heql2.
  - destruct vr1; destruct vr2; inversion Heql1; now inversion Heql2.
  - destruct vr1; destruct vr2; inversion Heql1; inversion Heql2; subst.
    simpl; rewrite H2.
    case (R_order_dec (eval_Poly val p0)); intros He;
      try apply Permutation_Type_skip;
      now apply IHHperm.
  - destruct vr1; [ | destruct vr1]; (destruct vr2; [ | destruct vr2]); inversion Heql1; inversion Heql2; simpl; subst.
    rewrite H3; rewrite H4.
    replace (eval_p_sequent val (vec vr1 A)) with (eval_p_sequent val (vec vr2 A)) ; [ case (R_order_dec (eval_Poly val p1)); case (R_order_dec (eval_Poly val p2));intros; now try apply Permutation_Type_swap | ].
    clear - H5.
    revert vr2 H5; induction vr1; intros vr2 H5; destruct vr2; inversion H5; subst; try reflexivity.
    simpl; rewrite H0; now rewrite IHvr1.
  - subst.
    apply Permutation_Type_map_inv in Hperm2 as [vr' Heq' Hperm']; subst.    
    etransitivity; [apply IHHperm1 | apply IHHperm2]; auto.
Qed.

Lemma sum_mul_vec : forall val l r, eval_Poly val (sum_vec (mul_vec r l)) = eval_Poly val (Poly_mul r (sum_vec l)).
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
    eval_Poly val (sum_vec vr) = eval_Poly val (sum_vec vs).
Proof.
  intros val vr vs Hperm; induction Hperm; simpl in *; nra.
Qed.

Lemma mul_vec_length : forall r vr,
    length (mul_vec r vr) = length vr.
Proof.
  intros r; induction vr; simpl; try rewrite IHvr; reflexivity.
Qed.

(** ** Sequent *)

Lemma In_inf_seq_mul :
  forall A r T,
    In_inf A (seq_mul r T) ->
    {' (b , B) : _ & prod (A = ((r *R b) , B)) (In_inf (b, B) T)}.
Proof.
  intros [a A] r; induction T; try destruct a0 as [b B]; intros Hin; simpl in *; inversion Hin.
  - split with (b , B); split; auto.
  - destruct (IHT X) as [[b0 B0] [Heq Hin']].
    split with (b0, B0); split; auto.
Qed.

Lemma Permutation_Type_eval_p_sequent : forall val T D,
    Permutation_Type T D ->
    Permutation_Type (eval_p_sequent val T) (eval_p_sequent val D).
Proof.
  intros val T D Hperm; induction Hperm; auto.
  - destruct x as [a A]; simpl.
    case_eq (R_order_dec (eval_Poly val a)); intros e He; try apply Permutation_Type_skip; assumption.
  - destruct x as [a A]; destruct y as [b B]; simpl.
    case_eq (R_order_dec (eval_Poly val a)); case_eq (R_order_dec (eval_Poly val b)); intros eb Heb ea Hea; try reflexivity; try apply Permutation_Type_swap.
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
    revert Heqs; case_eq (R_order_dec (eval_Poly val a)); intros e He Heqs;
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
      case_eq (R_order_dec (eval_Poly val a)); intros e He; rewrite He in Heqs; inversion Heqs.
    + destruct p as [a A]; destruct p0 as [b B]; simpl in Heqs.
      case_eq (R_order_dec (eval_Poly val a)); intros ea Hea; rewrite Hea in Heqs;
        case_eq (R_order_dec (eval_Poly val b)); intros eb Heb; rewrite Heb in Heqs;
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

Lemma seq_mul_app : forall T1 T2 r, seq_mul r (T1 ++ T2) = seq_mul r T1 ++ seq_mul r T2.
Proof.
  induction T1; intros T2 r; try reflexivity.
  destruct a as (a , A).
  simpl; rewrite IHT1.
  reflexivity.
Qed.

Lemma seq_mul_perm : forall T1 T2 r, Permutation_Type T1 T2 -> Permutation_Type (seq_mul r T1) (seq_mul r T2).
Proof.
  intros T1 T2 r Hperm; induction Hperm; try destruct x; try destruct y; simpl; Permutation_Type_solve.
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

(** ** sum_weight_p_seq_(co)var *)
(*
Lemma sum_weight_var_p_seq_lt_max_var : forall val n T1,
    (max_var_p_seq T1 < n)%nat ->
    eval_Poly val (sum_weight_var_p_seq n T1) = 0.
Proof.
  intros val n; induction T1; intros Hlt; auto.
  destruct a as [a A].
  destruct A; simpl in *; try (apply IHT1; simpl ; lia);
    replace (n =? n0) with false by (symmetry; apply Nat.eqb_neq; lia);
    apply IHT1;
    lia.
Qed.*)
    
Lemma sum_weight_var_p_seq_app : forall val n T1 T2,
    eval_Poly val (sum_weight_var_p_seq n (T1 ++ T2)) = eval_Poly val (sum_weight_var_p_seq n T1 +R sum_weight_var_p_seq n T2).
Proof.
  intros val n T1; induction T1; intros T2; simpl; try nra.
  destruct a as [a A]; simpl.
  specialize (IHT1 T2).
  destruct A; try case (term.V_eq n v); simpl in *; try nra.
Qed.

Lemma sum_weight_var_p_seq_mul : forall val n T r,
    eval_Poly val (sum_weight_var_p_seq n (seq_mul r T)) = eval_Poly val (r *R sum_weight_var_p_seq n T).
Proof.
  intros val n T r; induction T; simpl in *; try nra.
  destruct a as [a A]; simpl.
  destruct A; try case (term.V_eq n v); destruct a; destruct r; simpl in *; try nra.
Qed.

Lemma sum_weight_var_p_seq_vec_var_eq : forall val n r,
    eval_Poly val (sum_weight_var_p_seq n (vec r (RS_var n))) = eval_Poly val (sum_vec r).
Proof.
  intros val n; induction r; simpl in *; try reflexivity.
  case (term.V_eq n n); intros H; try contradiction.
  simpl; nra.
Qed.

Lemma sum_weight_var_p_seq_vec_neq : forall val n A r,
    RS_var n <> A ->
    RS_covar n <> A ->
    eval_Poly val (sum_weight_var_p_seq n (vec r A)) = 0.
Proof.
  intros val n A; induction r; intros Hneqv Hneqcv; simpl; try reflexivity.
  destruct A; try (case_eq (term.V_eq n v) ; [ intros H; exfalso; now subst | ]); auto.
Qed.

Lemma p_sum_weight_var_seq_sem :
  forall T val n,
    eval_Poly val (sum_weight_var_p_seq n T) = sum_weight_var_seq n (eval_p_sequent val T).
Proof.
  induction T; intros val n; try reflexivity.
  specialize (IHT val n).
  destruct a as [a A].
  simpl; destruct A; case (R_order_dec (eval_Poly val a)); intros H;
    simpl; try case (term.V_eq n v); simpl; try nra.
Qed.

Lemma p_sum_weight_var_sem :
  forall G val n,
    eval_Poly val (p_sum_weight_var n G) = sum_weight_var n (map (eval_p_sequent val) G).
Proof.
  induction G; intros val n; try reflexivity.
  simpl; rewrite p_sum_weight_var_seq_sem; rewrite IHG; reflexivity.
Qed.

Lemma p_seq_non_atomic_perm :
  forall T,
    (p_seq_is_atomic T -> False) ->
    {' (A , D) : _ &
                 Permutation_Type T (A :: D) &
                 ~ (is_atom (snd A)) }.
Proof.
  induction T; intros Hnat; [exfalso; apply Hnat; apply Forall_inf_nil | ].
  destruct a as [a A].
  destruct A.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (A, ((a, RS_var v) :: D)); auto.
    Permutation_Type_solve.
  - destruct IHT as [[A D] Hperm H].
    { intros Hat; apply Hnat; apply Forall_inf_cons; auto.
      apply I. }
    split with (A, ((a, RS_covar v) :: D)); auto.
    Permutation_Type_solve.
  - split with ((a, RS_zero), T); auto.
  - split with ((a, A1 +S A2), T); auto.
  - split with ((a, r *S A), T); auto.
  - split with ((a, A1 \/S A2), T); auto.
  - split with ((a, A1 /\S A2), T); auto.
Qed.

Lemma p_seq_atomic_seq_atomic : forall val T,
    p_seq_is_atomic T ->
    seq_is_atomic (eval_p_sequent val T).
Proof.
  intros val; induction T; intros Hat; try apply Forall_inf_nil.
  destruct a as [a A].
  simpl in Hat |- *.
  inversion Hat; subst.
  case_eq (R_order_dec (eval_Poly val a)); intros; simpl; try apply Forall_inf_cons; try apply IHT; auto.
  destruct A; inversion X; auto.
Qed.

Lemma p_hseq_atomic_hseq_atomic : forall val G,
    p_hseq_is_atomic G ->
    hseq_is_atomic (map (eval_p_sequent val) G).
Proof.
  intros val; induction G; intros Hat; try apply Forall_inf_nil.
  simpl; inversion Hat; subst; apply Forall_inf_cons; [ apply p_seq_atomic_seq_atomic | apply IHG]; auto.
Qed.

(** Complexity related theorem *)

Lemma complexity_p_hseq_cons : forall T G,
    fst (HR_outer_complexity_p_hseq (T :: G)) = max (HR_outer_complexity_p_seq T) (fst (HR_outer_complexity_p_hseq G)).
Proof.
  intros T G.
  simpl.
  case_eq (HR_outer_complexity_p_seq T =? fst (HR_outer_complexity_p_hseq G)); intros H; (apply Nat.eqb_eq in H + apply Nat.eqb_neq in H);
    case_eq (HR_outer_complexity_p_seq T <? fst (HR_outer_complexity_p_hseq G))%nat; intros H2; (apply Nat.ltb_lt in H2 + apply Nat.ltb_nlt in H2); simpl in *; lia.
Qed.  

Lemma complexity_p_hseq_app : forall G1 G2,
    fst (HR_outer_complexity_p_hseq (G1 ++ G2)) = max (fst (HR_outer_complexity_p_hseq G1)) (fst (HR_outer_complexity_p_hseq G2)).
Proof.
  induction G1; intros G2; try specialize (IHG1 G2); simpl; try lia.
  rewrite IHG1.
  case_eq (HR_outer_complexity_p_seq a =? Init.Nat.max (fst (HR_outer_complexity_p_hseq G1)) (fst (HR_outer_complexity_p_hseq G2))); intros H1; (apply Nat.eqb_eq in H1 + apply Nat.eqb_neq in H1);
    case_eq ((HR_outer_complexity_p_seq a <? Init.Nat.max (fst (HR_outer_complexity_p_hseq G1)) (fst (HR_outer_complexity_p_hseq G2)))%nat); intros H2; (apply Nat.ltb_lt in H2 + apply Nat.ltb_nlt in H2);
      case_eq (HR_outer_complexity_p_seq a =? fst (HR_outer_complexity_p_hseq G1)); intros H3; (apply Nat.eqb_eq in H3 + apply Nat.eqb_neq in H3);
        case_eq ((HR_outer_complexity_p_seq a <? fst (HR_outer_complexity_p_hseq G1))%nat); intros H4; (apply Nat.ltb_lt in H4 + apply Nat.ltb_nlt in H4); simpl; lia.
Qed.

Lemma outer_complexity_p_seq_perm : forall T1 T2,
    Permutation_Type T1 T2 ->
    HR_outer_complexity_p_seq T1 = HR_outer_complexity_p_seq T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; try destruct x; try destruct y; simpl; lia.
Qed.

Lemma outer_complexity_p_hseq_perm : forall G1 G2,
    Permutation_Type G1 G2 ->
    HR_outer_complexity_p_hseq G1 = HR_outer_complexity_p_hseq G2.
Proof.
  intros G1 G2 Hperm; induction Hperm.
  - reflexivity.
  - simpl.
    rewrite IHHperm.
    case (HR_outer_complexity_p_seq x =? fst (HR_outer_complexity_p_hseq l'));
      case (HR_outer_complexity_p_seq x <? fst (HR_outer_complexity_p_hseq l'))%nat; reflexivity.
  - simpl.
    case_eq (HR_outer_complexity_p_seq x =? fst (HR_outer_complexity_p_hseq l)); intros H1;
      case_eq (HR_outer_complexity_p_seq y =? fst (HR_outer_complexity_p_hseq l)); intros H2;
        case_eq (HR_outer_complexity_p_seq x <? fst (HR_outer_complexity_p_hseq l))%nat; intros H3;
          case_eq (HR_outer_complexity_p_seq y <? fst (HR_outer_complexity_p_hseq l))%nat; intros H4;
            case_eq (HR_outer_complexity_p_seq x =? HR_outer_complexity_p_seq y); intros H5;
              case_eq (HR_outer_complexity_p_seq x <? HR_outer_complexity_p_seq y)%nat; intros H6;
                case_eq (HR_outer_complexity_p_seq y <? HR_outer_complexity_p_seq x)%nat; intros H7;
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
  - transitivity (HR_outer_complexity_p_hseq l'); assumption.
Qed.

Lemma outer_complexity_p_hseq_perm_fst : forall G,
    G <> nil ->
    {' (T, H) : _ &
                Permutation_Type G (T :: H) &
                HR_outer_complexity_p_seq T = fst (HR_outer_complexity_p_hseq G) }.
  induction G; intros H; [ exfalso; apply H; reflexivity | clear H ].
  simpl.
  case_eq (HR_outer_complexity_p_seq a =? fst (HR_outer_complexity_p_hseq G)); intros H1.
  - split with (a, G); try reflexivity.
    apply Nat.eqb_eq in H1; rewrite H1; reflexivity.
  - case_eq (HR_outer_complexity_p_seq a <? fst (HR_outer_complexity_p_hseq G))%nat; intros H2.
    + destruct G; [ inversion H2 | ].
      destruct IHG as [[T H] Hperm Heq].
      { intros H; inversion H. }
      split with (T, (a :: H)).
      * transitivity (a :: T :: H); Permutation_Type_solve.
      * rewrite (outer_complexity_p_hseq_perm _ _ Hperm).
        rewrite (outer_complexity_p_hseq_perm _ _ Hperm) in Heq.
        rewrite Heq; reflexivity.
    + split with (a, G); reflexivity.
Qed.

Lemma outer_complexity_p_hseq_perm_fst_p_seq : forall T1 T2 G,
    Permutation_Type T1 T2 ->
    HR_outer_complexity_p_hseq (T1 :: G) = HR_outer_complexity_p_hseq (T2 :: G).
Proof.
  intros T1 T2 G Hperm.
  simpl.
  rewrite (outer_complexity_p_seq_perm _ _ Hperm).
  reflexivity.
Qed.

Lemma complexity_p_seq_app : forall T1 T2,
    HR_outer_complexity_p_seq (T1 ++ T2) = (HR_outer_complexity_p_seq T1 + HR_outer_complexity_p_seq T2)%nat.
Proof.
  induction T1; intros T2; simpl; try rewrite IHT1; try destruct a; lia.
Qed.

Lemma complexity_p_seq_vec : forall r A,
    HR_outer_complexity_p_seq (vec r A) = (length r * RS_outer_complexity_term A)%nat.
Proof.
  induction r; intros A; simpl; try rewrite IHr; lia.
Qed.

Lemma p_seq_is_atomic_complexity_0 :
  forall T,
    p_seq_is_atomic T ->
    HR_outer_complexity_p_seq T = 0%nat.
Proof.
  induction T; intros Hat;
    inversion Hat; simpl; try destruct a; try rewrite IHT; try rewrite is_atom_outer_complexity_0;
      auto.
Qed.

Lemma p_seq_is_atomic_complexity_0_inv :
  forall T,
    HR_outer_complexity_p_seq T = 0%nat ->
    p_seq_is_atomic T.
Proof.
  induction T; intros Heq; [ apply Forall_inf_nil |] .
  destruct a as [a A]; simpl in *.
  apply Forall_inf_cons ; [ apply is_atom_outer_complexity_0_inv  | apply IHT]; lia.
Qed.

Lemma p_seq_is_atomic_app : forall T1 T2,
    p_seq_is_atomic T1 ->
    p_seq_is_atomic T2 ->
    p_seq_is_atomic (T1 ++ T2).
Proof.
  induction T1; intros T2 Hat1 Hat2; inversion Hat1; subst; auto.
  simpl; apply Forall_inf_cons; auto.
  apply IHT1; auto.
Qed.

Lemma p_seq_is_atomic_seq_mul : forall r T,
    p_seq_is_atomic T ->
    p_seq_is_atomic (seq_mul r T).
Proof.
  intros r; induction T; intros Hat; inversion Hat; subst; auto.
  destruct a as [a A]; simpl; apply Forall_inf_cons; auto.
  apply IHT.
  apply X0.
Qed.

Lemma p_hseq_is_atomic_flat_map :
  forall k G l,
    p_hseq_is_atomic G ->
    p_hseq_is_atomic (flat_map (fun i : nat => seq_mul (Poly_var (k + i)) (nth i G nil)) l :: nil).
Proof.
  intros k G l Hat; revert k; induction l; intros k; apply Forall_inf_cons; try apply Forall_inf_nil.
  simpl.
  apply p_seq_is_atomic_app.
  - apply p_seq_is_atomic_seq_mul.
    case_eq (a <? length G)%nat; intros H; (apply Nat.ltb_lt in H + apply Nat.ltb_nlt in H); [ | rewrite nth_overflow; try lia; apply Forall_inf_nil].
    apply Forall_inf_forall with G; auto.
    apply nth_In_inf; assumption.
  - specialize (IHl k).
    inversion IHl; assumption.
Qed.

Lemma p_seq_is_atomic_perm :
  forall T1 T2,
    Permutation_Type T1 T2 ->
    p_seq_is_atomic T1 ->
    p_seq_is_atomic T2.
Proof.
  intros T1 T2 Hperm; induction Hperm; intros Hat1; try destruct x; try destruct y; repeat apply Forall_inf_cons; try inversion Hat1; try inversion X0; subst; auto.
  - apply IHHperm; apply Forall_inf_nil.
  - apply IHHperm.
    apply Forall_inf_cons; assumption.
Qed.

Lemma p_hseq_is_atomic_perm :
  forall G1 G2,
    Permutation_Type G1 G2 ->
    p_hseq_is_atomic G1 ->
    p_hseq_is_atomic G2.
Proof.
  intros G1 G2 Hperm; induction Hperm; intros Hat1; repeat apply Forall_inf_cons; try inversion Hat1; try inversion X0; subst; auto.
  - apply IHHperm; apply Forall_inf_nil.
  - apply IHHperm.
    apply Forall_inf_cons; assumption.
Qed.

Lemma p_seq_is_atomic_eval : forall T val,
    p_seq_is_atomic T ->
    seq_is_atomic (eval_p_sequent val T).
Proof.
  induction T; intros val Hat; inversion Hat; subst.
  - apply Forall_inf_nil.
  - destruct a as [a A].
    simpl.
    case_eq (R_order_dec (eval_Poly val a)); intros; simpl; try apply Forall_inf_cons; try (apply IHT; assumption); try assumption.
    destruct A; inversion X; apply I.
Qed.

Lemma p_hseq_is_atomic_eval : forall G val,
    p_hseq_is_atomic G ->
    hseq_is_atomic (map (eval_p_sequent val) G).
Proof.
  induction G; intros val Hat; [ apply Forall_inf_nil | ]; simpl.
  inversion Hat; subst; specialize (IHG val X0).
  apply Forall_inf_cons; try assumption.
  apply p_seq_is_atomic_eval; assumption.
Qed.

Lemma p_hseq_is_atomic_outer_complexity_0 :
  forall G,
    p_hseq_is_atomic G ->
    fst (HR_outer_complexity_p_hseq G) = 0%nat.
Proof.
  induction G; intros Hat; [ reflexivity | ].
  inversion Hat; subst; specialize (IHG X0).
  simpl.
  rewrite p_seq_is_atomic_complexity_0 ; [ | apply X].
  rewrite IHG; reflexivity.
Qed.

Lemma p_hseq_is_atomic_outer_complexity_0_inv :
  forall G,
    fst (HR_outer_complexity_p_hseq G) = 0%nat ->
    p_hseq_is_atomic G.
Proof.
  induction G; intros Heq; [ apply Forall_inf_nil | ].
  simpl in *.
  case_eq (HR_outer_complexity_p_seq a =? fst (HR_outer_complexity_p_hseq G)); intros H; rewrite H in Heq; simpl in Heq ; [ apply Nat.eqb_eq in H | apply Nat.eqb_neq in H ].
  { apply Forall_inf_cons; [ apply p_seq_is_atomic_complexity_0_inv | apply IHG ]; lia. }
  exfalso.
  case_eq (HR_outer_complexity_p_seq a <? fst (HR_outer_complexity_p_hseq G))%nat; intros H2; rewrite H2 in Heq; [apply Nat.ltb_lt in H2 | apply Nat.ltb_nlt in H2]; simpl in *; lia.
Qed.

Lemma HR_outer_complexity_perm_fst_seq : forall G T D,
    Permutation_Type T D ->
    HR_outer_complexity_p_hseq (T :: G) = HR_outer_complexity_p_hseq (D :: G).
Proof.
  intros G T D Hperm.
  simpl.
  rewrite outer_complexity_p_seq_perm with _ D; auto.
Qed.

Lemma outer_complexity_seq_mul : forall T r,
    HR_outer_complexity_p_seq (seq_mul r T) = HR_outer_complexity_p_seq T.
Proof.
  induction T; intros r; simpl; try specialize (IHT r); try destruct a as [a A];simpl; try lia.
Qed.

Lemma outer_complexity_seq_mul_nth :
  forall G v k,
    HR_outer_complexity_p_seq (flat_map (fun i : nat => seq_mul (Poly_var (k + i)) (nth i G nil)) v) = HR_outer_complexity_p_seq (flat_map (fun i : nat => nth i G nil) v).
Proof.
  intros G; induction v; intros k; auto.
  simpl in *.
  rewrite ? complexity_p_seq_app; rewrite IHv.
  rewrite outer_complexity_seq_mul.
  reflexivity.
Qed.

Lemma hrr_Z_decrease_complexity : forall G T r,
    r <> nil ->
    HR_outer_complexity_p_seq (vec r RS_zero ++ T) = fst (HR_outer_complexity_p_hseq ((vec r RS_zero ++ T) :: G)) ->
    HR_outer_complexity_p_hseq (T :: G) <2 HR_outer_complexity_p_hseq ((vec r RS_zero ++ T) :: G).
Proof.
  intros G T r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_p_seq T =? fst (HR_outer_complexity_p_hseq G)); intros H1; case_eq (HR_outer_complexity_p_seq (vec r RS_zero ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H2.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H2.
    rewrite complexity_p_seq_app in H2.
    lia.
  - case_eq (HR_outer_complexity_p_seq (vec r RS_zero ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_p_seq T <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite complexity_p_seq_app in H2; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_p_seq T <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_p_seq (vec r RS_zero ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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
    HR_outer_complexity_p_seq (vec r (A +S B) ++ T) = fst (HR_outer_complexity_p_hseq ((vec r (A +S B) ++ T) :: G)) ->
    HR_outer_complexity_p_hseq ((vec r A ++ vec r B ++ T) :: G) <2 HR_outer_complexity_p_hseq ((vec r (A +S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_p_seq (vec r A ++ vec r B ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H1; case_eq (HR_outer_complexity_p_seq (vec r (A +S B) ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H2; rewrite 2 complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_outer_complexity_p_seq (vec r (A +S B) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_p_seq (vec r A ++ vec r B ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_p_seq (vec r A ++ vec r B ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_p_seq (vec r (A +S B) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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
    HR_outer_complexity_p_seq (vec r (r0 *S A) ++ T) = fst (HR_outer_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G)) ->
    HR_outer_complexity_p_hseq ((vec (mul_vec (Poly_cst (projT1 r0)) r) A ++ T) :: G) <2 HR_outer_complexity_p_hseq ((vec r (r0 *S A) ++ T) :: G).
Proof.
  intros G T A r0 r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_p_seq (vec (mul_vec (Poly_cst (projT1 r0)) r) A ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H1; case_eq (HR_outer_complexity_p_seq (vec r (r0 *S A) ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    rewrite mul_vec_length in H1.
    lia.
  - case_eq (HR_outer_complexity_p_seq (vec r (r0 *S A) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
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
  - case_eq (HR_outer_complexity_p_seq (vec (mul_vec (Poly_cst (projT1 r0)) r) A ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      rewrite mul_vec_length in *; lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_p_seq (vec (mul_vec (Poly_cst (projT1 r0)) r) A ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_p_seq (vec r (r0 *S A) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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
    HR_outer_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HR_outer_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HR_outer_complexity_p_hseq ((vec r A ++ T) :: G) <2 HR_outer_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_p_seq (vec r A ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H1; case_eq (HR_outer_complexity_p_seq (vec r (A /\S B) ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H2; rewrite ? complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_outer_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_p_seq (vec r A ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_p_seq (vec r A ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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
    HR_outer_complexity_p_seq (vec r (A /\S B) ++ T) = fst (HR_outer_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G)) ->
    HR_outer_complexity_p_hseq ((vec r B ++ T) :: G) <2 HR_outer_complexity_p_hseq ((vec r (A /\S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_p_seq (vec r B ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H1; case_eq (HR_outer_complexity_p_seq (vec r (A /\S B) ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_outer_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + apply fst_lt2.
      apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
      lia.
  - case_eq (HR_outer_complexity_p_seq (vec r B ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + apply snd_lt2.
      lia.
    + exfalso.
      apply Nat.eqb_eq in H2; apply Nat.ltb_nlt in H3.
      rewrite ? complexity_p_seq_app in *; destruct r ; [ apply Hnnil; reflexivity | ].
      simpl in H2; rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
  - simpl in Heq; rewrite H2 in Heq.
    case_eq (HR_outer_complexity_p_seq (vec r B ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3;
      case_eq (HR_outer_complexity_p_seq (vec r (A /\S B) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H4; rewrite H4 in Heq; simpl in Heq.
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
    HR_outer_complexity_p_seq (vec r (A \/S B) ++ T) = fst (HR_outer_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G)) ->
    HR_outer_complexity_p_hseq ((vec r B ++ T) :: (vec r A ++ T) :: G) <2 HR_outer_complexity_p_hseq ((vec r (A \/S B) ++ T) :: G).
Proof.
  intros G T A B r Hnnil Heq.
  simpl.
  case_eq (HR_outer_complexity_p_seq (vec r A ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H1; case_eq (HR_outer_complexity_p_seq (vec r (A \/S B) ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H2; rewrite complexity_p_seq_app in H1.
  - exfalso.
    destruct r; [ apply Hnnil; reflexivity | ].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2.
    simpl in H1, H2.
    rewrite complexity_p_seq_app in H2.
    rewrite ? complexity_p_seq_vec in *.
    simpl in H2.
    lia.
  - case_eq (HR_outer_complexity_p_seq (vec r (A \/S B) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H3.
    + exfalso.
      apply Nat.eqb_eq in H1; apply Nat.eqb_neq in H2; apply Nat.ltb_lt in H3.
      destruct r; [ apply Hnnil; reflexivity | ].
      simpl; rewrite complexity_p_seq_app in H2; rewrite complexity_p_seq_app in H3.
      rewrite ? complexity_p_seq_vec in *; simpl in H1,H2,H3.
      lia.
    + simpl.
      case_eq (HR_outer_complexity_p_seq (vec r B ++ T) =? fst (HR_outer_complexity_p_hseq G)); intros H4.
      * apply fst_lt2.
        apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
        lia.
      * case_eq (HR_outer_complexity_p_seq (vec r B ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H5.
        -- apply fst_lt2.
           apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3.
           lia.
        -- apply fst_lt2.
           rewrite ? complexity_p_seq_app; rewrite ? complexity_p_seq_vec; destruct r; [ exfalso; apply Hnnil; reflexivity | ]; simpl; lia.        
  - replace (HR_outer_complexity_p_seq (vec r A ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_neq in H1; apply Nat.eqb_eq in H2.
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    simpl.
    replace (HR_outer_complexity_p_seq (vec r B ++ T) =? fst (HR_outer_complexity_p_hseq G)) with false.
    2:{ symmetry.
        apply Nat.eqb_neq; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    replace (HR_outer_complexity_p_seq (vec r B ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat with true.
    2:{ symmetry.
        apply Nat.ltb_lt; apply Nat.eqb_eq in H2.
        destruct r; [ exfalso; apply Hnnil; reflexivity | ].
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *; simpl in *; lia. }
    apply snd_lt2; lia.
  - simpl in Heq.
    rewrite H2 in Heq.
    assert ((HR_outer_complexity_p_seq (vec r (A \/S B) ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat = false) as H3.
    { apply Nat.ltb_nlt; apply Nat.eqb_neq in H2.
      intros H; apply Nat.ltb_lt in H.
      rewrite H in Heq.
      simpl in Heq.
      apply H2; apply Heq. }
    rewrite H3; clear Heq.
    case_eq (HR_outer_complexity_p_seq (vec r A ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat; intros H4; simpl.
    + case (HR_outer_complexity_p_seq (vec r B ++ T) =? fst (HR_outer_complexity_p_hseq G));
        [ | case (HR_outer_complexity_p_seq (vec r B ++ T) <? fst (HR_outer_complexity_p_hseq G))%nat];
        apply fst_lt2; apply Nat.eqb_neq in H2; apply Nat.ltb_nlt in H3; apply Nat.ltb_lt in H4;
          rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *;
            (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
    + case (HR_outer_complexity_p_seq (vec r B ++ T) =? HR_outer_complexity_p_seq (vec r A ++ T));
        [ | case (HR_outer_complexity_p_seq (vec r B ++ T) <? HR_outer_complexity_p_seq (vec r A ++ T))%nat];
      apply fst_lt2;
        rewrite ? complexity_p_seq_app in *; rewrite ? complexity_p_seq_vec in *;
          (destruct r; [ exfalso; apply Hnnil; reflexivity | ]); simpl in *; lia.
Qed.

(** ** max_var *)

Lemma max_var_weight_p_seq_app:
  forall T1 T2,
    max_var_weight_p_seq (T1 ++ T2) = Nat.max
                                        (max_var_weight_p_seq T1)
                                        (max_var_weight_p_seq T2).
Proof.
  induction T1; intros T2; try specialize (IHT1 T2); try destruct a; simpl in *; try lia.
Qed.

Lemma max_var_Poly_In_inf_p_seq :
  forall a A T,
    In_inf (a, A) T ->
    (max_var_Poly a <= max_var_weight_p_seq T)%nat.
Proof.
  intros a A; induction T; intros Hin; try destruct a0 as [b B]; simpl in *; inversion Hin; try (inversion H; subst); try specialize (IHT X); lia.
Qed.

Lemma max_var_weight_p_seq_In_inf_p_hseq :
  forall T G,
    In_inf T G ->
    (max_var_weight_p_seq T <= max_var_weight_p_hseq G)%nat.
Proof.
  intros T; induction G; intros Hin; simpl in *; inversion Hin; subst; try specialize (IHG X); lia.
Qed.

Lemma max_var_weight_p_seq_concat :
  forall L k,
    L <> nil ->
    Forall_inf (fun x => max_var_weight_p_seq x < k)%nat L ->
    (max_var_weight_p_seq (concat L) < k)%nat.
Proof.
  induction L; intros k Hnnil Hall; inversion Hall; subst; simpl in *; [exfalso; apply Hnnil; reflexivity | ].
  rewrite max_var_weight_p_seq_app.
  destruct L; try (simpl; lia).
  apply Nat.max_lub_lt; auto.
  apply IHL; auto.
  intros H'; inversion H'.
Qed.

Lemma max_var_weight_p_seq_seq_mul :
  forall r T,
    T <> nil ->
    max_var_weight_p_seq (seq_mul r T) = Nat.max (max_var_Poly r) (max_var_weight_p_seq T).
Proof.
  intros r; induction T; intros Hnnil; [exfalso; apply Hnnil; reflexivity | ]; destruct a as [a A]; simpl.
  destruct T; [simpl; lia | ].
  assert (p :: T <> nil).
  { intros H; inversion H. }
  specialize (IHT H).
  lia.
Qed.

(** ** well defined *)
Lemma p_seq_well_defined_perm : forall val T D,
    Permutation_Type T D ->
    p_seq_well_defined val T ->
    p_seq_well_defined val D.
Proof.
  intros val T D Hperm Hall.
  apply (Forall_inf_Permutation_Type _ _ _ _ Hperm Hall).
Qed.

Lemma p_hseq_well_defined_perm : forall val G H,
    Permutation_Type G H ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined val H.
Proof.
  intros val G H Hperm Hall.
  apply (Forall_inf_Permutation_Type _ _ _ _ Hperm Hall).
Qed.

Lemma p_seq_well_defined_seq_mul : forall val T r,
    0 <= eval_Poly val r ->
    p_seq_well_defined val T ->
    p_seq_well_defined val (seq_mul r T).
Proof.
  intros val; induction T; intros r Hr Hwd; auto.
  inversion Hwd; subst.
  destruct a as [a A].
  apply Forall_inf_cons; [ | apply (IHT r Hr); apply X ].
  simpl in *; nra.
Qed.

Lemma well_defined_concat :forall val G,
    Forall_inf (p_seq_well_defined val) G ->
    p_seq_well_defined val (concat G).
Proof.
  intros val; induction G; intros Hall; inversion Hall as [ | x1 x2 Hwd Hall']; subst.
  - simpl.
    apply Forall_inf_nil.
  - simpl.
    apply Forall_inf_app; auto.
    apply IHG.
    apply Hall'.
Qed.

Lemma p_seq_well_defined_upd_val :
  forall val T x r,
    (max_var_weight_p_seq T < x)%nat ->
    p_seq_well_defined val T ->
    p_seq_well_defined (upd_val val x r) T.
Proof.
  intros val T x r; induction T; intros Hlt Hwd; [ apply Forall_inf_nil | ].
  destruct a as [a A].
  inversion Hwd; subst.
  simpl in *; apply Forall_inf_cons; [ | apply IHT; auto; lia].
  simpl.
  rewrite upd_val_term_lt; auto.
  lia.
Qed.

Lemma p_hseq_well_defined_upd_val:
  forall val G x r,
    (max_var_weight_p_hseq G < x)%nat ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined (upd_val val x r) G.
Proof.
  intros val G x r; induction G; intros Hlt Hwd; [ apply Forall_inf_nil | ].
  inversion Hwd; subst.
  simpl in *; apply Forall_inf_cons; [ | apply IHG; auto; lia].
  apply p_seq_well_defined_upd_val; auto.
  lia.
Qed.

Lemma p_seq_well_defined_upd_val_vec:
  forall val T vx vr,
    Forall_inf (fun x => (max_var_weight_p_seq T < x)%nat) vx ->
    p_seq_well_defined val T ->
    p_seq_well_defined (upd_val_vec val vx vr) T.
Proof.
  intros val T vx; revert val; induction vx; intros val vr Hall Hwd; auto.
  destruct vr; simpl; inversion Hall; subst; auto.
  apply IHvx; auto.
  apply p_seq_well_defined_upd_val; auto.
Qed.

Lemma p_hseq_well_defined_upd_val_vec :
  forall val G vx vr,
    Forall_inf (fun x => max_var_weight_p_hseq G < x)%nat vx ->
    p_hseq_well_defined val G ->
    p_hseq_well_defined (upd_val_vec val vx vr) G.
Proof.
  intros val G vx; revert val; induction vx; intros val vr Hlt Hwd; auto.
  destruct vr; auto.
  simpl.
  inversion Hlt; subst.
  apply IHvx; auto.
  apply p_hseq_well_defined_upd_val; auto.
Qed.

Lemma p_seq_well_defined_lim : forall T (val_n : nat -> val_UniformSpace) val_l,
    is_lim_seq val_n val_l ->
    (forall n, p_seq_well_defined (val_n n) T) ->
    p_seq_well_defined val_l T.
Proof.
  induction T; intros val_n val_l Hlim Hwd_n; [ apply Forall_inf_nil | ].
  apply Forall_inf_cons ;[ | apply IHT with val_n; try assumption ].
  - apply is_lim_seq_lb with (fun n => eval_Poly (val_n n) (fst a)).
    + apply Poly_lim; try assumption.
    + intros n.
      specialize (Hwd_n n).
      inversion Hwd_n; subst.
      apply H0.
    + intro n.
      specialize (Hwd_n n).
      inversion Hwd_n; subst; assumption.
Qed.

Lemma p_hseq_well_defined_lim : forall G (val_n : nat -> val_UniformSpace) val_l,
    is_lim_seq val_n val_l ->
    (forall n, p_hseq_well_defined (val_n n) G) ->
    p_hseq_well_defined val_l G.
Proof.
  induction G; intros val_n val_l Hlim Hwd_n; [ apply Forall_inf_nil | ].
  apply Forall_inf_cons ;[ | apply IHG with val_n; try assumption ].
  - apply p_seq_well_defined_lim with val_n; try assumption.
    intros n.
    specialize (Hwd_n n); inversion Hwd_n; subst; assumption.
  - intros n.
    specialize (Hwd_n n); inversion Hwd_n; subst; assumption.
Qed.

(** ** to_p_hypersequent and eval_p_sequent *)

Lemma eval_p_sequent_cons : forall val r H A T,
    (existT _ (eval_Poly val r) H, A) :: eval_p_sequent val T = eval_p_sequent val ((r, A) :: T).
Proof.
  intros val r H A T.
  simpl in *.
  case_eq (R_order_dec (eval_Poly val r)); intros e He;
    [ | exfalso; clear - H e; apply R_blt_lt in H; apply R_blt_lt in e; lra
      | exfalso; clear - H e; apply R_blt_lt in H; lra].
  replace H with e by (apply Eqdep_dec.UIP_dec; apply Bool.bool_dec).
  reflexivity.
Qed.

Lemma to_p_sequent_well_defined : forall val T,
    p_seq_well_defined val (to_p_sequent T).
Proof.
  intros val; induction T; [ apply Forall_inf_nil | ].
  destruct a as [[a Ha] A]; simpl.
  apply Forall_inf_cons; try assumption.
  apply R_blt_lt in Ha.
  simpl; lra.
Qed.

Lemma to_p_hypersequent_well_defined : forall val G,
    p_hseq_well_defined val (to_p_hypersequent G).
Proof.
  intros val; induction G; [ apply Forall_inf_nil | ].
  apply Forall_inf_cons; [ apply to_p_sequent_well_defined | assumption ].
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
  replace e with Ha by (apply Eqdep_dec.UIP_dec; apply Bool.bool_dec).
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

Lemma eval_p_sequent_upd_val_lt_max_var : forall val T x r,
    (max_var_weight_p_seq T < x)%nat ->
    eval_p_sequent (upd_val val x r) T = eval_p_sequent val T.
Proof.
  intros val; induction T; intros x r Hlt; simpl in *; auto.
  destruct a as [a A].
  rewrite upd_val_term_lt; try lia.
  rewrite IHT; try lia.
  reflexivity.
Qed.

Lemma eval_p_sequent_upd_val_vec_lt_max_var : forall val T vx vr,
    Forall_inf (fun x => (max_var_weight_p_seq T < x)%nat) vx ->
    eval_p_sequent (upd_val_vec val vx vr) T = eval_p_sequent val T.
Proof.
  intros val T vx; revert val; induction vx; intros val vr Hall; auto.
  inversion Hall; subst.
  destruct vr; auto.
  simpl; rewrite IHvx; auto.
  rewrite eval_p_sequent_upd_val_lt_max_var; auto.
Qed.

Lemma eval_p_hseq_upd_val_lt_max_var : forall val G x r,
    (max_var_weight_p_hseq G < x)%nat ->
    map (eval_p_sequent (upd_val val x r)) G = map (eval_p_sequent val) G.
Proof.
  intros val; induction G; intros x r Hlt; simpl in *; auto.
  simpl; rewrite eval_p_sequent_upd_val_lt_max_var; try lia.
  rewrite IHG; try lia.
  reflexivity.
Qed.

Lemma eval_p_hseq_upd_val_vec_lt_max_var : forall val G vx vr,
    Forall_inf (fun x => (max_var_weight_p_hseq G < x)%nat) vx ->
    map (eval_p_sequent (upd_val_vec val vx vr)) G = map (eval_p_sequent val) G.
Proof.
  intros val G vx; revert val; induction vx; intros val vr Hall; auto.
  inversion Hall; subst.
  destruct vr; auto.
  simpl; rewrite IHvx; auto.
  rewrite eval_p_hseq_upd_val_lt_max_var; auto.
Qed.
   
Lemma eval_p_sequent_app :
  forall val T1 T2,
    eval_p_sequent val (T1 ++ T2) = eval_p_sequent val T1 ++ eval_p_sequent val T2.
Proof.
  intros val; induction T1; intros T2; simpl; try destruct a as [a A];
    try case_eq (R_order_dec (eval_Poly val a)); intros; try rewrite IHT1; try rewrite app_assoc; reflexivity.
Qed.

Lemma concat_eval_p_sequent : forall G val,
    concat (map (eval_p_sequent val) G)  = eval_p_sequent val (concat G).
Proof.
  induction G; intros val; try reflexivity.
  simpl.
  rewrite eval_p_sequent_app.
  f_equal; apply IHG.
Qed.

Lemma eval_p_sequent_upd_val_lt :
  forall T r val i,
    (max_var_weight_p_seq T < i)%nat ->
    eval_p_sequent (upd_val val i r) T = eval_p_sequent val T.
Proof.
  intros T; intros r val i Hlt.
  change (upd_val val i r) with (upd_val_vec val (seq i (length (r :: nil))) (r :: nil)).
  apply eval_p_sequent_upd_val_vec_lt_max_var.
  simpl.
  apply Forall_inf_cons; [ | apply Forall_inf_nil].
  apply Hlt.
Qed.

Lemma eval_p_hseq_upd_val_lt :
  forall G r val i,
    (max_var_weight_p_hseq G < i)%nat ->
    map (eval_p_sequent (upd_val val i r)) G = map (eval_p_sequent val) G.
Proof.
  intros G; intros r val i Hlti.
  change (upd_val val i r) with (upd_val_vec val (seq i (length (r :: nil))) (r :: nil)).
  apply eval_p_hseq_upd_val_vec_lt_max_var.
  simpl.
  apply Forall_inf_cons; [ | apply Forall_inf_nil].
  apply Hlti.
Qed.

Lemma eval_p_sequent_seq_mul_0 :
  forall T r val,
    eval_Poly val r = 0 ->
    eval_p_sequent val (seq_mul r T) = nil.
Proof.
  induction T; intros r val Heq; try reflexivity.
  specialize (IHT r val Heq).
  destruct a as [a A].
  simpl.
  case (R_order_dec (eval_Poly val r * eval_Poly val a)); intros e;
    try (exfalso; clear - e Heq; apply R_blt_lt in e; nra).
  apply IHT.
Qed.

Lemma eval_p_sequent_seq_mul_pos :
  forall T r (rp : Rpos) val,
    eval_Poly val r = projT1 rp ->
    eval_p_sequent val (seq_mul r T) = hseq.seq_mul rp (eval_p_sequent val T).
Proof.
  induction T; intros r rp val Heq; try reflexivity.
  destruct a as [a A].
  specialize (IHT r rp val Heq).
  simpl; rewrite IHT.
  case (R_order_dec (eval_Poly val r * eval_Poly val a)); intros Hra;
    case (R_order_dec (eval_Poly val a)); intros Ha; simpl;
      try (exfalso; clear - r rp Hra Ha Heq; try apply R_blt_lt in Hra; try apply R_blt_lt in Ha; destruct rp as [rp Hrp]; simpl in Heq; apply R_blt_lt in Hrp;  nra);
      do 2 f_equal;
      apply Rpos_eq; destruct rp; simpl in *; nra.
Qed.

Lemma sum_weight_var_eval_p_sequent_seq_mul :
  forall T r val n,
    sum_weight_var_seq n (eval_p_sequent val (seq_mul r T)) = (eval_Poly val r) * sum_weight_var_seq n (eval_p_sequent val T).
Proof.
  induction T; intros r val n; [ simpl; lra | ].
  specialize (IHT r val n).
  destruct a as [a A].
  destruct A; simpl;
    case (R_order_dec (eval_Poly val a)); intros H;
      try (case (R_order_dec (eval_Poly val r * eval_Poly val a)); intros H');
      simpl; try (case (term.V_eq n v)); simpl;
        try lra;
        exfalso; (apply R_blt_lt in H' + apply R_blt_nlt in H'); nra.
Qed.

Lemma concat_eval_p_hseq : forall G val,
    concat (map (eval_p_sequent val) G) :: nil  = map (eval_p_sequent val) (concat G :: nil).
Proof.
  intros G val.
  simpl; f_equal.
  apply concat_eval_p_sequent.
Qed.

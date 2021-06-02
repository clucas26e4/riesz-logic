(** * Equational reasoning for Riesz spaces restricted to terms in negative normal form *)

Require Import CMorphisms.

Require Import EqNat.
Require Import PeanoNat.
Require Import Lra.

Require Import Rpos.
Require Import RL.hr.term.

Local Open Scope R_scope.

(** ** Basic definitions needed for equational reasoning *)
(** Context *)
Inductive context : Type :=
| RS_hole : context
| RS_cohole : context
| RS_TC : term -> context
| RS_varC : term.V -> context
| RS_covarC : term.V -> context
| RS_zeroC : context
| RS_minC : context -> context -> context
| RS_maxC : context -> context -> context
| RS_plusC : context -> context -> context
| RS_mulC : Rpos -> context -> context.

Fixpoint evalContext (c : context) (t : term) : term :=
  match c with
  | RS_hole => t
  | RS_cohole => -S t
  | RS_TC t' => t'
  | RS_varC n => RS_var n
  | RS_covarC n => RS_covar n
  | RS_zeroC => RS_zero
  | RS_minC c1 c2 => RS_min (evalContext c1 t) (evalContext c2 t)
  | RS_maxC c1 c2 => RS_max (evalContext c1 t) (evalContext c2 t)
  | RS_plusC c1 c2 => RS_plus (evalContext c1 t) (evalContext c2 t)
  | RS_mulC x c => RS_mul x (evalContext c t)
  end.

Fixpoint minusC c :=
  match c with
  | RS_hole => RS_cohole
  | RS_cohole => RS_hole
  | RS_TC t => RS_TC (-S t)
  | RS_varC n => RS_covarC n
  | RS_covarC n => RS_varC n
  | RS_zeroC => RS_zeroC
  | RS_plusC c1 c2 => RS_plusC (minusC c1) (minusC c2)
  | RS_mulC r c1 => RS_mulC r (minusC c1)
  | RS_maxC c1 c2 => RS_minC (minusC c1) (minusC c2)
  | RS_minC c1 c2 => RS_maxC (minusC c1) (minusC c2)
  end.

(** ** Equational Reasoning *)
Inductive eqMALG : term -> term -> Type :=
(** equational rules *)
| refl t : eqMALG t t
| trans t1 t2 t3 : eqMALG t1 t2 -> eqMALG t2 t3 -> eqMALG t1 t3
| ctxt c t1 t2 : eqMALG t1 t2 -> eqMALG (evalContext c t1) (evalContext c t2)
| sym t1 t2 : eqMALG t1 t2 -> eqMALG t2 t1
| subs_r t1 t2 n t : eqMALG t1 t2 -> eqMALG (subs t1 n t) (subs t2 n t)
(** vector space axioms *)
| asso_plus t1 t2 t3 : eqMALG (t1 +S (t2 +S t3)) ((t1 +S t2) +S t3)
| commu_plus t1 t2 : eqMALG (t1 +S t2) (t2 +S t1)
| neutral_plus t : eqMALG (t +S RS_zero) t
| opp_plus t : eqMALG (t -S t) RS_zero
| minus_ax a b t (Hlt: (projT1 b < projT1 a)%R) : eqMALG ((a *S t) +S (b *S (-S t))) ((minus_pos Hlt) *S t)
| mul_1 t  : eqMALG (One *S t) t
| mul_assoc x y t : eqMALG (x *S (y *S t)) ((time_pos x y) *S t)
| mul_distri_term x t1 t2 : eqMALG (x *S (t1 +S t2)) ((x *S t1) +S (x *S t2))
| mul_distri_coeff x y t : eqMALG ((plus_pos x y) *S t) ((x *S t) +S (y *S t))
| mul_minus x t : eqMALG (x *S (-S t)) (-S (x *S t))
(** lattice axioms *)
| asso_max t1 t2 t3 : eqMALG (t1 \/S (t2 \/S t3)) ((t1 \/S t2) \/S t3)
| commu_max t1 t2 : eqMALG (t1 \/S t2) (t2 \/S t1)
| abso_max t1 t2 : eqMALG (t1 \/S (t1 /\S t2)) t1
| asso_min t1 t2 t3 : eqMALG (t1 /\S (t2 /\S t3)) ((t1 /\S t2) /\S t3)
| commu_min t1 t2 : eqMALG (t1 /\S t2) (t2 /\S t1)
| abso_min t1 t2 : eqMALG (t1 /\S (t1 \/S t2)) t1
(** compability axiom *)
| compa_plus_ax t1 t2 t3 : eqMALG (((t1 /\S t2) +S t3) /\S (t2 +S t3)) ((t1 /\S t2) +S t3)
| compa_mul_ax r t : eqMALG (RS_zero /\S (r *S (t \/S RS_zero))) RS_zero.

Notation "A === B" := (eqMALG A B) (at level 90, no associativity).
Notation "A <== B" := (eqMALG (A /\S B) A) (at level 90, no associativity).

(** *** === is an equivalence relation **)

Instance eqMALG_Equivalence : Equivalence eqMALG | 10 := {
  Equivalence_Reflexive := refl ;
  Equivalence_Symmetric := sym ;
  Equivalence_Transitive := trans }.

(** *** Proofs of a equalities *)

Hint Constructors eqMALG : core.

Lemma cong_S : forall A B, A = B -> A === B.
Proof.
  intros A B eq.
  subst.
  reflexivity.
Qed.
Hint Resolve cong_S : core.

Lemma plus_left : forall A B C, A === C -> A +S B === C +S B.
Proof.
  intros A B C eq.
  apply (@ctxt (RS_plusC RS_hole (RS_TC B))).
  apply eq.
Qed.

Lemma plus_right : forall A B C, B === C -> A +S B === A +S C.
Proof.
  intros A B C eq.
  apply (@ctxt (RS_plusC (RS_TC A) RS_hole)).
  apply eq.
Qed.

Lemma plus_cong : forall A B C D, A === B -> C === D -> A +S C === B +S D.
Proof.
  intros A B C D eq1 eq2.
  transitivity (A +S D); [apply plus_right | apply plus_left]; assumption.
Qed.

Global Instance plus_cong_instance : Proper (eqMALG ==> eqMALG ==> eqMALG) RS_plus | 10.
Proof. repeat intro; now apply plus_cong. Qed.

Lemma max_left : forall A B C, A === C -> A \/S B === C \/S B.
Proof.
  intros A B C eq.
  apply (@ctxt (RS_maxC RS_hole (RS_TC B))).
  apply eq.
Qed.

Lemma max_right : forall A B C, B === C -> A \/S B === A \/S C.
Proof.
  intros A B C eq.
  apply (@ctxt (RS_maxC (RS_TC A) RS_hole)).
  apply eq.
Qed.

Lemma max_cong : forall A B C D, A === B -> C === D -> A \/S C === B \/S D.
Proof.
  intros A B C D eq1 eq2.
  transitivity (A \/S D); [apply max_right | apply max_left]; assumption.
Qed.

Global Instance max_cong_instance : Proper (eqMALG ==> eqMALG ==> eqMALG) RS_max | 10.
Proof. repeat intro; now apply max_cong. Qed.

Lemma min_left : forall A B C, A === C -> A /\S B === C /\S B.
Proof.
  intros A B C eq.
  apply (@ctxt (RS_minC RS_hole (RS_TC B))).
  apply eq.
Qed.

Lemma min_right : forall A B C, B === C -> A /\S B === A /\S C.
Proof.
  intros A B C eq.
  apply (@ctxt (RS_minC (RS_TC A) RS_hole)).
  apply eq.
Qed.

Lemma mul_left : forall x y A , x = y -> RS_mul x A === RS_mul y A.
Proof.
  intros x y A eq.
  rewrite eq.
  auto.
Qed.

Lemma min_cong : forall A B C D, A === B -> C === D -> A /\S C === B /\S D.
Proof.
  intros A B C D eq1 eq2.
  transitivity (A /\S D); [apply min_right | apply min_left]; assumption.
Qed.

Global Instance min_cong_instance : Proper (eqMALG ==> eqMALG ==> eqMALG) RS_min | 10.
Proof. repeat intro; now apply min_cong. Qed.

Lemma mul_right : forall x A B , A === B -> x *S A === x *S B.
Proof.
  intros x A B eq.
  apply (@ctxt (RS_mulC x RS_hole)).
  apply eq.
Qed.

Global Instance mul_right_instance x : Proper (eqMALG ==> eqMALG) (RS_mul x) | 10.
Proof. repeat intro; now apply mul_right. Qed.

Lemma minus_cong : forall A B , A === B -> -S A === -S B.
Proof.
  intros A B eq.
  apply (@ctxt RS_cohole).
  assumption.
Qed.

Global Instance minus_cong_instance : Proper (eqMALG ==> eqMALG) RS_minus | 10.
Proof. repeat intro; now apply minus_cong. Qed.

Hint Resolve plus_left plus_right max_left max_right min_left min_right minus_cong mul_left mul_right : core.

Lemma evalContext_cong : forall c t1 t2, t1 === t2 -> evalContext c t1 === evalContext c t2.
Proof.
  induction c; simpl; auto.
  all:intros t1 t2 eq; specialize (IHc1 t1 t2 eq); specialize (IHc2 t1 t2 eq).
  - etransitivity; [apply (@ctxt (RS_minC RS_hole (RS_TC (evalContext c2 t1)))); apply IHc1 |]; simpl.
    apply (@ctxt (RS_minC (RS_TC (evalContext c1 t2)) RS_hole)); apply IHc2.
  - etransitivity; [apply (@ctxt (RS_maxC RS_hole (RS_TC (evalContext c2 t1)))); apply IHc1 |]; simpl.
    apply (@ctxt (RS_maxC (RS_TC (evalContext c1 t2)) RS_hole)); apply IHc2.
  - etransitivity; [apply (@ctxt (RS_plusC RS_hole (RS_TC (evalContext c2 t1)))); apply IHc1 |]; simpl.
    apply (@ctxt (RS_plusC (RS_TC (evalContext c1 t2)) RS_hole)); apply IHc2.
Qed.

Global Instance evalContext_cong_instance c : Proper (eqMALG ==> eqMALG) (evalContext c) | 10.
Proof. repeat intro; now apply evalContext_cong. Qed.

Lemma leq_compa_plus : forall A B C, (A /\S B) +S C <== B +S C.
Proof.
  intros A B C.
  auto.
Qed.

Hint Resolve leq_compa_plus : MGA_solver.

Lemma minus_distri : forall A B, -S (A +S B) === (-S A) +S (-S B).
Proof.
  intros A B.
  auto.
Qed.

Hint Resolve minus_distri : MGA_solver.

Lemma minus_zero : RS_zero === -S RS_zero.
Proof.
  auto.
Qed.

Lemma minus_minus : forall A , -S (-S A) = A.
Proof with auto.
  induction A; simpl; try rewrite IHA; try rewrite IHA1; try rewrite IHA2...
Qed.

Hint Resolve minus_zero : MGA_solver.
Hint Resolve minus_minus : MGA_solver.

Lemma leq_antisym : forall A B, A <== B -> B <== A -> A === B.
Proof with auto.
  intros A B eq1 eq2.
  apply trans with (B /\S A)...
  apply trans with (A /\S B)...
Qed.

Lemma leq_cong_l : forall A A' B, A === A' -> A' <== B -> A <== B.
Proof with auto.
  intros A A' B eq leq.
  apply trans with (A' /\S B)...
  apply trans with A'...
Qed.

Lemma leq_cong_r : forall A B B', B === B' -> A <== B' -> A <== B.
Proof with auto.
  intros A B B' eq leq.
  apply trans with (A /\S B')...
Qed.

Lemma leq_trans : forall A B C, A <== B -> B <== C -> A <== C.
Proof with auto.
  intros A B C leq1 leq2.
  apply trans with ((A /\S B) /\S C)...
  apply trans with (A /\S (B /\S C))...
  apply trans with (A /\S B)...
Qed.

Lemma leq_plus : forall A B C, A <== B -> (A +S C) <== (B +S C).
Proof with auto.
  intros A B C leq.
  apply leq_cong_l with ((A /\S B) +S C)...
Qed.

Hint Resolve leq_plus : MGA_solver.

Lemma min_max : forall A B , (A /\S B) === A -> (A \/S B) === B.
Proof with auto.
  intros A B eq.
  apply trans with ((A /\S B) \/S B)...
  apply trans with ((B /\S A) \/S B)...
  apply trans with (B \/S (B /\S A))...
Qed.

Lemma max_min : forall A B , (A \/S B) === A -> (A /\S B) === B.
Proof with auto.
  intros A B eq.
  apply trans with ((A \/S B) /\S B)...
  apply trans with ((B \/S A) /\S B)...
  apply trans with (B /\S (B \/S A))...
Qed.

Hint Resolve max_min min_max : MGA_solver.

Lemma leq_refl_cong : forall A B, ((A /\S A) /\S B) === A /\S B.
Proof with auto.
  intros A B.
  apply trans with (A /\S (A /\S B))...
  apply max_min.
  apply abso_max.
Qed.

Lemma leq_refl : forall A , A /\S A === A.
Proof with auto.
  intro A.
  apply trans with (A /\S (A /\S (A \/S A)))...
  apply trans with ((A /\S A) /\S (A \/S A))...
  apply trans with (A /\S (A \/S A)); auto using leq_refl_cong.
Qed.

Hint Resolve leq_refl : MGA_solver.

Lemma leq_min : forall A B C, A <== B -> A <== C -> A <== (B /\S C).
Proof with auto.
  intros A B C leq1 leq2.
  apply trans with ((A /\S B) /\S C)...
  apply trans with (A /\S C)...
Qed.

Lemma leq_max : forall A B , A <== (A \/S B).
Proof with auto.
  intros A B.
  auto.
Qed.

Lemma min_leq : forall A B, (A /\S B) <== A.
Proof with auto with *.
  intros A B.
  apply trans with (A /\S (A /\S B))...
Qed.

Lemma max_leq : forall A B C, A <== C -> B <== C -> (A \/S B) <== C.
Proof with auto with *.
  intros A B C leq1 leq2.
  apply trans with (C /\S (A \/S B))...
  apply max_min.
  apply trans with ((A \/S B) \/S C)...
  apply trans with (A \/S (B \/S C))...
  apply trans with (A \/S C)...
Qed.

Hint Resolve leq_max min_leq min_leq max_leq : MGA_solver.

Lemma leq_plus_left : forall A B C, A <== B -S C -> A +S C <== B.
Proof with auto with *.
  intros A B C leq.
  apply leq_cong_r with (B +S (-S C) +S C)...
  apply trans with (B +S ((-S C) +S C))...
  apply trans with (B +S (C -S C))...
  apply trans with (B +S RS_zero)...
Qed.

Lemma leq_plus_right : forall A B C, A -S B <== C -> A <== C +S B.
Proof with auto with *.
  intros A B C leq.
  apply leq_cong_l with ( A -S B +S B)...
  apply trans with (A +S RS_zero)...
  apply trans with (A +S (B -S B))...
  apply trans with (A +S ((-S B) +S B))...
Qed.

Lemma leq_minus_left : forall A B C, A <== B +S C -> A -S C <== B.
Proof with auto.
  intros A B C leq.
  apply leq_plus_left...
  apply trans with (A /\S (B +S C)); auto using minus_minus.
Qed.

Lemma leq_minus_right : forall A B C , A +S C <== B -> A <== B -S C.
Proof with auto.
  intros A B C leq.
  apply leq_plus_right.
  apply trans with ((A +S C) /\S B); auto using minus_minus.
  apply trans with (A +S C); auto using minus_minus.
Qed.
  
Lemma max_plus : forall A B C, ((A \/S B) +S C) === (A +S C) \/S (B +S C).
Proof with auto.
  intros A B C.
  apply leq_antisym.
  - apply leq_plus_left.
    apply max_leq.
    + apply leq_minus_right...
    + apply leq_minus_right...
      apply trans with ((B +S C) /\S ((B +S C) \/S (A +S C)))...
  - apply max_leq; auto using leq_plus.
    apply leq_plus_right.
    apply leq_cong_l with B.
      * apply trans with (B +S (C -S C))...
        apply trans with (B +S RS_zero)...
      * apply leq_cong_r with (B \/S A)...
Qed.

Hint Resolve max_plus : MGA_solver.

Lemma minus_reverse_leq : forall A B, B <== A -> (-S A) <== (-S B).
Proof with auto.
  intros A B leq.
  apply leq_cong_r with (-S B +S RS_zero)...
  apply leq_cong_r with (RS_zero -S B)...
  apply leq_minus_right.
  apply leq_cong_l with (B -S A)...
  apply leq_minus_left.
  apply leq_cong_r with (A +S RS_zero)...
  apply leq_cong_r with A...
Qed.

Hint Resolve minus_reverse_leq : MGA_solver.

Lemma minus_min_max : forall A B, -S (A /\S B) === (-S A) \/S (-S B).
Proof with auto with MGA_solver.
  intros A B.
  apply leq_antisym.
  - apply leq_cong_r with (-S (-S ((-S A) \/S (-S B))))...
    apply minus_reverse_leq.
    apply leq_min.
    + apply leq_cong_r with (-S (-S A))...
    + apply leq_cong_r with (-S (-S B))...
      apply leq_cong_l with (-S (-S B \/S -S A))...
  - apply max_leq.
    + apply minus_reverse_leq...
    + apply leq_cong_r with (-S (B /\S A))...
Qed.

Lemma min_leq_max : forall A B, A /\S B <== A \/S B.
Proof with auto with MGA_solver.
  intros A B.
  apply leq_trans with A...
Qed.

Hint Resolve minus_min_max min_leq_max : MGA_solver.

Lemma minus_inj : forall A B, -S A === -S B -> A === B.
Proof with auto with MGA_solver.
  intros A B eq.
  apply trans with (-S (-S A))...
  apply trans with (-S (-S B))...
Qed.

Lemma leq_plus_cong : forall A B C D, A <== B -> C <== D -> A +S C <== B +S D.
Proof with auto with MGA_solver.
  intros A B C D leq1 leq2.
  apply leq_trans with (B +S C)...
  apply leq_cong_l with (C +S B)...
  apply leq_cong_r with (D +S B)...
Qed.

Hint Resolve leq_plus_cong : MGA_solver.

Lemma cond_leq : forall A B, RS_zero <== (A -S B) -> B <== A.
Proof with auto with MGA_solver.
  intros A B Hleq.
  apply leq_cong_r with ((A -S B) +S B).
  { apply trans with (A +S RS_zero)...
    apply trans with (A +S (B -S B))...
    apply trans with (A +S ((-S B) +S B))... }
  apply leq_cong_l with (RS_zero +S B)...
  apply trans with (B +S RS_zero)...
Qed.

Lemma cond_leq_inv : forall A B, B <== A -> RS_zero <== (A -S B).
Proof with auto with MGA_solver.
  intros A B Hleq.
  apply leq_cong_l with (B -S B)...
Qed.

Lemma eq_minus : forall A B, A === B -> A -S B === RS_zero.
Proof with auto with MGA_solver.
  intros A B eq.
  apply trans with (B -S B)...
Qed.

Hint Resolve eq_minus : MGA_solver.

Lemma minus_eq : forall A B, A -S B === RS_zero -> A === B.
Proof with auto with MGA_solver.
  intros A B eq.
  apply trans with (A +S RS_zero)...
  apply trans with (A +S (B -S B))...
  apply trans with (A +S ((-S B) +S B))...
  apply trans with (A -S B +S B)...
  apply trans with (RS_zero +S B)...
  apply trans with (B +S RS_zero)...
Qed.  

Lemma mul_compa : forall (r : Rpos) A B, A <== B -> (r *S A) <== (r *S B).
Proof with auto with MGA_solver.
  intros r A B HleqAB.
  apply cond_leq.
  apply leq_cong_r with ((r *S ((B -S A) \/S RS_zero))).
  { apply trans with ((r *S B) +S (r *S (-S A)))...
    apply trans with (r *S (B -S A))...
    apply mul_right.
    apply sym.
    apply trans with (RS_zero \/S (B -S A))...
    apply min_max.
    apply cond_leq_inv...
  }
  apply compa_mul_ax...
Qed.

Hint Resolve mul_compa : MGA_solver.

Lemma mul_0 :  forall r, r *S RS_zero === RS_zero.
Proof with auto with MGA_solver.
  intro r.
  transitivity (r *S (RS_zero +S RS_zero))...
  transitivity (r *S RS_zero +S r *S RS_zero)...
  transitivity (r *S RS_zero +S r *S (-S RS_zero))...
  transitivity (r *S RS_zero +S (-S (r *S RS_zero)))...
Qed.

Hint Resolve mul_0 : MGA_solver.  

Lemma no_div_zero : forall r A, r *S A === RS_zero -> A === RS_zero.
Proof with auto with MGA_solver.
  intros r A eq.
  transitivity (One *S A)...
  transitivity ((time_pos (inv_pos r) r) *S A)...
  { apply mul_left.
    apply Rpos_eq; destruct r; simpl. clear eq; apply R_blt_lt in e.
    rewrite Rinv_l...
    nra. }
  apply trans with ((inv_pos r) *S (r *S A))...
  apply trans with ((inv_pos r) *S RS_zero)...
Qed.

Lemma mul_distri_minus : forall k A B, (k *S A) -S (k *S B) === k *S (A -S B).
Proof with auto with MGA_solver.
  intros k A B.
  apply trans with ((k *S A) +S (k *S (-S B)))...
Qed.  

Lemma minus_max_min : forall A B, -S (A \/S B) === (-S A) /\S (-S B).
Proof with auto with MGA_solver.
  intros A B.
  apply trans with (-S (A \/S (-S (-S B))))...
  apply trans with (-S ((-S (-S A)) \/S (-S (-S B))))...
  apply trans with (-S (-S ((-S A) /\S (-S B))))...
Qed.

Hint Resolve mul_distri_minus minus_max_min : MGA_solver.

Lemma zero_leq_pos : forall A , RS_zero <== pos A.
Proof with auto with MGA_solver.
  intro A.
  apply leq_cong_r with (RS_zero \/S A)...
Qed.

Lemma zero_leq_neg : forall A , RS_zero <== neg A.
Proof with auto with MGA_solver.
  intro A.
  apply leq_cong_r with (RS_zero \/S (-S A))...
Qed.

Hint Resolve zero_leq_pos zero_leq_neg : MGA_solver.

Lemma eq_minus_right : forall A B C, A +S C === B -> A === B -S C.
Proof with auto with MGA_solver.
  intros A B C eq.
  apply trans with (A +S RS_zero)...
  apply trans with (A +S (C -S C))...
  apply trans with ((A +S C) -S C)...
Qed.

Lemma eq_plus_right : forall A B C, A -S C === B -> A === B +S C.
Proof with auto with MGA_solver.
  intros A B C eq.
  apply trans with (A +S RS_zero)...
  apply trans with (A +S (C -S C))...
  apply trans with (A +S ((-S C) +S C))...
  apply trans with ((A -S C) +S C)...
Qed.

Lemma decomp_pos_neg : forall A, A === (pos A) -S (neg A).
Proof with auto with MGA_solver.
  intros A.
  apply eq_minus_right.
  apply trans with (A \/S (A -S A))...
  apply trans with ((A +S RS_zero) \/S (A -S A))...
  apply trans with ((RS_zero +S A) \/S (A -S A))...
  apply trans with ((A -S A) \/S (RS_zero +S A))...
  apply trans with (((-S A) +S A) \/S (RS_zero +S A))...
  apply trans with (neg A +S A)...
Qed.

Hint Resolve decomp_pos_neg : MGA_solver.

Lemma pos_neg : forall A, pos A === A +S (neg A).
Proof.
  intros A.
  apply trans with ((pos A -S neg A) +S neg A); auto using eq_plus_right with MGA_solver.
Qed.

Lemma neg_pos : forall A , neg A === (pos A) -S A.
Proof with auto with MGA_solver.
  intros A.
  apply eq_minus_right...
  apply trans with (A +S neg A); auto using eq_plus_right with MGA_solver.
Qed.

Hint Resolve pos_neg neg_pos : MGA_solver.
  
Lemma min_plus : forall A B C, (A /\S B) +S C === (A +S C) /\S (B +S C).
Proof with auto with MGA_solver.
  intros A B C.
  apply trans with (-S (-S ((A +S C) /\S (B +S C))))...
  apply trans with (-S ((-S (A +S C)) \/S (-S (B +S C))))...
  apply trans with (-S (((-S A) -S C) \/S ((-S (B +S C)))))...
  apply trans with (-S (((-S A) -S C) \/S (((-S B) -S C))))...
  apply trans with (-S (((-S A) \/S ((-S B))) -S C))...
  apply trans with ((-S (((-S A) \/S ((-S B))))) -S (-S C))...
  apply trans with ((-S (((-S A) \/S ((-S B))))) +S C)...
  apply trans with (((-S (-S A)) /\S ((-S (-S B)))) +S C)...
  apply trans with ((A /\S ((-S (-S B)))) +S C)...
Qed.

Hint Resolve min_plus : MGA_solver.

Lemma min_pos_neg : forall A, (pos A) /\S (neg A) === RS_zero.
Proof with auto with MGA_solver.
  intros A.
  apply trans with ((A +S (neg A)) /\S (neg A))...
  apply trans with ((A +S (neg A)) /\S (neg A +S RS_zero))...
  apply trans with ((A +S (neg A)) /\S (RS_zero +S neg A))...
  apply trans with ((A /\S RS_zero) +S neg A)...
  apply trans with ( (-S (-S (A /\S RS_zero))) +S neg A)...
  apply trans with ( (-S ((-S A) \/S (-S RS_zero))) +S neg A)...
  apply trans with ( (-S (neg A)) +S neg A)...
  apply trans with (neg A -S neg A)...
Qed.

Hint Resolve min_pos_neg : MGA_solver.

Lemma cond_zero_leq_max : forall A B,
    (A \/S B) === (pos A \/S pos B) -> RS_zero <== A \/S B.
Proof with auto with MGA_solver.
  intros A B eq.
  apply trans with ((A \/S B) /\S RS_zero)...
  apply max_min.
  apply trans with ((A \/S B) \/S (RS_zero \/S RS_zero))...
  apply trans with (A \/S (B \/S (RS_zero \/S RS_zero)))...
  apply trans with (A \/S (pos B \/S RS_zero))...
  apply trans with (A \/S (RS_zero \/S pos B))...
  apply trans with (pos A \/S pos B)...
Qed.

Lemma cond_eq_pos : forall A B,
    RS_zero <== A \/S B -> (A \/S B) === (pos A \/S pos B).
Proof with auto with MGA_solver.
  intros A B eq.
  apply trans with (A \/S (RS_zero \/S pos B))...
  apply trans with (A \/S (pos B \/S RS_zero))...
  apply trans with (A \/S (B \/S (RS_zero \/S RS_zero)))...
  apply trans with ((A \/S B) \/S (RS_zero \/S RS_zero))...
  apply trans with (A \/S B \/S RS_zero)...
  apply trans with (RS_zero \/S (A \/S B))...
Qed.

Lemma max_pos : forall A B, A \/S B === (pos (A -S B)) +S B.
Proof with auto with MGA_solver.
  intros A B.
  apply trans with ((A +S RS_zero) \/S B)...
  apply trans with ((A +S (B -S B)) \/S B)...
  apply trans with ((A +S ((-S B) +S B)) \/S B)...
  apply trans with ((A +S (-S B) +S B) \/S B)...
  apply trans with ((A +S (-S B) +S B) \/S (B +S RS_zero))...
  apply trans with ((A +S (-S B) +S B) \/S (RS_zero +S B))...
Qed.

Hint Resolve max_pos : MGA_solver.

Lemma min_pos : forall A B, A /\S B === A -S (pos (A -S B)).
Proof with auto with MGA_solver.
  intros A B.
  apply eq_minus_right.
  apply trans with ((pos (A -S B)) +S (A /\S B))...
  apply sym.
  apply eq_plus_right.
  apply trans with (A +S ((-S A) \/S (-S B)))...
  apply trans with (((-S A) \/S (-S B)) +S A)...
  apply trans with (((-S A) +S A) \/S ((-S B) +S A))...
  apply trans with ((A -S A) \/S ((-S B) +S A))...
  apply trans with (RS_zero \/S ((-S B) +S A))...
  apply trans with (RS_zero \/S (A -S B))...
Qed.

Hint Resolve min_pos : MGA_solver.

Lemma min_max_plus : forall A B, (A \/S B) +S (A /\S B) === A +S B.
Proof with auto with MGA_solver.
  intros A B.
  apply trans with (((pos (A -S B)) +S B) +S (A /\S B))...
  apply trans with (((pos (A -S B)) +S B) +S (A -S (pos (A -S B))))...
  apply trans with ((B +S (pos (A -S B))) +S (A -S (pos (A -S B))))...
  apply trans with (B +S ((pos (A -S B)) +S (A -S (pos (A -S B)))))...
  apply trans with (B +S ((pos (A -S B)) +S ((-S (pos (A -S B))) +S A)))...
  apply trans with (B +S ((pos (A -S B)) +S (-S (pos (A -S B))) +S A))...
  apply trans with (B +S (RS_zero +S A))...
  apply trans with (B +S (A +S RS_zero))...
  apply trans with (B +S A)...
Qed.

Hint Resolve min_max_plus : MGA_solver.

Lemma max_distri_min : forall A B C, (A /\S B) \/S C === (A \/S C) /\S (B \/S C).
Proof with auto with MGA_solver.
  intros A B C.
  remember ((A \/S C) /\S (B \/S C)) as m.
  apply leq_antisym.
  - apply leq_cong_r with (A \/S C /\S B \/S C)...
    apply leq_min.
    + apply max_leq.
      * apply leq_trans with A...
      * apply leq_cong_r with (C \/S A)...
    + apply max_leq...
      * apply leq_trans with B...
        apply leq_cong_l with (B /\S A)...
      * apply leq_cong_r with (C \/S B)...
  - apply leq_cong_r with ((A /\S B) -S ((-S C) +S ((A /\S B) /\S C)))...
    + apply trans with ((A /\S B) +S ((-S (-S C)) -S ((A /\S B) /\S C)))...
      apply trans with ((A /\S B) +S (C -S ((A /\S B) /\S C)))...
      apply trans with (((A /\S B) +S C) -S ((A /\S B) /\S C)); auto using eq_minus_right with MGA_solver.
    + apply leq_minus_right...
      apply leq_min...
      * apply leq_cong_l with ((m +S ((A /\S B) /\S C)) -S C)...
        ** apply trans with (m +S (((A /\S B) /\S C) -S C))...
        ** apply leq_cong_r with ((A +S C) -S C); auto using eq_minus_right with MGA_solver.
           apply leq_plus.
           apply leq_cong_r with ((A \/S C) +S (A /\S C))...
           apply leq_trans with (m +S (A /\S C))...
           *** apply leq_plus_cong...
               apply leq_cong_l with (A /\S (B /\S C))...
               apply leq_cong_l with (A /\S (C /\S B))...
               apply leq_cong_l with (A /\S C /\S B)...
           *** apply leq_plus_cong...
               apply leq_cong_l with (A \/S C /\S B \/S C)...
      * apply leq_cong_l with (m +S ((A /\S B /\S C) -S C))...
        apply leq_cong_l with ((m +S (A /\S B /\S C)) -S C)...
        apply leq_cong_r with (B +S RS_zero)...
        apply leq_cong_r with (B +S (C -S C))...
        apply leq_cong_r with ((B +S C) -S C)...
        apply leq_plus...
        apply leq_cong_r with ((B \/S C) +S (B /\S C))...
        apply leq_plus_cong...
        apply leq_cong_l with (A \/S C /\S B \/S C)...
        ** apply leq_cong_l with (B \/S C /\S A \/S C)...
        ** apply leq_cong_l with (A /\S (B /\S C))...
           apply leq_cong_l with ((B /\S C) /\S A)...
Qed.

Hint Resolve max_distri_min : MGA_solver.

Lemma min_distri_max : forall A B C, (A \/S B) /\S C === (A /\S C) \/S (B /\S C).
Proof with auto with MGA_solver.
  intros A B C.
  apply trans with (-S (-S (A \/S B /\S C)))...
  apply trans with (-S ((-S (A \/S B) \/S (-S C))))...
  apply trans with (-S (((-S A) /\S (-S B)) \/S (-S C)))...
  apply trans with (-S (((-S A) \/S (-S C)) /\S ((-S B) \/S (-S C))))...
  apply trans with ((-S ((-S A) \/S (-S C))) \/S (-S ((-S B) \/S (-S C))))...
  apply trans with (((-S (-S A)) /\S (-S (-S C))) \/S (-S ((-S B) \/S (-S C))))...
  apply trans with (((-S (-S A)) /\S (-S (-S C))) \/S ((-S (-S B)) /\S (-S (-S C))))...
  apply trans with ((A /\S (-S (-S C))) \/S ((-S (-S B)) /\S (-S (-S C))))...
  apply trans with ((A /\S C) \/S ((-S (-S B)) /\S (-S (-S C))))...
  apply trans with ((A /\S C) \/S (B /\S (-S (-S C))))...
Qed.

Hint Resolve min_distri_max : MGA_solver.

Lemma decomp_max_pos_neg : forall A B, A \/S B === ((pos A) \/S (pos B)) -S ((neg A) /\S (neg B)).
Proof with auto with MGA_solver.
  intros A B.
  apply trans with (pos (A \/S B) -S (neg (A \/S B)))...
  apply trans with ((pos A \/S pos B) -S (neg (A \/S B))).
  - apply (@ctxt (RS_plusC RS_hole (minusC (RS_TC (neg (A \/S B)))))).
    apply trans with (A \/S B \/S (RS_zero \/S RS_zero))...
    apply trans with (A \/S (B \/S pos RS_zero))...
    apply trans with (A \/S (pos B \/S RS_zero))...
    apply trans with (A \/S (RS_zero \/S pos B))...
  - apply trans with ((pos A \/S pos B) -S (((-S A) /\S (-S B)) \/S RS_zero))...
Qed.

Hint Resolve decomp_max_pos_neg : MGA_solver.

Lemma cond_zero_leq_max_2 : forall A B, (neg A) /\S (neg B) === RS_zero -> RS_zero <== A \/S B.
Proof with auto with MGA_solver.
  intros A B eq.
  apply cond_zero_leq_max...
  apply trans with ((pos A \/S pos B) +S RS_zero)...
  apply trans with ((pos A \/S pos B) -S RS_zero)...
  apply trans with ((pos A \/S pos B) -S (neg A /\S neg B))...
Qed.

Lemma cond_min_neg_eq_zero : forall A B, RS_zero <== A \/S B -> (neg A) /\S (neg B) === RS_zero.
Proof with auto with MGA_solver.
  intros A B leq.
  apply trans with (((pos A) \/S (pos B)) -S (A \/S B)); auto using eq_minus_right, cond_eq_pos with MGA_solver.
  apply eq_minus_right...
  apply trans with ((A \/S B) +S (neg A /\S neg B)); auto using eq_plus_right with MGA_solver.
Qed.

Lemma zero_leq_abs : forall A, RS_zero <== abs A.
Proof with auto with MGA_solver.
  intro A.
  apply cond_zero_leq_max_2.
  apply trans with ((neg A) /\S (pos A))...
  apply trans with ((pos A) /\S (neg A))...
Qed.

Hint Resolve zero_leq_abs : MGA_solver.

Lemma mul_distri_max_pos : forall r A B, r *S (A \/S B) === (r *S A) \/S (r *S B).
Proof with auto with MGA_solver.
  intros r A B.
  apply leq_antisym.
  - apply leq_cong_r with (r *S ((inv_pos r) *S ((r *S A) \/S (r *S B)))).
    { apply trans with ((time_pos r (inv_pos r)) *S (r *S A \/S r *S B))...
      replace (time_pos r (inv_pos r)) with One...
      destruct r; apply Rpos_eq; simpl.
      apply R_blt_lt in e; rewrite Rinv_r...
      nra. }
    apply mul_compa.
    apply max_leq.
    + apply leq_cong_l with ((inv_pos r) *S (r *S A)).
      { apply trans with ((time_pos (inv_pos r) r) *S A)...
        replace (time_pos (inv_pos r) r) with One.
        2:{ apply Rpos_eq; destruct r; simpl; apply R_blt_lt in e; rewrite Rinv_l; try auto; try nra. }
        auto with MGA_solver; apply Rgt_not_eq; apply Hlt. }
      apply mul_compa; try apply Rlt_le; try auto with MGA_solver.
    + apply leq_cong_l with ((inv_pos r) *S (r *S B)).
      { apply trans with ((time_pos (inv_pos r) r) *S B)...
        replace (time_pos (inv_pos r) r) with One.
        2:{ apply Rpos_eq; destruct r; simpl; apply R_blt_lt in e; rewrite Rinv_l; try auto; try nra. }
        symmetry; apply mul_1. }
      apply mul_compa.
      eapply leq_cong_r ; [ apply commu_max | apply leq_max].
  - apply max_leq; apply mul_compa...
    apply leq_cong_r with (B \/S A)...
Qed.

Lemma mul_distri_min_pos : forall r A B, r *S (A /\S B) === (r *S A) /\S (r *S B).
Proof with auto with MGA_solver.
  intros r A B.
  apply leq_antisym.
  - apply leq_min; apply mul_compa...
    apply leq_cong_l with (B /\S A)...
  - apply leq_cong_l with (r *S ((inv_pos r) *S ((r *S A) /\S (r *S B)))).
    { apply trans with ((time_pos r (inv_pos r)) *S (r *S A /\S r *S B))...
      replace (time_pos r (inv_pos r)) with One...
      apply Rpos_eq; destruct r; simpl; apply R_blt_lt in e; rewrite Rinv_r; nra. }
    apply mul_compa...
    apply leq_min.
    + apply leq_cong_r with ((inv_pos r) *S (r *S A)).
      { apply trans with ((time_pos (inv_pos r) r) *S A)...
        replace (time_pos (inv_pos r) r) with One...
        apply Rpos_eq; destruct r; simpl; apply R_blt_lt in e; rewrite Rinv_l; nra. }
      apply mul_compa; try apply Rlt_le; try auto with MGA_solver.
    + apply leq_cong_r with ((inv_pos r) *S (r *S B)).
      { apply trans with ((time_pos (inv_pos r) r) *S B)...
        replace (time_pos (inv_pos r) r) with One...
        apply Rpos_eq; destruct r; simpl; apply R_blt_lt in e; rewrite Rinv_l; nra. }
      apply mul_compa; try apply Rlt_le; try auto with MGA_solver.
      apply leq_cong_l with (r *S B /\S r *S A)...
Qed.
Hint Resolve mul_distri_max_pos : MGA_solver.
Hint Resolve mul_distri_min_pos : MGA_solver.

Require Import Lra. 
   
Lemma mul_distri_min : forall A B, (plus_pos One One) *S (A /\S B) === ((plus_pos One One) *S A) /\S ((plus_pos One One) *S B).
Proof with auto with MGA_solver.
  intros A B.
  apply trans with (-S (-S ((plus_pos One One) *S (A /\S B))))...
  apply trans with (-S ((plus_pos One One) *S (-S (A /\S B))))...
  apply trans with (-S ((plus_pos One One) *S ((-S A) \/S (-S B))))...
  apply trans with (-S (((plus_pos One One) *S (-S A)) \/S ((plus_pos One One) *S (-S B))))...
  apply trans with (-S ((-S ((plus_pos One One) *S A)) \/S ((plus_pos One One) *S (-S B))))...
  apply trans with (-S ((-S ((plus_pos One One) *S A)) \/S (-S ((plus_pos One One) *S B))))...
  apply trans with (-S (-S (((plus_pos One One) *S A) /\S ((plus_pos One One) *S B))))...
Qed.

Hint Resolve mul_distri_min : MGA_solver.

Lemma mul_2 : forall A , (plus_pos One One) *S A === A +S A.
Proof with auto with MGA_solver.
  intros A.
  transitivity (One *S A +S One *S A)...
  transitivity (One *S A +S A)...
Qed. 

Hint Resolve mul_2 : MGA_solver.

Lemma mean_prop : forall A B , A +S B <== (plus_pos One One) *S (A \/S B).
Proof with auto with MGA_solver.
  intros A B.
  apply leq_cong_r with (((plus_pos One One) *S A) \/S ((plus_pos One One) *S B))...
  apply leq_trans with (A +S (A \/S B))...
  { apply leq_cong_r with (A +S (B \/S A))... }
  apply leq_cong_r with ((plus_pos One One) *S (A \/S B))...
  apply leq_cong_r with ((A \/S B) +S (A \/S B))...
Qed.

Hint Resolve mean_prop : MGA_solver.

Lemma decomp_abs : forall A , abs A === pos A +S neg A.
Proof with auto with MGA_solver.
  intro A.
  apply trans with ((A +S RS_zero) \/S (-S A))...
  etransitivity.
  { apply (@ctxt (RS_maxC (RS_plusC (RS_TC A) RS_hole) (RS_TC (-S A)))).
    symmetry; apply (@opp_plus A). }
  simpl.
  apply trans with (((A +S A) -S A) \/S (-S A))...
  apply trans with (((A +S A) -S A) \/S ((-S A) +S RS_zero))...
  apply trans with (((A +S A) -S A) \/S (RS_zero -S A))...
  apply trans with (((A +S A) \/S RS_zero) -S A)...
  transitivity ((((plus_pos One One) *S A) \/S RS_zero) -S A)...
  transitivity ((((plus_pos One One) *S A) \/S (RS_zero +S RS_zero)) -S A)...
  transitivity ((((plus_pos One One) *S A) \/S ((plus_pos One One) *S RS_zero)) -S A)...
  apply trans with (((plus_pos One One) *S (pos A)) -S A)...
  apply trans with ((pos A +S pos A) -S A)...
  apply trans with (pos A +S (pos A -S A))...
Qed.

Hint Resolve decomp_abs : MGA_solver.

Lemma pos_leq_abs : forall A , pos A <== abs A.
Proof with auto with MGA_solver.
  intro A.
  apply leq_cong_l with (pos A +S RS_zero)...
  apply leq_cong_r with (pos A +S neg A)...
Qed.

Lemma neg_leq_abs : forall A , neg A <== abs A.
Proof with auto with MGA_solver.
  intro A.
  apply leq_cong_l with (neg A +S RS_zero)...
  apply leq_cong_l with (RS_zero +S neg A)...
  apply leq_cong_r with (pos A +S neg A)...
Qed.

Hint Resolve pos_leq_abs neg_leq_abs : MGA_solver.

Lemma abs_eq_zero : forall A , abs A === RS_zero -> A === RS_zero.
Proof with auto with MGA_solver.
  intros A eq.
  apply trans with (pos A -S neg A)...
  apply trans with (pos A -S RS_zero)...
  - apply plus_right.
    apply minus_cong.
    apply leq_antisym...
    apply leq_trans with (abs A)...
    apply leq_cong_r with (abs A)...
  - apply trans with (pos A +S RS_zero)...
    apply trans with (pos A)...
    apply leq_antisym...
    apply leq_trans with (abs A)...
    apply leq_cong_r with (abs A)...
Qed.

Lemma min_minus_leq_zero : forall A , A /\S (-S A) <== RS_zero.
Proof with auto with MGA_solver. 
  intro A.
  apply leq_cong_l with (-S (-S (A /\S (-S A))))...
  apply leq_cong_r with (-S RS_zero)...
  apply minus_reverse_leq.
  apply leq_cong_r with ((-S A) \/S (-S (-S A)))...
Qed.

Hint Resolve min_minus_leq_zero : MGA_solver.

Lemma two_eq_zero : forall A , (plus_pos One One) *S A === RS_zero -> A === RS_zero.
Proof with auto with MGA_solver.
  intros A eq.
  assert (A === -S A).
  - apply trans with ((-S A) +S RS_zero)...
    apply trans with (RS_zero -S A)...
    apply eq_minus_right...
    apply trans with ((plus_pos One One) *S A)...
  - apply abs_eq_zero.
    apply leq_antisym...
    apply leq_cong_l with (A /\S (-S A))...
    apply trans with (A \/S A)...
    apply trans with A...
    apply trans with (A /\S A)...
Qed.

Lemma inj_mul_two : forall A B, (plus_pos One One) *S A === (plus_pos One One) *S B -> A === B.
Proof with auto with MGA_solver.
  intros A B eq.
  apply trans with (B +S RS_zero)...
  apply trans with (RS_zero +S B)...
  apply eq_plus_right.
  apply two_eq_zero...
  apply trans with (((plus_pos One One) *S A) +S ((plus_pos One One) *S (-S B)))...
  apply trans with (((plus_pos One One) *S A) -S ((plus_pos One One) *S B))...
Qed.

Lemma leq_div_2 : forall A B , (plus_pos One One) *S A <== (plus_pos One One) *S B -> A <== B.
Proof with auto with MGA_solver.
  intros A B eq.
  apply inj_mul_two...
  apply trans with (((plus_pos One One) *S A) /\S ((plus_pos One One) *S B))...
Qed.

Lemma neg_subdistri_plus : forall A B, neg (A +S B) <== (neg A) +S (neg B).
Proof with auto with MGA_solver.
  intros A B.
  apply max_leq...
  - apply leq_cong_l with ((-S A) +S (-S B))...
  - apply leq_cong_l with (RS_zero +S RS_zero)...
Qed.

Hint Resolve neg_subdistri_plus : MGA_solver.

Lemma Rpos_mul_neg : forall t A, t *S neg A === neg (t *S A).
Proof with auto with MGA_solver.
  intros t A.
  etransitivity; [ apply mul_distri_max_pos | ].
  auto using mul_0.
Qed.

Hint Resolve Rpos_mul_neg : MGA_solver.

Lemma mul_leq : forall t A B, A <== B -> t *S A <== t *S B.
Proof.
  auto with MGA_solver.
Qed.

Hint Resolve mul_leq : MGA_solver.

Lemma mul_leq_inv : forall t A B, t *S A <== t *S B -> A <== B.
Proof with auto with MGA_solver.
  intros t A B Hle.
  apply leq_cong_r with (One *S B); try auto.
  apply leq_cong_l with (One *S A); try auto.
  replace One with (time_pos (inv_pos t) t).
  2:{ destruct t; apply Rpos_eq; simpl; clear Hle; apply R_blt_lt in e; rewrite Rinv_l; nra. }
  eapply leq_cong_r; [ symmetry; apply mul_assoc | ].
  eapply leq_cong_l; [ symmetry; apply mul_assoc | ]...
Qed.


Lemma neg_leq_cond : forall A B, A <== B -> neg B <== neg A.
Proof with try assumption.
  intros A B Hleq.
  apply max_leq.
  - apply leq_trans with (-S A).
    + apply minus_reverse_leq...
    + apply leq_max.
  - auto with MGA_solver.
Qed.

Lemma max_idempotence : forall A, A \/S A === A.
Proof.
  intros A.
  apply min_max.
  apply leq_refl.
Qed.

Lemma eq_subs_minus : forall A B n, subs (-S A) n B = -S (subs A n B).
Proof with try reflexivity.
  induction A ; intros B v'; try (simpl; constructor; assumption); try (simpl; rewrite IHA1; rewrite IHA2; auto with MGA_solver; fail)...
  - simpl; case (term.V_eq v' v)...
  - simpl; case (term.V_eq v' v)...
    rewrite minus_minus...
  - simpl; rewrite IHA...
Qed.

Lemma leq_pos_max_mul_l : forall A B r,
    RS_zero <== (r *S A) \/S B ->
    RS_zero <== A \/S B.
Proof.
  intros A B [r Hpos]; 
    remember (existT (fun r : R => (0 <? r)%R = true) r Hpos) as t; intros Hleq.
  apply cond_min_neg_eq_zero in Hleq.
  apply cond_zero_leq_max_2.
  apply leq_antisym.
  - case (Rlt_dec 1 r); intros Hlt; [ | case (Rlt_dec r 1); intros Hnlt].
    + eapply leq_cong_r; [ symmetry; apply Hleq | ].
      apply leq_min.
      * apply leq_trans with (neg A); [ apply min_leq | ].
        apply leq_cong_l with (RS_zero +S neg A).
        { etransitivity; [ | apply commu_plus ].
         symmetry; apply neutral_plus. }
        apply leq_plus_left.
        change (1%R) with (projT1 One) in Hlt.
        replace r with (projT1 t) in Hlt by now rewrite Heqt.
        eapply leq_cong_r.
        { etransitivity.
          { apply (@ctxt (RS_plusC RS_hole (RS_TC (-S neg A)))).
            symmetry; apply Rpos_mul_neg. }
          simpl evalContext.
          etransitivity.
          { change ((-S (-S A)) /\S RS_zero) with (-S neg A).
            apply (@ctxt (RS_plusC (RS_TC (t *S neg A)) RS_cohole)).
            etransitivity; [ symmetry; apply mul_1 | ].
            reflexivity. }
          simpl.
          change (One *S ((-S (-S A)) /\S RS_zero)) with (-S (One *S neg A)).
          etransitivity; [apply (minus_ax _ _ _ Hlt) | ].
          reflexivity. }
        apply leq_cong_r with (minus_pos Hlt *S (pos (neg A))).
        { etransitivity.
          2:{ apply (@ctxt (RS_mulC (minus_pos Hlt) RS_hole)).
              symmetry; apply (commu_max (neg A)). }
          simpl.
          apply (@ctxt (RS_mulC (minus_pos Hlt) RS_hole)).
          symmetry.
          apply min_max.
          auto with MGA_solver. }
        apply compa_mul_ax.
      * eapply leq_cong_l; [apply commu_min | ].
        apply min_leq.
    + apply (@mul_leq_inv t).
      eapply leq_cong_l; [ apply mul_distri_min_pos | ].
      eapply leq_cong_r; [ apply mul_0 | ].
      eapply leq_cong_r; [ symmetry; apply Hleq | ].
      apply leq_cong_r with ((t *S neg A) /\S neg B); [auto with MGA_solver | ].
      apply leq_min; [apply min_leq | ].
      eapply leq_cong_l; [ apply commu_min | ].
      apply leq_trans with (t *S neg B) ; [ apply min_leq | ].
      eapply leq_cong_l; [ symmetry; apply neutral_plus | ].
      eapply leq_cong_l; [ apply commu_plus | ].
      apply leq_plus_left.
      apply leq_cong_r with ((One *S neg B) -S (t *S neg B)); [ auto | ].
      apply leq_cong_r with ((One *S neg B) +S (t *S (-S neg B))); [auto | ].
      change (1%R) with (projT1 One) in Hnlt.
      replace r with (projT1 t) in Hnlt by now rewrite Heqt.
      eapply leq_cong_r; [ apply (minus_ax _ _ _ Hnlt) | ].
      apply leq_cong_r with (minus_pos Hnlt *S (pos (neg B))).
      { transitivity (minus_pos Hnlt *S (RS_zero \/S neg B)) ; [ | auto].
        apply (@ctxt (RS_mulC (minus_pos Hnlt) RS_hole)).
        symmetry.
        apply min_max; auto with MGA_solver. }
      apply compa_mul_ax.
    + assert (t = One) as Heq.
      { apply Rpos_eq; rewrite Heqt;simpl; nra. }
      eapply leq_cong_r; [ symmetry; apply Hleq | ].
      rewrite Heq.
      eapply leq_cong_r ; [ | apply leq_refl ].
      auto.
  - apply leq_min; (eapply leq_cong_r ; [ apply commu_max | ]); apply leq_max.
Qed.

Lemma leq_pos_max_mul_l_inv : forall A B r,
    RS_zero <== A \/S B ->
    RS_zero <== (r *S A) \/S B.
Proof.
  intros A B r Hleq.
  apply leq_pos_max_mul_l with (inv_pos r).
  apply leq_cong_r with ((time_pos (inv_pos r) r) *S A \/S B); [ auto | ].
  rewrite inv_pos_l.
  apply leq_cong_r with (A \/S B); [ auto | ].
  apply Hleq.
Qed.

Lemma plus_pos_min : forall A B C, RS_zero <== A -> RS_zero <== B -> RS_zero <== C -> A +S B /\S C <== (A /\S C) +S (B /\S C).
Proof.
  intros A B C H1 H2 H3.
  apply leq_plus_right.
  apply leq_min.
  - apply leq_minus_left.
    eapply leq_cong_r; [ apply commu_plus | ].
    apply leq_plus_right.
    apply leq_min.
    + apply leq_minus_left.
      eapply leq_cong_r; [ apply commu_plus | ].
      apply min_leq.
    + apply leq_trans with (A +S B /\S C).
      * apply leq_minus_left.
        eapply leq_cong_l ; [ symmetry; apply neutral_plus | ].
        apply leq_plus_cong; try assumption.
        apply leq_refl.
      * eapply leq_cong_l; [ apply commu_min | ].
        apply min_leq.
  - apply leq_minus_left.
    eapply leq_cong_r; [apply commu_plus | ].
    apply leq_plus_right.
    apply leq_min.
    + apply leq_minus_left.
      eapply leq_cong_r; [ apply commu_plus | ].
      eapply leq_cong_l; [ symmetry; apply neutral_plus | ].
      apply leq_plus_cong; try assumption.
      eapply leq_cong_l; [ apply commu_min | ].
      apply min_leq.
    + apply leq_minus_left.
      eapply leq_cong_l ; [ symmetry; apply neutral_plus | ].
      apply leq_plus_cong; try assumption.
      eapply leq_cong_l; [ apply commu_min | ].
      apply min_leq.
Qed.

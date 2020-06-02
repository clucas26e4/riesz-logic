From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Equational reasoning for modal lattice-ordered Abelian groups *)
Require Import Rterm.
Require Import Rpos.
Require Import term.
Require Import Rsemantic.
Require Import semantic.

Require Import Reals.
Require Import Lra.
Require Import Lia.


Local Open Scope R_scope.

(* Definitions *)
Fixpoint NNF (A : Rterm) : term.
  case: A => [x | | A B |  r A | A B | A B].
  (* A = var x *)
  - by apply (var x).
  (* A = zero *)
  - by apply zero.
  (* A = A + B *)
  - by apply (plus (NNF A) (NNF B)).
  (* A = r * A *)
  - case_eq (0 <? r) => Hr.
    (* 0 < r *)
    + by apply (mul (existT _ r Hr) (NNF A)).
    + case_eq (0 <? -r) => Hr'.
      (* r < 0 *)
      * by apply (mul (existT _ (-r) Hr') (-S (NNF A))).
      (* r = 0 *)
      * by apply zero.
  (* A = A \/ B *)
  - by apply (max (NNF A) (NNF B)).
  (* A = A /\ B *)
  - by apply (min (NNF A) (NNF B)).
Defined.

Fixpoint CNNF (C : Rcontext) : context.
  case: C => [ | A | x | | C1 C2 | C1 C2 | C1 C2 | r C ].
  - by apply hole.
  - by apply (TC (NNF A)).
  - by apply (varC x).
  - by apply zeroC.
  - by apply (minC (CNNF C1) (CNNF C2)).
  - by apply (maxC (CNNF C1) (CNNF C2)).
  - by apply (plusC (CNNF C1) (CNNF C2)).
  - case_eq (0 <? r) => Hr.
    + by apply (mulC (existT _ r Hr) (CNNF C)).
    + case_eq (0 <? -r) => Hr'.
      * by apply (mulC (existT _ (-r) Hr') (minusC (CNNF C))).
      * by apply zeroC.
Defined.

Fixpoint toRterm A :=
  match A with
  | var x => R_var x
  | covar x => -R (R_var x)
  | zero => R_zero
  | plus A B => R_plus (toRterm A) (toRterm B)
  | mul (existT _ r _) A => R_mul r (toRterm A)
  | max A B => R_max (toRterm A) (toRterm B)
  | min A B => R_min (toRterm A) (toRterm B)
  end.

Fixpoint toRcontext C :=
  match C with
  | hole => R_hole
  | cohole => R_mulC (-1) R_hole
  | varC x => R_varC x
  | covarC x => R_mulC (-1) (R_varC x)
  | TC A => R_TC (toRterm A)
  | zeroC => R_zeroC
  | plusC C1 C2 => R_plusC (toRcontext C1) (toRcontext C2)
  | mulC (existT _ r _) C => R_mulC r (toRcontext C)
  | maxC C1 C2 => R_maxC (toRcontext C1) (toRcontext C2)
  | minC C1 C2 => R_minC (toRcontext C1) (toRcontext C2)
  end.

(* Soundness of the translation *)

Lemma aux_dep_if_true : forall (b : bool) (t : b = true -> term) (f : b = false -> term) (H : true = b),
       (if b as b' return b = b' -> term
        then t
        else f) eq_refl
       = t (eq_sym H).
Proof.
  destruct H; reflexivity.
Defined.

Lemma aux_dep_if_false : forall (b : bool) (t : b = true -> term) (f : b = false -> term) (H : false = b),
       (if b as b' return b = b' -> term
        then t
        else f) eq_refl
       = f (eq_sym H).
Proof.
  destruct H; reflexivity.
Defined.

Lemma R_eq_minus : forall A, (toRterm (-S A)) =R= (-R (toRterm A)).
Proof with auto with Rsem_solver.
  elim => [ x | x | | A IHA B IHB | [r Hr] A IHA | A IHA B IHB | A IHA B IHB] /=; try rewrite IHA; try rewrite IHB...
Qed.

Lemma toRterm_NNF : forall A, toRterm (NNF A) =R= A.
Proof with auto with Rsem_solver.
  induction A; try (simpl; rewrite IHA1 IHA2); try (simpl; rewrite IHA)...
  - case_eq (0 <? r) => Hr; [ | case_eq (0 <? -r) => Hnr]; simpl.
    + rewrite aux_dep_if_true...
      intro.
      simpl; rewrite IHA.
      reflexivity.        
    + rewrite aux_dep_if_false...
      rewrite aux_dep_if_true...
      intro; simpl; rewrite R_eq_minus; rewrite IHA.
      rewrite R_mul_assoc.
      replace (-r * -1) with r by lra...
    + rewrite aux_dep_if_false...
      rewrite aux_dep_if_false...
      replace r with 0.
      * simpl.
        symmetry.
        replace 0 with (0 + 0) by lra.
        rewrite R_mul_distri_coeff.
        replace 0 with (-1 * 0) at 2 by lra.
        rewrite -(R_mul_assoc)...
      * unfold f in Hr; unfold f in Hnr.
        apply R_blt_nlt in Hr.
        apply R_blt_nlt in Hnr.
        lra.
Qed.

Lemma NNF_toRterm : forall A, NNF (toRterm A) === A.
Proof with auto with MGA_solver.
  induction A; simpl; try (rewrite IHA1 IHA2); try rewrite IHA...
  - rewrite aux_dep_if_false.
    2:{ symmetry; apply R_blt_nlt; lra. }
    rewrite aux_dep_if_true.
    2:{ symmetry; apply R_blt_lt; lra. }
    intro.
    replace (existT (fun r : R => (0 <? r) = true) (- -1) (eq_sym Hyp0)) with One...
    apply Rpos_eq.
    simpl; lra.
  - destruct r as [r Hr].
    simpl.
    rewrite aux_dep_if_true...
    intro.
    replace ( existT (fun r0 : R => (0 <? r0) = true) r (eq_sym Hyp0)) with (existT (fun r0 : R => (0 <? r0) = true) r Hr)...
    apply Rpos_eq...
Qed.    

(* Semantic to Rsemantic *)

Lemma R_eq_term_context : forall C T, (toRterm (evalContext C T)) =R= (evalRcontext (toRcontext C) (toRterm T)).
Proof with auto with Rsem_solver.
  elim => [ | | B | x | x | | C1 IHC1 C2 IHC2 | C1 IHC1 C2 IHC2 | C1 IHC1 C2 IHC2 | [r Hr] C IHC ] A /= ; try (constructor; assumption); try rewrite IHC1; try rewrite IHC2; try rewrite IHC...
  - apply R_eq_minus.
Qed.

Lemma R_eq_term_subs : forall A B n, (toRterm (subs A n B)) =R= (Rsubs (toRterm A) n (toRterm B)).
Proof with auto with Rsem_solver.
  elim => [ x | x | | A1 IHA1 A2 IHA2 | [r Hr] A IHA | A1 IHA1 A2 IHA2 | A1 IHA1 A2 IHA2 ] B /=; try (constructor; assumption); move => n; try rewrite IHA1; try rewrite IHA2; try rewrite IHA...
  - case (n =? x); apply R_refl.
  - case (n =? x)...
    + apply R_eq_minus.
Qed.
      
Fixpoint R_subs_gen (A : Rterm) (v : nat -> Rterm) : Rterm :=
  match A with
  | R_zero => R_zero
  | R_var n => v n
  | R_plus A B => R_plus (R_subs_gen A v) (R_subs_gen B v)
  | R_mul r A => R_mul r (R_subs_gen A v)
  | R_max A B => R_max (R_subs_gen A v) (R_subs_gen B v)
  | R_min A B => R_min (R_subs_gen A v) (R_subs_gen B v)
  end.

Lemma R_subs_gen_sub : forall A v n t, R_subs_gen (Rsubs A n t) v = R_subs_gen A (fun x => if n =? x then (R_subs_gen t v) else v x).
Proof.
  induction A => v n' t; simpl; try (specialize (IHA1 v n' t)); try (specialize (IHA2 v n' t)); try (specialize (IHA v n' t)); try (rewrite IHA1); try (rewrite IHA2); try (rewrite IHA); try reflexivity.
  - case (n' =? n); reflexivity.
Qed.

Lemma R_subs_gen_cong : forall A B v, R_eqMALG A B -> R_eqMALG (R_subs_gen A v) (R_subs_gen B v).
Proof.
  move => A B v Heq; move : v; induction Heq => v; try (constructor; assumption).
  - apply R_trans with (R_subs_gen t2 v); [apply IHHeq1 | apply IHHeq2].
  - induction c; simpl; try apply R_refl.
    + apply IHHeq.
    + apply R_trans with (R_min (R_subs_gen (evalRcontext c1 t2) v) (R_subs_gen (evalRcontext c2 t1) v)).
      * apply (R_ctxt (R_minC R_hole (R_TC (R_subs_gen (evalRcontext c2 t1) v)))).
        apply IHc1.
      * apply (R_ctxt (R_minC (R_TC (R_subs_gen (evalRcontext c1 t2) v)) R_hole)).
        apply IHc2.
    + apply R_trans with (R_max (R_subs_gen (evalRcontext c1 t2) v) (R_subs_gen (evalRcontext c2 t1) v)).
      * apply (R_ctxt (R_maxC R_hole (R_TC (R_subs_gen (evalRcontext c2 t1) v)))).
        apply IHc1.
      * apply (R_ctxt (R_maxC (R_TC (R_subs_gen (evalRcontext c1 t2) v)) R_hole)).
        apply IHc2.
    + apply R_trans with (R_plus (R_subs_gen (evalRcontext c1 t2) v) (R_subs_gen (evalRcontext c2 t1) v)).
      * apply (R_ctxt (R_plusC R_hole (R_TC (R_subs_gen (evalRcontext c2 t1) v)))).
        apply IHc1.
      * apply (R_ctxt (R_plusC (R_TC (R_subs_gen (evalRcontext c1 t2) v)) R_hole)).
        apply IHc2.
    + apply (R_ctxt (R_mulC r R_hole)).
      apply IHc.
  - apply R_sym; apply IHHeq.
  - rewrite 2?R_subs_gen_sub.
    apply IHHeq.
Qed.

Lemma R_subs_to_gen : forall A n t, Rsubs A n t = R_subs_gen A (fun x => if n =? x then t else R_var x).
Proof.
  induction A => n' t; simpl; try (rewrite IHA1; rewrite IHA2); try rewrite IHA; try reflexivity.
Qed.
      
Lemma semantic_to_Rsemantic : forall A B, A === B -> (R_eqMALG (toRterm A) (toRterm B)).
Proof with try assumption.
  move => A B Heq.
  induction Heq; simpl; try (constructor; assumption);
    try (move: x y => [x Hx] [y Hy] /=; constructor; assumption);
    try (move: x => [x Hx] /=; constructor; assumption).
  - apply R_trans with (toRterm t2)...
  - apply R_trans with (evalRcontext (toRcontext c) (toRterm t1)); [apply R_eq_term_context | ].
    apply R_trans with (evalRcontext (toRcontext c) (toRterm t2)) ; [ | apply R_sym ; apply R_eq_term_context].
    apply R_ctxt...
  - apply R_trans with (Rsubs (toRterm t1) n (toRterm t)); [apply R_eq_term_subs | ].
    apply R_trans with (Rsubs (toRterm t2) n (toRterm t)); [ | apply R_sym; apply R_eq_term_subs ].
    rewrite 2?R_subs_to_gen.
    apply R_subs_gen_cong.
    apply IHHeq.
  - rewrite R_eq_minus; apply R_opp_plus.
  - move: a b Hlt => [a Ha] [b Hb] /= => Hlt.
    rewrite R_mul_distri_coeff.
    rewrite R_eq_minus.
    replace (- b) with (b * (- 1)) by nra.
    auto with Rsem_solver.
  - move: r => [x Hx] /=; apply R_compa_mul_ax.
    apply Rlt_le.
    move: Hx; rewrite /R_lt_dec; case (Rlt_dec 0 x) => //=.
Qed.

    
(* Rsemantic to Semantic *)

Lemma eq_subs_minus : forall A B n, subs (-S A) n B === -S (subs A n B).
Proof with auto with MGA_solver.
  induction A => B n'; try (simpl; constructor; assumption); try (simpl; rewrite IHA1 IHA2; auto with MGA_solver; fail)...
  - simpl; case (n' =? n)...
  - simpl; case (n' =? n)...
  - simpl; rewrite IHA...
Qed.
    
Lemma eq_term_subs : forall A B n, (NNF (Rsubs A n B)) === (subs (NNF A) n (NNF B)).
Proof with auto with MGA_solver.
  elim => [ x | | A1 IHA1 A2 IHA2 | r A IHA | A1 IHA1 A2 IHA2 | A1 IHA1 A2 IHA2 ] B; try (simpl; constructor; assumption); move => n; try (simpl; rewrite IHA1 IHA2; auto with MGA_solver; fail)...
  - simpl; case (n =? x)...
  - unfold Rsubs; fold Rsubs.
    case_eq (0 <? r) => Hr; [ | case_eq (0 <? -r) => Hnr]; simpl.
    + rewrite aux_dep_if_true; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      intros.
      rewrite IHA.
      simpl.
      replace (existT (fun r0 : R => (0 <? r0) = true) r (eq_sym Hyp0)) with (existT (fun r0 : R => (0 <? r0) = true) r (eq_sym Hyp1))...
      apply Rpos_eq; simpl;  nra.
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      intros; simpl; rewrite IHA.
      rewrite eq_subs_minus.
      replace (existT (fun r0 : R => (0 <? r0) = true) (-r) (eq_sym Hyp0)) with (existT (fun r0 : R => (0 <? r0) = true) (-r) (eq_sym Hyp1))...
      apply Rpos_eq; simpl; nra.
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
Qed.
      
Fixpoint subs_gen (A : term) (v : nat -> term) : term :=
  match A with
  | zero => zero
  | var n => v n
  | covar n => -S (v n)
  | plus A B => plus (subs_gen A v) (subs_gen B v)
  | mul r A => mul r (subs_gen A v)
  | max A B => max (subs_gen A v) (subs_gen B v)
  | min A B => min (subs_gen A v) (subs_gen B v)
  end.

Lemma eq_subs_gen_minus : forall A v, subs_gen (-S A) v === -S (subs_gen A v).
Proof with auto with MGA_solver.
  induction A => v; try (simpl; constructor; assumption); simpl; try (rewrite IHA1 IHA2; auto with MGA_solver; fail)...
Qed.

Lemma subs_gen_sub : forall A v n t, subs_gen (subs A n t) v === subs_gen A (fun x => if n =? x then (subs_gen t v) else v x).
Proof.
  induction A => v n' t; simpl; try (specialize (IHA1 v n' t)); try (specialize (IHA2 v n' t)); try (specialize (IHA v n' t)); try (rewrite IHA1); try (rewrite IHA2); try (rewrite IHA); try reflexivity.
  - case (n' =? n); reflexivity.
  - case (n' =? n); [ rewrite eq_subs_gen_minus | ]; reflexivity.
Qed.

Lemma subs_gen_cong : forall A B v, A === B -> (subs_gen A v) === (subs_gen B v).
Proof with auto with MGA_solver.
  move => A B v Heq; move : v; induction Heq => v; simpl; try rewrite IHHeq; try (constructor; now assumption).
  - transitivity (subs_gen t2 v); [ apply IHHeq1 | apply IHHeq2].
  - induction c; simpl; try rewrite IHc1; try rewrite IHc2; try rewrite IHc...
    rewrite 2?eq_subs_gen_minus.
    rewrite IHHeq...
  - rewrite 2?subs_gen_sub.
    apply IHHeq.
  - rewrite eq_subs_gen_minus...
  - rewrite eq_subs_gen_minus...
Qed.

Lemma subs_to_gen : forall A n t, subs A n t = subs_gen A (fun x => if n =? x then t else var x).
Proof.
  induction A => n' t; simpl; try (rewrite IHA1; rewrite IHA2); try rewrite IHA; try reflexivity.
  case (n' =? n); reflexivity.
Qed.

Lemma Rsemantic_to_semantic : forall A B, A =R= B -> (NNF A) === (NNF B).
Proof with auto with MGA_solver.
  move => A B Heq.
  induction Heq; try (simpl; by auto with MGA_solver).
  - transitivity (NNF t2)...
  - induction c; try (simpl; rewrite IHc1; rewrite IHc2; auto with MGA_solver);try (simpl; rewrite IHc1; auto with MGA_solver)...
    case_eq (0 <? r) => Hr ; [ | case_eq (0 <? (-r)) => Hnr]; simpl.
    + rewrite aux_dep_if_true; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      intros.
      replace (existT (fun r0 : R => (0 <? r0) = true) r (eq_sym Hyp1)) with (existT (fun r0 : R => (0 <? r0) = true) r (eq_sym Hyp0)) by (apply Rpos_eq; simpl; nra)...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      intros.
      replace (existT (fun r0 : R => (0 <? r0) = true) (-r) (eq_sym Hyp1)) with (existT (fun r0 : R => (0 <? r0) = true) (-r) (eq_sym Hyp0)) by (apply Rpos_eq; simpl; nra)...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...      
  - rewrite 2?eq_term_subs.
    rewrite 2!(subs_to_gen).
    apply subs_gen_cong...
  - simpl.
    rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt; lra].
    rewrite aux_dep_if_true; [ | symmetry; apply R_blt_lt; lra].
    intro.
    replace (existT (fun r : R => (0 <? r) = true) (- -1) (eq_sym Hyp0)) with One.
    2:{ apply Rpos_eq;simpl; lra. }
    rewrite mul_1...
  - simpl.
    rewrite aux_dep_if_true; [ | symmetry; apply R_blt_lt; lra].
    intro.
    replace (existT (fun r : R => (0 <? r) = true) 1 (eq_sym Hyp0)) with One...
    apply Rpos_eq;simpl; lra.
  -  case_eq (0 <? x) => Hx ; [ | case_eq (0 <? -x) => Hnx]; (case_eq (0 <? y) => Hy; [ | case_eq (0 <?  - y) => Hny]); simpl.
     + rewrite aux_dep_if_true; [ | symmetry]...
       intro.
       rewrite aux_dep_if_true; [ | symmetry]...
       intro.
       rewrite aux_dep_if_true; [ | apply R_blt_lt in Hx; apply R_blt_lt in Hy; symmetry; apply R_blt_lt].
       2:{ apply Rmult_lt_0_compat... }
       intro.
       rewrite mul_assoc.
       apply mul_left.
       apply Rpos_eq...
     + rewrite aux_dep_if_true; [ | symmetry]...
       intro.
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_true; [ | symmetry]...
       intro.
       rewrite aux_dep_if_false.
       2:{ symmetry.
           apply R_blt_lt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt.
           nra. }
       rewrite aux_dep_if_true.
       2:{ symmetry.
           apply R_blt_lt in Hx; apply R_blt_lt in Hny; apply R_blt_lt.
           nra. }
       intro.
       rewrite mul_assoc.
       apply mul_left.
       apply Rpos_eq; simpl; nra.
     + rewrite aux_dep_if_true; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_lt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_lt in Hx; apply R_blt_nlt in Hny; apply R_blt_nlt; nra]...
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_true; [ | symmetry]...
       rewrite aux_dep_if_true; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hx; apply R_blt_lt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_true; [ | symmetry; apply R_blt_lt in Hnx; apply R_blt_lt in Hy; apply R_blt_lt; nra].
       intros.
       rewrite mul_assoc; apply mul_left; apply Rpos_eq; simpl; nra.
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_true; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_true; [ | symmetry]...
       rewrite aux_dep_if_true; [ | symmetry; apply R_blt_lt in Hnx; apply R_blt_lt in Hny; apply R_blt_lt; nra].
       intros.
       rewrite -(mul_minus).
       rewrite minus_minus.
       rewrite mul_assoc; apply mul_left; apply Rpos_eq; simpl; nra.
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_true; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_lt in Hnx; apply R_blt_nlt in Hy; apply R_blt_nlt in Hny; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_lt in Hnx; apply R_blt_nlt in Hy; apply R_blt_nlt in Hny; apply R_blt_nlt; nra].
       intro...
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_lt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_lt in Hy; apply R_blt_nlt; nra]...
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra]...
     + rewrite aux_dep_if_false; [ | symmetry ]...
       rewrite aux_dep_if_false; [ | symmetry]...
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra].
       rewrite aux_dep_if_false; [ | symmetry; apply R_blt_nlt in Hnx; apply R_blt_nlt in Hx; apply R_blt_nlt in Hy; apply R_blt_nlt; nra]...
  - case_eq (0 <? x) => Hx; [ | case_eq (0 <? - x) => Hnx]; simpl.
    + rewrite aux_dep_if_true; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      pose r := (existT (fun x => (0 <? x) = true) x Hx).
      intros.
      replace (existT (fun r0 : R => (0 <? r0) = true) x (eq_sym Hyp2)) with r by now apply Rpos_eq.
      replace (existT (fun r0 : R => (0 <? r0) = true) x (eq_sym Hyp1)) with r by now apply Rpos_eq.
      replace (existT (fun r0 : R => (0 <? r0) = true) x (eq_sym Hyp0)) with r by now apply Rpos_eq...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_true; [ | symmetry]...
      pose r := (existT (fun x => (0 <? x) = true) (-x) Hnx).
      intros.
      replace (existT (fun r0 : R => (0 <? r0) = true) (-x) (eq_sym Hyp2)) with r by now apply Rpos_eq.
      replace (existT (fun r0 : R => (0 <? r0) = true) (-x) (eq_sym Hyp1)) with r by now apply Rpos_eq.
      replace (existT (fun r0 : R => (0 <? r0) = true) (-x) (eq_sym Hyp0)) with r by now apply Rpos_eq...
    + rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
  - (case_eq (0 <? x) => Hx ; [ apply R_blt_lt in Hx | apply R_blt_nlt in Hx]); (case_eq (0 <? -x) => Hnx ; [ apply R_blt_lt in Hnx | apply R_blt_nlt in Hnx]); (case_eq (0 <? y) => Hy ; [ apply R_blt_lt in Hy | apply R_blt_nlt in Hy]); (case_eq (0 <? -y) => Hny ; [ apply R_blt_lt in Hny | apply R_blt_nlt in Hny]); (case_eq (0 <? x + y) => Hxy ; [ apply R_blt_lt in Hxy | apply R_blt_nlt in Hxy]); (case_eq (0 <? -(x+y)) => Hnxy ; [ apply R_blt_lt in Hnxy | apply R_blt_nlt in Hnxy]); simpl; repeat (try (rewrite aux_dep_if_true; [ | symmetry; now apply R_blt_lt]); try (rewrite aux_dep_if_false; [ | symmetry; now apply R_blt_nlt])); intros; try nra; try (symmetry in Hyp0); try (symmetry in Hyp1);try (symmetry in Hyp2).
    + set ry := (existT (fun r => (0 <? r) = true) y (eq_sym Hyp0)).
      set rx := (existT (fun r => (0 <? r) = true) x (eq_sym Hyp1)).
      replace (existT (fun r : R => (0 <? r) = true) (x + y) (eq_sym Hyp2)) with (plus_pos rx ry) by (now apply Rpos_eq)...
    + set ry := (existT (fun r => (0 <? r) = true) (-y) (eq_sym Hyp0)).
      set rx := (existT (fun r => (0 <? r) = true) x (eq_sym Hyp1)).
      have Rxly : (-y) < x by nra.
      replace (existT (fun r : R => (0 <? r) = true) (x + y) (eq_sym Hyp2)) with (@minus_pos rx ry Rxly) by (apply Rpos_eq; simpl; nra)...    
    + set ry := (existT (fun r => (0 <? r) = true) (-y) (eq_sym Hyp0)).
      set rx := (existT (fun r => (0 <? r) = true) x (eq_sym Hyp1)).
      rewrite commu_plus.
      transitivity (ry *S (-S NNF t) +S rx *S (-S (-S (NNF t))))...
      have Hlt : x < -y by nra.
      replace (existT (fun r : R => (0 <? r) = true) (- (x + y)) (eq_sym Hyp2)) with (@minus_pos ry rx Hlt)...
      apply Rpos_eq; simpl; nra.
    + have Heq: x = -y by nra.
      set rx := (existT (fun r => (0 <? r) = true) x (eq_sym Hyp1)).
      replace (existT (fun r : R => (0 <? r) = true) (- y) (eq_sym Hyp0)) with rx by (now apply Rpos_eq).
      rewrite mul_minus...
    + have Hy0 : y = 0 by nra.
      set rx := (existT (fun r => (0 <? r) = true) x (eq_sym Hyp0)).
      replace (existT (fun r : R => (0 <? r) = true) (x + y) (eq_sym Hyp1)) with rx by (apply Rpos_eq; simpl; nra)...
    + set ry := (existT (fun r => (0 <? r) = true) y (eq_sym Hyp0)).
      set rx := (existT (fun r => (0 <? r) = true) (-x) (eq_sym Hyp1)).
      have Hlt : (- x) < y by nra.
      rewrite commu_plus.
      replace (existT (fun r : R => (0 <? r) = true) (x + y) (eq_sym Hyp2)) with (@minus_pos ry rx Hlt)...
      apply Rpos_eq; simpl; nra.
    + set ry := (existT (fun r => (0 <? r) = true) y (eq_sym Hyp0)).
      set rx := (existT (fun r => (0 <? r) = true) (-x) (eq_sym Hyp1)).
      have Hlt : y < - x by nra.
      transitivity (rx *S (-S NNF t) +S ry *S (-S (-S NNF t)))...
      replace (existT (fun r : R => (0 <? r) = true) (- (x + y)) (eq_sym Hyp2)) with (@minus_pos rx ry Hlt)...
      apply Rpos_eq; simpl; nra.
    + have Heq: -x = y by nra.
      set rx := (existT (fun r => (0 <? r) = true) (-x) (eq_sym Hyp1)).
      replace (existT (fun r : R => (0 <? r) = true)  y (eq_sym Hyp0)) with rx by (now apply Rpos_eq).
      rewrite mul_minus.
      rewrite commu_plus...
    + set ry := (existT (fun r => (0 <? r) = true) (-y) (eq_sym Hyp0)).
      set rx := (existT (fun r => (0 <? r) = true) (-x) (eq_sym Hyp1)).
      replace (existT (fun r : R => (0 <? r) = true) (-(x + y)) (eq_sym Hyp2)) with (plus_pos rx ry) by (apply Rpos_eq; simpl; nra)...
    + have Hy0 : y = 0 by nra.
      set rx := (existT (fun r => (0 <? r) = true) (-x) (eq_sym Hyp0)).
      replace (existT (fun r : R => (0 <? r) = true)  (-(x + y)) (eq_sym Hyp1)) with rx by (apply Rpos_eq; simpl; nra)...
    + have rx0 : x = 0 by nra.
      set ry := (existT (fun r => (0 <? r) = true) (y) (eq_sym Hyp0)).
      replace (existT (fun r : R => (0 <? r) = true)  ((x + y)) (eq_sym Hyp1)) with ry by (apply Rpos_eq; simpl; nra)...
      rewrite commu_plus...
    + have rx0 : x = 0 by nra.
      set ry := (existT (fun r => (0 <? r) = true) (-y) (eq_sym Hyp0)).
      replace (existT (fun r : R => (0 <? r) = true)  (-(x + y)) (eq_sym Hyp1)) with ry by (apply Rpos_eq; simpl; nra)...
      rewrite commu_plus...
    + auto.                                                       
  - case_eq (0 <? r) => Hr.
    + simpl.
      rewrite aux_dep_if_true; [ | symmetry]...
    + have Hnr : (0 <? (- r)) = false.
      { apply R_blt_nlt; apply R_blt_nlt in Hr; lra. }
      simpl.
      rewrite aux_dep_if_false; [ | symmetry]...
      rewrite aux_dep_if_false; [ | symmetry]...
Qed.
      
       
       
           
   
  

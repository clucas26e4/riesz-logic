Require Import Reals.

Require Import RL.OLlibs.List_Type.
Require Import List.

Require Import RL.Utilities.riesz_logic_List_more.
Require Import RL.Utilities.Rpos.
Require Import RL.Utilities.polynomials.

Require Import RL.Utilities.Lim_seq_US.

Require Import Lra.
Require Import Lia.

Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rcomplements.

Local Open Scope R_scope.

(** Infinitary pigeonhole principle *)
Axiom IPP : forall (u : nat -> nat) m,
    (forall n, u n < m)%nat ->
    {' (phi, i) & prod (subseq_support phi)
                       ((i < m)%nat *
                        (forall n, u (phi n) = i))}.

(** Equivalent definition of the limit on reals *)
Lemma lim_def_eps : forall (u : nat -> R_UniformSpace) (l : R_UniformSpace),
    (forall (eps : posreal), exists N, forall n, (N <= n)%nat -> Rabs (u n - l) < eps) ->
    is_lim_seq u l.
Proof.
  intros u l Hlim.
  intros P [eps H].
  specialize (Hlim eps) as [N Hlim].
  split with N.
  intros n Hle.
  specialize (Hlim n Hle).
  apply H.
  apply Hlim.
Qed.

Lemma lim_def_eps_inv : forall (u : nat -> R_UniformSpace) (l : R_UniformSpace),
    is_lim_seq u l ->
    forall (eps : posreal), exists N, forall n, (N <= n)%nat -> Rabs (u n - l) < eps.
Proof.
  intros u l Hlim eps.
  specialize (Hlim (fun x => Rabs (x - l) < eps)).
  assert (locally l (fun x => Rabs (x - l) < eps)).
  { split with eps.
    intros y Hball; apply Hball. }
  specialize (Hlim H); clear H.
  apply Hlim.
Qed.

(** A bound on the sequence is also a bound on the limit *)
Lemma is_lim_seq_ub : forall (u : nat -> R_UniformSpace) (l : R_UniformSpace) ub,
    is_lim_seq u l ->
    (forall n, u n <= ub) ->
    l <= ub.
Proof.
  intros u l ub Hlim Hle.
  apply le_epsilon.
  intros eps Hpos.
  apply lim_def_eps_inv with _ _ (mkposreal eps Hpos) in Hlim as [N Hlim].
  simpl in Hlim.
  specialize (Hlim N (le_refl N)).
  assert (l - u N < eps).
  { unfold Rabs in Hlim.
    revert Hlim; case (Rcase_abs (u N - l)); lra. }
  specialize (Hle N).
  lra.
Qed.  

Lemma is_lim_seq_lb : forall (u : nat -> R_UniformSpace) (l : R_UniformSpace) lb,
    is_lim_seq u l ->
    (forall n, lb <= u n) ->
    lb <= l.
Proof.
  intros u l lb Hlim Hle.
  apply Ropp_le_cancel.
  apply is_lim_seq_ub with (fun n => - u n).
  - intros P Hloc.
    destruct Hloc as [eps Hloc].
    specialize (Hlim (fun x => P ( -x))).
    assert (locally l (fun x => P (- x))).
    { split with eps.
      intros y Hball.
      apply Hloc.
      change (ball (- l) eps (- y)) with (Rabs (- y - (- l)) < eps).
      replace (- y - - l) with (- (y - l)) by lra.
      rewrite Rabs_Ropp.
      apply Hball. }
    specialize (Hlim H); clear H.
    apply Hlim.
  - intros n; specialize (Hle n); lra.
Qed.

(** Returns an antecedent of 1 lower than i if it exists, and 0 otherwise *)
Fixpoint u_n_ante_1 (u : nat -> R) i :=
  match i with
  | 0%nat => 0%nat
  | S i => if (R_eqb (u (S i)) 1) then (S i) else u_n_ante_1 u i
  end.

Lemma u_n_ante_1_lt : forall u i m,
    (i <= m)%nat ->
    (u_n_ante_1 u i < S m)%nat.
Proof.
  intros u i m; induction i; intros Hle.
  - simpl; lia.
  - simpl; case (R_eqb (u (S i)) 1); lia.
Qed.

Lemma u_n_ante_1_correct : forall u m,
    {i & prod (i < (S m))%nat (u i = 1)} ->
    u (u_n_ante_1 u m) = 1.
Proof.
  intros u m; induction m; intros [i [Hlt Heq]].
  - destruct i; [ | exfalso; lia].
    apply Heq.
  - case_eq (i =? S m); intros H; (apply Nat.eqb_eq in H + apply Nat.eqb_neq in H).
    + subst.
      simpl.
      case_eq (R_eqb (u (S m)) 1); intros H1; (apply R_eqb_eq in H1 + apply R_eqb_neq in H1); [ apply H1 | exfalso; lra].
    + assert (i < S m)%nat by lia.
      simpl.
      case_eq (R_eqb (u (S m)) 1); [intros H1; apply R_eqb_eq in H1; apply H1 | intros _].
      apply IHm.
      split with i.
      split; assumption.
Qed.

(** Instantiation of IPP where a sequence of function take the value 1 infinitely often on [0..m], and therefore there is subsequence of function always taking the value 1 on i \in [0..m] *)
Lemma IPP_eq_1 : forall (u : nat -> nat -> R) m,
    (forall n, {i & prod (i < m)%nat (u n i = 1)}) ->
    {' (phi , i) : (nat -> nat) * nat & prod (subseq_support phi)
                                             ((i < m)%nat *
                                              (forall n, u (phi n) i = 1))}.
Proof.
  intros u m H.
  destruct m.
  { specialize (H 0%nat) as [i [Hlt _]].
    exfalso; inversion Hlt. }
  destruct (IPP (fun n => u_n_ante_1 (fun i => u n i) m) (S m)) as [[phi i] [Hsubseq [Hlt Hipp]]].
  - intros n.
    apply u_n_ante_1_lt.
    reflexivity.
  - split with (phi, i).
    repeat split; try assumption.
    intros n; specialize (Hipp n).
    rewrite <- Hipp.
    apply u_n_ante_1_correct.
    apply (H (phi n)).
Qed.

(** A sequence on [lb;ub] has a converging subsequence *)
Axiom SequentialCompactness : forall (u : nat -> R) lb ub,
    (forall n, prod (lb <= u n) (u n <= ub)) ->
    {' (phi , l) & prod (subseq_support phi)
                        (is_lim_seq (fun n => u (phi n)) l)}.

(** A sequence on [lb;ub]^n has a converging subsequence *)
Lemma seq_compact_Rn : forall n lb ub (u : nat -> list R),
    (forall i, length (u i) = n) ->
    (forall i j, (j < n)%nat -> prod (lb <= nth j (u i) 0) (nth j (u i) 0 <= ub)) ->
    {' (phi, ul) & prod (subseq_support phi)
                       ((length ul = n) *
                        (forall j, (j < n)%nat -> is_lim_seq (fun i => nth j (u (phi i)) 0) (nth j ul 0)))}.
Proof.
  enough (forall k n lb ub (u : nat -> list R),
             (k < n)%nat ->
             (forall i, length (u i) = n) ->
             (forall i j, (j < n)%nat -> prod (lb <= nth j (u i) 0) (nth j (u i) 0 <= ub)) ->
             {' (phi, ul) & prod (subseq_support phi)
                                 ((length ul = n) *
                                  (forall j, (j <= k)%nat -> is_lim_seq (fun i => nth j (u (phi i)) 0) (nth j ul 0)))}).
  { intros n lb ub u Hlen Hborned.
    destruct n.
    2:{ destruct (X n (S n) lb ub u (Nat.lt_succ_diag_r n) Hlen Hborned) as [[phi ul] [Hsubseq [Hlenul Hlimul]]].
        split with (phi, ul).
        repeat split; try assumption.
        intros j Hlt.
        apply Hlimul.
        lia. }
    split with (fun x => x, nil).
    repeat split.
    - intros n; lia.
    - intros j Hlt.
      exfalso; lia. }
  induction k; intros n lb ub u Hlt Hlen Hborned.
  - destruct (SequentialCompactness (fun n => nth 0 (u n) 0) lb ub) as [[phi l] [Hsubseq Hlim]].
    { intros i.
      destruct (Hborned i 0%nat); try split; assumption. }
    split with (phi, l :: repeat 0 (n - 1)).
    repeat split; try assumption.
    + simpl; rewrite repeat_length.
      destruct n; [ inversion Hlt | ].
      lia.
    + intros j Hle.
      destruct j; try now inversion Hle.
  - destruct (IHk n lb ub u) as [[phi ul] [Hsubseq [Hlenul Hlimul]]]; try assumption; try lia.
    destruct (SequentialCompactness (fun n => nth (S k) (u (phi n)) 0) lb ub) as [[phi' l] [Hsubseq' Hlim]].
    { intros i.
      destruct (Hborned (phi i) (S k)); try split; assumption. }
    split with (fun i => phi (phi' i), replace ul l (S k)).
    repeat split.
    + intros i.
      apply lt_le_trans with (phi (S (phi' i))).
      * apply Hsubseq. 
      * case_eq ((S (phi' i)) =? phi' (S i));
          intros Heq; [ apply Nat.eqb_eq in Heq | apply Nat.eqb_neq in Heq].
        -- subst.
           rewrite Heq.
           reflexivity.
        -- apply Nat.lt_le_incl.
           apply subseq_support_implies_incr; [assumption | ].
           assert (phi' i < phi' (S i))%nat.
           { apply Hsubseq'. }
           lia.
    + rewrite replace_length.
      apply Hlenul.
    + intros j Hle.
      inversion Hle; subst.
      * rewrite replace_nth_eq; try lia.
        eapply is_lim_seq_ext; [ | apply Hlim].
        auto.
      * rewrite replace_nth_neq; try lia.
        apply is_lim_seq_subseq with (fun i => nth j (u (phi i)) 0).
        -- split with phi'.
           split; try assumption.
           intros n.
           reflexivity.
        -- apply Hlimul.
           apply H0.
Qed.


(** Equivalent definition of limit on functions *)
Lemma lim_def_fun_eps {A} : forall (u : nat -> A -> R_UniformSpace) (l : A -> R_UniformSpace),
    (forall (eps : posreal), exists N, forall n, (N <= n)%nat -> forall a, Rabs (u n a - l a) < eps) ->
    is_lim_seq u l.
Proof.
  intros u l Hlim.
  intros P [eps H].
  specialize (Hlim eps) as [N Hlim].
  split with N.
  intros n Hle.
  specialize (Hlim n Hle).
  apply H.
  intros a.
  apply Hlim.
Qed.

Lemma lim_def_fun_eps_inv {A} : forall (u : nat -> A -> R_UniformSpace) (l : A -> R_UniformSpace),
    is_lim_seq u l ->
    forall (eps : posreal), exists N, forall n, (N <= n)%nat -> forall a, Rabs (u n a - l a) < eps.
Proof.
  intros u l Hlim eps.
  specialize (Hlim (fun x => forall a, Rabs (x a - l a) < eps)).
  assert (locally l (fun x => forall a, Rabs (x a - l a) < eps)).
  { split with eps.
    intros y Hball; apply Hball. }
  specialize (Hlim H); clear H.
  apply Hlim.
Qed.

Require Import PeanoNat.
Require Import Reals.

Require Import Coquelicot.Continuity.
Require Import Coquelicot.Hierarchy.
Require Import Coquelicot.Rcomplements.

Require Import Lia.
Require Import Lra.

Section Lim_seq_US_def.
Context {U : UniformSpace}.
  
(** * Limit of sequences *)
(** ** Definition *)
Definition is_lim_seq (u : nat -> U) (l : U) :=
  filterlim u eventually (locally l).

Definition ex_lim_seq (u : nat -> U) :=
  exists l, is_lim_seq u l.

Definition ex_lim_seq_inf (u : nat -> U) :=
  {l & is_lim_seq u l}.

(** Extensionality *)

Lemma is_lim_seq_ext_loc (u v : nat -> U) (l : U) :
  eventually (fun n => u n = v n) ->
  is_lim_seq u l -> is_lim_seq v l.
Proof.
  intros H1 H2.
  intros P Hl.
  specialize (H2 P Hl).
  unfold filtermap.
  destruct H1 as [N1 H1].
  destruct H2 as [N2 H2].
  split with (Nat.max N1 N2).
  intros n H.
  rewrite <- H1; try lia.
  apply H2; lia.
Qed.  
  
Lemma ex_lim_seq_ext_loc (u v : nat -> U) :
  eventually (fun n => u n = v n) ->
  ex_lim_seq u -> ex_lim_seq v.
Proof.
  intros H1 [l H2].
  split with l.
  apply is_lim_seq_ext_loc with u; assumption.
Qed.
  
Lemma is_lim_seq_ext (u v : nat -> U) (l : U) :
  (forall n, u n = v n) -> is_lim_seq u l -> is_lim_seq v l.
Proof.
  intros H1 H2.
  intros P Hl.
  specialize (H2 P Hl).
  destruct H2 as [N H2].
  split with N.
  intros n H.
  rewrite <- H1.
  apply H2; assumption.
Qed.
  
Lemma ex_lim_seq_ext (u v : nat -> U) :
  (forall n, u n = v n) -> ex_lim_seq u -> ex_lim_seq v.
Proof.
  intros H1 [l H2].
  split with l; apply is_lim_seq_ext with u; assumption.
Qed.

(** ** Arithmetic operations and order *)

(** Constants *)
Lemma is_lim_seq_const (a : U) :
  is_lim_seq (fun n => a) a.
Proof.
  intros P Hl.
  destruct Hl as [e Hl].
  split with 0%nat.
  intros n _.
  apply Hl.
  apply ball_center.
Qed.
  
Lemma ex_lim_seq_const (a : U) :
  ex_lim_seq (fun n => a).
Proof.
  split with a.
  apply is_lim_seq_const.
Qed.

(** Increasing natural functions *)
Definition subseq_support phi := forall n, (phi n < phi (S n))%nat.

Lemma subseq_support_implies_incr : forall phi,
    subseq_support phi ->
    forall a b, (a < b)%nat -> (phi a < phi b)%nat.
Proof.
  intros phi Hsup a b.
  revert a; induction b; intros a Hlt; try now inversion Hlt.
  inversion Hlt.
  { apply Hsup. }
  transitivity (phi b).
  - apply IHb.
    apply H0.
  - apply Hsup.
Qed.

Lemma subseq_support_ge_id : forall phi,
    subseq_support phi ->
    forall n, (n <= phi n)%nat.
Proof.
  intros phi Hsup n.
  induction n; try lia.
  transitivity (S (phi n)); try lia.
  apply Hsup.
Qed.

Lemma eventually_subseq_loc_gt_id :
  forall phi N k, (forall n, (N <= n)%nat -> (phi n < phi (S n))%nat) ->
                  (k <= phi (N + k))%nat.
Proof.
  intros phi N k H.
  induction k; try lia.
  rewrite Nat.add_succ_r.
  transitivity (S (phi (N + k)))%nat; try lia.
  apply H.
  lia.
Qed.

Lemma eventually_subseq_loc_incr :
  forall phi N n k, (forall n, (N <= n)%nat -> (phi n < phi (S n))%nat) ->
                    (N <= n)%nat -> (n <= k)%nat ->
                    (phi n <= phi k)%nat.
Proof.
  intros phi N n k H; revert n; induction k; intros n Hln Hlk.
  - inversion Hlk; inversion Hln; subst; lia.
  - inversion Hlk; try lia; subst.
    etransitivity; [ apply IHk; try lia | ].
    apply Nat.lt_le_incl.
    apply H; lia.
Qed.
  
Lemma eventually_subseq_loc :
  forall phi,  eventually (fun n => (phi n < phi (S n))%nat) ->
               filterlim phi eventually eventually.
Proof.
  intros phi [N H].
  intros P [N' H'].
  split with (N + N')%nat.
  intros n Hle.
  apply H'.
  etransitivity; [ apply eventually_subseq_loc_gt_id; apply H | ].
  apply eventually_subseq_loc_incr with N; try lia.
  apply H.
Qed.  
  
Lemma eventually_subseq :
  forall phi,
    subseq_support phi ->
    filterlim phi eventually eventually.
Proof.
  intros phi H.
  apply eventually_subseq_loc.
  split with 0%nat.
  intros n _; apply H.
Qed.


(** Subsequences *)

Definition is_subseq {A} (v u : nat -> A) := { phi & prod (subseq_support phi) (forall n, v n = u (phi n))}.
  
Lemma is_lim_seq_subseq_eventually (u : nat -> U) (l : U) (phi : nat -> nat) :
  filterlim phi eventually eventually ->
  is_lim_seq u l ->
  is_lim_seq (fun n => u (phi n)) l.
Proof.
  intros Hes H.
  intros P Hloc.
  specialize (H P Hloc) as [N H].
  specialize (Hes (fun x => N <= x)%nat).
  assert (eventually (fun x : nat => (N <= x)%nat)).
  { split with N.
    intros; lia. }
  specialize (Hes H0); clear H0.
  destruct Hes as [N' Hes].
  split with N'.
  intros n Hle'.
  apply H.
  apply Hes.
  apply Hle'.
Qed.

Lemma is_lim_seq_subseq (u v : nat -> U) (l : U) :
  is_subseq v u ->
  is_lim_seq u l ->
  is_lim_seq v l.
Proof.
  intros [phi [sub_support Heqn]] Hlim.
  apply is_lim_seq_ext with (fun n => u (phi n)); [intros n; rewrite Heqn; reflexivity | ].
  apply is_lim_seq_subseq_eventually; try assumption.
  apply eventually_subseq.
  apply sub_support.
Qed.
  
Lemma ex_lim_seq_subseq (u v : nat -> U) :
  is_subseq v u ->
  ex_lim_seq u ->
  ex_lim_seq v.
Proof.
  intros Hsubseq [l Hlim].
  split with l.
  apply is_lim_seq_subseq with u; assumption.
Qed.

Lemma is_lim_seq_incr_1 (u : nat -> U) (l : U) :
  is_lim_seq u l <-> is_lim_seq (fun n => u (S n)) l.
Proof.
  split.
  - apply is_lim_seq_subseq.
    split with S.
    split; try auto.
    intro n.
    lia.
  - intros Hlim P H.
    specialize (Hlim P H) as [N Hlim].
    split with (S N).
    intros n Hle.
    destruct n; try now inversion Hle.
    apply Hlim; lia.
Qed.    

Lemma ex_lim_seq_incr_1 (u : nat -> U) :
  ex_lim_seq u <-> ex_lim_seq (fun n => u (S n)).
Proof.
  split; intros [l Hlim]; split with l.
  - apply ->is_lim_seq_incr_1; assumption.
  - apply is_lim_seq_incr_1; assumption.
Qed.

Lemma is_lim_seq_incr_n (u : nat -> U) (N : nat) (l : U) :
  is_lim_seq u l <-> is_lim_seq (fun n => u (n + N)%nat) l.
Proof.
  induction N.
  - split; intros Hlim; eapply is_lim_seq_ext; try apply Hlim; intros; simpl; rewrite Nat.add_0_r; reflexivity.
  - eapply iff_trans; [ apply IHN | ].
    eapply iff_trans; [ apply is_lim_seq_incr_1 | ].
    split; intros Hlim; eapply is_lim_seq_ext; try apply Hlim; intros; simpl; rewrite Nat.add_succ_r; reflexivity.
Qed.

Lemma ex_lim_seq_incr_n (u : nat -> U) (N : nat) :
  ex_lim_seq u <-> ex_lim_seq (fun n => u (n + N)%nat).
Proof.
  split; intros [l Hlim]; split with l.
  - apply ->is_lim_seq_incr_n; assumption.
  - apply <-is_lim_seq_incr_n; eassumption.
Qed.

End Lim_seq_US_def.

Section Lim_US_CT.
(** ** Image by a continuous function *)
Context {U V : UniformSpace}.
Lemma is_lim_seq_continuous (f : U -> V) (u : nat -> U) (l : U) :
  continuous f l -> is_lim_seq u l ->
  is_lim_seq (fun n => f (u n)) (f l).
Proof.
  intros Hc Hlim.
  intros P Hloc.
  specialize (Hlim (fun x => P (f x))).
  assert (locally l (fun x => P (f x))) as Hlocf.
  { apply Hc.
    apply Hloc. }
  specialize (Hlim Hlocf).
  destruct Hlim as [N Hlim].
  split with N.
  apply Hlim.
Qed.
End Lim_US_CT.

(** Unicity *)
Section Lim_US_Unicity.
  
Context {U : UniformSpace}.
Hypothesis all_ball_eq : forall (x y : U), (forall (eps : posreal), ball x eps y) -> x = y.

Lemma is_lim_seq_unique (u : nat -> U) (l1 l2 : U) :
  is_lim_seq u l1 -> is_lim_seq u l2 ->
  l1 = l2.
Proof.
  intros Hlim1 Hlim2.
  apply all_ball_eq.
  intros eps.
  specialize (Hlim1 (fun x => ball l1 (pos_div_2 eps) x)).
  assert (locally l1 (fun x => ball l1 (pos_div_2 eps) x)).
  { split with (pos_div_2 eps); auto. }
  specialize (Hlim1 H); clear H.
  destruct Hlim1 as [N Hlim1].
  specialize (Hlim2 (fun x => ball l2 (pos_div_2 eps) x)).
  assert (locally l2 (fun x => ball l2 (pos_div_2 eps) x)).
  { split with (pos_div_2 eps); auto. }
  specialize (Hlim2 H); clear H.
  destruct Hlim2 as [N2 Hlim2].
  destruct eps; simpl in *.
  replace pos with (pos / 2 + pos / 2) by lra.
  apply ball_triangle with (u (Nat.max N N2)).
  - apply Hlim1; lia.
  - apply ball_sym; apply Hlim2; lia.
Qed.
End Lim_US_Unicity.

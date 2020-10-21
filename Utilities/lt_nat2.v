Require Import Lt.
Require Import Wf_nat.

Inductive lt_nat2 : (nat * nat) -> (nat * nat) -> Prop :=
| fst_lt2 : forall a b c d, a < b -> lt_nat2 (a , c) (b, d)
| snd_lt2 : forall a b c, b < c -> lt_nat2 (a, b) (a, c).

Notation "a <2 b" := (lt_nat2 a b) (at level 90) : nat_scope.

Lemma wf_lt_nat2 : well_founded lt_nat2.
Proof.
  intros [n m].
  revert m.
  apply (lt_wf_ind n) ; clear n.
  intros n Hn m.
  apply (lt_wf_ind m); clear m.
  intros m Hm.
  apply Acc_intro.
  intros [n' m'] Hlt2.
  inversion Hlt2; subst.
  - apply Hn.
    apply H0.
  - apply Hm.
    apply H0.
Qed.

Lemma lt_nat2_wf_rect :
  forall n (P:(nat*nat) -> Type), (forall n, (forall m, m <2 n -> P m) -> P n) -> P n.
Proof.
intros n P Hw.
apply well_founded_induction_type with lt_nat2.
- apply wf_lt_nat2.
- assumption.
Qed.


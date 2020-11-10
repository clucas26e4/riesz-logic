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


Inductive lt_nat3 : (nat * nat * nat) -> (nat * nat * nat) -> Prop :=
| fst_lt3 : forall a b c d e f, a < b -> lt_nat3 (a , c, e) (b, d , f)
| snd_lt3 : forall a b c d e, b < c -> lt_nat3 (a, b, d) (a, c,e)
| trd_lt3 : forall a b c d, c < d -> lt_nat3 (a, b, c) (a, b,d).

Notation "a <3 b" := (lt_nat3 a b) (at level 90) : nat_scope.

Lemma wf_lt_nat3 : well_founded lt_nat3.
Proof.
  intros [[a b] c].
  revert b c.
  apply (lt_wf_ind a) ; clear a.
  intros a Ha b.
  apply (lt_wf_ind b); clear b.
  intros b Hb c.
  apply (lt_wf_ind c); clear c.
  intros c Hc.
  apply Acc_intro.
  intros [[a' b'] c'] Hlt3.
  inversion Hlt3; subst.
  - apply Ha.
    apply H0.
  - apply Hb.
    apply H0.
  - apply Hc.
    apply H0.
Qed.

Lemma lt_nat3_wf_rect :
  forall n (P:(nat*nat*nat) -> Type), (forall n, (forall m, m <3 n -> P m) -> P n) -> P n.
Proof.
intros n P Hw.
apply well_founded_induction_type with lt_nat3.
- apply wf_lt_nat3.
- assumption.
Qed.

Inductive lt_nat4 : (nat * nat * nat * nat) -> (nat * nat * nat * nat) -> Prop :=
| fst_lt4 : forall a b c d e f g h, a < b -> lt_nat4 (a , c, e, g) (b, d , f, h)
| snd_lt4 : forall a b c d e f g, b < c -> lt_nat4 (a, b, d,f) (a, c,e,g)
| trd_lt4 : forall a b c d e f, c < d -> lt_nat4 (a, b, c,e) (a, b,d,f)
| fth_lt4 : forall a b c d e, d < e -> lt_nat4 (a,b,c,d) (a,b,c,e).

Notation "a <4 b" := (lt_nat4 a b) (at level 90) : nat_scope.

Lemma wf_lt_nat4 : well_founded lt_nat4.
Proof.
  intros [[[a b] c] d].
  revert b c d.
  apply (lt_wf_ind a) ; clear a.
  intros a Ha b.
  apply (lt_wf_ind b); clear b.
  intros b Hb c.
  apply (lt_wf_ind c); clear c.
  intros c Hc d.
  apply (lt_wf_ind d); clear d.
  intros d Hd.
  apply Acc_intro.
  intros [[[a' b'] c'] d'] Hlt4.
  inversion Hlt4; subst.
  - apply Ha.
    apply H0.
  - apply Hb.
    apply H0.
  - apply Hc.
    apply H0.
  - apply Hd.
    apply H0.
Qed.

Lemma lt_nat4_wf_rect :
  forall n (P:(nat*nat*nat*nat) -> Type), (forall n, (forall m, m <4 n -> P m) -> P n) -> P n.
Proof.
intros n P Hw.
apply well_founded_induction_type with lt_nat4.
- apply wf_lt_nat4.
- assumption.
Qed.

Lemma lt_nat2_fst_eq_lt_nat3 : forall n a b,
    a <2 b ->
    (n, fst a, snd a) <3 (n, fst b, snd b).
Proof.
  intros n a b Hlt2; inversion Hlt2; subst; now constructor.
Qed.

Lemma lt_nat3_to_lt_nat4 : forall n m a b,
    a <3 b ->
    (a , n) <4 (b , m).
Proof.
  intros n m a b Hlt3; inversion Hlt3; try now constructor.
Qed.

Lemma lt_nat4_last :
  forall a n m,
    (n < m)%nat ->
    (a , n) <4 (a, m).
Proof.
  intros a n m Hlt.
  destruct a as [[a b] c]; apply fth_lt4.
  apply Hlt.
Qed.

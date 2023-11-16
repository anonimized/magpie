Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Hypothesis eq_ind_r : forall (A : Type)
                             (x : A)
                             (P : forall _ : A, Prop)
                             (_ : P x)
                             (y : A)
                             (_ : eq A y x),
                              P y.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint plus (n m : nat) {struct n} : nat :=
  match n return nat with
  | O    => m
  | S k  => S (plus k m)
  end.

Fixpoint mult (n m : nat) {struct n} : nat :=
  match n return nat with
  | O    => O
  | S k  => plus m (mult k m)
  end.

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m : nat, le n m -> le n (S m).

Definition lt : nat -> nat -> Prop :=
  fun n m : nat => le (S n) m.

Lemma plus_n_O : forall n : nat, n = plus n O.
Proof.
  intro n.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.

Lemma plus_n_Sm : forall n m : nat, S (plus n m) = plus n (S m).
Proof.
  intros n m.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma plus_assoc : forall a b c : nat, plus a (plus b c) = plus (plus a b) c.
Proof.
  intros a b c.
  induction a.
  simpl.
  reflexivity.
  simpl.
  rewrite IHa.
  reflexivity.
Qed.

Lemma plus_comm : forall n m : nat, plus n m = plus m n.
Proof.
  intro n.
  induction n.
  simpl.
  apply plus_n_O.
  intro m.
  simpl.
  replace (plus m (S n)) with (plus (S n) m).
  simpl.
  reflexivity.
  rewrite <- plus_n_Sm.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma plus_mult_n_plus_m : forall n m : nat, plus m (mult m n) = mult m (S n).
Proof.
  intros n m.
  induction m.
  simpl.
  reflexivity.
  simpl.
  rewrite plus_assoc.
  rewrite <- IHm.
  rewrite plus_assoc.
  replace (plus m n) with (plus n m).
  reflexivity.
  apply plus_comm.
Qed.

Lemma le_n_m_le_S_n_S_m : forall n m : nat, le n m -> le (S n) (S m).
Proof.
  induction 1.
  apply le_n.
  apply le_S.
  assumption.
Qed.

Lemma plus_le_compat : forall n m p q : nat, le n m -> le p q -> le (plus n p) (plus m q).
Proof.
  induction 1.
  intro H1.
  induction n; simpl.
  assumption.
  apply le_n_m_le_S_n_S_m.
  assumption.
  intro H2.
  simpl.
  apply le_S.
  apply IHle.
  assumption.
Qed.

Lemma le_n_Sn : forall n : nat, le n (S n).
Proof.
  intro n.
  apply le_S.
  apply le_n.
Qed.

Lemma le_O_n : forall n : nat, le O n.
Proof.
  intro n.
  induction n.
  apply le_n.
  apply le_S.
  assumption.
Qed.

Lemma le_trans : forall m n p : nat, le n m -> le m p -> le n p.
Proof.
  induction 2.
  assumption.
  apply le_S.
  assumption.
Qed.

Lemma mult_le_l : forall a b c : nat, le b c -> le (mult a b) (mult a c).
Proof.
  induction 1.
  apply le_n.
  rewrite <- plus_mult_n_plus_m.
  rewrite plus_comm.
  replace (mult a b) with (plus (mult a b) O).
  apply plus_le_compat.
  assumption.
  apply le_O_n.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Lemma mult_lt_l : forall a b c : nat, lt O a -> lt b c -> lt (mult a b) (mult a c).
Proof.
  unfold lt.
  induction a; intros; simpl.
  inversion H.
  rewrite plus_comm.
  rewrite plus_n_Sm.
  rewrite plus_comm.
  apply plus_le_compat.
  assumption.
  apply mult_le_l.
  apply le_trans with (S b).
  apply le_n_Sn.
  assumption.
Qed.

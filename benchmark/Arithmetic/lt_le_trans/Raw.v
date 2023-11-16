Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m : nat, le n m -> le n (S m).

Definition lt : nat -> nat -> Prop :=
  fun n m : nat => le (S n) m.

Lemma le_trans : forall m n p : nat, le n m -> le m p -> le n p.
Proof.
  induction 2.
  assumption.
  apply le_S.
  assumption.
Qed.

Lemma le_n_Sn : forall n : nat, le n (S n).
Proof.
  intro n.
  apply le_S.
  apply le_n.
Qed.

Lemma lt_le_trans : forall n m p : nat, lt n m -> le m p -> lt n p.
Proof.
  unfold lt.
  induction 1.
  auto.
  intro H1.
  apply IHle.
  apply le_trans with (S m).
  apply le_n_Sn.
  assumption.
Qed.

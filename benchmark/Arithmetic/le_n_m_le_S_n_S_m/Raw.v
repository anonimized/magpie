Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m : nat, le n m -> le n (S m).

Lemma le_n_m_le_S_n_S_m : forall n m : nat, le n m -> le (S n) (S m).
Proof.
  induction 1.
  apply le_n.
  apply le_S.
  assumption.
Qed.

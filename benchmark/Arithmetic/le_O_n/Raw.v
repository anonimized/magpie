Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m : nat, le n m -> le n (S m).

Lemma le_O_n : forall n : nat, le O n.
Proof.
  intro n.
  induction n.
  apply le_n.
  apply le_S.
  assumption.
Qed.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m : nat, le n m -> le n (S m).

Lemma le_trans : forall m n p : nat, le n m -> le m p -> le n p.
Proof.
  induction 2.
  assumption.
  apply le_S.
  assumption.
Qed.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m : nat, le n m -> le n (S m).

Lemma le_n_Sn : forall n : nat, le n (S n).
Proof.
  intro n.
  apply le_S.
  apply le_n.
Qed.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint plus (n m : nat) {struct n} : nat :=
  match n return nat with
  | O    => m
  | S k  => S (plus k m)
  end.

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

Lemma plus_le_compact : forall n m p q : nat, le n m -> le p q -> le (plus n p) (plus m q).
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

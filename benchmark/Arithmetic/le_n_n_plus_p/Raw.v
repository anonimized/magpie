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

Inductive le (n : nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m : nat, le n m -> le n (S m).

Lemma le_n_n_plus_p : forall p n : nat, le n (plus n p).
Proof.
  induction p.
  intro n.
  rewrite plus_comm.
  simpl.
  apply le_n.
  intro n.
  rewrite <- plus_n_Sm.
  apply le_S.
  apply IHp.
Qed.

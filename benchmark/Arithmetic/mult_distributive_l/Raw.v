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

Fixpoint mult (n m : nat) {struct n} : nat :=
  match n return nat with
  | O    => O
  | S k  => plus m (mult k m)
  end.

Lemma mult_n_O : forall n : nat, O = mult n O.
Proof.
  intro n.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn.
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

Lemma mult_comm : forall a b : nat, mult a b = mult b a.
Proof.
  intros a b.
  induction a.
  simpl.
  apply mult_n_O.
  simpl.
  rewrite IHa.
  apply plus_mult_n_plus_m.
Qed.

Theorem mult_distributive_l: forall (n m p : nat), mult n (plus m p) = plus (mult n m) (mult n p).
Proof.
  intros m n p.
  induction n.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
  simpl.
  rewrite mult_comm.
  simpl.
  rewrite mult_comm.
  rewrite IHn.
  pattern (mult m (S n)); rewrite mult_comm.
  simpl.
  rewrite mult_comm.
  apply plus_assoc.
Qed.

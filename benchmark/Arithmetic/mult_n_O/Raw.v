Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

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

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

Inductive or (A B : Prop) : Prop :=  or_introl : A -> or A B | or_intror : B -> or A B.

Lemma factor_is_O:
  forall n m : nat, or (n = O) (m = O) -> (mult n m) = O.
Proof.
  intros n m H.
  destruct H as [Hn | Hm].
  rewrite Hn; simpl; reflexivity.
  rewrite Hm; rewrite <- mult_n_O; reflexivity.
Qed.

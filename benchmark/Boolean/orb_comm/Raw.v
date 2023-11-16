Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Inductive bool : Set :=
  | true : bool
  | false : bool.

Definition ifb (b1 b2 b3 : bool) : bool :=
  match b1 return bool with
    | true => b2
    | false => b3
  end.

Definition orb (b1 b2 : bool) : bool := ifb b1 true b2.

Lemma orb_comm : forall b1 b2 : bool, orb b1 b2 = orb b2 b1.
Proof.
  intros b1 b2.
  destruct b1; destruct b2; simpl; reflexivity.
Qed.

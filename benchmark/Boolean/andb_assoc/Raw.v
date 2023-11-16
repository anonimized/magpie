Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Inductive bool : Set :=
  | true : bool
  | false : bool.

Definition ifb (b1 b2 b3 : bool) : bool :=
  match b1 return bool with
    | true => b2
    | false => b3
  end.

Definition andb (b1 b2 : bool) : bool := ifb b1 b2 false.

Lemma andb_assoc : forall b1 b2 b3 : bool, andb b1 (andb b2 b3) = andb (andb b1 b2) b3.
Proof.
  intros b1 b2 b3.
  destruct b1; destruct b2; destruct b3; simpl; reflexivity.
Qed.

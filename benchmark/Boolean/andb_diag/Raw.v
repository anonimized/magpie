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

Lemma andb_diag : forall b : bool, andb b b = b.
Proof.
  intro b.
  destruct b; simpl; reflexivity.
Qed.

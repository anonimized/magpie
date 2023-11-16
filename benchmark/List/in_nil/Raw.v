Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Inductive list (T : Set) : Set :=
  | nil : list T
  | cons : T -> list T -> list T.

Inductive False : Prop := .

Inductive or (A B : Prop) : Prop :=  or_introl : A -> or A B | or_intror : B -> or A B.

Fixpoint In (A : Set) (a : A) (l : list A) {struct l} : Prop :=
  match l as l0 return Prop with
    | nil  _     => False
    | cons _ b m => or (b = a) (In A a m)
end.

Theorem in_nil : forall (A : Set) (a : A), In A a (nil A) -> False.
Proof.
  intros A a H; simpl in * |- *; contradiction.
Qed.

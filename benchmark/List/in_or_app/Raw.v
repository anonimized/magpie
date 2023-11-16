Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Inductive list (T : Set) : Set :=
  | nil : list T
  | cons : T -> list T -> list T.

Fixpoint app (T : Set) (l1 l2 : list T) : list T :=
  match l1 with
    | nil _      => l2
    | cons _ h t => cons T h (app T t l2)
  end.

Inductive False : Prop := .

Inductive or (A B : Prop) : Prop :=  or_introl : A -> or A B | or_intror : B -> or A B.

Fixpoint In (A : Set) (a : A) (l : list A) {struct l} : Prop :=
  match l as l0 return Prop with
    | nil  _     => False
    | cons _ b m => or (b = a) (In A a m)
end.

Lemma in_or_app : forall (A : Set) (l m : list A) (a : A), 
  or (In A a l) (In A a m) -> In A a (app A l m).
Proof.
  intros A l m a H.
  induction l; simpl in * |- *.
  destruct H.
  contradiction.
  assumption.
  destruct H.
  destruct H.
  apply or_introl.
  assumption.
  apply or_intror.
  apply IHl.
  apply or_introl.
  assumption.
  apply or_intror.
  apply IHl.
  apply or_intror.
  assumption.
Qed.

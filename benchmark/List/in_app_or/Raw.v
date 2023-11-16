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

Inductive True : Prop := I : True.

Inductive or (A B : Prop) : Prop :=  or_introl : A -> or A B | or_intror : B -> or A B.

Fixpoint In (A : Set) (a : A) (l : list A) {struct l} : Prop :=
  match l as l0 return Prop with
    | nil  _     => False
    | cons _ b m => or (b = a) (In A a m)
end.

Lemma or_assoc_l: forall (A B C : Prop), or A (or B C) -> or (or A B) C.
Proof.
  intros A B C H.
  destruct H as [HA | HBC].
  apply or_introl; apply or_introl; assumption.
  destruct HBC.
  apply or_introl; apply or_intror; assumption.
  apply or_intror; assumption.
Qed.

Lemma in_app_or : forall (A : Set) (l m : list A) (a : A), In A a (app A l m) -> or (In A a l) (In A a m).
Proof.
  intros A l m a H.
  induction l; simpl in * |- *.
  apply or_intror; assumption.
  destruct H.
  apply or_introl; apply or_introl; assumption.
  apply IHl in H.
  apply or_assoc_l.
  apply or_intror.
  assumption.
Qed.

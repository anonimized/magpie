Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Inductive list (T : Set) : Set :=
  | nil : list T
  | cons : T -> list T -> list T.

Fixpoint app (T : Set) (l1 l2 : list T) : list T :=
  match l1 with
    | nil _      => l2
    | cons _ h t => cons T h (app T t l2)
  end.

Inductive False : Prop :=  .

Theorem app_cons_not_nil : forall (A : Set) (l l' : list A) (a : A), nil A = app A l (cons A a l') -> False.
Proof.
  destruct l as [| a l]; simpl; intros l' x H.
  discriminate H.
  discriminate H.
Qed.

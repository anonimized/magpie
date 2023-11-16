Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Hypothesis eq_ind_r : forall (A : Type)
                             (x : A)
                             (P : forall _ : A, Prop)
                             (_ : P x)
                             (y : A)
                             (_ : eq A y x),
                              P y.

Inductive list (T : Set) : Set :=
  | nil : list T
  | cons : T -> list T -> list T.

Fixpoint app (T : Set) (l1 l2 : list T) : list T :=
  match l1 with
    | nil _      => l2
    | cons _ h t => cons T h (app T t l2)
  end.

Inductive and (A B : Prop) : Prop :=  conj : A -> B -> and A B.

Theorem app_eq_nil : forall (A : Set) (l l':list A), app A l l' = nil A -> and (l = nil A) (l' = nil A).
Proof.
  destruct l as [|x l]; destruct l' as [|y l']; simpl.
  intro; apply conj; assumption.
  intro; apply conj.
  reflexivity.
  assumption.
  intro.
  apply conj.
  discriminate.
  reflexivity.
  intro H.
  discriminate H.
Qed.

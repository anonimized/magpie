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

Lemma app_assoc : forall (T : Set) (l1 l2 l3 : list T), app T l1 (app T l2 l3) = app T (app T l1 l2) l3.
Proof.
  intros T l1.
  induction l1.
  intros l2 l3.
  simpl.
  reflexivity.
  intros l2 l3.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

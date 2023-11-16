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

Fixpoint rev (T : Set) (l : list T) : list T :=
  match l with
    | nil _      => nil T
    | cons _ h t => app T (rev T t) (cons T h (nil T))
  end.

Lemma app_nil_end : forall (T : Set) (l : list T), app T l (nil T) = l.
Proof.
  intros T l.
  induction l.
  simpl. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

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

Theorem rev_app : forall (T : Set) (l1 l2 : list T), rev T (app T l1 l2) = app T (rev T l2) (rev T l1).
Proof.
  intros T l1.
  induction l1.
  intro l2.
  simpl.
  rewrite app_nil_end.
  reflexivity.
  intro l2.
  simpl.
  rewrite IHl1.
  rewrite app_assoc.
  reflexivity.
Qed.

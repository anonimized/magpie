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

Fixpoint map (T S : Set) (l : list T) (f : T -> S) : list S :=
  match l return list S with
    | nil _      => nil S
    | cons _ h t => cons S (f h) (map T S t f)
  end.

Theorem map_app : 
  forall (T S : Set) (l1 l2 : list T) (f : T -> S),
    map T S (app T l1 l2) f = app S (map T S l1 f) (map T S l2 f).
Proof.
  intros T S l1 l2 f.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Theorem rev_map :
  forall (T S : Set) (l : list T) (f : T -> S),
    rev S (map T S l f) = map T S (rev T l) f.
Proof.
  intros T S l.
  induction l as [| t tl IHtl].
  intro f.
  simpl.
  reflexivity.
  intro f.
  replace (map T S (cons T t tl) f) with (cons S (f t) (map T S tl f)).
  simpl.
  rewrite map_app.
  rewrite IHtl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

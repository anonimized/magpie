Inductive list (T : Set) : Set :=
  | nil : list T
  | cons : T -> list T -> list T.

Fixpoint app (T : Set) (l1 l2 : list T) : list T :=
  match l1 with
    | nil _      => l2
    | cons _ h t => cons T h (app T t l2)
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

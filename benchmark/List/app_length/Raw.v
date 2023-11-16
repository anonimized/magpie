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

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint length (T : Set) (l : list T) : nat :=
  match l with
    | nil _ => O
    | cons _ _ tl => S (length T tl)
  end.

Fixpoint plus (n m : nat) {struct n} : nat :=
  match n return nat with
  | O    => m
  | S k  => S (plus k m)
  end.

Lemma app_length : forall (A : Set) (l l' : list A), length A (app A l l') = plus (length A l) (length A l').
Proof.
  induction l as [| T l IHl]; intros; simpl.
  reflexivity.
  rewrite IHl.
  reflexivity.
Qed.

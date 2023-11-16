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

Inductive prod (A B : Type) : Type :=
  pair : A -> B -> prod A B.

Fixpoint zip (T1 T2 : Set) (l1 : list T1) (l2 : list T2) : list (prod T1 T2) :=
  match l1, l2 with
    | nil _, _ => nil (prod T1 T2)
    | _, nil _ => nil (prod T1 T2)
    | cons _ t1 tl1, cons _ t2 tl2 => cons (prod T1 T2) (pair T1 T2 t1 t2) (zip T1 T2 tl1 tl2)
  end.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint min (a b : nat) : nat :=
  match a, b with
    | O, _ => O
    | _, O => O
    | S a1, S b1 => S (min a1 b1)
  end.

Fixpoint length (A : Set) (l : list A) : nat :=
  match l with
    | nil _ => O
    | cons _ _ l' => S (length A l')
  end.

Theorem zip_preserves_length :
  forall (T1 T2 : Set) (l1 : list T1) (l2 : list T2),
    length (prod T1 T2) (zip T1 T2 l1 l2) = min (length T1 l1) (length T2 l2).
Proof.
  intros T1 T2 l1.
  induction l1; intro l2.
  simpl.
  reflexivity.
  induction l2; simpl.
  reflexivity.
  rewrite IHl1.
  reflexivity.
Qed.

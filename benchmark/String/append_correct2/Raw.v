Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Hypothesis eq_ind_r : forall (A : Type)
                             (x : A)
                             (P : forall _ : A, Prop)
                             (_ : P x)
                             (y : A)
                             (_ : eq A y x),
                              P y.

Inductive bool : Set :=
  | true : bool
  | false : bool.

Inductive ascii : Set :=
    Ascii : bool
            -> bool
            -> bool
            -> bool
            -> bool
            -> bool
            -> bool
            -> bool
            -> ascii.

Inductive string : Set :=
  | EmptyString : string
  | String : ascii -> string -> string.

Fixpoint append (s1 s2 : string) {struct s1} : string :=
  match s1 return string with
  | EmptyString => s2
  | String c s1' => String c (append s1' s2)
  end.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Fixpoint plus (n m : nat) {struct n} : nat :=
  match n return nat with
  | O    => m
  | S k  => S (plus k m)
  end.

Fixpoint length (s : string) : nat :=
  match s return nat with
  | EmptyString => O
  | String c s' => S (length s')
  end.

Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A.

Fixpoint get (n : nat) (s : string) {struct s} : option ascii :=
  match s with
  | EmptyString => None ascii
  | String c s' => match n with
                     | O => Some ascii c
                     | S n' => get n' s'
                   end
  end.

Lemma plus_n_O : forall n : nat, n = plus n O.
Proof.
  intro n.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.

Lemma plus_n_Sm : forall n m : nat, S (plus n m) = plus n (S m).
Proof.
  intros n m.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Theorem append_correct2 :
 forall (s1 s2 : string) (n : nat),
 get n s2 = get (plus n (length s1)) (append s1 s2).
Proof.
  intro s1; induction s1; intros s2 n; simpl.
  rewrite <- plus_n_O; reflexivity.
  rewrite <- plus_n_Sm.
  apply IHs1.
Qed.

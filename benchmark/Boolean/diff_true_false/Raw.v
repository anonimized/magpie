Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Inductive bool : Set :=
  | true : bool
  | false : bool.

Inductive False : Prop := .

Inductive True : Prop :=  I : True.

Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.

Definition not : Prop -> Prop := fun A : Prop => A -> False.

Lemma diff_true_false : not (eq bool true false).
Proof.
  unfold not.
  intro H.
  change (Is_true false).
  rewrite <- H; simpl; exact I.
Qed.

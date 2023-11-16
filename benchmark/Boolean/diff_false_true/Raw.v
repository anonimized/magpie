Inductive eq (A : Type) (x : A) : forall _ : A, Prop := eq_refl : eq A x x.

Definition eq_sym (A : Type) (x y : A) (H : eq A x y) :=
  match H in (eq _ _ a) return (eq A a x) with
    | eq_refl _ _ => eq_refl A x
  end.

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

Lemma diff_false_true : not (eq bool false true).
Proof.
  unfold not.
  intro H.
  apply eq_sym in H.
  apply diff_true_false.
  assumption.
Qed.

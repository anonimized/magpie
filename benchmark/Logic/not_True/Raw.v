Inductive False : Prop := .

Inductive True : Prop :=  I : True.

Definition not : Prop -> Prop := fun A : Prop => A -> False.

Theorem not_True : (not True) -> False.
Proof.
  unfold not.
  intro H.
  apply H.
  exact I.
Qed.

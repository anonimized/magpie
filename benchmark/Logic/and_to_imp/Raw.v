Inductive and (A B : Prop) : Prop :=  conj : A -> B -> and A B.

Theorem and_to_imp : forall P Q R : Prop, ((and P Q) -> R) -> (P -> (Q -> R)).
Proof.
  intros P Q R H1 H2 H3.
  apply H1.
  apply conj; assumption.
Qed.

Inductive and (A B : Prop) : Prop :=  conj : A -> B -> and A B.

Lemma and_assoc: forall (A B C : Prop), and (and A (and B C) -> and (and A B) C) (and (and A B) C -> and A (and B C)).
Proof.
  intros A B C.
  apply conj; intro H.
  destruct H as [HA].
  destruct H as [HB].
  apply conj; [apply conj; assumption | assumption].
  destruct H as [HAB].
  destruct HAB as [HA].
  apply conj; [assumption | apply conj; assumption].
Qed.

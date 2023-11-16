Inductive and (A B : Prop) : Prop :=  conj : A -> B -> and A B.

Lemma and_comm: forall (A B : Prop), and A B -> and B A.
Proof.
  intros A B H.
  destruct H as [HA].
  apply conj; assumption.
Qed.

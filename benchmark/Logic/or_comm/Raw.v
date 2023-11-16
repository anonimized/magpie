Inductive or (A B : Prop) : Prop :=  or_introl : A -> or A B | or_intror : B -> or A B.

Lemma or_comm: forall (A B : Prop), or A B -> or B A.
Proof.
  intros A B H.
  destruct H.
  apply or_intror; assumption.
  apply or_introl; assumption.
Qed.

Inductive or (A B : Prop) : Prop :=  or_introl : A -> or A B | or_intror : B -> or A B.

 Inductive and (A B : Prop) : Prop :=
    conj : forall (_ : A) (_ : B), and A B.

Lemma or_assoc: forall (A B C : Prop), and (or A (or B C) -> or (or A B) C) (or (or A B) C -> or A (or B C)).
Proof.
  intros A B C.
  apply conj; intro H.
  destruct H as [HA | HBC].
  apply or_introl; apply or_introl; assumption.
  destruct HBC.
  apply or_introl; apply or_intror; assumption.
  apply or_intror; assumption.
  destruct H as [HAB | HC].
  destruct HAB.
  apply or_introl; assumption.
  apply or_intror; apply or_introl; assumption.
  apply or_intror; apply or_intror; assumption.
Qed.

Inductive or (A B : Prop) : Prop :=  or_introl : A -> or A B | or_intror : B -> or A B.

Inductive and (A B : Prop) : Prop :=  conj : A -> B -> and A B.

Lemma or_distr_and : forall P Q R : Prop, or P (and Q R) -> and (or P Q) (or P R).
Proof.
  intros P Q R H.
  destruct H as [HP | HQR].
  apply conj; apply or_introl; assumption.
  destruct HQR.
  apply conj; apply or_intror; assumption.
Qed.

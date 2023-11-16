Definition not : Prop -> Prop := fun A : Prop => A -> False.

Inductive or (A B : Prop) : Prop :=  or_introl : A -> or A B | or_intror : B -> or A B.

Inductive and (A B : Prop) : Prop :=  conj : A -> B -> and A B.

Theorem demorgan2 : forall P Q : Prop, not (or P Q) -> and (not P) (not Q).
Proof.
  unfold not.
  intros P Q H.
  apply conj.
  intro HP; apply H; apply or_introl; assumption.
  intro HQ; apply H; apply or_intror; assumption.
Qed.

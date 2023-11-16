Theorem imp_trans : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R H1 H2 H3.
  apply H2; apply H1; assumption.
Qed.

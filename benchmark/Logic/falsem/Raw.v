Inductive False : Prop := .

Theorem falsem : forall P : Prop, False -> P.
Proof.
  intros P F.
  contradiction.
Qed.

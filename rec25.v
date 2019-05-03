Theorem great_peter : forall p q : Prop,
    p /\ q -> q /\ p.
Proof.
  intros p q pandq.
  destruct pandq as [ep eq].
  split;assumption.
Qed.

Print great_peter.
Check great_peter.

Theorem bad_andrew : forall p q : Prop,
    p \/ q -> q \/ p.
Proof.
  intros p q porq.
  destruct porq as [ep | eq].
  - right. assumption.
  - left. assumption.
Qed.

Print bad_andrew.
Check bad_andrew.

  


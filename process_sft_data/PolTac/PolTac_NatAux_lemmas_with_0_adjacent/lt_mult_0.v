Require Export Arith.

Theorem lt_mult_0: forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
intros a b; case a ; case b; simpl; auto with arith.
intros n H1 H2; absurd (0 < 0); auto with arith.

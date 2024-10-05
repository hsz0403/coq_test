Require Export Arith.

Theorem lt_mult_rev_0_l: forall a b, 0 < a * b -> 0 < a .
Proof.
intros a b; case a; simpl; auto with arith.

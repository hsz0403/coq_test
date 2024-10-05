Require Export Arith.

Theorem lt_mult_rev_0_r: forall a b, 0 < a * b -> 0 < b .
Proof.
intros a b; case b; simpl; auto with arith.
rewrite mult_0_r; auto with arith.

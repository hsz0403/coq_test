Require Export Arith.

Theorem gt_mult_rev_0_r: forall a b, a * b > 0 -> b > 0 .
Proof.
intros a b; case b; simpl; auto with arith.
rewrite mult_0_r; auto with arith.

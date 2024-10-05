Require Export Arith.

Theorem gt_mult_rev_0_l: forall a b, a * b > 0 -> a > 0.
Proof.
intros a b; case a; simpl; auto with arith.

Require Export Arith.

Theorem gt_mult_0: forall a b, a > 0 -> b > 0 -> a * b > 0.
Proof.
intros a b H1 H2; red; apply lt_mult_0; auto with arith.

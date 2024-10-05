Require Export Arith.

Theorem mult_gt_compat_l: forall n m p : nat, n > m -> p > 0 -> p * n > p * m.
Proof.
intros n m p H H1; red; apply mult_lt_compat_l; auto.

Require Export Arith.

Theorem mult_gt_compat_rev_l1: forall n m p : nat, p * n > p * m -> p > 0.
Proof.
intros n m p; case p; auto with arith.

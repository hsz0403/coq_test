Require Export Arith.

Theorem mult_gt_compat_rev_l2: forall n m p : nat, p * n > p * m -> n > m.
Proof.
intros n m p H; case (le_or_lt n m); auto with arith; intros H1.
absurd (p * n > p * m); auto with arith.

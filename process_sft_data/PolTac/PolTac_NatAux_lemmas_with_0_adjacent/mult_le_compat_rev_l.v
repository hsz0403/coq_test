Require Export Arith.

Theorem mult_le_compat_rev_l: forall n m p : nat, p * n <= p * m -> 0 < p -> n <= m.
Proof.
intros n m p H H1; case (le_or_lt n m); auto with arith; intros H2; absurd (p * n <= p * m); auto with arith.
apply lt_not_le; apply mult_lt_compat_l; auto.

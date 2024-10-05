Require Export Arith.

Theorem mult_lt_compat_rev_l2: forall n m p : nat, p * n < p * m -> n < m.
Proof.
intros n m p H; case (le_or_lt m n); auto with arith; intros H1.
absurd (p * n < p * m); auto with arith.
apply le_not_lt; apply mult_le_compat_l; auto.

Require Export Arith.

Theorem mult_ge_compat_l: forall n m p : nat, n >= m -> p * n >= p * m.
Proof.
Admitted.

Theorem mult_gt_compat_l: forall n m p : nat, n > m -> p > 0 -> p * n > p * m.
Proof.
Admitted.

Theorem mult_lt_compat_rev_l1: forall n m p : nat, p * n < p * m -> 0 < p.
Proof.
Admitted.

Theorem mult_lt_compat_rev_l2: forall n m p : nat, p * n < p * m -> n < m.
Proof.
intros n m p H; case (le_or_lt m n); auto with arith; intros H1.
absurd (p * n < p * m); auto with arith.
Admitted.

Theorem mult_gt_compat_rev_l1: forall n m p : nat, p * n > p * m -> p > 0.
Proof.
Admitted.

Theorem mult_gt_compat_rev_l2: forall n m p : nat, p * n > p * m -> n > m.
Proof.
intros n m p H; case (le_or_lt n m); auto with arith; intros H1.
Admitted.

Theorem mult_le_compat_rev_l: forall n m p : nat, p * n <= p * m -> 0 < p -> n <= m.
Proof.
intros n m p H H1; case (le_or_lt n m); auto with arith; intros H2; absurd (p * n <= p * m); auto with arith.
Admitted.

Theorem mult_ge_compat_rev_l: forall n m p : nat, p * n >= p * m -> 0 < p -> n >= m.
Proof.
intros n m p H H1; case (le_or_lt m n); auto with arith; intros H2; absurd (p * n >= p * m); auto with arith.
Admitted.

Theorem lt_mult_0: forall a b, 0 < a -> 0 < b -> 0 < a * b.
Proof.
intros a b; case a ; case b; simpl; auto with arith.
Admitted.

Theorem gt_mult_0: forall a b, a > 0 -> b > 0 -> a * b > 0.
Proof.
Admitted.

Theorem mult_lt_compat_l: forall n m p : nat, n < m -> 0 < p -> p * n < p * m.
Proof.
intros n m p H H1; repeat rewrite (mult_comm p); apply mult_lt_compat_r; auto.

Require Export Arith.

Theorem mult_lt_compat_l: forall n m p : nat, n < m -> 0 < p -> p * n < p * m.
Proof.
intros n m p H H1; repeat rewrite (mult_comm p); apply mult_lt_compat_r; auto.

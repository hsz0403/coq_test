Require Export Arith.

Theorem le_0_eq_0: forall n, n <= 0 -> n = 0.
Proof.
intros n; case n; auto with arith.

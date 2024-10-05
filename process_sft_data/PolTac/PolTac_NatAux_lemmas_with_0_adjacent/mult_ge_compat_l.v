Require Export Arith.

Theorem mult_ge_compat_l: forall n m p : nat, n >= m -> p * n >= p * m.
Proof.
intros n m p H; auto with arith.

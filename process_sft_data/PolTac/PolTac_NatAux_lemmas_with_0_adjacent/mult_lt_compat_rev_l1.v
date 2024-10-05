Require Export Arith.

Theorem mult_lt_compat_rev_l1: forall n m p : nat, p * n < p * m -> 0 < p.
Proof.
intros n m p; case p; auto with arith.

Require Export Reals.
Open Scope R_scope.

Theorem Rmult_le_compat_l_rev n m p : 0 < p -> p * n <= p * m -> n <= m.
Proof.
case (Rle_or_lt n m); trivial.
intros; absurd (p * n <= p * m); trivial.
now apply Rlt_not_le; apply Rmult_lt_compat_l.

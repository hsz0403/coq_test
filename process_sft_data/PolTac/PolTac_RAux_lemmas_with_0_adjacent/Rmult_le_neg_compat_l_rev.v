Require Export Reals.
Open Scope R_scope.

Theorem Rmult_le_neg_compat_l_rev n m p : p < 0 -> p * n <= p * m -> m <= n.
Proof.
case (Rle_or_lt m n); trivial.
intros; absurd (p * n <= p * m); trivial.
now apply Rlt_not_le; apply Rmult_lt_neg_compat_l.

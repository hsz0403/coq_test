Require Export Reals.
Open Scope R_scope.

Theorem Rmult_lt_compat_l_rev n m p : 0 < p -> p * n < p * m -> n < m.
Proof.
case (Rle_or_lt m n); trivial.
intros; absurd (p * n < p * m); trivial.
now apply Rle_not_lt; apply Rmult_le_compat_l; auto with real.

Require Export Reals.
Open Scope R_scope.

Theorem Rmult_ge_neg_compat_l_rev n m p : 0 > p -> p * n >= p * m -> m >= n.
Proof.
intros; apply Rle_ge; apply Rmult_le_neg_compat_l_rev with p; auto with real.

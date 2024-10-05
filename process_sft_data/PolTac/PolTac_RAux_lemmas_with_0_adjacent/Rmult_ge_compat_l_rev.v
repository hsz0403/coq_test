Require Export Reals.
Open Scope R_scope.

Theorem Rmult_ge_compat_l_rev n m p : p > 0 -> p * n >= p * m -> n >= m.
Proof.
intros; apply Rle_ge; apply Rmult_le_compat_l_rev with p; auto with real.

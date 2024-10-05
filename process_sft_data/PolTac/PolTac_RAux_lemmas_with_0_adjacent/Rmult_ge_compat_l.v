Require Export Reals.
Open Scope R_scope.

Theorem Rmult_ge_compat_l n m p : m >= n -> p >= 0 -> p * m >= p * n.
Proof.
intros; apply Rle_ge; auto with real.

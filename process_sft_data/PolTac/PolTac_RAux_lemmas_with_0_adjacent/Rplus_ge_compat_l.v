Require Export Reals.
Open Scope R_scope.

Theorem Rplus_ge_compat_l n m p : n >= m -> p + n >= p + m.
Proof.
now intros; apply Rle_ge; apply Rplus_le_compat_l; apply Rge_le.

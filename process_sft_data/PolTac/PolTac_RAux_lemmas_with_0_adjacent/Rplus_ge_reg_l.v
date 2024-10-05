Require Export Reals.
Open Scope R_scope.

Theorem Rplus_ge_reg_l n m p : p + n >= p + m -> n >= m.
Proof.
now intros; apply Rle_ge; apply Rplus_le_reg_l with p; apply Rge_le.

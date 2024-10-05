Require Export Reals.
Open Scope R_scope.

Theorem Rmult_gt_compat_l n m p : n > m -> p > 0 -> p * n > p * m.
Proof.
unfold Rgt; auto with real.

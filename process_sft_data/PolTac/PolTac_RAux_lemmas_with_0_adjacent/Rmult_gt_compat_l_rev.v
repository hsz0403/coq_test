Require Export Reals.
Open Scope R_scope.

Theorem Rmult_gt_compat_l_rev n m p : p > 0 -> p * n > p * m -> n > m.
Proof.
intros; apply Rmult_lt_compat_l_rev with p; auto with real.

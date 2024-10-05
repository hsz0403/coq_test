Require Export Reals.
Open Scope R_scope.

Theorem Rmult_gt_neg_compat_l_rev n m p : 0 > p -> p * n > p * m -> m > n.
Proof.
intros; apply Rmult_lt_neg_compat_l_rev with p; auto with real.

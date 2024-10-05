Require Export Reals.
Open Scope R_scope.

Theorem Rgt_sign_neg_neg_rev x y : 0 > x -> x * y > 0 -> 0 > y.
Proof.
intros; apply Rlt_sign_neg_neg_rev with x; auto with real.

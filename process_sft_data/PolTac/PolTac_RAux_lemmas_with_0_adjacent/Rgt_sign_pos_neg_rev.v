Require Export Reals.
Open Scope R_scope.

Theorem Rgt_sign_pos_neg_rev x y : x > 0 -> 0 > x * y -> 0 > y.
Proof.
intros; apply Rlt_sign_pos_neg_rev with x; auto with real.

Require Export Reals.
Open Scope R_scope.

Theorem Rgt_sign_neg_pos x y : 0 > x -> y > 0 -> 0 > x * y.
Proof.
apply Rlt_sign_neg_pos; auto with real.

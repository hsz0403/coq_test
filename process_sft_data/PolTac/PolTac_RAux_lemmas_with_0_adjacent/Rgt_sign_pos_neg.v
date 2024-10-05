Require Export Reals.
Open Scope R_scope.

Theorem Rgt_sign_pos_neg x y : x > 0 -> 0 > y -> 0 > x * y.
Proof.
apply Rlt_sign_pos_neg; auto with real.

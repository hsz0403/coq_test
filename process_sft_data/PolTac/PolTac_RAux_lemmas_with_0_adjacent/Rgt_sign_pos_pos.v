Require Export Reals.
Open Scope R_scope.

Theorem Rgt_sign_pos_pos x y : x > 0 -> y > 0 -> x * y > 0.
Proof.
apply Rlt_sign_pos_pos; auto with real.

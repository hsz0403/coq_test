Require Export Reals.
Open Scope R_scope.

Theorem Rgt_sign_neg_neg x y : 0 > x -> 0 > y -> x * y > 0.
Proof.
intros; apply Rlt_sign_neg_neg; auto with real.

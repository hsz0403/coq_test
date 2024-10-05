Require Export Reals.
Open Scope R_scope.

Theorem Rlt_sign_neg_pos x y : x < 0 -> 0 < y -> x * y < 0.
Proof.
intros; apply Rlt_pos_neg.
replace (- (x * y)) with (-x * y) by ring.
now apply Rmult_lt_0_compat; auto with real.

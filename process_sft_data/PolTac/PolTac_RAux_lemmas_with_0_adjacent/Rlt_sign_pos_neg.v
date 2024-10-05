Require Export Reals.
Open Scope R_scope.

Theorem Rlt_sign_pos_neg x y : 0 < x -> y < 0 -> x * y < 0.
Proof.
intros; apply Rlt_pos_neg.
replace (- (x * y)) with (x * -y) by ring.
apply Rmult_lt_0_compat; trivial.
replace 0 with (-0); auto with real.

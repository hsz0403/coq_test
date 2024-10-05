Require Export Reals.
Open Scope R_scope.

Theorem Rlt_sign_pos_pos x y : 0 < x -> 0 < y -> 0 < x * y.
Proof.
intros; apply Rmult_lt_0_compat; auto with real.

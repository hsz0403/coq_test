Require Export Reals.
Open Scope R_scope.

Theorem Rle_sign_pos_pos x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
intros; apply Rmult_le_pos; auto with real.

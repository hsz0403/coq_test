Require Export Reals.
Open Scope R_scope.

Theorem Rge_sign_pos_neg x y : x >= 0 -> 0 >= y -> 0 >= x * y.
Proof.
intros; apply Rle_ge; apply Rle_sign_pos_neg; auto with real.

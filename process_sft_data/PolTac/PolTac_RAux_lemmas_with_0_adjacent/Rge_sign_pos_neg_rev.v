Require Export Reals.
Open Scope R_scope.

Theorem Rge_sign_pos_neg_rev x y : x > 0 -> 0 >= x * y -> 0 >= y.
Proof.
intros; apply Rle_ge; apply Rle_sign_pos_neg_rev with x; auto with real.

Require Export Reals.
Open Scope R_scope.

Theorem Rge_sign_neg_pos_rev x y : 0 > x -> 0 >= x * y -> y >= 0.
Proof.
intros; apply Rle_ge; apply Rle_sign_neg_pos_rev with x; auto with real.

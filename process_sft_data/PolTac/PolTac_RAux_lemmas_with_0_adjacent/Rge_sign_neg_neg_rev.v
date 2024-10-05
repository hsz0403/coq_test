Require Export Reals.
Open Scope R_scope.

Theorem Rge_sign_neg_neg_rev x y : 0 > x -> x * y >= 0 -> 0 >= y.
Proof.
intros; apply Rle_ge; apply Rle_sign_neg_neg_rev with x; auto with real.

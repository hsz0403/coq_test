Require Export Reals.
Open Scope R_scope.

Theorem Rge_sign_neg_neg x y : 0 >= x -> 0 >= y -> x * y >= 0.
Proof.
intros; apply Rle_ge; apply Rle_sign_neg_neg; auto with real.

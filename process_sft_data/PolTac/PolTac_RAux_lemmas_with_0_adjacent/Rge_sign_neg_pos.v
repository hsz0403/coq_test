Require Export Reals.
Open Scope R_scope.

Theorem Rge_sign_neg_pos x y : 0 >= x -> y >= 0 -> 0 >= x * y.
Proof.
intros; apply Rle_ge; apply Rle_sign_neg_pos; auto with real.

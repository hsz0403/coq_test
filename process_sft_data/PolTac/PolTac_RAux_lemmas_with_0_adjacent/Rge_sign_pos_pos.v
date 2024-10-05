Require Export Reals.
Open Scope R_scope.

Theorem Rge_sign_pos_pos x y : x >= 0 -> y >= 0 -> x * y >= 0.
Proof.
intros; apply Rle_ge; apply Rle_sign_pos_pos; auto with real.

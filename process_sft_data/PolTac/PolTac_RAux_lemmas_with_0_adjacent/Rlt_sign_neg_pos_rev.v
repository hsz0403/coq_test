Require Export Reals.
Open Scope R_scope.

Theorem Rlt_sign_neg_pos_rev x y : x < 0 -> x * y < 0 -> 0 < y.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (x * y < 0); trivial.
apply Rle_not_lt;apply Rle_sign_neg_neg; auto with real.

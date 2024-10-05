Require Export Reals.
Open Scope R_scope.

Theorem Rle_sign_neg_neg_rev x y : x < 0 -> 0 <= x * y -> y <= 0.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (0 <= x * y); trivial.
now apply Rlt_not_le;apply Rlt_sign_neg_pos.

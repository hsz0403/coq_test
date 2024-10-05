Require Export Reals.
Open Scope R_scope.

Theorem Rle_sign_pos_neg_rev x y : 0 < x -> x * y <= 0 -> y <= 0.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (x * y <= 0); trivial.
now apply Rlt_not_le;apply Rlt_sign_pos_pos.

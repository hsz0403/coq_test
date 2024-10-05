Require Export Reals.
Open Scope R_scope.

Theorem Rle_sign_neg_pos_rev x y : x < 0 -> x * y <= 0 -> 0 <= y.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (x * y <= 0); trivial.
now apply Rlt_not_le;apply Rlt_sign_neg_neg.

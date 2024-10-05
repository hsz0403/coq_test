Require Export Reals.
Open Scope R_scope.

Theorem Rle_sign_pos_pos_rev x y : 0 < x -> 0 <= x * y -> 0 <= y.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (0 <= x * y); trivial.
now apply Rlt_not_le;apply Rlt_sign_pos_neg.

Require Export Reals.
Open Scope R_scope.

Theorem Rlt_sign_neg_neg_rev x y : x < 0 -> 0 < x * y -> y < 0.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (0 < x * y); trivial.
apply Rle_not_lt;apply Rle_sign_neg_pos; auto with real.

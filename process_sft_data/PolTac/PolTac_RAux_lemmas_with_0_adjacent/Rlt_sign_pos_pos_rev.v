Require Export Reals.
Open Scope R_scope.

Theorem Rlt_sign_pos_pos_rev x y : 0 < x -> 0 < x * y -> 0 < y.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (0 < x * y); trivial.
apply Rle_not_lt;apply Rle_sign_pos_neg; auto with real.

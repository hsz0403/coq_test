Require Export Reals.
Open Scope R_scope.

Theorem Rlt_sign_pos_neg_rev x y : 0 < x -> x * y < 0 -> y < 0.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (x * y < 0); trivial.
apply Rle_not_lt;apply Rle_sign_pos_pos; auto with real.

Require Export Reals.
Open Scope R_scope.

Theorem Rle_sign_neg_neg x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof.
intros; replace (x * y) with (-x * -y) by ring.
now apply Rmult_le_pos; auto with real.

Require Export Reals.
Open Scope R_scope.

Theorem Rle_sign_pos_neg x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof.
intros; apply Rle_pos_neg.
replace (- (x * y)) with (x * -y) by ring.
now apply Rmult_le_pos; auto with real.

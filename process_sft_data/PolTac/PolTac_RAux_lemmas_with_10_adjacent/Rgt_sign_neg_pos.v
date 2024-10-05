Require Export Reals.
Open Scope R_scope.

Theorem Rlt_sign_pos_neg x y : 0 < x -> y < 0 -> x * y < 0.
Proof.
intros; apply Rlt_pos_neg.
replace (- (x * y)) with (x * -y) by ring.
apply Rmult_lt_0_compat; trivial.
Admitted.

Theorem Rlt_sign_neg_pos x y : x < 0 -> 0 < y -> x * y < 0.
Proof.
intros; apply Rlt_pos_neg.
replace (- (x * y)) with (-x * y) by ring.
Admitted.

Theorem Rge_sign_neg_neg x y : 0 >= x -> 0 >= y -> x * y >= 0.
Proof.
Admitted.

Theorem Rge_sign_pos_pos x y : x >= 0 -> y >= 0 -> x * y >= 0.
Proof.
Admitted.

Theorem Rge_neg_pos x : 0 >= -x -> x >= 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
Admitted.

Theorem Rge_sign_neg_pos x y : 0 >= x -> y >= 0 -> 0 >= x * y.
Proof.
Admitted.

Theorem Rge_sign_pos_neg x y : x >= 0 -> 0 >= y -> 0 >= x * y.
Proof.
Admitted.

Theorem Rgt_sign_neg_neg x y : 0 > x -> 0 > y -> x * y > 0.
Proof.
Admitted.

Theorem Rgt_sign_pos_pos x y : x > 0 -> y > 0 -> x * y > 0.
Proof.
Admitted.

Theorem Rgt_neg_pos x : 0 > -x -> x > 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
Admitted.

Theorem Rgt_sign_pos_neg x y : x > 0 -> 0 > y -> 0 > x * y.
Proof.
Admitted.

Theorem Rle_sign_pos_pos_rev x y : 0 < x -> 0 <= x * y -> 0 <= y.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (0 <= x * y); trivial.
Admitted.

Theorem Rle_sign_neg_neg_rev x y : x < 0 -> 0 <= x * y -> y <= 0.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (0 <= x * y); trivial.
Admitted.

Theorem Rle_sign_pos_neg_rev x y : 0 < x -> x * y <= 0 -> y <= 0.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (x * y <= 0); trivial.
Admitted.

Theorem Rle_sign_neg_pos_rev x y : x < 0 -> x * y <= 0 -> 0 <= y.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (x * y <= 0); trivial.
Admitted.

Theorem Rge_sign_pos_pos_rev x y : x > 0 -> x * y >= 0 -> y >= 0.
Proof.
Admitted.

Theorem Rge_sign_neg_neg_rev x y : 0 > x -> x * y >= 0 -> 0 >= y.
Proof.
Admitted.

Theorem Rge_sign_pos_neg_rev x y : x > 0 -> 0 >= x * y -> 0 >= y.
Proof.
Admitted.

Theorem Rge_sign_neg_pos_rev x y : 0 > x -> 0 >= x * y -> y >= 0.
Proof.
Admitted.

Theorem Rlt_sign_pos_pos_rev x y : 0 < x -> 0 < x * y -> 0 < y.
Proof.
case (Rle_or_lt y 0); trivial.
intros; absurd (0 < x * y); trivial.
Admitted.

Theorem Rgt_sign_neg_pos x y : 0 > x -> y > 0 -> 0 > x * y.
Proof.
apply Rlt_sign_neg_pos; auto with real.

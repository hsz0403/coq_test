Require Export Reals.
Open Scope R_scope.

Theorem Rplus_ge_compat_l n m p : n >= m -> p + n >= p + m.
Proof.
Admitted.

Theorem Rplus_neg_reg_l a b c : a + b <> a + c -> b <> c.
Proof.
Admitted.

Theorem Rplus_ge_reg_l n m p : p + n >= p + m -> n >= m.
Proof.
Admitted.

Theorem Rle_sign_pos_pos x y : 0 <= x -> 0 <= y -> 0 <= x * y.
Proof.
Admitted.

Theorem Rle_sign_neg_neg x y : x <= 0 -> y <= 0 -> 0 <= x * y.
Proof.
intros; replace (x * y) with (-x * -y) by ring.
Admitted.

Theorem Rle_pos_neg x : 0 <= -x -> x <= 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
Admitted.

Theorem Rle_sign_pos_neg x y : 0 <= x -> y <= 0 -> x * y <= 0.
Proof.
intros; apply Rle_pos_neg.
replace (- (x * y)) with (x * -y) by ring.
Admitted.

Theorem Rle_sign_neg_pos x y : x <= 0 -> 0 <= y -> x * y <= 0.
Proof.
intros; apply Rle_pos_neg.
replace (- (x * y)) with (-x * y) by ring.
Admitted.

Theorem Rlt_sign_pos_pos x y : 0 < x -> 0 < y -> 0 < x * y.
Proof.
Admitted.

Theorem Rlt_sign_neg_neg x y : x < 0 -> y < 0 -> 0 < x * y.
Proof.
intros; replace (x * y) with (-x * -y) by ring.
Admitted.

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

Theorem Rlt_pos_neg x : 0 < -x -> x < 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
now apply Ropp_lt_contravar; rewrite Ropp_0; auto with real.

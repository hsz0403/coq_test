Require Export Reals.
Open Scope R_scope.

Theorem Rplus_eq_compat_l a b c : b = c -> a + b = a + c.
Proof.
Admitted.

Theorem Rplus_neg_compat_l a b c : b <> c -> a + b <> a + c.
Proof.
Admitted.

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

Theorem Rlt_pos_neg x : 0 < -x -> x < 0.
Proof.
intros; rewrite <- (Ropp_involutive 0), <- (Ropp_involutive x).
Admitted.

Theorem Rlt_sign_pos_neg x y : 0 < x -> y < 0 -> x * y < 0.
Proof.
intros; apply Rlt_pos_neg.
replace (- (x * y)) with (x * -y) by ring.
apply Rmult_lt_0_compat; trivial.
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

Theorem Rgt_sign_neg_pos x y : 0 > x -> y > 0 -> 0 > x * y.
Proof.
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

Theorem Rlt_sign_neg_neg_rev x y : x < 0 -> 0 < x * y -> y < 0.
Proof.
case (Rle_or_lt 0 y); trivial.
intros; absurd (0 < x * y); trivial.
Admitted.

Theorem Rlt_sign_neg_pos x y : x < 0 -> 0 < y -> x * y < 0.
Proof.
intros; apply Rlt_pos_neg.
replace (- (x * y)) with (-x * y) by ring.
now apply Rmult_lt_0_compat; auto with real.

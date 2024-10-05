Require Export Reals.
Open Scope R_scope.

Theorem Rgt_sign_neg_neg_rev x y : 0 > x -> x * y > 0 -> 0 > y.
Proof.
Admitted.

Theorem Rgt_sign_pos_neg_rev x y : x > 0 -> 0 > x * y -> 0 > y.
Proof.
Admitted.

Theorem Rgt_sign_neg_pos_rev x y : 0 > x -> 0 > x * y -> y > 0.
Proof.
Admitted.

Theorem Rmult_le_compat_l n m p : m <= n -> 0 <= p -> p * m <= p * n.
Proof.
Admitted.

Theorem Rmult_le_neg_compat_l n m p : m <= n -> p <= 0 -> p * n <= p * m.
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
Admitted.

Theorem Ropp_lt n m : m < n -> -n < -m.
Proof.
Admitted.

Theorem Rmult_lt_neg_compat_l n m p : m < n -> p < 0 -> p * n < p * m.
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
Admitted.

Theorem Ropp_ge n m : m >= n -> -n >= -m.
Proof.
Admitted.

Theorem Rmult_ge_compat_l n m p : m >= n -> p >= 0 -> p * m >= p * n.
Proof.
Admitted.

Theorem Rmult_ge_neg_compat_l n m p : m >= n -> 0 >= p -> p * n >= p * m.
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
Admitted.

Theorem Rmult_gt_compat_l n m p : n > m -> p > 0 -> p * n > p * m.
Proof.
Admitted.

Theorem Rmult_gt_neg_compat_l n m p : (m > n) -> (0 > p) -> (p * n > p * m).
Proof.
replace (p * n) with (-(-p * n)) by ring.
replace (p * m) with (-(-p * m)) by ring.
Admitted.

Theorem Rmult_le_compat_l_rev n m p : 0 < p -> p * n <= p * m -> n <= m.
Proof.
case (Rle_or_lt n m); trivial.
intros; absurd (p * n <= p * m); trivial.
Admitted.

Theorem Rmult_le_neg_compat_l_rev n m p : p < 0 -> p * n <= p * m -> m <= n.
Proof.
case (Rle_or_lt m n); trivial.
intros; absurd (p * n <= p * m); trivial.
Admitted.

Theorem Rmult_lt_compat_l_rev n m p : 0 < p -> p * n < p * m -> n < m.
Proof.
case (Rle_or_lt m n); trivial.
intros; absurd (p * n < p * m); trivial.
Admitted.

Theorem Rmult_lt_neg_compat_l_rev n m p : p < 0 -> p * n < p * m -> m < n.
Proof.
case (Rle_or_lt n m); trivial.
intros; absurd (p * n < p * m); trivial.
Admitted.

Theorem Rmult_ge_compat_l_rev n m p : p > 0 -> p * n >= p * m -> n >= m.
Proof.
Admitted.

Theorem Rmult_ge_neg_compat_l_rev n m p : 0 > p -> p * n >= p * m -> m >= n.
Proof.
Admitted.

Theorem Rmult_gt_compat_l_rev n m p : p > 0 -> p * n > p * m -> n > m.
Proof.
Admitted.

Theorem Rmult_gt_neg_compat_l_rev n m p : 0 > p -> p * n > p * m -> m > n.
Proof.
Admitted.

Theorem Ropp_gt n m : m > n -> -n > -m.
Proof.
auto with real.

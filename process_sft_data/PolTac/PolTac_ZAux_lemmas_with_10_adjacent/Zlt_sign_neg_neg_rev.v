Require Export ZArith.
Open Scope Z_scope.

Theorem Zgt_sign_pos_neg: forall x y: Z, (x > 0 -> 0 > y -> 0 > x * y)%Z.
Proof.
Admitted.

Theorem Zle_sign_pos_pos_rev: forall x y: Z, (0 < x -> 0 <= x * y -> 0 <= y)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (0 <= x * y)%Z; auto with zarith.
Admitted.

Theorem Zle_sign_neg_neg_rev: forall x y: Z, (x < 0 -> 0 <= x * y -> y <= 0)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (0 <= x * y)%Z; auto with zarith.
Admitted.

Theorem Zle_sign_pos_neg_rev: forall x y: Z, (0 < x -> x * y <= 0 -> y <= 0)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (x * y <= 0)%Z; auto with zarith.
Admitted.

Theorem Zle_sign_neg_pos_rev: forall x y: Z, (x < 0 -> x * y <= 0 -> 0 <= y)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (x * y <= 0)%Z; auto with zarith.
Admitted.

Theorem Zge_sign_pos_pos_rev: forall x y: Z, (x > 0 -> x * y >= 0 -> y >= 0)%Z.
Proof.
Admitted.

Theorem Zge_sign_neg_neg_rev: forall x y: Z, (0 > x -> x * y >= 0 -> 0 >= y)%Z.
Proof.
Admitted.

Theorem Zge_sign_pos_neg_rev: forall x y: Z, (x > 0 -> 0 >= x * y -> 0 >= y)%Z.
Proof.
Admitted.

Theorem Zge_sign_neg_pos_rev: forall x y: Z, (0 > x -> 0 >= x * y -> y >= 0)%Z.
Proof.
Admitted.

Theorem Zlt_sign_pos_pos_rev: forall x y: Z, (0 < x -> 0 < x * y -> 0 < y)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (0 < x * y)%Z; auto with zarith.
Admitted.

Theorem Zlt_sign_pos_neg_rev: forall x y: Z, (0 < x -> x * y < 0 -> y < 0)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (x * y < 0)%Z; auto with zarith.
Admitted.

Theorem Zlt_sign_neg_pos_rev: forall x y: Z, (x < 0 -> x * y < 0 -> 0 < y)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt y 0); auto with zarith.
intros H3; absurd (x * y < 0)%Z; auto with zarith.
Admitted.

Theorem Zgt_sign_pos_pos_rev: forall x y: Z, (x > 0 -> x * y > 0 -> y > 0)%Z.
Proof.
Admitted.

Theorem Zgt_sign_neg_neg_rev: forall x y: Z, (0 > x -> x * y > 0 -> 0 > y)%Z.
Proof.
Admitted.

Theorem Zgt_sign_pos_neg_rev: forall x y: Z, (x > 0 -> 0 > x * y -> 0 > y)%Z.
Proof.
Admitted.

Theorem Zgt_sign_neg_pos_rev: forall x y: Z, (0 > x -> 0 > x * y -> y > 0)%Z.
Proof.
Admitted.

Theorem Zmult_le_neg_compat_l: forall n m p : Z, (m <= n)%Z -> (p <= 0)%Z -> (p * n <= p * m)%Z.
Proof.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
Admitted.

Theorem Zopp_lt: forall n m, (m < n -> -n < -m)%Z.
Proof.
Admitted.

Theorem Zmult_lt_neg_compat_l: forall n m p : Z, (m < n)%Z -> (p < 0)%Z -> (p * n < p * m)%Z.
Proof.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
Admitted.

Theorem Zopp_ge: forall n m, (m >= n -> -n >= -m)%Z.
Proof.
Admitted.

Theorem Zlt_sign_neg_neg_rev: forall x y: Z, (x < 0 -> 0 < x * y -> y < 0)%Z.
Proof.
intros x y H1 H2; case (Zle_or_lt 0 y); auto with zarith.
intros H3; absurd (0 < x * y)%Z; auto with zarith.
apply Zle_not_lt;apply Zle_sign_neg_pos; auto with zarith.

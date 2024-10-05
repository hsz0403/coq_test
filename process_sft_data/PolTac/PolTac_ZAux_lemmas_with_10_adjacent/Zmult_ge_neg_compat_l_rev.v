Require Export ZArith.
Open Scope Z_scope.

Theorem Zmult_lt_neg_compat_l: forall n m p : Z, (m < n)%Z -> (p < 0)%Z -> (p * n < p * m)%Z.
Proof.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
Admitted.

Theorem Zopp_ge: forall n m, (m >= n -> -n >= -m)%Z.
Proof.
Admitted.

Theorem Zmult_ge_neg_compat_l: forall n m p : Z, (m >= n)%Z -> (0 >= p)%Z -> (p * n >= p * m)%Z.
Proof.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
Admitted.

Theorem Zopp_gt: forall n m, (m > n -> -n > -m)%Z.
Proof.
Admitted.

Theorem Zmult_gt_neg_compat_l: forall n m p : Z, (m > n)%Z -> (0 > p)%Z -> (p * n > p * m)%Z.
Proof.
intros n m p H1 H2; replace (p * n)%Z with (-(-p * n))%Z; auto with zarith; try ring.
replace (p * m)%Z with (-(-p * m))%Z; auto with zarith; try ring.
Admitted.

Theorem Zmult_le_compat_l_rev: forall n m p : Z, (0 < p)%Z -> (p * n <= p * m)%Z -> (n <= m)%Z.
Proof.
intros n m p H H1; case (Zle_or_lt n m); auto; intros H2.
absurd (p * n <= p * m)%Z; auto with zarith.
Admitted.

Theorem Zmult_le_neg_compat_l_rev: forall n m p : Z, (p < 0)%Z -> (p * n <= p * m)%Z -> (m <= n)%Z.
Proof.
intros n m p H H1; case (Zle_or_lt m n); auto; intros H2.
absurd (p * n <= p * m)%Z; auto with zarith.
Admitted.

Theorem Zmult_lt_compat_l_rev: forall n m p : Z, (0 < p)%Z -> (p * n < p * m)%Z -> (n < m)%Z.
Proof.
intros n m p H H1; case (Zle_or_lt m n); auto; intros H2.
absurd (p * n < p * m)%Z; auto with zarith.
Admitted.

Theorem Zmult_lt_neg_compat_l_rev: forall n m p : Z, (p < 0)%Z -> (p * n < p * m)%Z -> (m < n)%Z.
Proof.
intros n m p H H1; case (Zle_or_lt n m); auto; intros H2.
absurd (p * n < p * m)%Z; auto with zarith.
Admitted.

Theorem Zmult_ge_compat_l_rev: forall n m p : Z, (p > 0)%Z -> (p * n >= p * m)%Z -> (n >= m)%Z.
Proof.
Admitted.

Theorem Zmult_gt_compat_l_rev: forall n m p : Z, (p > 0)%Z -> (p * n > p * m)%Z -> (n > m)%Z.
Proof.
Admitted.

Theorem Zmult_gt_neg_compat_l_rev: forall n m p : Z, (0 > p)%Z -> (p * n > p * m)%Z -> (m > n)%Z.
Proof.
Admitted.

Theorem Zmult_ge_neg_compat_l_rev: forall n m p : Z, (0 > p)%Z -> (p * n >= p * m)%Z -> (m >= n)%Z.
Proof.
intros n m p H H1; apply Z.le_ge; apply Zmult_le_neg_compat_l_rev with p; auto with zarith.

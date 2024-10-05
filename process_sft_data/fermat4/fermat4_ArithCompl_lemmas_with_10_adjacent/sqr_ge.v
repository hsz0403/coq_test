Require Export Wf_nat.
Require Export ZArith.
Require Export Znumtheory.
Require Export Reals.
Open Scope Z_scope.
Unset Standard Proposition Elimination Names.
Definition is_sqr (n : Z) : Prop := 0 <= n /\ exists i : Z, i * i = n /\ 0 <= i.
Definition both_odd (x y : Z) := Zodd x /\ Zodd y.
Definition distinct_parity (a b : Z) := (Zeven a) /\ (Zodd b) \/ (Zodd a) /\ (Zeven b).
Definition R_prime (x y : Z) := 1 < x /\ 1 < y /\ x < y.
Definition f_Z (x : Z) := Z.abs_nat x.
Definition R_fact (x y : Z) := 1 < x /\ 1 < y /\ exists q : Z, y = q * x /\ 1 < q.
Definition R_p4 (x y : Z) := 0 <= x /\ 1 < y /\ exists d : Z, y = d * d * x /\ 1 < d.
Definition frac (a b : Z) := ((IZR a) / (IZR b))%R.
Definition is_rat (r : R) := exists pq : Z * Z, let (p,q) := pq in ~(q = 0) /\ r = (frac p q).
Definition is_ratp (c : R * R) := let (x,y) := c in (is_rat x) /\ (is_rat y).
Hint Resolve rel_prime_sym : zarith.
Hint Immediate sqr_0 sqr_pos sqr_spos sqr_sum sqr_sum2 sqr_sum3 sqr_sum4 sqr_sum5 sqr_sub1 sqr_sub2 sqr_sub3 sqr_ge : zarith.
Hint Immediate sqr_inv Rdiv_ge_0 : reals.

Lemma sqr_lt : forall a : Z, a <> 0 -> a <> 1 -> a < a * a.
Proof.
Admitted.

Lemma sqr_sum : forall a b : Z, b <> 0 -> a * a + b * b <> 0.
Proof.
intros; elim (Z.eq_dec a 0).
intro; rewrite a0; simpl; generalize (sqr_spos b H); intro; auto with zarith.
Admitted.

Lemma sqr_sum2 : forall a b : Z, 0 <= a * a + b * b.
Proof.
Admitted.

Lemma sqr_sum3 : forall a b : Z, b > 0 -> a * a + b * b > 0.
Proof.
Admitted.

Lemma sqr_sum4: forall a b : Z, a * a + b * b = 0 -> a = 0 /\ b = 0.
Proof.
Admitted.

Lemma sqr_sub1 : forall a b : Z, 0 <= b -> b <= a -> 0 <= a * a - b * b.
Proof.
Admitted.

Lemma sqr_sub2 : forall a b : Z, 0 <= b -> b < a -> 0 < a * a - b * b.
Proof.
Admitted.

Lemma sqr_sub3 : forall a b : Z, 0 < a -> 0 < b -> 0 < a * a - b * b -> b < a.
Proof.
Admitted.

Lemma sqr_2 : forall a : Z, 0 <= 2 * (a * a).
Proof.
Admitted.

Lemma sqr_gt : forall a b : Z, a >= 0 -> a < b -> a * a < b * b.
Proof.
intros; generalize (Z.ge_le _ _ H); clear H; intro; elim (Zle_lt_or_eq _ _ H); clear H; intro.
generalize (Zmult_lt_compat_l _ _ _ H H0); intro; assert (0 < b); auto with zarith; generalize (Zmult_lt_compat_r _ _ _ H2 H0); auto with zarith.
Admitted.

Lemma Zle_square_simpl : forall n m:Z, 0 <= n -> 0 <= m -> m * m <= n * n -> m <= n.
Proof.
Admitted.

Lemma neq_1 : forall u v m n : Z, m <> 0 -> n <> 0 -> u * u = m * m + n * n -> v * v = n * n - m * m -> u <> 1 /\ v <> 1.
Proof.
Admitted.

Lemma Zmult_eq_reg_l : forall z z1 z2, z * z1 = z * z2 -> z <> 0 -> z1 = z2.
Proof.
Admitted.

Lemma Zmult_neq_0 : forall a b : Z, a * b <> 0 -> a <> 0 /\ b <> 0.
Proof.
Admitted.

Lemma ndistp_eq : forall a : Z, ~ distinct_parity a a.
Proof.
Admitted.

Lemma sqr_sum5 : forall a b: Z, a <> 0 -> b <> 0 -> distinct_parity a b -> a + b < a * a + b * b.
Proof.
Admitted.

Lemma Zeven_def1 : forall z : Z, (Zeven z) -> exists k : Z, z = 2 * k.
Proof.
Admitted.

Lemma Zeven_def2 : forall z : Z, (exists k : Z, z = 2 * k) -> (Zeven z).
Proof.
Admitted.

Lemma Zodd_def1 : forall z : Z, (Zodd z) -> exists k : Z, z = 2 * k + 1.
Proof.
Admitted.

Lemma Zodd_def2 : forall z : Z, (exists k : Z, z = 2 * k + 1) -> (Zodd z).
Proof.
intros; elim H; intros; rewrite H0; elim x; intros; simpl; auto.
Admitted.

Lemma sqr_ge : forall a b : Z, a >= 0 -> a <= b -> a * a <= b * b.
Proof.
intros; apply Zmult_le_compat; auto with zarith.

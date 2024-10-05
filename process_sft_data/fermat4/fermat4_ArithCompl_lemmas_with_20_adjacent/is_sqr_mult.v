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

Lemma is_sqr_sqr : forall n: Z, is_sqr (n * n).
Proof.
Admitted.

Lemma sqr_0 : forall z : Z, z * z = 0 -> z = 0.
Proof.
Admitted.

Lemma sqr_compat : forall a b : Z, a * a = b * b -> a = b \/ a = -b.
Proof.
Admitted.

Lemma sqr_le : forall a : Z, a <= a * a.
Proof.
Admitted.

Lemma sqr_spos : forall z : Z, z <> 0 -> z * z > 0.
Proof.
intros; elim (not_Zeq _ _ H); clear H; intro.
unfold Z.lt in H; rewrite Zcompare_opp in H; fold (- (0) < - z) in H; simpl in H; cut (z * z = - z * - z); [ intro; rewrite H0; apply Zmult_gt_0_compat; auto with zarith | ring ].
Admitted.

Lemma sqr_poss : forall z : Z, 0 < z * z -> z <> 0.
Proof.
Admitted.

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

Lemma sqr_ge : forall a b : Z, a >= 0 -> a <= b -> a * a <= b * b.
Proof.
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

Lemma is_sqr_mult : forall p q : Z, is_sqr p -> is_sqr q -> is_sqr (p * q).
Proof.
unfold is_sqr; intros; elim H; clear H; intros; elim H0; clear H0; intros; elim H1; clear H1; intros; elim H1; clear H1; intros; elim H2; clear H2; intros; elim H2; clear H2; intros.
split; [ auto with zarith | exists (x * x0); rewrite <- H1; rewrite <- H2; intuition; ring ].

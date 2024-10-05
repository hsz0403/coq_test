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

Lemma gcd2_rel_prime : forall a b s w : Z, (Zis_gcd a b 2) -> a = 4 * s -> b = 2 * w -> rel_prime s w.
Proof.
Admitted.

Lemma relp_neq : forall m n : Z, m <> 1 -> m <> -1 -> rel_prime m n -> m <> n.
Proof.
Admitted.

Lemma prop2 : forall m n : Z, rel_prime m n -> rel_prime (m * m) (n * n).
Proof.
Admitted.

Lemma is_sqr_compat : forall k a : Z, k <> 0 -> is_sqr ((k * k) * a) -> is_sqr a.
Proof.
Admitted.

Lemma divide_trans : forall a b c : Z, (a | b) -> (b | c) -> (a | c).
Proof.
Admitted.

Lemma divide_sum : forall a b c : Z, (a | b) -> (a | b + c) -> (a | c).
Proof.
Admitted.

Lemma divide_mult_l : forall a b c : Z, c <> 0 -> (c * a | c * b) -> (a | b).
Proof.
Admitted.

Lemma divide_0 : forall z : Z, (0 | z) -> z = 0.
Proof.
Admitted.

Lemma divide_2 : forall z : Z, 0 <= z -> z <> 0 -> z <> 1 -> (z | 2) -> z = 2.
Proof.
Admitted.

Lemma divide_2b : forall z : Z, z <> 1 -> z <> -1 -> (z | 2) -> z = 2 \/ z = -2.
Proof.
Admitted.

Lemma divide_sqr : forall a b : Z, (a | b) -> (a * a | b * b).
Proof.
Admitted.

Lemma gcd2_relp_odd : forall u v : Z, Zodd u -> Zodd v -> rel_prime u v -> (Zis_gcd (u - v) (u + v) 2).
Proof.
Admitted.

Lemma rel_prime_opp : forall x y : Z, rel_prime x y -> rel_prime (-x) (-y).
Proof.
Admitted.

Lemma rel_prime_oppr : forall x y : Z, rel_prime x y -> rel_prime x (-y).
Proof.
Admitted.

Lemma rel_prime_2 : forall z : Z, Zodd z -> rel_prime 2 z.
Proof.
Admitted.

Lemma relp_mult1 : forall a b c d k: Z, 0 <= a -> 0 <= b -> 0 < c -> 0 <= d -> a = k * c -> b = k * d -> rel_prime a b -> k = 1.
Proof.
Admitted.

Lemma relp_parity : forall x y : Z, (rel_prime x y) -> (distinct_parity x y) \/ (both_odd x y).
Proof.
intros; unfold distinct_parity, both_odd; elim (Zeven_odd_dec x); intro; elim (Zeven_odd_dec y); intro; intuition.
Admitted.

Lemma relp_sum : forall m n : Z, (rel_prime (m + n) (m - n)) -> (rel_prime m n).
Proof.
intros; elim (rel_prime_dec m n); intro; try assumption.
Admitted.

Lemma prop1 : forall m n : Z, rel_prime m n -> distinct_parity m n -> rel_prime (m + n) (n - m).
Proof.
Admitted.

Lemma prop2b : forall m n : Z, rel_prime m n -> rel_prime m (m * m + n * n).
Proof.
Admitted.

Lemma divide_4 : forall a b : Z, (a * a * a * a | b * b * b * b) -> (a | b).
Proof.
intros a b (q,H); cut (is_sqr ((a * a * (a * a)) * q)); [ intro; elim (Z.eq_dec a 0); intro; try (rewrite a0 in H; rewrite (Zmult_comm q) in H; simpl in H; rewrite <- Zmult_assoc in H; do 2 (generalize (sqr_0 _ H); clear H; intro); rewrite H; apply Zdivide_0); cut (a * a <> 0); try (generalize (sqr_spos _ b0); solve [ auto with zarith ]); intro; generalize (is_sqr_compat _ _ H1 H0); clear H0; intro; elim H0; clear H0; intros; do 2 (elim H2; clear H2; intros); rewrite <- H2 in H; replace (x * x * (a * a * a * a)) with (a * a * x * (a * a * x)) in H; try ring; cut (0 <= a * a * x); try (apply Zmult_le_0_compat; try assumption; apply Z.ge_le; apply sqr_pos); intro; rewrite <- Zmult_assoc in H; elim (sqr_compat _ _ H); intro; try (elim (Z.eq_dec b 0); intro; [ rewrite a0; exists 0 | elimtype False; generalize (sqr_spos _ b1); intro ]; solve [ auto with zarith ]); cut (is_sqr (a * a * x)); try (unfold is_sqr; intuition; elim (Z_le_dec b 0); intro; [ exists (-b) | exists b ]; intuition; rewrite <- H5; ring); intro; generalize (is_sqr_compat _ _ b0 H6); clear H6; intro; elim H6; clear H6; intros; do 2 (elim H7; clear H7; intros); rewrite <- H7 in H5; replace (a * a * (x0 * x0)) with (a * x0 * (a * x0)) in H5; try ring; elim (sqr_compat _ _ H5); intro; [ exists x0 | exists (-x0) ]; rewrite H9; ring | split; [ replace (a * a * (a * a) * q) with (q * (a * a * a * a)); try ring; rewrite <- H; rewrite <- (Zmult_assoc (b * b)); apply Z.ge_le; apply sqr_pos | exists (b * b); split; [ rewrite Zmult_assoc; rewrite H; ring | apply Z.ge_le; apply sqr_pos ] ] ].

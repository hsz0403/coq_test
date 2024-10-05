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

Lemma divide_2b : forall z : Z, z <> 1 -> z <> -1 -> (z | 2) -> z = 2 \/ z = -2.
Proof.
Admitted.

Lemma divide_4 : forall a b : Z, (a * a * a * a | b * b * b * b) -> (a | b).
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

Lemma prop2c : forall m n : Z, rel_prime m n -> rel_prime m (m * m - n * n).
Proof.
Admitted.

Lemma prop3 : forall m n : Z, rel_prime (m * m) (n * n) -> rel_prime m n.
Proof.
Admitted.

Lemma R_prime_wf : well_founded R_prime.
Proof.
Admitted.

Lemma ind_prime : forall P : Z -> Prop, (forall x : Z, (forall y : Z, (R_prime y x -> P y)) -> P x) -> forall x : Z, P x.
Proof.
Admitted.

Lemma prime_dec_gen : forall a b : Z, 1 < b -> b < a -> (forall c : Z, b < c < a -> rel_prime c a) -> prime a \/ ~ prime a.
Proof.
Admitted.

Lemma prime_dec : forall a : Z, prime a \/ ~ prime a.
Proof.
Admitted.

Lemma not_prime_gen : forall a b : Z, 1 < a -> 1 < b -> b < a -> ~ prime a -> (forall c : Z, b < c < a -> rel_prime c a) -> exists q : Z, exists b : Z, a = q * b /\ 1 < q /\ 1 < b.
Proof.
induction b using ind_prime; intros.
destruct (Zdivide_dec b a) as [(q,H5)|n].
-
exists q; exists b; intuition; apply (Zmult_gt_0_lt_reg_r 1 q b); auto with zarith.
-
case (rel_prime_dec b a); intro.
*
case (Z.eq_dec b 2); intro.
+
absurd (prime a); try assumption.
apply prime_intro; auto; rewrite e in H4; rewrite e in r; generalize (rel_prime_1 a); intros; case (Z.eq_dec n0 1); intro; try (rewrite e0; assumption); case (Z.eq_dec n0 2); intro; try (rewrite e0; assumption); apply H4; auto with zarith.
+
assert (R_prime (b - 1) b) by (unfold R_prime; intuition).
assert (1 < b - 1) by auto with zarith.
assert (b - 1 < a) by auto with zarith.
assert (forall c : Z, (b - 1) < c < a -> rel_prime c a) by (intros; case (Z.eq_dec c b); intro; try (rewrite e; assumption); apply H4; auto with zarith).
elim (H _ H5 H0 H6 H7 H3 H8); intros; elim H9; clear H9; intros; exists x; exists x0; intuition.
*
elim (not_rel_prime1 _ _ n0); clear n0; intros; do 2 (elim H5; clear H5; intros); elim H6; clear H6; intros; destruct H7 as (q,H7).
assert (x <> 0) by (assert (a <> 0) by auto with zarith; rewrite H7 in H10; elim (Zmult_neq_0 _ _ H10); auto).
case (Z_le_dec 0 x); intro.
+
exists q; exists x; intuition; rewrite H7 in H0.
assert (0 < q * x) by auto with zarith.
assert (0 < x) by auto with zarith.
generalize (Zmult_lt_0_reg_r _ _ H12 H11); intro; case (Z.eq_dec q 1); auto with zarith; intro; elimtype False; rewrite e in H7; rewrite Zmult_1_l in H7; destruct H5 as (q0,H5); rewrite H5 in H1; cut (0 < q0 * x); auto with zarith; intro; generalize (Zmult_lt_0_reg_r _ _ H12 H14); intro; rewrite H7 in H2; rewrite <- (Zmult_1_l x) in H2; rewrite H5 in H2; generalize (Zmult_lt_reg_r _ _ _ H12 H2); auto with zarith.
+
exists (-q); exists (-x); intuition; try (rewrite H7; ring); rewrite H7 in H0; replace (q * x) with (-q * -x) in H0 by ring.
assert (0 < -q * -x) by auto with zarith.
assert (0 < -x) by auto with zarith.
Admitted.

Lemma not_prime : forall a : Z, 1 < a -> ~ prime a -> exists q : Z, exists b : Z, a = q * b /\ 1 < q /\ 1 < b.
Proof.
Admitted.

Lemma ind_fact : forall P : Z -> Prop, (forall x : Z, (forall y : Z, (R_fact y x -> P y)) -> P x) -> forall x : Z, P x.
Proof.
Admitted.

Lemma Zfact : forall a : Z, 1 < a -> exists b : Z, (b | a) /\ prime b.
Proof.
Admitted.

Lemma R_p4_wf : well_founded R_p4.
Proof.
Admitted.

Lemma ind_p4 : forall P : Z -> Prop, (forall x : Z, (forall y : Z, (R_p4 y x -> P y)) -> P x) -> forall x : Z, P x.
Proof.
Admitted.

Lemma sqr_prime1 : forall a : Z, is_sqr a -> forall b : Z, (b | a) -> prime b -> (b * b | a).
Proof.
Admitted.

Lemma sqr_prime2 : forall a b c : Z, (a | b) -> (a * a | b * c) -> prime a -> (a * a | b) \/ (a | c).
Proof.
Admitted.

Lemma prop4 : forall p q : Z, 0 <= p -> 0 <= q -> rel_prime p q -> is_sqr (p * q) -> is_sqr p /\ is_sqr q.
Proof.
Admitted.

Lemma prop4b : forall p q : Z, 0 <= p -> 0 <= q -> p <= q -> rel_prime p q -> is_sqr (p * (q * (q * q - p * p))) -> is_sqr p /\ is_sqr q /\ is_sqr (q * q - p * p).
Proof.
Admitted.

Lemma relp_pq1 : forall p q : Z, p >= 0 -> p <= q -> (rel_prime p q) -> (distinct_parity p q) -> (rel_prime (q * q - p * p) (p * p + q * q)).
Proof.
Admitted.

Lemma relp_pq2 : forall p q : Z, (rel_prime p q) -> (distinct_parity p q) -> (rel_prime (2 * p * q) (p * p + q * q)).
Proof.
Admitted.

Lemma not_IZR_0 : forall a : Z, (IZR a <> 0)%R -> a <> 0.
Proof.
Admitted.

Lemma sqr_inv : forall a b : Z, b <> 0 -> (1 + IZR a * / IZR b * (IZR a * / IZR b) <> 0)%R.
Proof.
intros; cut (1 + IZR a * / IZR b * (IZR a * / IZR b) = ((IZR a * IZR a + IZR b * IZR b) / (IZR b * IZR b)))%R.
intro; rewrite H0; unfold Rdiv; split_Rmult; [ discrR; apply sqr_sum; assumption | apply Rinv_neq_0_compat; split_Rmult; discrR; assumption ].
Admitted.

Lemma Rdiv_ge_0 : forall a b : R, (a >= 0 -> b > 0 -> a / b >= 0)%R.
Proof.
Admitted.

Lemma Rcross_prod : forall a b c d : R, (b <> 0 -> d <> 0 -> a / b = c / d -> a * d = b * c)%R.
Proof.
Admitted.

Lemma frac_eq : forall a b c d : Z, b <> 0 -> c <> 0 -> (frac a (b * c)) = (frac d c) -> a = b * d.
Proof.
Admitted.

Lemma frac_rat : forall a b : Z, b <> 0 -> (frac a b >= 0)%R -> (frac a b <= 1)%R -> a >= 0 /\ b > 0 /\ a <= b \/ a <= 0 /\ b < 0 /\ b <= a.
Proof.
Admitted.

Lemma frac_simp : forall a b c : Z, b <> 0 -> c <> 0 -> frac (c * a) (c * b) = frac a b.
Proof.
Admitted.

Lemma frac_opp : forall a b : Z, b <> 0 -> frac (-a) (-b) = frac a b.
Proof.
Admitted.

Lemma relp_rat : forall r : R, (is_rat r) -> (r >= 0)%R -> (r <= 1)%R -> exists pq : Z * Z, let (p,q) := pq in (p >= 0) /\ (q > 0) /\ (p <= q) /\ (rel_prime p q) /\ r = (frac p q).
Proof.
Admitted.

Lemma R_fact_wf : well_founded R_fact.
Proof.
apply (well_founded_lt_compat _ f_Z R_fact); unfold R_fact, f_Z; intros; apply Zabs_nat_lt; intuition; elim H2; clear H2; intros; elim H1; clear H1; intros; replace x with (1 * x); try ring; rewrite H1; apply Zmult_lt_compat_r; auto with zarith.

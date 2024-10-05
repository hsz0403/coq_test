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

Lemma relp_mult3 : forall a b c : Z, rel_prime (a * b) c -> rel_prime a c.
Proof.
Admitted.

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

Lemma R_fact_wf : well_founded R_fact.
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

Lemma prop1 : forall m n : Z, rel_prime m n -> distinct_parity m n -> rel_prime (m + n) (n - m).
Proof.
unfold rel_prime; intros; elim (distp_odd _ _ H0); clear H0; intros; elim (Zgcd_spec (m + n) (n - m)); intros; elim p; clear p; intros; elim (Z.eq_dec x 1); intro; [ rewrite a in H2; assumption | elimtype False; elim H2; clear H2; intros; generalize (Zdivide_plus_r _ _ _ H2 H4); ring_simplify (m + n + (n - m)); intro; generalize (Zdivide_minus_l _ _ _ H2 H4); ring_simplify (m + n - (n - m)); intro; elim (Zdivide_dec x 2); intro; [ elim (Z.eq_dec x 0); intro; [ rewrite a0 in a; clear a0; elim a; clear a; intros; auto with zarith | generalize (divide_2 _ H3 b0 b a); clear a; intro; rewrite H8 in H2; rewrite H8 in H4; clear x H3 b H5 H6 H7 b0 H8; destruct H2 as (q,H2), H4 as (q0,H3); rewrite Zmult_comm in H2; rewrite Zmult_comm in H3; generalize (Zeven_def2 _ (ex_intro (fun x => m + n = 2 * x) q H2)); clear q H2; intro; generalize (Zeven_not_Zodd _ H2); auto ] | elim (Zdivide_dec 2 x); intro; [ generalize (divide_trans _ _ _ a H2); clear H H1 x H3 b H2 H4 H5 H6 H7 b0 a; intro; destruct H as (q,H); rewrite Zmult_comm in H; generalize (Zeven_def2 _ (ex_intro (fun x => m + n = 2 * x) q H)); clear H; intro; generalize (Zeven_not_Zodd _ H); auto | generalize (prime_rel_prime _ prime_2 _ b1); intro; generalize (rel_prime_sym _ _ H8); clear H8; intro; generalize (Gauss _ _ _ H6 H8); clear H6; intro; generalize (Gauss _ _ _ H7 H8); clear H7; intro; cut (x <> -1); auto with zarith; intro; generalize (not_rel_prime2 _ _ _ H7 H6 b H9); auto ] ] ].

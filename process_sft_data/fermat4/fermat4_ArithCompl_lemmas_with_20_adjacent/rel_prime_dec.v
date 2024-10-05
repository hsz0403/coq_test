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

Lemma Zodd_0: forall n : Z, Zodd n -> n <> 0.
Proof.
Admitted.

Lemma Zodd_opp1 : forall a : Z, Zodd (-a) -> Zodd a.
Proof.
Admitted.

Lemma Zodd_opp2 : forall a : Z, Zodd a -> Zodd (-a).
Proof.
Admitted.

Lemma Zodd_sum1 : forall a b : Z, Zodd a -> Zodd b -> Zeven (a + b).
Proof.
Admitted.

Lemma Zodd_sum2 : forall a b : Z, Zodd a -> Zodd b -> Zeven (a - b).
Proof.
Admitted.

Lemma Zodd_sum3 : forall a b : Z, Zodd (a + 2 * b) -> Zodd a.
Proof.
Admitted.

Lemma Zodd_mult : forall u v : Z, Zodd u -> Zodd v -> (exists s : Z, (exists w : Z, (u - v = 4 * s /\ u + v = 2 * w) \/ (u - v = 2 * w /\ u + v = 4 * s))).
Proof.
intros; elim (Zodd_def1 u H); elim (Zodd_def1 v H0); intros k Hk k' Hk'; elim (Zeven_odd_dec k); elim (Zeven_odd_dec k'); intros.
elim (Zeven_def1 k a0); elim (Zeven_def1 k' a); intros t Ht t' Ht'; split with (t - t'); split with (2 * t + 2 * t' + 1); left; auto with zarith.
elim (Zeven_def1 k a); elim (Zodd_def1 k' b); intros t Ht t' Ht'; split with (t + t' + 1); split with (2 * t - 2 * t' + 1); right; auto with zarith.
elim (Zeven_def1 k' a); elim (Zodd_def1 k b); intros t Ht t' Ht'; split with (t + t' +1); split with (2 * t' - 2 * t - 1); right; auto with zarith.
Admitted.

Lemma Zeven_sqr1 : forall z : Z, Zeven z -> Zeven (z * z).
Proof.
Admitted.

Lemma Zeven_sqr2 : forall n, Zeven (n * n) -> Zeven n.
Proof.
Admitted.

Lemma Zodd_sqr1 : forall z : Z, Zodd z -> Zodd (z * z).
Proof.
Admitted.

Lemma Zodd_sqr2 : forall n, Zodd (n * n) -> Zodd n.
Proof.
Admitted.

Lemma distp_neq : forall p q : Z, distinct_parity p q -> p <> q.
Proof.
Admitted.

Lemma distp_sqr1 : forall p q : Z, (distinct_parity p q) -> (distinct_parity (p * p) (q * q)).
Proof.
Admitted.

Lemma distp_sqr2 : forall p q : Z, (distinct_parity (p * p) (q * q)) -> (distinct_parity p q).
Proof.
Admitted.

Lemma distp_odd : forall p q : Z, (distinct_parity p q) -> both_odd (p + q) (q - p).
Proof.
Admitted.

Lemma not_divide1 : forall a b : Z, a <> 1 -> a <> -1 -> b <> 0 -> ~(a * b | b).
Proof.
Admitted.

Lemma not_divide2 : forall a b : Z, 0 < a -> 0 < b -> b < a -> ~(a | b).
Proof.
Admitted.

Lemma rel_prime_1: forall a : Z, rel_prime 1 a.
Proof.
Admitted.

Lemma prime_2 : prime 2.
Proof.
Admitted.

Lemma rel_prime_sym : forall x y : Z, rel_prime x y -> rel_prime y x.
Proof.
Admitted.

Lemma not_rel_prime1 : forall x y : Z, ~ rel_prime x y -> exists d : Z, Zis_gcd x y d /\ d <> 1 /\ d <> -1.
Proof.
Admitted.

Lemma not_rel_prime2 : forall x y d : Z, (d | x) -> (d | y) -> d <> 1 -> d <> -1 -> ~ rel_prime x y.
Proof.
Admitted.

Lemma gcd_rel_prime : forall x y d : Z, Zis_gcd x y d -> exists a : Z, exists b : Z, x = d * a /\ y = d * b /\ rel_prime a b.
Proof.
Admitted.

Lemma relp_mult2 : forall a b : Z, rel_prime (a * b) a -> a = 1 \/ a = -1.
Proof.
Admitted.

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

Lemma rel_prime_dec : forall x y : Z, {rel_prime x y} + {~ rel_prime x y}.
Proof.
intros; unfold rel_prime; elim (Zgcd_spec x y); intros; elim p; clear p; intros; elim (Z.eq_dec x0 1); intro; [ rewrite a in H; left; assumption | right; red; intro; elim H; clear H; intros; elim H1; clear H1; intros; generalize (H5 _ H H2); clear H H2 H3 H1 H4 H5; intro; elim (Zdivide_1 _ H); clear H; intro; auto with zarith ].

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

Lemma gcd2_relp_odd : forall u v : Z, Zodd u -> Zodd v -> rel_prime u v -> (Zis_gcd (u - v) (u + v) 2).
Proof.
intros; elim (Zgcd_spec (u - v) (u + v)); intros; elim p; clear p; intros; elim H2; intros; generalize (Zdivide_plus_r _ _ _ H4 H5); ring_simplify (u - v + (u + v)); intro; generalize (Zdivide_opp_r _ _ H4); intro; generalize (Zdivide_plus_r _ _ _ H5 H8); ring_simplify (u + v + - (u - v)); clear H8; intro; generalize (Zodd_sum2 _ _ H H0); intro; elim (Zeven_def1 _ H9); clear H9; intros; rewrite Zmult_comm in H9; generalize (Zdivide_intro _ _ _ H9); clear x0 H9; intro; generalize (Zodd_sum1 _ _ H H0); intro; elim (Zeven_def1 _ H10); clear H10; intros; rewrite Zmult_comm in H10; generalize (Zdivide_intro _ _ _ H10); clear x0 H10; intro; generalize (H6 _ H9 H10); clear H9 H10; intro; elim H9; clear H9; intros; rewrite Zmult_comm in H9; rewrite H9 in H7; rewrite H9 in H8; cut (2 <> 0); auto with zarith; intro; generalize (divide_mult_l _ _ _ H10 H7); clear H7; intro; generalize (divide_mult_l _ _ _ H10 H8); clear H8 H10; intro; elim H1; intros; generalize (H12 _ H7 H8); intro; elim (Zdivide_1 _ H13); intro; try (elimtype False; rewrite H14 in H9; progress auto with zarith); rewrite H14 in H9; simpl in H9; rewrite H9 in H2; assumption.

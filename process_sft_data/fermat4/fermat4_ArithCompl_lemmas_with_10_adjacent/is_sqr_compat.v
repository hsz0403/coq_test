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

Lemma rel_prime_sym : forall x y : Z, rel_prime x y -> rel_prime y x.
Proof.
Admitted.

Lemma rel_prime_dec : forall x y : Z, {rel_prime x y} + {~ rel_prime x y}.
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

Lemma is_sqr_compat : forall k a : Z, k <> 0 -> is_sqr ((k * k) * a) -> is_sqr a.
Proof.
intros; elim H0; clear H0; intros; do 2 (elim H1; clear H1; intros); elim (rel_prime_dec x k); intro; [ generalize (prop2 _ _ a0); clear a0; intro; rewrite H1 in H3; elim (relp_mult2 _ _ H3); intro; [ rewrite H4 in H1; rewrite Zmult_1_l in H1; rewrite <- H1; unfold is_sqr; intuition; exists x; intuition | elimtype False; generalize (sqr_pos k); intro; rewrite H4 in H5; auto with zarith ] | elim (not_rel_prime1 _ _ b); clear b; intros; elim H3; clear H3; intros; elim H4; clear H4; intros; elim (gcd_rel_prime _ _ _ H3); clear H3; intros; do 2 (elim H3; clear H3; intros); elim H6; clear H6; intros; rewrite H3 in H1; rewrite H6 in H1; elim (Z.eq_dec x0 0); intro; try (elimtype False; rewrite a0 in H6; simpl in H6; auto); replace (x0 * x1 * (x0 * x1)) with (x0 * x0 * (x1 * x1)) in H1; try ring; replace (x0 * x2 * (x0 * x2) * a) with (x0 * x0 * (x2 * x2 * a)) in H1; try ring; generalize (sqr_spos _ b); clear b; intro; cut ((x1 * x1) = x2 * x2 * a); try (apply Zcompare_Eq_eq; rewrite (Zmult_compare_compat_l (x1 * x1) (x2 * x2 * a) (x0 * x0) H8); elim (Zcompare_Eq_iff_eq (x0 * x0 * (x1 * x1)) (x0 * x0 * (x2 * x2 * a))); auto); clear H1; intro; generalize (prop2 _ _ H7); clear H7; intro; rewrite H1 in H7; elim (relp_mult2 _ _ H7); intro; [ rewrite H9 in H1; rewrite Zmult_1_l in H1; rewrite <- H1; elim (Z_le_dec 0 x1); intro; [ unfold is_sqr; intuition; exists x1; intuition | split; [ apply Z.ge_le; apply sqr_pos | exists (-x1); intuition; ring ] ] | elimtype False; generalize (sqr_pos x2); intro; rewrite H9 in H10; auto with zarith ] ].

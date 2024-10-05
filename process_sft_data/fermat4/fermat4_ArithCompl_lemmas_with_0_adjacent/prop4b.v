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

Lemma prop4b : forall p q : Z, 0 <= p -> 0 <= q -> p <= q -> rel_prime p q -> is_sqr (p * (q * (q * q - p * p))) -> is_sqr p /\ is_sqr q /\ is_sqr (q * q - p * p).
Proof.
intros; generalize (prop2c _ _ H2); intro; generalize (rel_prime_oppr _ _ H4); clear H4; intro; replace (- (p * p - q * q)) with (q * q - p * p) in H4; try ring; generalize (rel_prime_sym _ _ H2); intro; generalize (prop2c _ _ H5); clear H5; intro; generalize (rel_prime_sym _ _ H4); clear H4; intro; generalize (rel_prime_sym _ _ H5); clear H5; intro; generalize (rel_prime_mult _ _ _ H4 H5); clear H4 H5; intro; generalize (rel_prime_sym _ _ H4); clear H4; intro; rewrite Zmult_assoc in H3; cut (0 <= p * q); auto with zarith; intro; cut (0 <= q * q - p * p); try (apply sqr_sub1; assumption); intro; generalize (prop4 _ _ H5 H6 H4 H3); clear H3 H4 H5 H6; intro; elim H3; clear H3; intros; generalize (prop4 _ _ H H0 H2 H3); tauto.

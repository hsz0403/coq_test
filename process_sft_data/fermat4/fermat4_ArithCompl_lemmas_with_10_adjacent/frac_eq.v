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

Lemma frac_eq : forall a b c d : Z, b <> 0 -> c <> 0 -> (frac a (b * c)) = (frac d c) -> a = b * d.
Proof.
unfold frac; intros; cut (IZR (b * c) <> 0%R); [ intro; cut (IZR c <> 0%R); [ intro; generalize (Rcross_prod _ _ _ _ H2 H3 H1); clear H1; intro; rewrite mult_IZR in H1; cut (IZR c * IZR a = IZR c * (IZR b * IZR d))%R; [ clear H1; intro; generalize (Rmult_eq_reg_l _ _ _ H1 H3); clear H1; intro; rewrite <- mult_IZR in H1; apply eq_IZR; assumption | rewrite (Rmult_comm (IZR c) (IZR a)); rewrite H1; ring ] | apply not_O_IZR; assumption ] | rewrite mult_IZR; split_Rmult; apply not_O_IZR; assumption ].

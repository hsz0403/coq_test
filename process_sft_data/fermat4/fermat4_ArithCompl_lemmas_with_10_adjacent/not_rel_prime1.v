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

Lemma rel_prime_dec : forall x y : Z, {rel_prime x y} + {~ rel_prime x y}.
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

Lemma not_rel_prime1 : forall x y : Z, ~ rel_prime x y -> exists d : Z, Zis_gcd x y d /\ d <> 1 /\ d <> -1.
Proof.
unfold rel_prime; intros; elim (Zgcd_spec x y); intros; elim p; clear p; intros; exists x0; split; [ assumption | split; [ elim (Z.eq_dec x0 1); intro; [ rewrite a in H0; auto | assumption ] | elim (Z.eq_dec x0 (-1)); intro; [ rewrite a in H0; generalize (Zis_gcd_opp _ _ _ H0); simpl; clear H0; intro; generalize (Zis_gcd_sym _ _ _ H0); auto | assumption ] ] ].

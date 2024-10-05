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

Lemma relp_mult1 : forall a b c d k: Z, 0 <= a -> 0 <= b -> 0 < c -> 0 <= d -> a = k * c -> b = k * d -> rel_prime a b -> k = 1.
Proof.
intros; rewrite H3 in H5; rewrite H4 in H5; rewrite H3 in H; clear H3 H4; elim H5; clear H5; intros; elim (Zdivide_1 k); auto with zarith; intro; rewrite H6 in H; clear H6; auto with zarith.

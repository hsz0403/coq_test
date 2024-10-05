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

Lemma relp_pq1 : forall p q : Z, p >= 0 -> p <= q -> (rel_prime p q) -> (distinct_parity p q) -> (rel_prime (q * q - p * p) (p * p + q * q)).
Proof.
intros; cut (rel_prime (p * p) (q * q)); [ clear H1; intro; cut (distinct_parity (p * p) (q * q)); [ clear H2; intro; apply rel_prime_sym; apply prop1; try apply sqr_ge; assumption | apply (distp_sqr1 _ _ H2) ] | generalize (rel_prime_mult _ _ _ H1 H1); clear H1; intro; generalize (rel_prime_sym _ _ H1); clear H1; intro; generalize (rel_prime_mult _ _ _ H1 H1); clear H1; intro; apply rel_prime_sym; assumption ].

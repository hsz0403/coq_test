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

Lemma neq_1 : forall u v m n : Z, m <> 0 -> n <> 0 -> u * u = m * m + n * n -> v * v = n * n - m * m -> u <> 1 /\ v <> 1.
Proof.
intros; case (Z.eq_dec u 1); intro; case (Z.eq_dec v 1); intro; try tauto; elimtype False; [ rewrite e in H1; simpl in H1; rewrite e0 in H2; simpl in H2; rewrite H2 in H1; cut (2 * (m * m) = 0); auto with zarith; intro; elim (Zmult_integral _ _ H3); auto with zarith; intro; generalize (sqr_0 _ H4); auto | rewrite e in H1; simpl in H1; generalize (sqr_pos m); intro; generalize (sqr_pos n); intro; cut (m * m = 0 \/ n * n = 0); try omega; intro; elim H5; clear H5; intros; generalize (sqr_0 _ H5); auto | rewrite e in H2; simpl in H2; replace (n * n - m * m) with ((n + m) * (n - m)) in H2; try ring; symmetry in H2; elim (Zmult_1_inversion_l _ _ H2); intro; rewrite Zmult_comm in H2; elim (Zmult_1_inversion_l _ _ H2); auto with zarith ].

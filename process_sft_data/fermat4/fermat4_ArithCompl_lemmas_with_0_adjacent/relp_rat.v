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

Lemma relp_rat : forall r : R, (is_rat r) -> (r >= 0)%R -> (r <= 1)%R -> exists pq : Z * Z, let (p,q) := pq in (p >= 0) /\ (q > 0) /\ (p <= q) /\ (rel_prime p q) /\ r = (frac p q).
Proof.
intros; elim H; clear H; induction x; intro; elim H; clear H; intros; elim (rel_prime_dec a b); intro; [ rewrite H2 in H0; rewrite H2 in H1; elim (frac_rat _ _ H H0 H1); intro; [ exists (a, b); tauto | exists (-a, -b); intuition; [ apply rel_prime_opp | rewrite (frac_opp a b H) ]; assumption ] | elim (not_rel_prime1 _ _ b0); clear b0; intros; elim H3; clear H3; intros; elim (gcd_rel_prime _ _ _ H3); clear H3; intros; elim H3; clear H3; intros; elim H3; clear H3; intros; elim H5; clear H5; intros; rewrite H5 in H; elim (Zmult_neq_0 _ _ H); clear H; intros; rewrite H3 in H2; rewrite H5 in H2; rewrite (frac_simp x0 _ _ H7 H) in H2; rewrite H2 in H0; rewrite H2 in H1; elim (frac_rat _ _ H7 H0 H1); intro; [ exists (x0, x1); intuition | exists (-x0, -x1); intuition; [ apply rel_prime_opp | rewrite (frac_opp x0 x1 H7) ]; assumption ] ].

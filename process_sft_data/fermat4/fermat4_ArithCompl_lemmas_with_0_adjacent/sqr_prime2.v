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

Lemma sqr_prime2 : forall a b c : Z, (a | b) -> (a * a | b * c) -> prime a -> (a * a | b) \/ (a | c).
Proof.
intros; elim H; intros q H2; elim H0; intros q0 H3; rewrite H2 in H3; elim H1; intros; replace (q * a * c) with (a * (q * c)) in H3; try ring; replace (q0 * (a * a)) with (a * (q0 * a)) in H3; try ring; cut (a <> 0); auto with zarith; intro; generalize (Zmult_eq_reg_l _ _ _ H3 H6); clear H3; intro; generalize (Zdivide_intro _ _ _ H3); clear H3; intro; elim (prime_mult _ H1 _ _ H3); try tauto; intro; elim H7; intros; rewrite H8 in H2; rewrite <- Zmult_assoc in H2; generalize (Zdivide_intro _ _ _ H2); tauto.

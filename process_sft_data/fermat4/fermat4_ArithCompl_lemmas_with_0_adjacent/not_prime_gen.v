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

Lemma not_prime_gen : forall a b : Z, 1 < a -> 1 < b -> b < a -> ~ prime a -> (forall c : Z, b < c < a -> rel_prime c a) -> exists q : Z, exists b : Z, a = q * b /\ 1 < q /\ 1 < b.
Proof.
induction b using ind_prime; intros.
destruct (Zdivide_dec b a) as [(q,H5)|n].
-
exists q; exists b; intuition; apply (Zmult_gt_0_lt_reg_r 1 q b); auto with zarith.
-
case (rel_prime_dec b a); intro.
*
case (Z.eq_dec b 2); intro.
+
absurd (prime a); try assumption.
apply prime_intro; auto; rewrite e in H4; rewrite e in r; generalize (rel_prime_1 a); intros; case (Z.eq_dec n0 1); intro; try (rewrite e0; assumption); case (Z.eq_dec n0 2); intro; try (rewrite e0; assumption); apply H4; auto with zarith.
+
assert (R_prime (b - 1) b) by (unfold R_prime; intuition).
assert (1 < b - 1) by auto with zarith.
assert (b - 1 < a) by auto with zarith.
assert (forall c : Z, (b - 1) < c < a -> rel_prime c a) by (intros; case (Z.eq_dec c b); intro; try (rewrite e; assumption); apply H4; auto with zarith).
elim (H _ H5 H0 H6 H7 H3 H8); intros; elim H9; clear H9; intros; exists x; exists x0; intuition.
*
elim (not_rel_prime1 _ _ n0); clear n0; intros; do 2 (elim H5; clear H5; intros); elim H6; clear H6; intros; destruct H7 as (q,H7).
assert (x <> 0) by (assert (a <> 0) by auto with zarith; rewrite H7 in H10; elim (Zmult_neq_0 _ _ H10); auto).
case (Z_le_dec 0 x); intro.
+
exists q; exists x; intuition; rewrite H7 in H0.
assert (0 < q * x) by auto with zarith.
assert (0 < x) by auto with zarith.
generalize (Zmult_lt_0_reg_r _ _ H12 H11); intro; case (Z.eq_dec q 1); auto with zarith; intro; elimtype False; rewrite e in H7; rewrite Zmult_1_l in H7; destruct H5 as (q0,H5); rewrite H5 in H1; cut (0 < q0 * x); auto with zarith; intro; generalize (Zmult_lt_0_reg_r _ _ H12 H14); intro; rewrite H7 in H2; rewrite <- (Zmult_1_l x) in H2; rewrite H5 in H2; generalize (Zmult_lt_reg_r _ _ _ H12 H2); auto with zarith.
+
exists (-q); exists (-x); intuition; try (rewrite H7; ring); rewrite H7 in H0; replace (q * x) with (-q * -x) in H0 by ring.
assert (0 < -q * -x) by auto with zarith.
assert (0 < -x) by auto with zarith.
generalize (Zmult_lt_0_reg_r _ _ H12 H11); intro; case (Z.eq_dec q (-1)); auto with zarith; intro; elimtype False; rewrite e in H7; rewrite Zmult_comm in H7; rewrite <- Zopp_eq_mult_neg_1 in H7; destruct H5 as (q0,H5); replace (q0 * x) with (-q0 * -x) in H5 by ring; rewrite H5 in H1; assert (0 < -q0 * -x) by auto with zarith; generalize (Zmult_lt_0_reg_r _ _ H12 H14); intro; rewrite <- (Zmult_1_l a) in H2; rewrite H7 in H2; rewrite H5 in H2; generalize (Zmult_lt_reg_r _ _ _ H12 H2); auto with zarith.

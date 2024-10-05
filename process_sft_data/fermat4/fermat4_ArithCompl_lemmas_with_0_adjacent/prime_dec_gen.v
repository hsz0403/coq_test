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

Lemma prime_dec_gen : forall a b : Z, 1 < b -> b < a -> (forall c : Z, b < c < a -> rel_prime c a) -> prime a \/ ~ prime a.
Proof.
intros a b; pattern b; match goal with | |- (?p _) => simpl; case (Z_lt_dec 1 a); intro; try (right; red; intro; elim H2; clear H2; intros; progress auto); apply (ind_prime p); intros; case (rel_prime_dec x a); intro; [ case (Z.eq_dec x 2); intro; [ left; rewrite e in H2; rewrite e in r; generalize (rel_prime_1 a); intro; apply prime_intro; try assumption; intros; case (Z.eq_dec n 1); intro; try (rewrite e0; assumption); case (Z.eq_dec n 2); intro; try (rewrite e0; assumption); apply H2; auto with zarith | apply (H (x - 1)); try unfold R_prime; auto with zarith; intros; case (Z.eq_dec c x); intro; try (rewrite e; assumption); apply H2; auto with zarith ] | right; red; intro; elim H3; clear H3; intros; cut (1 <= x < a); auto with zarith; intro; generalize (H4 _ H5); auto ] end.

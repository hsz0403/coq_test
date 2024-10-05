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

Lemma gcd_rel_prime : forall x y d : Z, Zis_gcd x y d -> exists a : Z, exists b : Z, x = d * a /\ y = d * b /\ rel_prime a b.
Proof.
intros; elim (Z.eq_dec d 0); intro; [ rewrite a in H; elim H; clear H; intros; destruct H as (q,H), H0 as (q0,H0); revert H H0; ring_simplify (q * 0); ring_simplify (q0 * 0); intros; exists 1; exists 1; rewrite a; intuition; apply rel_prime_1 | elim H; clear H; intros; destruct H as (q,H), H0 as (q0,H0); exists q; exists q0; rewrite (Zmult_comm d q); rewrite (Zmult_comm d q0); intuition; elim (rel_prime_dec q q0); intro; [ auto | elimtype False; elim (not_rel_prime1 _ _ b0); clear b0; intros; elim H2; clear H2; intros; elim H2; clear H2; intros; generalize (Zdivide_mult_l _ _ d H2); intro; generalize (Zdivide_mult_l _ _ d H4); intro; rewrite <- H in H6; rewrite <- H0 in H7; generalize (H1 _ H6 H7); clear H5 H6 H7; intro; elim H2; clear H2; intros; elim H4; clear H4; intros; rewrite H2 in H; clear H2; rewrite H4 in H0; clear H4; rewrite <- Zmult_assoc in H; rewrite <- Zmult_assoc in H0; generalize (Zdivide_intro (x0 * d) x _ H); clear H; intro; generalize (Zdivide_intro (x0 * d) y _ H0); clear H0; intro; generalize (H1 _ H H0); elim H3; clear H H0 H3; do 2 intro; apply not_divide1; auto ] ].

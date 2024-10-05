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

Lemma gcd2_relp_odd : forall u v : Z, Zodd u -> Zodd v -> rel_prime u v -> (Zis_gcd (u - v) (u + v) 2).
Proof.
intros; elim (Zgcd_spec (u - v) (u + v)); intros; elim p; clear p; intros; elim H2; intros; generalize (Zdivide_plus_r _ _ _ H4 H5); ring_simplify (u - v + (u + v)); intro; generalize (Zdivide_opp_r _ _ H4); intro; generalize (Zdivide_plus_r _ _ _ H5 H8); ring_simplify (u + v + - (u - v)); clear H8; intro; generalize (Zodd_sum2 _ _ H H0); intro; elim (Zeven_def1 _ H9); clear H9; intros; rewrite Zmult_comm in H9; generalize (Zdivide_intro _ _ _ H9); clear x0 H9; intro; generalize (Zodd_sum1 _ _ H H0); intro; elim (Zeven_def1 _ H10); clear H10; intros; rewrite Zmult_comm in H10; generalize (Zdivide_intro _ _ _ H10); clear x0 H10; intro; generalize (H6 _ H9 H10); clear H9 H10; intro; elim H9; clear H9; intros; rewrite Zmult_comm in H9; rewrite H9 in H7; rewrite H9 in H8; cut (2 <> 0); auto with zarith; intro; generalize (divide_mult_l _ _ _ H10 H7); clear H7; intro; generalize (divide_mult_l _ _ _ H10 H8); clear H8 H10; intro; elim H1; intros; generalize (H12 _ H7 H8); intro; elim (Zdivide_1 _ H13); intro; try (elimtype False; rewrite H14 in H9; progress auto with zarith); rewrite H14 in H9; simpl in H9; rewrite H9 in H2; assumption.

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

Lemma prop1 : forall m n : Z, rel_prime m n -> distinct_parity m n -> rel_prime (m + n) (n - m).
Proof.
unfold rel_prime; intros; elim (distp_odd _ _ H0); clear H0; intros; elim (Zgcd_spec (m + n) (n - m)); intros; elim p; clear p; intros; elim (Z.eq_dec x 1); intro; [ rewrite a in H2; assumption | elimtype False; elim H2; clear H2; intros; generalize (Zdivide_plus_r _ _ _ H2 H4); ring_simplify (m + n + (n - m)); intro; generalize (Zdivide_minus_l _ _ _ H2 H4); ring_simplify (m + n - (n - m)); intro; elim (Zdivide_dec x 2); intro; [ elim (Z.eq_dec x 0); intro; [ rewrite a0 in a; clear a0; elim a; clear a; intros; auto with zarith | generalize (divide_2 _ H3 b0 b a); clear a; intro; rewrite H8 in H2; rewrite H8 in H4; clear x H3 b H5 H6 H7 b0 H8; destruct H2 as (q,H2), H4 as (q0,H3); rewrite Zmult_comm in H2; rewrite Zmult_comm in H3; generalize (Zeven_def2 _ (ex_intro (fun x => m + n = 2 * x) q H2)); clear q H2; intro; generalize (Zeven_not_Zodd _ H2); auto ] | elim (Zdivide_dec 2 x); intro; [ generalize (divide_trans _ _ _ a H2); clear H H1 x H3 b H2 H4 H5 H6 H7 b0 a; intro; destruct H as (q,H); rewrite Zmult_comm in H; generalize (Zeven_def2 _ (ex_intro (fun x => m + n = 2 * x) q H)); clear H; intro; generalize (Zeven_not_Zodd _ H); auto | generalize (prime_rel_prime _ prime_2 _ b1); intro; generalize (rel_prime_sym _ _ H8); clear H8; intro; generalize (Gauss _ _ _ H6 H8); clear H6; intro; generalize (Gauss _ _ _ H7 H8); clear H7; intro; cut (x <> -1); auto with zarith; intro; generalize (not_rel_prime2 _ _ _ H7 H6 b H9); auto ] ] ].

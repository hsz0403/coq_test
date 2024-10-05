Require Export Descent.
Require Export Pythagorean.

Lemma multiple4_2: forall u v : Z, Zodd v -> Zodd u -> v <= u -> rel_prime u v -> 1 < u -> 1 < v -> exists two : Z * Z, let (s, w) := two in (u - v = 4 * s /\ u + v = 2 * w \/ u - v = 2 * w /\ u + v = 4 * s) /\ 0 < s /\ 0 < w /\ rel_prime s w.
Proof.
intros; elim (Zodd_mult u v H0 H); intros; elim H5; clear H5; intros; elim_hyps; split with (x,x0); intuition; cut (u <> 1); auto with zarith; intro; cut (u <> -1); auto with zarith; intro.
apply (Zmult_lt_0_reg_r 4 x); auto with zarith; rewrite Zmult_comm; rewrite <- H5; generalize (relp_neq _ _ H7 H8 H2); auto with zarith.
apply (gcd2_rel_prime (u - v) (u + v) x x0); auto; apply gcd2_relp_odd; auto.
apply (Zmult_lt_0_reg_r 2 x0); auto with zarith; rewrite Zmult_comm; rewrite <- H5; generalize (relp_neq _ _ H7 H8 H2); auto with zarith.
apply (gcd2_rel_prime (u + v) (u - v) x x0); auto; apply Zis_gcd_sym; apply gcd2_relp_odd; auto.

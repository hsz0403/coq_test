Require Export Diophantus20.

Lemma fermat4_weak: ~ exists x : Z, exists y : Z, exists z : Z, 0 < x /\ 0 < y /\ 0 < z /\ rel_prime y z /\ distinct_parity y z /\ x * x * x * x + y * y * y * y = z * z * z * z.
Proof.
intro; elim_hyps; rename x0 into y; rename x1 into z; cut ((z * z + y * y) * (z * z - y * y) = x * x * (x * x)).
intro; elim (diophantus20_equiv y z); auto with zarith.
generalize (Zmult_lt_0_compat _ _ H H); intro; generalize (Zmult_lt_0_compat _ _ H6 H6); clear H6; intro; rewrite <- H5 in H6; generalize (Z.lt_gt _ _ H0); intro; cut (z * z + y * y > 0); auto with zarith; intro; generalize (Z.lt_gt _ _ H6); intro; generalize (Zmult_gt_0_reg_l _ _ H8 H9); intro; generalize (Z.gt_lt _ _ H10); intro; cut (y < z); auto with zarith.
split; [ rewrite H5; apply Z.ge_le; apply sqr_pos | exists (x * x); intuition ].
replace ((z * z + y * y) * (z * z - y * y)) with (z * z * z * z - y * y * y * y); try solve [ ring ]; rewrite <- H4; ring.

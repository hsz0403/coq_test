Require Export Tactics.
Definition nnl_triple (a b c : Z) := ~(a = 0) /\ ~(b = 0) /\ ~(c = 0).
Definition pos_triple (a b c : Z) := (a >= 0) /\ (b >= 0) /\ (c >= 0).
Definition is_pytha (a b c : Z) := (pos_triple a b c) /\ a * a + b * b = c * c.
Definition in_ucirc (x y : R) := (x * x + y * y = 1)%R.
Definition D_r (r x y : R) := (y = r * (x + 1))%R.
Definition interCDr (r x y : R) := (in_ucirc x y) /\ (D_r r x y).
Definition p1 := (-1,0)%R.
Definition p2 (r : R) := let den := (1 + r * r)%R in ((1 - r * r) / den, 2 * r / den)%R.
Definition eqp (p1 p2 : R * R) := (fst p1) = (fst p2) /\ (snd p1)= (snd p2).
Definition is_posp (c : R * R) := (fst c >= 0)%R /\ (snd c >= 0)%R.
Definition is_ucp (c : R * R) := (in_ucirc (fst c) (snd c)) /\ (is_ratp c) /\ (is_posp c).
Definition ucp (p q : Z) := let pr := (IZR p) in let qr := (IZR q) in let den := (pr * pr + qr * qr)%R in ((qr * qr - pr * pr) / den, (2 * pr * qr) / den)%R.
Definition cond_pqb (p q : Z) := p >= 0 /\ q > 0 /\ p <= q /\ (rel_prime p q).
Definition in_ucp_setb (x y : R) := exists p : Z, exists q : Z, x = (fst (ucp p q)) /\ y = (snd (ucp p q)) /\ (cond_pqb p q).
Definition cond_pq (p q : Z) := cond_pqb p q /\ (distinct_parity p q).
Definition in_ucp_set (x y : R) := exists p : Z, exists q : Z, (x = (fst (ucp p q)) /\ y = (snd (ucp p q)) \/ x = (snd (ucp p q)) /\ y = (fst (ucp p q))) /\ (cond_pq p q).
Definition pytha_set (a b c : Z) := exists p : Z, exists q : Z, exists m : Z, (a = m * (q * q - p * p) /\ b = 2 * m * (p * q) \/ a = 2 * m * (p * q) /\ b = m * (q * q - p * p)) /\ c = m * (p * p + q * q) /\ m >= 0 /\ (cond_pq p q).
Definition pytha_set_even (a b c : Z) := exists p : Z, exists q : Z, exists m : Z, a = m * (q * q - p * p) /\ b = 2 * m * (p * q) /\ c = m * (p * p + q * q) /\ m >= 0 /\ (cond_pq p q).

Lemma pytha_thm1 : forall a b c : Z, (is_pytha a b c) -> (pytha_set a b c).
Proof.
do 3 intro; elim (Z_gt_dec c 0); [ idtac | unfold is_pytha, pytha_set, pos_triple, cond_pq, cond_pqb ]; intros.
generalize (pytha_ucirc1 _ _ _ a0 H); intro; cut (is_ucp (frac a c, frac b c)); [ clear H0; intro; generalize (rat_pos_coo2 _ _ H0); clear H0; intro; generalize (nrat_pos_coo2 _ _ H0); clear H0; intro; unfold in_ucp_set, cond_pq, cond_pqb in H0; unfold pytha_set, cond_pq, cond_pqb; simpl in H0; elim_hyps; generalize (relp_pq1 _ _ H1 H4 H5 H2); intro; generalize (Z.gt_lt _ _ a0); intro; generalize (Zlt_not_eq _ _ H8); clear H8; intro; generalize (sym_not_eq H8); clear H8; intro; generalize (Z.gt_lt _ _ H3); intro; generalize (Zlt_not_eq _ _ H9); clear H9; intro; generalize (sym_not_eq H9); clear H9; intro; (cut (x * x + x0 * x0 <> 0); [ intro | auto with zarith ]; (cut ((IZR x0 * IZR x0 - IZR x * IZR x) / (IZR x * IZR x + IZR x0 * IZR x0) = frac (x0 * x0 - x * x) (x * x + x0 * x0))%R; [ intro | head_IZR; auto ]; (cut (2 * IZR x * IZR x0 / (IZR x * IZR x + IZR x0 * IZR x0) = frac (2 * x * x0) (x * x + x0 * x0))%R; [ intro | head_IZR; auto ]))) | idtac ].
rewrite H11 in H0; clear H11; rewrite H12 in H6; clear H12; generalize (relp_frac _ _ _ _ H8 H10 H0 H7); intro; elim_hyps; rewrite H12 in H0; rewrite H12 in H6; exists x; exists x0; exists x1; generalize (frac_eq _ _ _ _ H11 H10 H0); clear H0; intro; generalize (frac_eq _ _ _ _ H11 H10 H6); clear H6; intro; rewrite H0; rewrite H6; rewrite H12; intuition; (left; split; ring) || (cut (x1 * (x * x + x0 * x0) > 0); [ intro; rewrite Zmult_comm in H13; cut (x * x + x0 * x0 > 0); try (intro; generalize (Zmult_gt_0_reg_l _ _ H14 H13)); auto with zarith | rewrite <- H12; assumption ]).
rewrite H11 in H6; clear H11; rewrite H12 in H0; clear H12; generalize (relp_frac _ _ _ _ H8 H10 H6 H7); intro; elim_hyps; rewrite H12 in H0; rewrite H12 in H6; exists x; exists x0; exists x1; generalize (frac_eq _ _ _ _ H11 H10 H0); clear H0; intro; generalize (frac_eq _ _ _ _ H11 H10 H6); clear H6; intro; rewrite H0; rewrite H6; rewrite H12; intuition; (right; split; ring) || (cut (x1 * (x * x + x0 * x0) > 0); [ intro; rewrite Zmult_comm in H13; cut (x * x + x0 * x0 > 0); try (intro; generalize (Zmult_gt_0_reg_l _ _ H14 H13)); auto with zarith | rewrite <- H12; assumption ]).
unfold is_ucp, is_ratp, is_posp; simpl; intuition; unfold is_rat; unfold is_pytha, pos_triple in H; elim_hyps; generalize (Z.gt_lt _ _ a0); intro; generalize (IZR_lt _ _ H4); intro; simpl in H5; fold (IZR c > 0)%R in H5; [ exists (a, c); intuition | exists (b, c); intuition | unfold frac; generalize (IZR_ge _ _ H); clear H; intro; simpl in H | unfold frac; generalize (IZR_ge _ _ H2); clear H2; intro; simpl in H2 ]; auto with reals.
elim_hyps; cut (c = 0); [ intro; exists 0; exists 1; exists 0; rewrite H3; simpl; intuition; (left; rewrite H3 in H0; simpl in H0; progress auto with zarith) || (compute; auto with zarith) | auto with zarith ].

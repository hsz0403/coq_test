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

Lemma rat_pos_coo1 : forall x y : R, (is_ucp (x,y)) -> exists r : R, (is_rat r) /\ (r >= 0)%R /\ (r <= 1)%R /\ x = (fst (p2 r)) /\ y = (snd (p2 r)).
Proof.
intros; unfold is_ucp in H; elim H; intros; elim H1; intros; elim (rat_coo2 x y (conj H0 H2)); intros; elim H4; intros.
elim (interCDr_sol x0 x y).
unfold eqp; simpl; intro; elim H7; intros; elim H3; simpl; intros; rewrite H8 in H10; elimtype False; generalize (Rge_le (-1) 0 H10)%R; fold (~ (0 <= -1)%R); apply Rlt_not_le; prove_sup.
cut (0 < / (1 + x0 * x0))%R; [ intro | apply Rinv_0_lt_compat; rewrite <- (Rplus_0_r 0)%R; apply Rplus_lt_le_compat; [ prove_sup | fold (Rsqr x0); elim (Req_dec x0 0); intro; [ rewrite H7; rewrite Rsqr_0; unfold Rle; right; auto | unfold Rle; left; apply Rsqr_pos_lt; assumption ] ] ].
unfold eqp; simpl; intro; elim H8; intros; elim H3; simpl; rewrite H9; rewrite H10; intros; exists x0; split.
assumption.
split.
generalize (Rge_le (2 * x0 / (1 + x0 * x0)) 0 H12); intro; rewrite Rmult_comm in H13; rewrite <- (Rmult_0_l (2 / (1 + x0 * x0))) in H13; cut (0 < 2 / (1 + x0 * x0))%R; [ intro; rewrite Rmult_comm in H13; unfold Rdiv in H13; rewrite (Rmult_assoc x0 2) in H13; rewrite (Rmult_comm x0 (2 * / (1 + x0 * x0)))%R in H13; generalize (Rmult_le_reg_l (2 / (1 + x0 * x0)) 0 x0 H14 H13); intro; apply Rle_ge; assumption | unfold Rdiv; prove_sup; assumption ].
split.
generalize (Rge_le ((1 - x0 * x0) / (1 + x0 * x0)) 0 H11); intro; unfold Rdiv in H13; rewrite Rmult_comm in H13; rewrite <- (Rmult_0_r (/ (1 + x0 * x0)))%R in H13; generalize (Rmult_le_reg_l (/ (1 + x0 * x0)) 0 (1 - x0 * x0) H7 H13)%R; intro; generalize (Rplus_le_compat_r (x0 * x0) 0 (1 - x0 * x0) H14)%R; intro; rewrite Rplus_0_l in H15; unfold Rminus in H15; rewrite Rplus_assoc in H15; rewrite Rplus_opp_l in H15; rewrite Rplus_0_r in H15; rewrite <- (Rmult_1_r 1) in H15; fold (Rsqr x0) in H15; fold (Rsqr 1) in H15; apply (Rsqr_incr_0_var x0 1 H15); unfold Rle; left; prove_sup.
auto.
assumption.

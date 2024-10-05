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

Lemma interCDr_sol : forall r x y : R, (interCDr r x y) -> (eqp (x,y) p1) \/ (eqp (x,y) (p2 r)).
Proof.
unfold interCDr;unfold in_ucirc;unfold D_r;unfold eqp, p1, p2;simpl.
intros;elim H;intros;rewrite H1 in H0.
cut (((1 + r * r) * Rsqr x + 2 * r * r * x + (r * r - 1)) = 0)%R.
intro;cut ((1 + r * r) <> 0)%R.
intro;cut (Delta_is_pos (mknonzeroreal (1 + r * r) H3) (2 * r * r) (r * r - 1))%R.
intro;generalize (Rsqr_sol_eq_0_0 (mknonzeroreal (1 + r * r) H3) (2 * r * r) (r * r - 1) x H4 H2)%R.
unfold sol_x1, sol_x2;unfold Delta;unfold Rsqr;simpl.
cut ((2 * r * r * (2 * r * r) - 4 * (1 + r * r) * (r * r - 1))%R = 4%R).
intro;rewrite H5.
replace (4)%R with (2*2)%R by auto.
rewrite sqrt_square.
induction 1;[right|left].
split;[rewrite H6;field;assumption |rewrite H1;rewrite H6;field;assumption].
split;[rewrite H6;field;assumption |rewrite H1;rewrite H6;field;assumption].
unfold Rle;left;prove_sup.
ring.
unfold Delta_is_pos;unfold Delta;unfold Rsqr;simpl; ring_simplify (2 * r * r * (2 * r * r) - 4 * (1 + r * r) * (r * r - 1))%R; unfold Rle;left;prove_sup.
apply Rgt_not_eq;unfold Rgt;rewrite Rplus_comm;apply Rle_lt_0_plus_1; fold (Rsqr r);elim (Req_dec r 0);intro; [rewrite H3;rewrite Rsqr_0;unfold Rle;right;auto |unfold Rle;left;apply Rsqr_pos_lt;assumption].
pattern 1%R at 2;rewrite <- H0;unfold Rsqr;ring.

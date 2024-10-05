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

Lemma nrat_pos_coo2 : forall x y : R, (in_ucp_setb x y) -> (in_ucp_set x y).
Proof.
unfold in_ucp_setb, in_ucp_set, cond_pq, cond_pqb, distinct_parity; simpl; intros; elim_hyps.
elim (relp_parity x0 x1 H4); intro.
exists x0; exists x1; intuition.
unfold both_odd in H5; elim_hyps; generalize (Zodd_def1 _ H5); clear H5; intro; generalize (Zodd_def1 _ H6); clear H6; intro; elim_hyps.
exists (x2 - x3); exists (x2 + x3 + 1); split; [ right; rewrite H; rewrite H0; rewrite H5; rewrite H6; atomic_IZR; simpl; split; field; split; neq_0; apply sqr_sum; auto with zarith | rewrite H5 in H1; rewrite H6 in H2; rewrite H5 in H3; rewrite H6 in H3; do 4 try split; auto with zarith ].
apply rel_prime_sym; apply relp_sum; ring_simplify (x2 + x3 + 1 + (x2 - x3)); ring_simplify (x2 + x3 + 1 - (x2 - x3)); generalize H5; clear H5; ring_simplify (2 * x3 + 1); intro; generalize H6; clear H6; ring_simplify (2 * x2 + 1); intro; rewrite <- H5; rewrite <- H6; auto with zarith.
elim (Zeven_odd_dec x2); intro; elim (Zeven_odd_dec x3); intro; Zparity_hyps; rewrite H7; rewrite H8; [ left; split; [ apply Zeven_def2; exists (x4 - x5) | apply Zodd_def2; exists (x4 + x5) ] | right; split; [ apply Zodd_def2; exists (x5 - x4 - 1) | apply Zeven_def2; exists (x5 + x4 + 1) ] | right; split; [ apply Zodd_def2; exists (x4 - x5) | apply Zeven_def2; exists (x4 + x5 + 1) ] | left; split; [ apply Zeven_def2; exists (x4 - x5) | apply Zodd_def2; exists (x4 + x5 + 1) ] ]; ring.

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

Lemma rat_coo1 : forall x y : R, (in_ucirc x y) /\ (exists r : R, (is_rat r) /\ (interCDr r x y)) -> (is_ratp (x,y)).
Proof.
unfold in_ucirc, is_ratp, is_rat.
unfold frac; intros; elim H; intros; elim H1; intros; elim H2; intros; elim H3; intro; elim x1;intros; elim H5; intros; elim (interCDr_sol x0 x y H4); unfold eqp, p1, p2; simpl; intro; elim H8; intros; rewrite H9; rewrite H10.
split.
exists (-1,1); split; [ auto with zarith | simpl; field; discrR ].
exists (0,1); split; [ auto with zarith | simpl; field; discrR ].
split.
exists (b * b - a * a, a * a + b * b); split.
auto with zarith.
rewrite H7; rewrite <- Z_R_minus; rewrite plus_IZR; repeat rewrite mult_IZR; field; split;discrR; auto with zarith reals.
exists (2 * a * b * b, (a * a + b * b) * b); split.
apply not_IZR_0; rewrite mult_IZR; split_Rmult; discrR; auto with zarith.
rewrite H7; repeat rewrite mult_IZR; rewrite plus_IZR; repeat rewrite mult_IZR; simpl; field; split; discrR; auto with zarith reals.

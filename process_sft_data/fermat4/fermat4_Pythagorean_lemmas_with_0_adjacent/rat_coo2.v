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

Lemma rat_coo2 : forall x y : R, (in_ucirc x y) /\ (is_ratp (x,y)) -> exists r : R, (is_rat r) /\ (interCDr r x y).
Proof.
unfold in_ucirc, is_ratp, is_rat, interCDr.
unfold frac, in_ucirc, D_r; intros.
elim (Req_dec x (-1)%R); intro.
exists 1%R; split.
exists (1,1); split; [ auto with zarith | field; discrR ].
elim H; intros; split.
assumption.
rewrite H0; rewrite H0 in H1; ring_simplify (1 * (-1 + 1))%R; cut ((1 + y * y) = 1)%R; [ intro; apply Rsqr_0_uniq; unfold Rsqr; apply (Rplus_0_r_uniq 1 (y * y) H3)%R | pattern 1%R at 2; rewrite <- H1; ring ].
exists (y / (x + 1))%R; cut ((x + 1) <> 0)%R; [ intro; split | rewrite <- (Ropp_involutive 1); fold (x - -1)%R; apply Rminus_eq_contra; assumption ].
elim H; intros; elim H3; intros; elim H4; intro; elim x0; intros; elim H6; intros; elim H5; intro; elim x1; intros; elim H9; intros; rewrite H8; rewrite H11.
cut (a + b <> 0); [ intro | apply not_IZR_0; cut (((IZR a / IZR b + 1) * IZR b)%R = (IZR a + IZR b)%R); [ intro; rewrite plus_IZR; rewrite <- H12; split_Rmult; [ rewrite <- H8; assumption | discrR; assumption ] | field; discrR; assumption ] ].
exists (a0 * b, b0 * (a + b)); split.
apply not_IZR_0; rewrite mult_IZR; rewrite plus_IZR; split_Rmult; discrR; assumption.
repeat rewrite mult_IZR; rewrite plus_IZR; field; discrR; try assumption.
repeat split; discrR; try assumption; fold (IZR a / IZR b)%R; rewrite <- H8; assumption.
split; [ elim H; intros; assumption | field; assumption ].

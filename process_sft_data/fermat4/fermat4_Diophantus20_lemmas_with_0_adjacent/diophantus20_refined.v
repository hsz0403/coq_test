Require Export Descent.
Require Export Pythagorean.

Lemma diophantus20_refined : forall p q : Z, p > 0 -> q > 0 -> p <= q -> rel_prime p q -> distinct_parity p q -> ~ is_sqr (p * (q * (q * q - p * p))).
Proof.
intros p0 q0 Hp0 Hq0 H' H0' H1' H2'.
cut (0 <= p0).
intro; cut (0 <= q0).
intro; elim (prop4b _ _ H H0 H' H0' H2').
intros; elim H2; clear H2; intros; unfold is_sqr in H3; elim H3; clear H3; intros; do 2 (elim H4; clear H4; intros); unfold is_sqr in H1; unfold is_sqr in H2; elim H1; clear H1; intros; elim H2; clear H2; intros; elim H6; clear H6; intros; elim H7; clear H7; intros; elim H6; clear H6; intros; elim H7; clear H7; intros; apply (diophantus20_equiv x0 x1).
cut (p0 <> 0); auto with zarith; intro; rewrite <- H6 in H10; elim (Zmult_neq_0 _ _ H10); auto with zarith.
cut (q0 <> 0); auto with zarith; intro; rewrite <- H7 in H10; elim (Zmult_neq_0 _ _ H10); auto with zarith.
rewrite <- H6 in H'; rewrite <- H7 in H'; apply Zle_square_simpl; auto.
apply prop3; rewrite H6; rewrite H7; assumption.
apply distp_sqr2; rewrite H6; rewrite H7; assumption.
unfold is_sqr; split.
rewrite H6; rewrite H7; replace ((q0 + p0) * (q0 - p0)) with (q0 * q0 - p0 * p0).
assumption.
ring.
split with x; rewrite H6; rewrite H7; split.
rewrite H4; ring.
assumption.
auto with zarith.
auto with zarith.

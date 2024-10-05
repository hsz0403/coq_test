Require Export Descent.
Require Export Pythagorean.

Lemma for_mba_pytha2: forall m n u v a b : Z, u * u = m * m + n * n -> v * v = n * n - m * m -> u - v = 2 * (b * b) -> u + v = 4 * (a * a) -> b * b * (b * b) + 2 * (a * a) * (2 * (a * a)) = n * n.
Proof.
intros; cut (2 * n * n = u * u + v * v).
intro; cut (u = 2 * a * a + b * b).
intro; cut (v = 2 * a * a - b * b).
intro; rewrite H4 in H3; rewrite H5 in H3; symmetry; apply (Zmult_eq_reg_l 2).
replace (2 * (n * n)) with (2 * n * n); [ rewrite H3; ring | ring ].
discriminate.
apply (Zmult_eq_reg_l 2).
replace (2 * v) with (u + v - (u - v)); [ rewrite H2; rewrite H1; ring | ring ].
discriminate.
apply (Zmult_eq_reg_l 2).
replace (2 * u) with (u + v + (u - v)); [ rewrite H2; rewrite H1; ring | ring ].
discriminate.
replace (2 * n * n) with (m * m + n * n + (n * n - m * m)); [ rewrite H; rewrite H0; ring | ring ].

Require Export Wf_nat.
Require Export ZArith.
Require Export Znumtheory.
Require Export Reals.
Open Scope Z_scope.
Unset Standard Proposition Elimination Names.
Definition is_sqr (n : Z) : Prop := 0 <= n /\ exists i : Z, i * i = n /\ 0 <= i.
Definition both_odd (x y : Z) := Zodd x /\ Zodd y.
Definition distinct_parity (a b : Z) := (Zeven a) /\ (Zodd b) \/ (Zodd a) /\ (Zeven b).
Definition R_prime (x y : Z) := 1 < x /\ 1 < y /\ x < y.
Definition f_Z (x : Z) := Z.abs_nat x.
Definition R_fact (x y : Z) := 1 < x /\ 1 < y /\ exists q : Z, y = q * x /\ 1 < q.
Definition R_p4 (x y : Z) := 0 <= x /\ 1 < y /\ exists d : Z, y = d * d * x /\ 1 < d.
Definition frac (a b : Z) := ((IZR a) / (IZR b))%R.
Definition is_rat (r : R) := exists pq : Z * Z, let (p,q) := pq in ~(q = 0) /\ r = (frac p q).
Definition is_ratp (c : R * R) := let (x,y) := c in (is_rat x) /\ (is_rat y).
Hint Resolve rel_prime_sym : zarith.
Hint Immediate sqr_0 sqr_pos sqr_spos sqr_sum sqr_sum2 sqr_sum3 sqr_sum4 sqr_sum5 sqr_sub1 sqr_sub2 sqr_sub3 sqr_ge : zarith.
Hint Immediate sqr_inv Rdiv_ge_0 : reals.

Lemma prop4 : forall p q : Z, 0 <= p -> 0 <= q -> rel_prime p q -> is_sqr (p * q) -> is_sqr p /\ is_sqr q.
Proof.
split; generalize H2; generalize H1; generalize H0; generalize H; [ pattern p | pattern q ]; match goal with | |- (?p _) => simpl; apply (ind_p4 p); intros end; match goal with | |- is_sqr ?x => elim (Z_lt_dec 1 x); intro; [ idtac | elim (Z.eq_dec x 0); intro; [ rewrite a; unfold is_sqr; intuition; exists 0; intuition | elim (Z.eq_dec x 1); intro; [ rewrite a; unfold is_sqr; intuition; exists 1; intuition | elimtype False; auto with zarith ] ] ] end; generalize (sqr_prime1 _ H7); intro; elim (Zfact _ a); intros; elim H9; clear H9; intros; (generalize (Zdivide_mult_l _ _ q H9); intro; generalize (H8 _ H11 H10)) || (generalize (Zdivide_mult_r _ p _ H9); intro; generalize (H8 _ H11 H10)); intro; elim (sqr_prime2 _ _ _ H9 H12 H10) || (rewrite (Zmult_comm p) in H12; elim (sqr_prime2 _ _ _ H9 H12 H10)); intros; try (elimtype False; elim H10; intros; cut (x0 <> 1); auto with zarith; intro; cut (x0 <> -1); auto with zarith; intro; generalize (not_rel_prime2 _ _ _ H9 H13 H16 H17); progress auto || (generalize (rel_prime_sym _ _ H6); auto)); elim H13; intros q0 ?; cut (is_sqr q0); try (intro; elim H15; clear H15; intros; do 2 (elim H16; clear H16; intros); rewrite <- H16 in H14; unfold is_sqr; intuition; rewrite H14; exists (x0 * x1); split; try ring; elim H10; intros; apply Zmult_le_0_compat; auto with zarith); elim H10; intros; cut (0 <= q0); try (cut (x0 <> 0); auto with zarith; intro; generalize (sqr_spos _ H17); clear H17; intro; cut (0 < x); auto with zarith; intro; rewrite H14 in H18; generalize (Zmult_gt_0_lt_0_reg_r _ _ H17 H18); progress auto with zarith); intro; (apply H3; try assumption; [ unfold R_p4; intuition; exists x0; intuition; rewrite H14; ring | rewrite H14 in H6; (apply (relp_mult3 q0 (x0 * x0)) || (apply rel_prime_sym; apply (relp_mult3 q0 (x0 * x0)); apply rel_prime_sym)); assumption | rewrite H14 in H7; (replace (q0 * (x0 * x0) * q) with (x0 * x0 * (q0 * q)) in H7; try ring; apply (is_sqr_compat x0); progress auto with zarith) || (replace (p * (q0 * (x0 * x0))) with (x0 * x0 * (p * q0)) in H7; try ring; apply (is_sqr_compat x0); auto with zarith) ]).

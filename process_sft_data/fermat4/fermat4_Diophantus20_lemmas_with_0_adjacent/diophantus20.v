Require Export Descent.
Require Export Pythagorean.

Lemma diophantus20 : ~ (exists x : Z, exists y : Z, exists z : Z, exists t : Z, 0 < x /\ 0 < y /\ 0 < z /\ 0 < t /\ x * x + y * y = z * z /\ x * y = 2 * (t * t)).
Proof.
intro; elim_hyps; cut (is_pytha x x0 x1); try (unfold is_pytha, pos_triple; solve [ intuition ]).
intro; elim (pytha_thm1 _ _ _ H5); clear H5; unfold cond_pq, cond_pqb; intros; elim_hyps; (cut (x3 > 0); [ intro; apply (diophantus20_refined x3 x4); try assumption; generalize (Z.ge_le _ _ H8); intro; (cut (x5 > 0); [ intro; apply (is_sqr_compat x5); auto with zarith; repeat progress (apply Zmult_le_0_compat; auto with zarith); split; [ repeat progress (apply Zmult_le_0_compat; auto with zarith) | exists x2; intuition; rewrite H5 in H4; rewrite H13 in H4; match goal with | id : ?x = 2 * _ |- _ => replace x with (2 * (x5 * x5 * (x3 * (x4 * (x4 * x4 - x3 * x3))))) in id end; [ auto with zarith | ring ] ] | apply Z.lt_gt; apply (Zmult_lt_0_reg_r (x3 * x3 + x4 * x4)); try (apply Z.gt_lt; progress auto with zarith); rewrite <- H6; auto ]) | match goal with | id : ?x = 2 * _ * (_ * _) |- _ => cut (x <> 0); auto with zarith; intro; match goal with | id' : _ |- _ => rewrite id in id' end end; repeat match goal with | id : _ |- _ => elim (Zmult_neq_0 _ _ id); auto with zarith; intros end ]).

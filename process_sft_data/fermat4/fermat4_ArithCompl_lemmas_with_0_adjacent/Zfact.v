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

Lemma Zfact : forall a : Z, 1 < a -> exists b : Z, (b | a) /\ prime b.
Proof.
intro a; pattern a; match goal with | |- (?p _) => simpl; apply (ind_fact p); intros; case (prime_dec x); intro; [ exists x; intuition | elim (not_prime _ H0 H1); intros; do 2 (elim H2; clear H2; intros); elim H3; clear H3; intros; cut (exists b : Z, (b | x1) /\ prime b); try (apply H; try assumption; unfold R_fact; intuition; exists x0; intuition); intro; do 2 (elim H5; clear H5; intros); exists x2; intuition; elim H5; clear H5; intros; rewrite H5 in H2; rewrite Zmult_assoc in H2; apply (Zdivide_intro _ _ _ H2) ] end.

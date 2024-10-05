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

Lemma Zodd_mult : forall u v : Z, Zodd u -> Zodd v -> (exists s : Z, (exists w : Z, (u - v = 4 * s /\ u + v = 2 * w) \/ (u - v = 2 * w /\ u + v = 4 * s))).
Proof.
intros; elim (Zodd_def1 u H); elim (Zodd_def1 v H0); intros k Hk k' Hk'; elim (Zeven_odd_dec k); elim (Zeven_odd_dec k'); intros.
elim (Zeven_def1 k a0); elim (Zeven_def1 k' a); intros t Ht t' Ht'; split with (t - t'); split with (2 * t + 2 * t' + 1); left; auto with zarith.
elim (Zeven_def1 k a); elim (Zodd_def1 k' b); intros t Ht t' Ht'; split with (t + t' + 1); split with (2 * t - 2 * t' + 1); right; auto with zarith.
elim (Zeven_def1 k' a); elim (Zodd_def1 k b); intros t Ht t' Ht'; split with (t + t' +1); split with (2 * t' - 2 * t - 1); right; auto with zarith.
elim (Zodd_def1 k b0); elim (Zodd_def1 k' b); intros t Ht t' Ht'; split with (t - t'); split with (k' + k + 1); left; auto with zarith.

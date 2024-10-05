Require Import List Arith Lia Bool Permutation.
From Undecidability.Shared.Libs.DLW Require Import utils utils_tac utils_list utils_nat gcd rel_iter prime pos vec.
Set Implicit Arguments.
Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Set Implicit Arguments.
Hint Resolve prime_neq_0 : core.
Definition nxtprime n := proj1_sig (first_prime_above n).
Fact nxtprime_spec1 n : n < nxtprime n.
Proof.
apply (proj2_sig (first_prime_above n)).
Fact nxtprime_spec2 n : prime (nxtprime n).
Proof.
apply (proj2_sig (first_prime_above n)).
Hint Resolve nxtprime_spec1 nxtprime_spec2 prime_2 : core.
Fixpoint notprime_bool_rec n k := match k with | 0 => true | S k' => negb (prime_bool n) && notprime_bool_rec (S n) k' end.
Fact notprime_bool_rec_spec n k : notprime_bool_rec n k = true <-> forall i, n <= i < k+n -> ~ prime i.
Proof.
revert n; induction k as [ | k IHk ]; intros n; simpl.
+
split; auto; intros; lia.
+
rewrite andb_true_iff, negb_true_iff, <- not_true_iff_false, prime_bool_spec, IHk.
split.
*
intros (H1 & H2) i Hi.
destruct (eq_nat_dec n i); subst; auto.
apply H2; lia.
*
intros H; split; intros; apply H; lia.
Definition nxtprime_bool n p := Nat.leb (S n) p && notprime_bool_rec (S n) (p - S n) && prime_bool p.
Fact nxtprime_bool_spec n p : nxtprime_bool n p = true <-> nxtprime n = p.
Proof.
unfold nxtprime_bool.
rewrite !andb_true_iff, Nat.leb_le, notprime_bool_rec_spec, prime_bool_spec.
unfold nxtprime.
destruct (first_prime_above n) as (q & G1 & G2 & G3); simpl.
split.
+
intros ((H1 & H2) & H3).
apply le_antisym.
*
apply G3; auto.
*
apply Nat.nlt_ge.
intro; apply (H2 q); auto; lia.
+
intros ->; lsplit 2; auto.
intros q Hq C; apply G3 in C; lia.
Definition nthprime (n : nat) := iter nxtprime 2 n.
Hint Resolve nthprime_prime : core.
Fact nthprime_nxt i p q : nthprime i = p -> nxtprime p = q -> nthprime (S i) = q.
Proof.
replace (S i) with (i+1) by lia.
unfold nthprime at 2.
rewrite iter_plus; fold (nthprime i).
intros -> ?; simpl; auto.
Fact nthprime_0 : nthprime 0 = 2.
Proof.
auto.
Local Ltac nth_prime_tac H := apply nthprime_nxt with (1 := H); apply nxtprime_bool_spec; auto.
Fact nthprime_1 : nthprime 1 = 3.
Proof.
nth_prime_tac nthprime_0.
Fact nthprime_2 : nthprime 2 = 5.
Proof.
nth_prime_tac nthprime_1.
Fact nthprime_3 : nthprime 3 = 7.
Proof.
nth_prime_tac nthprime_2.
Fact nthprime_4 : nthprime 4 = 11.
Proof.
nth_prime_tac nthprime_3.
Fact nthprime_5 : nthprime 5 = 13.
Proof.
nth_prime_tac nthprime_4.
Fact nthprime_6 : nthprime 6 = 17.
Proof.
nth_prime_tac nthprime_5.
Record primestream := { str :> nat -> nat; str_inj : forall n m, str n = str m -> n = m; str_prime : forall n, prime (str n); }.
Hint Immediate str_prime : core.
Hint Resolve str_inj : core.
Definition ps : primestream.
Proof.
exists (fun n => nthprime (2 * n)); auto.
intros; apply nthprime_inj in H; lia.
Defined.
Fact ps_1 : ps 1 = 5.
Proof.
simpl; apply nthprime_2.
Definition qs : primestream.
Proof.
exists (fun n => nthprime (1 + 2 * n)); auto.
intros; apply nthprime_inj in H; lia.
Defined.
Fact qs_1 : qs 1 = 7.
Proof.
simpl; apply nthprime_3.
Hint Resolve ps_qs : core.
Fixpoint exp {n} (i : nat) (v : vec nat n) : nat := match v with | vec_nil => 1 | x##v => qs i ^ x * exp (S i) v end.
Fact exp_nil i : exp i vec_nil = 1.
Proof.
auto.
Fact exp_cons n i x v : @exp (S n) i (x##v) = qs i^x*exp (S i) v.
Proof.
auto.
Fact exp_zero n i : @exp n i vec_zero = 1.
Proof.
revert i; induction n as [ | n IHn ]; intros i; simpl; auto.
rewrite IHn; ring.
Fact exp_app n m i v w : @exp (n+m) i (vec_app v w) = exp i v * exp (n+i) w.
Proof.
revert i; induction v as [ | x n v IHv ]; intros i.
+
rewrite vec_app_nil, exp_zero; simpl; ring.
+
rewrite vec_app_cons, exp_cons.
simpl plus; rewrite exp_cons, IHv.
replace (n+S i) with (S (n+i)) by lia; ring.
Local Notation divides_mult_inv := prime_div_mult.
Hint Resolve not_prime_1 not_qs_1 : core.
Opaque ps qs.
Coercion tonat {n} := @pos2nat n.

Lemma prime_neq_0 p : prime p -> p <> 0.
Proof.
Admitted.

Lemma power_factor_lt_neq p i j x y : p <> 0 -> i < j -> ~ divides p x -> p^i * x <> p^j * y.
Proof.
intros H1 H2 H3 H5.
replace j with (i+S (j-i-1)) in H5 by lia.
rewrite Nat.pow_add_r, <- mult_assoc in H5.
rewrite Nat.mul_cancel_l in H5.
2: apply Nat.pow_nonzero; auto.
apply H3; subst x; simpl.
Admitted.

Lemma power_factor_uniq p i j x y : p <> 0 -> ~ divides p x -> ~ divides p y -> p^i * x = p^j * y -> i = j /\ x = y.
Proof.
intros H1 H2 H3 H4.
destruct (lt_eq_lt_dec i j) as [ [ H | H ] | H ].
+
exfalso; revert H4; apply power_factor_lt_neq; auto.
+
split; auto; subst j.
rewrite Nat.mul_cancel_l in H4; auto.
apply Nat.pow_nonzero; auto.
+
Admitted.

Lemma prime_above m : { p | m < p /\ prime p }.
Proof.
destruct (prime_factor (n := fact m + 1)) as (p & ? & ?).
-
pose proof (lt_O_fact m); lia.
-
exists p; eauto.
destruct (Nat.lt_ge_cases m p); eauto.
eapply divides_plus_inv in H0.
+
eapply divides_1_inv in H0; subst.
destruct H; lia.
+
eapply divides_fact.
Admitted.

Lemma prime_dec p : { prime p } + { ~ prime p }.
Proof.
destruct (le_lt_dec 2 p) as [ H | H ].
+
destruct (prime_or_div H) as [ (q & H1 & H2) | ? ]; auto.
right; intros C; apply C in H2; lia.
+
right; intros (H1 & H2).
destruct (H2 2); try lia.
Admitted.

Lemma first_prime_above m : { p | m < p /\ prime p /\ forall q, m < q -> prime q -> p <= q }.
Proof.
destruct min_dec with (P := fun p => m < p /\ prime p) as (p & H1 & H2).
+
intros n.
destruct (lt_dec m n); destruct (prime_dec n); tauto.
+
destruct (prime_above m) as (p & ?); exists p; auto.
+
Admitted.

Lemma prime_divides p q : prime p -> prime q -> divides p q -> p = q.
Proof.
Admitted.

Fact nxtprime_spec1 n : n < nxtprime n.
Proof.
Admitted.

Fact nxtprime_spec2 n : prime (nxtprime n).
Proof.
Admitted.

Theorem prime_bool_spec' p : prime_bool p = false <-> ~ prime p.
Proof.
Admitted.

Fact nxtprime_bool_spec n p : nxtprime_bool n p = true <-> nxtprime n = p.
Proof.
unfold nxtprime_bool.
rewrite !andb_true_iff, Nat.leb_le, notprime_bool_rec_spec, prime_bool_spec.
unfold nxtprime.
destruct (first_prime_above n) as (q & G1 & G2 & G3); simpl.
split.
+
intros ((H1 & H2) & H3).
apply le_antisym.
*
apply G3; auto.
*
apply Nat.nlt_ge.
intro; apply (H2 q); auto; lia.
+
intros ->; lsplit 2; auto.
Admitted.

Lemma nthprime_prime n : prime (nthprime n).
Proof.
Admitted.

Lemma nthprime_ge n m : n < m -> nthprime n < nthprime m.
Proof.
unfold nthprime.
induction 1; simpl iter; rewrite iter_swap; auto.
Admitted.

Lemma nthprime_inj n m : nthprime n = nthprime m -> n = m.
Proof.
Admitted.

Fact nthprime_nxt i p q : nthprime i = p -> nxtprime p = q -> nthprime (S i) = q.
Proof.
replace (S i) with (i+1) by lia.
unfold nthprime at 2.
rewrite iter_plus; fold (nthprime i).
Admitted.

Fact nthprime_0 : nthprime 0 = 2.
Proof.
Admitted.

Fact nthprime_1 : nthprime 1 = 3.
Proof.
Admitted.

Fact nthprime_2 : nthprime 2 = 5.
Proof.
Admitted.

Fact nthprime_3 : nthprime 3 = 7.
Proof.
Admitted.

Fact nthprime_4 : nthprime 4 = 11.
Proof.
Admitted.

Fact notprime_bool_rec_spec n k : notprime_bool_rec n k = true <-> forall i, n <= i < k+n -> ~ prime i.
Proof.
revert n; induction k as [ | k IHk ]; intros n; simpl.
+
split; auto; intros; lia.
+
rewrite andb_true_iff, negb_true_iff, <- not_true_iff_false, prime_bool_spec, IHk.
split.
*
intros (H1 & H2) i Hi.
destruct (eq_nat_dec n i); subst; auto.
apply H2; lia.
*
intros H; split; intros; apply H; lia.

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

Lemma ps_qs : forall n m, ps n = qs m -> False.
Proof.
Admitted.

Lemma ps_qs_div n m : ~ divides (ps n) (qs m).
Proof.
Admitted.

Lemma qs_ps_div n m : ~ divides (qs n) (ps m).
Proof.
Admitted.

Fact exp_nil i : exp i vec_nil = 1.
Proof.
Admitted.

Fact exp_cons n i x v : @exp (S n) i (x##v) = qs i^x*exp (S i) v.
Proof.
Admitted.

Fact exp_zero n i : @exp n i vec_zero = 1.
Proof.
revert i; induction n as [ | n IHn ]; intros i; simpl; auto.
Admitted.

Fact exp_app n m i v w : @exp (n+m) i (vec_app v w) = exp i v * exp (n+i) w.
Proof.
revert i; induction v as [ | x n v IHv ]; intros i.
+
rewrite vec_app_nil, exp_zero; simpl; ring.
+
rewrite vec_app_cons, exp_cons.
simpl plus; rewrite exp_cons, IHv.
Admitted.

Lemma not_prime_1 : ~ prime 1.
Proof.
Admitted.

Lemma not_ps_1 n : ~ ps n = 1.
Proof.
intros H; generalize (str_prime ps n).
Admitted.

Lemma not_qs_1 n : ~ qs n = 1.
Proof.
intros H; generalize (str_prime qs n).
Admitted.

Lemma ps_exp n m (v : vec nat m) i : ~ divides (ps n) (exp i v).
Proof.
revert i; induction v as [ | m x v IHv ]; intros i; simpl.
-
intros H % divides_1_inv; revert H; apply not_ps_1.
-
intros [H % divides_pow | ] % divides_mult_inv; eauto.
+
now eapply ps_qs_div in H.
+
Admitted.

Lemma vec_prod_div m (v : vec nat m) (u0 : nat) (p : pos m) i : vec_pos v p = S u0 -> qs (p + i) * exp i (vec_change v p u0) = exp i v.
Proof.
revert p i; induction v; intros p i; analyse pos p; simpl; intros H.
-
rewrite pos2nat_fst; subst; simpl; ring.
-
rewrite pos2nat_nxt; simpl.
rewrite <- IHv with (1 := H).
unfold tonat.
Admitted.

Lemma qs_exp_div i j n v : i < j -> ~ divides (qs i) (@exp n j v).
Proof with eauto.
revert i j; induction v; intros i j Hi.
+
cbn; intros ? % divides_1_inv % not_qs_1; auto.
+
cbn; intros [ H % divides_pow | H ] % divides_mult_inv; eauto.
*
eapply primestream_divides in H; lia.
*
Admitted.

Lemma qs_shift n m j k (v : vec nat k) : divides (qs n) (exp j v) <-> divides (qs (m + n)) (exp (m + j) v).
Proof.
revert m n j; induction v as [ | x k v IHv ]; intros m n j.
-
cbn; split; intros ? % divides_1_inv % not_qs_1; tauto.
-
cbn.
split.
+
intros [ | ] % divides_mult_inv; auto.
*
destruct x.
--
cbn in H; revert H.
intros ? % divides_1_inv % not_qs_1; tauto.
--
eapply divides_pow in H; auto.
eapply primestream_divides in H as ->.
cbn; do 2 apply divides_mult_r; apply divides_refl.
*
eapply divides_mult.
rewrite IHv with (m := m) in H.
rewrite <- plus_n_Sm in H; auto.
+
intros [ | ] % divides_mult_inv; auto.
*
destruct x.
--
cbn in H; revert H.
intros ? % divides_1_inv % not_qs_1; tauto.
--
eapply divides_pow in H; auto.
eapply primestream_divides in H.
assert (n = j) by lia.
subst.
cbn; do 2 apply divides_mult_r; apply divides_refl.
*
eapply divides_mult.
replace (S (m + j)) with (m + S j) in H by lia.
rewrite <- IHv in H.
Admitted.

Lemma vec_prod_mult m v (u : pos m) i : @exp m i (vec_change v u (1 + vec_pos v u)) = qs (u + i) * exp i v.
Proof.
revert i; induction v; analyse pos u; intros.
+
rewrite pos2nat_fst; simpl; ring.
+
rewrite pos2nat_nxt; simpl; rewrite IHv.
unfold tonat.
Admitted.

Lemma inv_exp q p1 p2 x y : q <> 0 -> ~ divides q p1 -> ~ divides q p2 -> q ^ x * p1 = q ^ y * p2 -> x = y.
Proof.
intros H1 H2 H3 H4.
Admitted.

Lemma exp_inj n i v1 v2 : @exp n i v1 = exp i v2 -> v1 = v2.
Proof.
revert i v2; induction v1 as [ | x n v1 IH ]; intros i v2.
+
vec nil v2; auto.
+
vec split v2 with y.
simpl; intros H.
assert (forall v, ~ divides (qs i) (@exp n (S i) v)) as G.
{
intros v; apply qs_exp_div; auto.
}
apply power_factor_uniq in H; auto.
Admitted.

Lemma exp_inv_inc n u v1 : @exp n 0 (vec_change v1 u (S (vec_pos v1 u))) = qs u * exp 0 v1.
Proof.
enough (forall i, exp i (vec_change v1 u (S (vec_pos v1 u))) = qs (i + u) * exp i v1).
eapply H.
induction v1 as [ | n x v1 IHv1 ]; analyse pos u; intros.
+
rewrite pos2nat_fst, Nat.add_0_r; cbn; ring.
+
intros; rewrite pos2nat_nxt; simpl; rewrite IHv1; unfold tonat.
Admitted.

Lemma divides_pow p n k : prime p -> divides p (n ^ k) -> divides p n.
Proof.
induction k.
-
cbn; intros H H0 % divides_1_inv; subst; exfalso; revert H; apply not_prime_1.
-
cbn; intros ? [ | ] % divides_mult_inv; eauto.

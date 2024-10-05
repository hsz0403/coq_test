Require Import Arith Lia List Bool.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd sums rel_iter bool_nat power_decomp prime.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Local Infix "≲" := binary_le (at level 70, no associativity).
Local Infix "⇣" := nat_meet (at level 40, left associativity).
Local Infix "⇡" := nat_join (at level 50, left associativity).
Hint Resolve power2_gt_0 : core.
Section stability_of_power.
Fact mult_lt_power_2 u v k : u < power k 2 -> v < power k 2 -> u*v < power (2*k) 2.
Proof.
intros H1 H2.
replace (2*k) with (k+k) by lia.
rewrite power_plus.
apply lt_le_trans with ((S u)*S v).
simpl; rewrite (mult_comm _ (S _)); simpl; rewrite mult_comm; lia.
apply mult_le_compat; auto.
Fact mult_lt_power_2_4 u v k : u < power k 2 -> v < power k 2 -> u*v < power (4*k) 2.
Proof.
intros H1 H2.
apply lt_le_trans with (1 := mult_lt_power_2 _ H1 H2).
apply power_mono_l; lia.
Fact mult_lt_power_2_4' u1 v1 u2 v2 k : u1 < power k 2 -> v1 < power k 2 -> u2 < power k 2 -> v2 < power k 2 -> u1*v1+v2*u2 < power (4*k) 2.
Proof.
intros H1 H2 H3 H4.
destruct (eq_nat_dec k 0) as [ ? | Hk ].
-
subst k; simpl.
rewrite power_0 in *.
destruct u1; destruct v1; destruct u2; destruct v2; subst; lia.
-
apply lt_le_trans with (power (S (2*k)) 2).
+
rewrite power_S, <- mult_2_eq_plus.
apply plus_lt_compat; apply mult_lt_power_2; auto.
+
apply power_mono_l; lia.
End stability_of_power.
Section power_decomp.
Variable (p : nat) (Hp : 2 <= p).
Let power_nzero x : power x p <> 0.
Proof.
generalize (@power_ge_1 x p); lia.
Fact power_decomp_lt n f a q : (forall i j, i < j < n -> f i < f j) -> (forall i, i < n -> f i < q) -> (forall i, i < n -> a i < p) -> ∑ n (fun i => a i * power (f i) p) < power q p.
Proof using Hp.
revert q; induction n as [ | n IHn ]; intros q Hf1 Hf2 Ha.
+
rewrite msum_0; apply power_ge_1; lia.
+
rewrite msum_plus1; auto.
apply lt_le_trans with (1*power (f n) p + a n * power (f n) p).
*
apply plus_lt_le_compat; auto.
rewrite Nat.mul_1_l.
apply IHn.
-
intros; apply Hf1; lia.
-
intros; apply Hf1; lia.
-
intros; apply Ha; lia.
*
rewrite <- Nat.mul_add_distr_r.
replace q with (S (q-1)).
-
rewrite power_S; apply mult_le_compat; auto.
++
apply Ha; auto.
++
apply power_mono_l; try lia.
generalize (Hf2 n); intros; lia.
-
generalize (Hf2 0); intros; lia.
End power_decomp.
Section power_decomp_uniq.
Variable (p : nat) (Hp : 2 <= p).
Let power_nzero x : power x p <> 0.
Proof.
generalize (@power_ge_1 x p); lia.
Let lt_minus_cancel a b c : a < b < c -> b - a - 1 < c - a - 1.
Proof.
intros; lia.
End power_decomp_uniq.
Fact mult_2_eq_plus x : x + x = 2 *x.
Proof.
ring.
Section power_injective.
Local Lemma power_2_inj_1 i j n : j < i -> 2* power n 2 <> power i 2 + power j 2.
Proof.
rewrite <- power_S; intros H4 E.
generalize (@power_ge_1 j 2); intro C.
destruct (lt_eq_lt_dec i (S n)) as [ [ H5 | H5 ] | H5 ].
+
apply power_mono_l with (x := 2) in H5; auto.
rewrite power_S in H5.
apply power_mono_l with (x := 2) in H4; auto.
rewrite power_S in H4; lia.
+
subst i; lia.
+
apply power_mono_l with (x := 2) in H5; auto.
rewrite power_S in H5; lia.
Fact power_2_n_ij_neq i j n : i <> j -> power (S n) 2 <> power i 2 + power j 2.
Proof.
intros H.
destruct (lt_eq_lt_dec i j) as [ [] | ]; try tauto.
+
rewrite plus_comm; apply power_2_inj_1; auto.
+
apply power_2_inj_1; auto.
Fact power_2_inj i j : power i 2 = power j 2 -> i = j.
Proof.
intros H.
destruct (lt_eq_lt_dec i j) as [ [ C | C ] | C ]; auto; apply power_smono_l with (x := 2) in C; lia.
Local Lemma power_plus_lt a b c : a < b < c -> power a 2 + power b 2 < power c 2.
Proof.
intros [ H1 H2 ].
apply power_mono_l with (x := 2) in H2; auto.
apply power_smono_l with (x := 2) in H1; auto.
rewrite power_S in H2; lia.
Local Lemma power_inj_2 i1 j1 i2 j2 : j1 < i1 -> j2 < i2 -> power i1 2 + power j1 2 = power i2 2 + power j2 2 -> i1 = i2 /\ j1 = j2.
Proof.
intros H1 H2 H3.
destruct (lt_eq_lt_dec i1 i2) as [ [ C | C ] | C ].
+
generalize (@power_plus_lt j1 i1 i2); intros; lia.
+
split; auto; apply power_2_inj; subst; lia.
+
generalize (@power_plus_lt j2 i2 i1); intros; lia.
End power_injective.
Fact divides_power p a b : a <= b -> divides (power a p) (power b p).
Proof.
*
induction 1 as [ | b H IH ].
+
apply divides_refl.
+
apply divides_trans with (1 := IH).
rewrite power_S; apply divides_mult, divides_refl.
Fact divides_msum k n f : (forall i, i < n -> divides k (f i)) -> divides k (∑ n f).
Proof.
revert f; induction n as [ | n IHn ]; intros f Hf.
+
rewrite msum_0; apply divides_0.
+
rewrite msum_S; apply divides_plus.
*
apply Hf; lia.
*
apply IHn; intros; apply Hf; lia.
Fact inc_seq_split_lt n f k : (forall i j, i < j < n -> f i < f j) -> { p | p <= n /\ (forall i, i < p -> f i < k) /\ forall i, p <= i < n -> k <= f i }.
Proof.
revert f; induction n as [ | n IHn ]; intros f Hf.
+
exists 0; split; auto; split; intros; lia.
+
destruct (le_lt_dec k (f 0)) as [ H | H ].
-
exists 0; split; try lia.
split; intros i Hi; try lia.
destruct i as [ | i ]; auto.
apply le_trans with (1 := H), lt_le_weak, Hf; lia.
-
destruct (IHn (fun i => f (S i))) as (p & H1 & H2 & H3).
*
intros; apply Hf; lia.
*
exists (S p); split; try lia; split.
++
intros [ | i ] Hi; auto; apply H2; lia.
++
intros [ | i ] Hi; try lia; apply H3; lia.
Fact inc_seq_split_le n f h : (forall i j, i < j < n -> f i < f j) -> { q | q <= n /\ (forall i, i < q -> f i <= h) /\ (forall i, q <= i < n -> h < f i) }.
Proof.
intros Hf.
destruct inc_seq_split_lt with (1 := Hf) (k := S h) as (q & H1 & H2 & H3); exists q; split; auto; split.
+
intros i Hi; specialize (H2 _ Hi); lia.
+
intros i Hi; specialize (H3 _ Hi); lia.
Fact divides_lt p q : q < p -> divides p q -> q = 0.
Proof.
intros H1 ([ | k] & H2); auto.
revert H2; simpl; generalize (k *p); intros; lia.
Fact sum_powers_inc_lt_last n f r : 2 <= r -> (forall i j, i < j <= n -> f i < f j) -> ∑ (S n) (fun i => power (f i) r) < power (S (f n)) r.
Proof.
intros Hr.
revert f.
induction n as [ | n IHn ]; intros f Hf.
+
rewrite msum_1; auto; apply power_smono_l; auto.
+
rewrite msum_plus1; auto.
rewrite power_S.
apply lt_le_trans with (power (S (f n)) r + power (f (S n)) r).
*
apply plus_lt_compat_r; auto.
apply IHn; intros; apply Hf; lia.
*
assert (power (S (f n)) r <= power (f (S n)) r) as H.
{
apply power_mono_l; try lia; apply Hf; lia.
}
apply le_trans with (2 * power (f (S n)) r); try lia.
apply mult_le_compat; auto.
Fact sum_powers_inc_lt n f p r : 2 <= r -> (forall i, i < n -> f i < p) -> (forall i j, i < j < n -> f i < f j) -> ∑ n (fun i => power (f i) r) < power p r.
Proof.
destruct n as [ | n ].
+
intros H _ _; rewrite msum_0; apply power_ge_1; lia.
+
intros H1 H2 H3.
apply lt_le_trans with (power (S (f n)) r).
*
apply sum_powers_inc_lt_last; auto.
intros; apply H3; lia.
*
apply power_mono_l; try lia.
apply H2; auto.
Fact sum_powers_injective r n f m g : 2 <= r -> (forall i j, i < j < n -> f i < f j) -> (forall i j, i < j < m -> g i < g j) -> ∑ n (fun i => power (f i) r) = ∑ m (fun i => power (g i) r) -> n = m /\ forall i, i < n -> f i = g i.
Proof.
intros Hr; revert m f g.
induction n as [ | n IHn ]; intros m f g Hf Hg.
+
rewrite msum_0.
destruct m as [ | m ].
*
rewrite msum_0; split; auto; intros; lia.
*
rewrite msum_S.
generalize (@power_ge_1 (g 0) r); intros; exfalso; lia.
+
destruct m as [ | m ].
*
rewrite msum_0, msum_S; intros; exfalso.
generalize (@power_ge_1 (f 0) r); intros; exfalso; lia.
*
destruct (lt_eq_lt_dec (f n) (g m)) as [ [E|E]| E].
-
rewrite msum_plus1 with (n := m); auto.
intros; exfalso.
assert (∑ (S n) (fun i => power (f i) r) < power (g m) r) as C; try lia.
apply sum_powers_inc_lt; auto.
intros i Hi.
destruct (eq_nat_dec i n); subst; auto.
apply lt_trans with (2 := E), Hf; lia.
-
do 2 (rewrite msum_plus1; auto); intros C.
destruct (IHn m f g) as (H1 & H2).
++
intros; apply Hf; lia.
++
intros; apply Hg; lia.
++
rewrite E in C; lia.
++
split; subst; auto.
intros i Hi.
destruct (eq_nat_dec i m); subst; auto.
apply H2; lia.
-
rewrite msum_plus1 with (n := n); auto.
intros; exfalso.
assert (∑ (S m) (fun i => power (g i) r) < power (f n) r) as C; try lia.
apply sum_powers_inc_lt; auto.
intros i Hi.
destruct (eq_nat_dec i m); subst; auto.
apply lt_trans with (2 := E), Hg; lia.
Fact power_divides_sum_power r p n f : 2 <= r -> 0 < n -> (forall i j, i < j < n -> f i < f j) -> divides (power p r) (∑ n (fun i => power (f i) r)) <-> p <= f 0.
Proof.
intros Hr Hn Hf.
split.
+
destruct inc_seq_split_lt with (k := p) (1 := Hf) as (k & H1 & H2 & H3).
replace n with (k+(n-k)) by lia.
rewrite msum_plus; auto.
rewrite plus_comm; intros H.
apply divides_plus_inv in H.
2: apply divides_msum; intros; apply divides_power, H3; lia.
destruct k as [ | k ].
*
apply H3; lia.
*
apply divides_lt in H.
-
rewrite msum_S in H.
generalize (@power_ge_1 (f 0) r); intros; lia.
-
apply sum_powers_inc_lt; auto.
intros; apply Hf; lia.
+
intros H.
apply divides_msum.
intros i Hi; apply divides_power.
apply le_trans with (1 := H).
destruct i; auto.
generalize (Hf 0 (S i)); intros; lia.
Fact smono_upto_injective n f : (forall i j, i < j < n -> f i < f j) -> (forall i j, i < n -> j < n -> f i = f j -> i = j).
Proof.
intros Hf i j Hi Hj E.
destruct (lt_eq_lt_dec i j) as [ [H|] | H ]; auto.
+
generalize (@Hf i j); intros; lia.
+
generalize (@Hf j i); intros; lia.
Fact product_sums n f g : (∑ n f)*(∑ n g) = ∑ n (fun i => f i*g i) + ∑ n (fun i => ∑ i (fun j => f i*g j + f j*g i)).
Proof.
induction n as [ | n IHn ].
+
repeat rewrite msum_0; auto.
+
repeat rewrite msum_plus1; auto.
repeat rewrite Nat.mul_add_distr_l.
repeat rewrite Nat.mul_add_distr_r.
rewrite IHn, msum_sum; auto.
*
rewrite sum_0n_scal_l, sum_0n_scal_r; ring.
*
intros; ring.
Section sums.
Fact square_sum n f : (∑ n f)*(∑ n f) = ∑ n (fun i => f i*f i) + 2*∑ n (fun i => ∑ i (fun j => f i*f j)).
Proof.
rewrite product_sums, <- sum_0n_scal_l; f_equal.
apply msum_ext; intros; rewrite <- sum_0n_scal_l.
apply msum_ext; intros; ring.
Fact sum_regroup r k n f : (forall i, i < n -> f i < k) -> (forall i j, i < j < n -> f i < f j) -> { g | ∑ n (fun i => power (f i) r) = ∑ k (fun i => g i * power i r) /\ (forall i, i < k -> g i <= 1) /\ (forall i, k <= i -> g i = 0) }.
Proof.
revert k f; induction n as [ | n IHn ]; intros k f Hf1 Hf2.
+
exists (fun _ => 0); split; auto.
rewrite msum_0, msum_of_unit; auto.
+
destruct (IHn (f n) f) as (g & H1 & H2 & H3).
*
intros; apply Hf2; lia.
*
intros; apply Hf2; lia.
*
exists (fun i => if eq_nat_dec i (f n) then 1 else g i).
split; [ | split ].
-
rewrite msum_plus1, H1; auto.
replace k with (f n + S (k - f n -1)).
2: generalize (Hf1 n); intros; lia.
rewrite msum_plus; auto; f_equal.
++
apply msum_ext.
intros i He.
destruct (eq_nat_dec i (f n)); try ring; lia.
++
rewrite msum_S, msum_of_unit; auto.
**
repeat (rewrite plus_comm; simpl).
destruct (eq_nat_dec (f n) (f n)); try ring; lia.
**
intros i Hi.
destruct (eq_nat_dec (f n+S i) (f n)); try lia.
rewrite H3; lia.
-
intros i Hi.
destruct (eq_nat_dec i (f n)); auto.
destruct (le_lt_dec (f n) i).
++
rewrite H3; lia.
++
apply H2; lia.
-
intros i Hi.
generalize (Hf1 n); intros.
destruct (eq_nat_dec i (f n)); try lia.
apply H3; lia.
Section sum_sum_regroup.
Variable (r n k : nat) (f : nat -> nat) (Hf1 : forall i, i < n -> f i <= k) (Hf2 : forall i j, i < j < n -> f i < f j).
End sum_sum_regroup.
Section all_ones.
Local Lemma equation_inj x y a b : 1 <= x -> 1+x*a = y -> 1+x*b = y -> a = b.
Proof.
intros H1 H2 H3.
rewrite <- H3 in H2; clear y H3.
rewrite <- (@Nat.mul_cancel_l _ _ x); lia.
Variables (r : nat) (Hr : 2 <= r).
Fact all_ones_equation l : 1+(r-1)*∑ l (fun i => power i r) = power l r.
Proof using Hr.
induction l as [ | l IHl ].
*
rewrite msum_0, Nat.mul_0_r, power_0; auto.
*
rewrite msum_plus1; auto.
rewrite Nat.mul_add_distr_l, power_S.
replace r with (1+(r-1)) at 4 by lia.
rewrite Nat.mul_add_distr_r.
rewrite <- IHl at 2; ring.
Fact all_ones_dio l w : w = ∑ l (fun i => power i r) <-> 1+(r-1)*w = power l r.
Proof using Hr.
split.
+
intros; subst; apply all_ones_equation.
+
intros H.
apply equation_inj with (2 := H).
*
lia.
*
apply all_ones_equation.
End all_ones.
Section const_1.
Variable (l q : nat) (Hl : 0 < l) (Hlq : l+1 < q).
Let Hq : 1 <= q.
Proof.
lia.
Let Hq' : 0 < 4*q.
Proof.
lia.
Let r := (power (4*q) 2).
Let Hr' : 4 <= r.
Proof.
apply (@power_mono_l 2 (4*q) 2); lia.
Let Hr : 2 <= r.
Proof.
lia.
Section all_ones.
Variable (n w : nat) (Hw : w = ∑ n (fun i => power i r)).
Local Lemma Hw_0 : w = ∑ n (fun i => 1*power i r).
Proof using Hw.
rewrite Hw; apply msum_ext; intros; ring.
Fact all_ones_joins : w = msum nat_join 0 n (fun i => 1*power i r).
Proof using Hl Hlq Hw.
rewrite Hw_0.
apply sum_powers_ortho with (q := 4*q); auto; try lia.
Local Lemma Hw_1 : 2*w = ∑ n (fun i => 2*power i r).
Proof using Hw.
rewrite Hw_0, <- sum_0n_scal_l.
apply msum_ext; intros; ring.
Fact all_ones_2_joins : 2*w = msum nat_join 0 n (fun i => 2*power i r).
Proof using Hl Hlq Hw.
rewrite Hw_1.
apply sum_powers_ortho with (q := 4*q); auto; try lia.
End all_ones.
Section increase.
Variable (m k k' u w : nat) (f : nat -> nat) (Hm : 2*m < r) (Hf1 : forall i, i < m -> f i <= k) (Hf2 : forall i j, i < j < m -> f i < f j) (Hw : w = ∑ k' (fun i => power i r)) (Hu : u = ∑ m (fun i => power (f i) r)).
Let Hf4 : forall i j, i < m -> j < m -> f i = f j -> i = j.
Proof.
apply smono_upto_injective; auto.
Let u1 := ∑ m (fun i => power (2*f i) r).
Let u2 := ∑ m (fun i => ∑ i (fun j => 2*power (f i + f j) r)).
Fact const_u_square : u * u = u1 + u2.
Proof using Hl Hlq Hw Hu Hm.
unfold u1, u2.
rewrite Hu, square_sum; f_equal.
+
apply msum_ext; intros; rewrite <- power_plus; f_equal; lia.
+
rewrite <- sum_0n_scal_l; apply msum_ext; intros i Hi.
rewrite <- sum_0n_scal_l; apply msum_ext; intros j Hj.
rewrite power_plus; ring.
Local Lemma Hu1_0 : u1 = ∑ m (fun i => 1*power (2*f i) r).
Proof.
apply msum_ext; intros; ring.
Local Lemma Hseq_u a : a <= m -> ∑ a (fun i => 1*power (2*f i) r) = msum nat_join 0 a (fun i => 1*power (2*f i) r).
Proof using Hw Hf2 Hl Hlq Hm Hu.
intros Ha.
apply sum_powers_ortho with (q := 4*q); auto; try lia.
intros i j Hi Hj ?; apply Hf4; lia.
Local Lemma Hu1 : u1 = msum nat_join 0 m (fun i => 1*power (2*f i) r).
Proof using Hw Hf2 Hl Hlq Hm Hu.
rewrite Hu1_0; apply Hseq_u; auto.
Local Lemma Hu2_0 : u2 = 2 * ∑ m (fun i => ∑ i (fun j => power (f i + f j) r)).
Proof.
unfold u2; rewrite <- sum_0n_scal_l; apply msum_ext.
intros; rewrite <- sum_0n_scal_l; apply msum_ext; auto.
Local Lemma g_full : { g | ∑ m (fun i => ∑ i (fun j => power (f i + f j) r)) = ∑ (2*k) (fun i : nat => g i * power i r) /\ forall i : nat, g i <= m }.
Proof using Hf1 Hf2.
apply sum_sum_regroup; auto.
Let g := proj1_sig g_full.
Local Lemma Hg1 : u2 = ∑ (2*k) (fun i => (2*g i) * power i r).
Proof.
rewrite Hu2_0, (proj1 (proj2_sig g_full)), <- sum_0n_scal_l.
apply msum_ext; unfold g; intros; ring.
Local Lemma Hg2 i : 2*g i <= 2*m.
Proof.
apply mult_le_compat; auto; apply (proj2_sig g_full).
Let Hg3 i : 2*g i < r.
Proof using Hm.
apply le_lt_trans with (1 := Hg2 _); auto.
Let Hu2 : u2 = msum nat_join 0 (2*k) (fun i => (2*g i) * power i r).
Proof.
rewrite Hg1.
apply sum_powers_ortho with (q := 4*q); auto; lia.
Let Hu1_u2_1 : u1 ⇣ u2 = 0.
Proof.
rewrite Hu1, Hu2.
apply nat_ortho_joins.
intros i j Hi Hj.
destruct (eq_nat_dec j (2*f i)) as [ H | H ].
+
unfold r; do 2 rewrite <- power_mult.
rewrite <- H.
rewrite nat_meet_mult_power2.
rewrite nat_meet_12n; auto.
+
rewrite nat_meet_powers_neq with (q := 4*q); auto; lia.
Let Hu1_u2 : u*u = u1 ⇡ u2.
Proof.
rewrite const_u_square.
apply nat_ortho_plus_join; auto.
Let Hw_1 : w = msum nat_join 0 k' (fun i => 1*power i r).
Proof.
rewrite Hw; apply all_ones_joins; auto.
Let H2w_1 : 2*w = msum nat_join 0 k' (fun i => 2*power i r).
Proof.
rewrite Hw; apply all_ones_2_joins; auto.
Local Lemma Hu2_w : u2 ⇣ w = 0.
Proof using Hf1 Hf2 H2w_1 Hu1_u2.
rewrite Hu2, Hw_1.
destruct (le_lt_dec k' (2*k)) as [ Hk | Hk ].
2: {
apply nat_ortho_joins.
intros i j Hi Hj.
rewrite nat_meet_comm.
destruct (eq_nat_dec i j) as [ H | H ].
+
subst j; rewrite nat_meet_powers_eq with (q := 4*q); auto.
rewrite nat_meet_12n; auto.
+
apply nat_meet_powers_neq with (q := 4*q); auto; try lia.
}
replace (2*k) with (k'+(2*k-k')) by lia.
rewrite msum_plus, nat_meet_comm, nat_meet_join_distr_l, nat_join_comm; auto.
rewrite (proj2 (nat_ortho_joins k' (2*k-k') _ _)), nat_join_0n.
2: {
intros i j H1 H2.
apply nat_meet_powers_neq with (q := 4*q); auto; try lia.
}
apply nat_ortho_joins.
intros i j Hi Hj.
destruct (eq_nat_dec i j) as [ H | H ].
+
subst j; rewrite nat_meet_powers_eq with (q := 4*q); auto.
rewrite nat_meet_12n; auto.
+
apply nat_meet_powers_neq with (q := 4*q); auto; try lia.
Fact const_u1_prefix : { q | q <= m /\ u*u ⇣ w = ∑ q (fun i => 1*power (2*f i) r) }.
Proof using H2w_1 Hf1 Hf2 Hu1_u2.
destruct inc_seq_split_lt with (n := m) (f := fun i => 2*f i) (k := k') as (a & H1 & H2 & H3).
+
intros i j Hij; apply Hf2 in Hij; lia.
+
exists a; split; auto.
rewrite Hu1_u2, nat_meet_comm, nat_meet_join_distr_l.
do 2 rewrite (nat_meet_comm w).
rewrite Hu2_w, nat_join_n0.
rewrite Hu1, Hw_1.
replace m with (a+(m-a)) by lia.
rewrite msum_plus, nat_meet_comm, nat_meet_join_distr_l.
rewrite nat_join_comm.
rewrite (proj2 (nat_ortho_joins k' (m-a) _ _)), nat_join_0n; auto.
3: apply nat_join_monoid.
*
rewrite Hseq_u; auto.
rewrite nat_meet_comm.
apply binary_le_nat_meet.
apply nat_joins_binary_le.
intros i Hi.
exists (2*f i); split; auto.
*
intros; apply nat_meet_powers_neq with (q := 4*q); auto; try lia.
generalize (H3 (a + j)); intros; lia.
Hypothesis (Hk : 2*k < k').
Let Hu1_w : u1 ⇣ w = u1.
Proof.
apply binary_le_nat_meet.
rewrite Hu1, Hw_1.
apply nat_joins_binary_le.
intros i Hi.
exists (2*f i); split; auto.
apply le_lt_trans with (2 := Hk), mult_le_compat; auto.
Let Hu1_2w : u1 ⇣ (2*w) = 0.
Proof.
rewrite H2w_1, Hu1, nat_ortho_joins.
intros i j Hi Hj.
destruct (eq_nat_dec j (2 * f i)) as [ H | H ].
+
rewrite <- H, nat_meet_powers_eq with (q := 4*q); auto; try lia.
rewrite nat_meet_12; auto.
+
apply nat_meet_powers_neq with (q := 4*q); auto; try lia.
Fact const_u1_meet p : p = (u*u) ⇣ w <-> p = u1.
Proof using Hu1_w.
rewrite Hu1_u2, nat_meet_comm, nat_meet_join_distr_l.
do 2 rewrite (nat_meet_comm w).
rewrite Hu1_w, Hu2_w, nat_join_n0; tauto.
Fact const_u1_eq : (u*u) ⇣ w = u1.
Proof using Hu1_w.
apply const_u1_meet; auto.
Hypothesis Hf : forall i, i < m -> f i = power (S i) 2.
Let Hu2_1 : u2 = msum nat_join 0 m (fun i => msum nat_join 0 i (fun j => 2*power (f i + f j) r)).
Proof.
unfold u2.
apply double_sum_powers_ortho with (q := 4*q); auto; try lia.
intros ? ? ? ? ? ?; repeat rewrite Hf; try lia.
intros E.
apply sum_2_power_2_injective in E; lia.
Let Hu2_2w : u2 ⇣ (2*w) = u2.
Proof.
apply binary_le_nat_meet.
rewrite H2w_1, Hu2_1.
apply nat_double_joins_binary_le.
intros i j Hij.
exists (f i + f j); split; auto.
apply le_lt_trans with (2*f i); auto.
+
apply Hf2 in Hij; lia.
+
apply le_lt_trans with (2 := Hk), mult_le_compat; auto.
apply Hf1; lia.
Fact const_u2_meet p : p = (u*u) ⇣ (2*w) <-> p = u2.
Proof using Hu1_w Hu2_2w.
rewrite Hu1_u2, nat_meet_comm, nat_meet_join_distr_l.
do 2 rewrite (nat_meet_comm (2*w)).
rewrite Hu1_2w, Hu2_2w, nat_join_0n; tauto.
End increase.
Let Hl'' : 2*l < r.
Proof.
unfold r.
rewrite (mult_comm _ q), power_mult.
change (power 4 2) with 16.
apply power_smono_l with (x := 16) in Hlq; try lia.
apply le_lt_trans with (2 := Hlq).
rewrite plus_comm; simpl plus; rewrite power_S.
apply mult_le_compat; try lia.
apply power_ge_n; lia.
Section const_1_cn.
Variable (u u1 : nat) (Hu : u = ∑ l (fun i => power (power (S i) 2) r)) (Hu1 : u1 = ∑ l (fun i => power (power (S (S i)) 2) r)).
Let w := ∑ (S (power (S l) 2)) (fun i => power i r).
Let u2 := ∑ l (fun i => ∑ i (fun j => 2*power (power (S i) 2 + power (S j) 2) r)).
Let H18 : 1+(r-1)*w = power (S (power (S l) 2)) r.
Proof.
rewrite <- all_ones_dio; auto.
Let H19 : u*u = u1 + u2.
Proof.
rewrite Hu1, Hu.
apply const_u_square with (k' := 0) (w := 0); eauto.
Let k := S (power (S l) 2).
Let f i := power (S i) 2.
Let Hf1 i : i < l -> 2*f i < k.
Proof.
unfold k, f.
intros; rewrite <- power_S; apply le_n_S, power_mono_l; lia.
Let Hf2 i j : i < j < l -> f i < f j.
Proof.
intros; apply power_smono_l; lia.
Let Hf3 i1 j1 i2 j2 : j1 <= i1 < l -> j2 <= i2 < l -> f i1 + f j1 = f i2 + f j2 -> i1 = i2 /\ j1 = j2.
Proof.
unfold f; intros H1 H2 E.
apply sum_2_power_2_injective in E; lia.
Let H20 : u1 = (u*u) ⇣ w.
Proof.
rewrite const_u1_meet with (k := power l 2) (m := l) (f := f); auto.
*
intros i Hi; specialize (Hf1 Hi).
revert Hf1; unfold k; rewrite power_S; intros; lia.
*
rewrite <- power_S; auto.
Let H21 : u2 = (u*u) ⇣ (2*w).
Proof.
rewrite const_u2_meet with (k := power l 2) (m := l) (f := f); auto.
*
intros i Hi; specialize (Hf1 Hi).
revert Hf1; unfold k; rewrite power_S; intros; lia.
*
rewrite <- power_S; auto.
Let H22 : power 2 r + u1 = u + power (power (S l) 2) r.
Proof.
rewrite Hu, Hu1.
destruct l.
+
do 2 rewrite msum_0.
rewrite power_1; auto.
+
rewrite msum_plus1, msum_S; auto.
rewrite power_1; ring.
Let H23 : divides (power 4 r) u1.
Proof.
rewrite Hu1.
apply divides_msum.
intros i _.
apply divides_power.
apply (@power_mono_l 2 _ 2); lia.
End const_1_cn.
Section const_1_cs.
Variable (w u u1 u2 : nat).
Hypothesis (H18 : 1+(r-1)*w = power (S (power (S l) 2)) r) (H19 : u*u = u1 + u2) (H20 : u1 = (u*u) ⇣ w) (H21 : u2 = (u*u) ⇣ (2*w)) (H22 : power 2 r + u1 = u + power (power (S l) 2) r) (H23 : divides (power 4 r) u1).
Let Hw_0 : w = ∑ (S (power (S l) 2)) (fun i => power i r).
Proof.
apply all_ones_dio; auto.
Let Hw_1 : w = ∑ (S (power (S l) 2)) (fun i => 1*power i r).
Proof.
rewrite Hw_0; apply msum_ext; intros; ring.
Let Hw : w = msum nat_join 0 (S (power (S l) 2)) (fun i => 1*power i r).
Proof.
apply all_ones_joins; auto.
Let H2w : 2*w = msum nat_join 0 (S (power (S l) 2)) (fun i => 2*power i r).
Proof.
apply all_ones_2_joins; auto.
Let Hu1_0 : u1 ≲ ∑ (S (power (S l) 2)) (fun i => 1*power i r).
Proof.
rewrite H20, <- Hw_1; auto.
Local Lemma mk_full : { m : nat & { k | u1 = ∑ (S m) (fun i => power (k i) r) /\ m <= power (S l) 2 /\ (forall i, i < S m -> k i <= power (S l) 2) /\ forall i j, i < j < S m -> k i < k j } }.
Proof using Hw Hu1_0 H19 H21 H22.
assert ({ k : nat & { g : nat -> nat & { h | u1 = ∑ k (fun i => g i * power (h i) r) /\ k <= S (power (S l) 2) /\ (forall i, i < k -> g i <> 0 /\ g i ≲ 1) /\ (forall i, i < k -> h i < S (power (S l) 2)) /\ (forall i j, i < j < k -> h i < h j) } } }) as H.
{
apply (@sum_powers_binary_le_inv _ Hq' r eq_refl _ (fun _ => _) (fun i => i)); auto.
intros; lia.
}
destruct H as (m' & g & h & H1 & H2 & H3 & H4 & H5).
assert (H6 : forall i, i < m' -> g i = 1).
{
intros i Hi; generalize (H3 _ Hi).
intros (? & G2); apply binary_le_le in G2; lia.
}
assert (H7 : u1 = ∑ m' (fun i => 1 * power (h i) r)).
{
rewrite H1; apply msum_ext; intros; rewrite H6; try ring; lia.
}
assert (H8 : u1 = ∑ m' (fun i => power (h i) r)).
{
rewrite H7; apply msum_ext; intros; ring.
}
assert (H9 : m' <> 0).
{
intros E; rewrite E, msum_0 in H1.
assert (power 2 r < power (power (S l) 2) r) as C.
{
apply power_smono_l; auto.
apply (@power_smono_l 1 _ 2); lia.
}
lia.
}
destruct m' as [ | m ]; try lia.
exists m, h; repeat (split; auto).
+
lia.
+
intros i; generalize (H4 i); intros; lia.
Let m := projT1 mk_full.
Let k := proj1_sig (projT2 mk_full).
Let Hu1 : u1 = ∑ (S m) (fun i => power (k i) r).
Proof.
apply (proj2_sig (projT2 mk_full)).
Let Hm : m <= (power (S l) 2).
Proof.
apply (proj2_sig (projT2 mk_full)).
Let Hk1 : forall i, i < S m -> k i <= power (S l) 2.
Proof.
apply (proj2_sig (projT2 mk_full)).
Let Hk2 : forall i j, i < j < S m -> k i < k j.
Proof.
apply (proj2_sig (projT2 mk_full)).
Let Hh_0 : 4 <= k 0.
Proof.
rewrite Hu1 in H23.
apply power_divides_sum_power in H23; auto; try lia.
Let f1 i := match i with 0 => 2 | S i => k i end.
Let f2 i := if le_lt_dec i m then power (S l) 2 else k i.
Let Hf1_0 : forall i, i <= S m -> f1 i < S (power (S l) 2).
Proof.
intros [ | i ] Hi; simpl; apply le_n_S.
+
rewrite power_S.
change 2 with (2*1) at 1.
apply mult_le_compat; auto.
apply power_ge_1; lia.
+
apply Hk1; auto.
Let Hf1_1 : forall i j, i < j <= S m -> f1 i < f1 j.
Proof.
intros [ | i ] [ | j ] Hij; simpl; try lia.
*
apply lt_le_trans with (k 0); try lia.
destruct j; auto; apply lt_le_weak, Hk2; lia.
*
apply Hk2; lia.
Let Hf1_2 : ∑ (S (S m)) (fun i => power (f1 i) r) = u + power (power (S l) 2) r.
Proof.
rewrite msum_S; unfold f1.
rewrite <- Hu1; auto.
Let Hh_1 : k m = power (S l) 2.
Proof.
destruct (le_lt_dec (power (S l) 2) (k m)) as [ H | H ].
+
apply le_antisym; auto.
+
assert (∑ (S (S m)) (fun i => power (f1 i) r) < power (power (S l) 2) r); try lia.
apply sum_powers_inc_lt; auto.
-
intros [ | i ] Hi; simpl.
*
apply (@power_smono_l 1 _ 2); lia.
*
apply le_lt_trans with (2 := H).
destruct (eq_nat_dec i m); subst; auto.
apply lt_le_weak, Hk2; lia.
-
intros; apply Hf1_1; lia.
Let Hu : u = ∑ (S m) (fun i => power (f1 i) r).
Proof.
rewrite msum_plus1 in Hf1_2; auto.
simpl f1 at 2 in Hf1_2.
rewrite Hh_1 in Hf1_2.
lia.
Let Huu : u*u = ∑ (S m) (fun i => power (2*f1 i) r) + ∑ (S m) (fun i => ∑ i (fun j => 2*power (f1 i + f1 j) r)).
Proof.
rewrite Hu, square_sum; f_equal.
+
apply msum_ext; intros; rewrite <- power_plus; f_equal; lia.
+
rewrite <- sum_0n_scal_l; apply msum_ext; intros i Hi.
rewrite <- sum_0n_scal_l; apply msum_ext; intros j Hj.
rewrite power_plus; ring.
Let HSl_q : 2 * S (power (S l) 2) < power (2 * q) 2.
Proof.
rewrite <- (mult_2_eq_plus q), power_plus.
apply le_lt_trans with (2*power q 2).
+
apply mult_le_compat; auto.
apply power_smono_l; lia.
+
assert (power 1 2 < power q 2) as H.
{
apply power_smono_l; lia.
}
rewrite power_1 in H.
apply Nat.mul_lt_mono_pos_r; lia.
Let Hu1_1 : { d | d <= S m /\ u1 = ∑ d (fun i => power (2*f1 i) r) }.
Proof.
destruct const_u1_prefix with (m := S m) (k := power (S l) 2) (k' := S (power (S l) 2)) (u := u) (w := w) (f := fun i => f1 i) as (d & H1 & H2); auto.
+
unfold r.
apply le_lt_trans with (2*S (power (S l) 2)); try lia.
apply le_lt_trans with (power (S (S (S l))) 2).
do 4 rewrite power_S.
*
generalize (@power_ge_1 l 2); intros; lia.
*
apply power_smono_l; lia.
+
intros i Hi; generalize (@Hf1_0 i); intros; lia.
+
intros; apply Hf1_1; lia.
+
exists d; split; auto.
rewrite H20, H2.
apply msum_ext; intros; ring.
Let Hk_final : k 0 = 4 /\ forall i, i < m -> k (S i) = 2*k i.
Proof.
destruct Hu1_1 as (d & Hd1 & E).
rewrite Hu1 in E.
apply sum_powers_injective in E; auto.
+
destruct E as (? & E); subst d; split.
*
rewrite E; try lia; auto.
*
intros; rewrite E; auto; lia.
+
intros i j H; specialize (@Hf1_1 i j); intros; lia.
Let Hk_is_power i : i <= m -> k i = power (S (S i)) 2.
Proof.
induction i as [ | i IHi ]; intros Hi.
+
rewrite (proj1 Hk_final); auto.
+
rewrite (proj2 Hk_final), IHi, <- power_S; auto; lia.
Let Hm_is_l : S m = l.
Proof.
rewrite Hk_is_power in Hh_1; auto.
apply power_2_inj in Hh_1; lia.
Fact obtain_u_u1_value : u = ∑ l (fun i => power (power (S i) 2) r) /\ u1 = ∑ l (fun i => power (power (S (S i)) 2) r).
Proof using Hu.
split.
+
rewrite <- Hm_is_l, Hu.
apply msum_ext.
intros [ | i ]; simpl; auto.
intros; rewrite Hk_is_power; auto; lia.
+
rewrite <- Hm_is_l, Hu1.
apply msum_ext.
intros [ | i ]; simpl; auto.
*
rewrite Hk_is_power; auto; lia.
*
intros; rewrite Hk_is_power; auto; lia.
End const_1_cs.
End const_1.
Variable (l q : nat).
Notation r := (power (4*q) 2).
Definition seqs_of_ones u u1 := l+1 < q /\ u = ∑ l (fun i => power (power (S i) 2) r) /\ u1 = ∑ l (fun i => power (power (S (S i)) 2) r).
Definition is_cipher_of f a := l+1 < q /\ (forall i, i < l -> f i < power q 2) /\ a = ∑ l (fun i => f i * power (power (S i) 2) r).
Fact is_cipher_of_0 f a : l = 0 -> is_cipher_of f a <-> 1 < q /\ a = 0.
Proof.
intros ?; unfold is_cipher_of; subst l.
rewrite msum_0; simpl.
repeat (split; try tauto).
intros; lia.
Fact is_cipher_of_inj f1 f2 a : is_cipher_of f1 a -> is_cipher_of f2 a -> forall i, i < l -> f1 i = f2 i.
Proof.
intros (H1 & H2 & H3) (_ & H4 & H5).
rewrite H3 in H5.
revert H5; apply power_decomp_unique.
+
apply (@power_mono_l 1 _ 2); lia.
+
intros; apply power_smono_l; lia.
+
intros i Hi; apply lt_le_trans with (1 := H2 _ Hi), power_mono_l; lia.
+
intros i Hi; apply lt_le_trans with (1 := H4 _ Hi), power_mono_l; lia.
Fact is_cipher_of_fun f1 f2 a b : (forall i, i < l -> f1 i = f2 i) -> is_cipher_of f1 a -> is_cipher_of f2 b -> a = b.
Proof.
intros H1 (_ & _ & H2) (_ & _ & H3); subst a b.
apply msum_ext; intros; f_equal; auto.
Fact is_cipher_of_u : l+1 < q -> is_cipher_of (fun _ => 1) (∑ l (fun i => power (power (S i) 2) r)).
Proof.
intros H; split; auto; split.
+
intros; apply (@power_mono_l 1 _ 2); lia.
+
apply msum_ext; intros; lia.
Definition the_cipher f : l+1 < q -> (forall i, i < l -> f i < power q 2) -> { c | is_cipher_of f c }.
Proof.
intros H1 H2.
exists (∑ l (fun i => f i * power (power (S i) 2) r)); split; auto.
Definition Code a := exists f, is_cipher_of f a.
Definition Const c v := exists f, is_cipher_of f v /\ forall i, i < l -> f i = c.
Let Hr : 1 < q -> 4 <= r.
Proof.
intros H.
replace (4*q) with (2*q+2*q) by lia.
rewrite power_plus.
change 4 with ((power 1 2)*(power 1 2)); apply mult_le_compat; apply power_mono_l; try lia.
Section plus.
Variable (a b c : nat-> nat) (ca cb cc : nat) (Ha : is_cipher_of a ca) (Hb : is_cipher_of b cb) (Hc : is_cipher_of c cc).
Definition Code_plus := ca = cb + cc.
End plus.
Notation u := (∑ l (fun i => power (power (S i) 2) r)).
Notation u1 := (∑ l (fun i => power (power (S (S i)) 2) r)).
Section mult_utils.
Variable (b c : nat-> nat) (cb cc : nat) (Hb : is_cipher_of b cb) (Hc : is_cipher_of c cc).
Let eq1 : cb*cc = ∑ l (fun i => (b i*c i)*power (power (S (S i)) 2) r) + ∑ l (fun i => ∑ i (fun j => (b i*c j + b j*c i)*power (power (S i) 2 + power (S j) 2) r)).
Proof.
destruct Hb as (H1 & Hb1 & Hb2).
destruct Hc as (_ & Hc1 & Hc2).
rewrite Hb2, Hc2, product_sums; f_equal.
*
apply msum_ext; intros; rewrite (power_S (S _)).
rewrite <- (mult_2_eq_plus (power _ _)), power_plus; ring.
*
apply msum_ext; intros i Hi.
apply msum_ext; intros j Hj.
rewrite power_plus; ring.
Let Hbc_1 i : i < l -> b i * c i < r.
Proof.
destruct Hb as (H1 & Hb1 & Hb2).
destruct Hc as (_ & Hc1 & Hc2).
intro; apply mult_lt_power_2_4; auto.
Let Hbc_2 i j : i < l -> j < l -> b i * c j + b j * c i < r.
Proof.
destruct Hb as (H1 & Hb1 & Hb2).
destruct Hc as (_ & Hc1 & Hc2).
intros; apply mult_lt_power_2_4'; auto.
Let Hbc_3 : ∑ l (fun i => (b i*c i)*power (power (S (S i)) 2) r) = msum nat_join 0 l (fun i => (b i*c i)*power (power (S (S i)) 2) r).
Proof.
destruct Hb as (H1 & Hb1 & Hb2).
destruct Hc as (_ & Hc1 & Hc2).
apply sum_powers_ortho with (q := 4*q); try lia; auto.
intros ? ? ? ? E; apply power_2_inj in E; lia.
Let Hbc_4 : ∑ l (fun i => ∑ i (fun j => (b i*c j + b j*c i)*power (power (S i) 2 + power (S j) 2) r)) = msum nat_join 0 l (fun i => msum nat_join 0 i (fun j => (b i*c j + b j*c i)*power (power (S i) 2 + power (S j) 2) r)).
Proof.
destruct Hb as (H1 & Hb1 & Hb2).
destruct Hc as (_ & Hc1 & Hc2).
rewrite double_sum_powers_ortho with (q := 4*q); auto; try lia.
+
intros; apply Hbc_2; lia.
+
intros ? ? ? ? ? ? E; apply sum_2_power_2_injective in E; lia.
Let eq2 : cb*cc = msum nat_join 0 l (fun i => (b i*c i)*power (power (S (S i)) 2) r) ⇡ msum nat_join 0 l (fun i => msum nat_join 0 i (fun j => (b i*c j + b j*c i)*power (power (S i) 2 + power (S j) 2) r)).
Proof.
destruct Hb as (H1 & Hb1 & Hb2).
rewrite eq1, Hbc_3, Hbc_4.
apply nat_ortho_plus_join.
apply nat_ortho_joins.
intros i j Hi Hj; apply nat_ortho_joins_left.
intros k Hk.
apply nat_meet_powers_neq with (q := 4*q); auto; try lia.
*
apply power_2_n_ij_neq; lia.
*
apply Hbc_2; lia.
Let Hr_1 : (r-1)*u1 = ∑ l (fun i => (r-1)*power (power (S (S i)) 2) r).
Proof.
rewrite sum_0n_scal_l; auto.
Let Hr_2 : (r-1)*u1 = msum nat_join 0 l (fun i => (r-1)*power (power (S (S i)) 2) r).
Proof.
destruct Hb as (H1 & Hb1 & Hb2).
destruct Hc as (_ & Hc1 & Hc2).
rewrite Hr_1.
apply sum_powers_ortho with (q := 4*q); auto; try lia.
intros ? ? ? ? E; apply power_2_inj in E; lia.
Fact cipher_mult_eq : (cb*cc)⇣((r-1)*u1) = ∑ l (fun i => (b i*c i)*power (power (S (S i)) 2) r).
Proof using Hb Hc.
destruct Hb as (H1 & Hb1 & Hb2).
destruct Hc as (_ & Hc1 & Hc2).
rewrite eq2, Hbc_3, Hr_2.
rewrite nat_meet_comm, nat_meet_join_distr_l.
rewrite <- Hr_2 at 1; rewrite Hr_1, <- Hbc_3.
rewrite meet_sum_powers with (q := 4*q); auto; try (intros; lia).
2: intros; apply power_smono_l; lia.
rewrite (proj2 (nat_ortho_joins _ _ _ _)), nat_join_n0.
*
apply msum_ext; intros i Hi; f_equal.
rewrite nat_meet_comm; apply binary_le_nat_meet, power_2_minus_1_gt; auto.
*
intros i j Hi Hj.
apply nat_ortho_joins_left.
intros k Hk; apply nat_meet_powers_neq with (q := 4*q); auto; try lia.
+
apply power_2_n_ij_neq; lia.
+
apply Hbc_2; lia.
End mult_utils.
Section mult.
Variable (a b c : nat-> nat) (ca cb cc : nat) (Ha : is_cipher_of a ca) (Hb : is_cipher_of b cb) (Hc : is_cipher_of c cc).
Definition Code_mult := l = 0 \/ l <> 0 /\ exists v v1 r' r'' p, r'' = r /\ r'' = r'+1 /\ seqs_of_ones v v1 /\ p = (ca*v)⇣(r'*v1) /\ p = (cb*cc)⇣(r'*v1).
End mult.
Section inc_seq.
Definition CodeNat c := is_cipher_of (fun i => i) c.
Local Lemma IncSeq_dio_priv y : CodeNat y <-> l = 0 /\ 1 < q /\ y = 0 \/ 0 < l /\ exists z v v1, seqs_of_ones v v1 /\ Code y /\ Code z /\ y + l*(power (power (S l) 2) r) = (z*v)⇣((r-1) * v1) /\ y+v1+power (power 1 2) r = z + power (power (S l) 2) r.
Proof.
split.
+
intros (H1 & H2 & H3).
destruct (le_lt_dec l 0) as [ | Hl ].
-
assert (l = 0) as -> by lia.
rewrite msum_0 in H3; left; lia.
-
right; split; auto.
exists (∑ l (fun i => (S i) * power (power (S i) 2) r)), u, u1; split; auto.
{
split; auto.
}
split.
{
rewrite H3; exists (fun i => i); split; auto.
}
split.
{
exists S; repeat (split; auto).
intros; apply lt_le_trans with q; try lia.
apply power_ge_n; auto.
}
split.
{
rewrite cipher_mult_eq with (b := S) (c := fun _ => 1).
*
rewrite H3.
rewrite <- msum_plus1 with (f := fun i => i*power (power (S i) 2) r); auto.
rewrite msum_S, Nat.mul_0_l, Nat.add_0_l.
apply msum_ext; intros; ring.
*
repeat split; auto; intros.
apply lt_le_trans with q; try lia.
apply power_ge_n; auto.
*
apply is_cipher_of_u; auto.
}
{
rewrite H3.
destruct l as [ | l' ]; try lia.
rewrite msum_S, Nat.mul_0_l, Nat.add_0_l.
rewrite msum_plus1; auto.
rewrite plus_assoc.
rewrite msum_S.
rewrite <- msum_sum; auto.
2: intros; ring.
rewrite Nat.mul_1_l, plus_comm.
repeat rewrite <- plus_assoc; do 2 f_equal.
apply msum_ext; intros; ring.
}
+
intros [ (H1 & H2 & H3) | (Hl & z & v & v1 & H1 & H2 & H3 & H4 & H5) ].
-
split; subst; auto; split; intros; try lia.
rewrite msum_0; auto.
-
destruct H1 as (Hq & ? & ?); subst v v1.
split; auto; split.
{
intros i Hi; apply lt_le_trans with q; try lia.
apply power_ge_n; auto.
}
destruct H2 as (f & Hf).
destruct H3 as (g & Hg).
generalize (is_cipher_of_u Hq); intros Hu.
rewrite cipher_mult_eq with (1 := Hg) (2 := Hu) in H4.
destruct Hf as (_ & Hf & Hy).
destruct Hg as (_ & Hg & Hz).
set (h i := if le_lt_dec l i then l else f i).
assert (y+l*power (power (S l) 2) r = ∑ (S l) (fun i => h i * power (power (S i) 2) r)) as H6.
{
rewrite msum_plus1; auto; f_equal.
*
rewrite Hy; apply msum_ext.
intros i Hi; unfold h.
destruct (le_lt_dec l i); try lia.
*
unfold h.
destruct (le_lt_dec l l); try lia.
}
rewrite H4 in H6.
set (g' i := match i with 0 => 0 | S i => g i end).
assert ( ∑ (S l) (fun i => g' i * power (power (S i) 2) r) = ∑ l (fun i : nat => g i * 1 * power (power (S (S i)) 2) r)) as H7.
{
unfold g'; rewrite msum_S; apply msum_ext; intros; ring.
}
rewrite <- H7 in H6.
assert (forall i, i < S l -> g' i = h i) as H8.
{
apply power_decomp_unique with (5 := H6); try lia.
*
intros; apply power_smono_l; lia.
*
unfold g'; intros [ | i ] Hi; try lia.
apply lt_S_n in Hi.
apply lt_le_trans with (1 := Hg _ Hi), power_mono_l; lia.
*
intros i Hi; unfold h.
destruct (le_lt_dec l i) as [ | Hi' ].
+
apply lt_le_trans with (4*q); try lia.
apply power_ge_n; auto.
+
apply lt_le_trans with (1 := Hf _ Hi'), power_mono_l; lia.
}
assert (h 0 = 0) as E0.
{
rewrite <- H8; simpl; lia.
}
assert (forall i, i < l -> h (S i) = g i) as E1.
{
intros i Hi; rewrite <- H8; simpl; lia.
}
assert (f 0 = 0) as E3.
{
unfold h in E0; destruct (le_lt_dec l 0); auto; lia.
}
assert (forall i, S i < l -> f (S i) = g i) as E4.
{
intros i Hi; specialize (E1 i); unfold h in E1.
destruct (le_lt_dec l (S i)); lia.
}
assert (g (l-1) = l) as E5.
{
specialize (E1 (l-1)); unfold h in E1.
destruct (le_lt_dec l (S (l-1))); lia.
}
clear H6 H7 g' H8 E0 E1 h H4.
assert (y + u1 + power (power 1 2) r = ∑ l (fun i => (1+f i) * power (power (S i) 2) r) + power (power (S l) 2) r) as E1.
{
rewrite sum_0n_distr_in_out.
rewrite <- Hy, sum_0n_scal_l, Nat.mul_1_l.
destruct l as [ | l' ]; try lia.
rewrite msum_plus1; auto.
rewrite msum_S; ring.
}
assert (forall i, i < l -> 1+f i = g i) as E2.
{
apply power_decomp_unique with (f := fun i => power (S i) 2) (p := r); try lia.
+
intros; apply power_smono_l; lia.
+
intros i Hi; apply le_lt_trans with (power q 2); auto.
*
apply Hf; auto.
*
apply power_smono_l; lia.
+
intros i Hi; apply lt_le_trans with (1 := Hg _ Hi), power_mono_l; lia.
}
rewrite Hy; apply msum_ext.
clear Hy Hf Hg Hz H5 E5 E1 Hu.
intros i Hi; f_equal; revert i Hi.
induction i as [ | i IHi ]; intros Hi; auto.
rewrite E4, <- E2; try lia.
End inc_seq.
End sums.

Fact product_sums n f g : (∑ n f)*(∑ n g) = ∑ n (fun i => f i*g i) + ∑ n (fun i => ∑ i (fun j => f i*g j + f j*g i)).
Proof.
induction n as [ | n IHn ].
+
repeat rewrite msum_0; auto.
+
repeat rewrite msum_plus1; auto.
repeat rewrite Nat.mul_add_distr_l.
repeat rewrite Nat.mul_add_distr_r.
rewrite IHn, msum_sum; auto.
*
rewrite sum_0n_scal_l, sum_0n_scal_r; ring.
*
Admitted.

Fact square_sum n f : (∑ n f)*(∑ n f) = ∑ n (fun i => f i*f i) + 2*∑ n (fun i => ∑ i (fun j => f i*f j)).
Proof.
rewrite product_sums, <- sum_0n_scal_l; f_equal.
apply msum_ext; intros; rewrite <- sum_0n_scal_l.
Admitted.

Fact sum_regroup r k n f : (forall i, i < n -> f i < k) -> (forall i j, i < j < n -> f i < f j) -> { g | ∑ n (fun i => power (f i) r) = ∑ k (fun i => g i * power i r) /\ (forall i, i < k -> g i <= 1) /\ (forall i, k <= i -> g i = 0) }.
Proof.
revert k f; induction n as [ | n IHn ]; intros k f Hf1 Hf2.
+
exists (fun _ => 0); split; auto.
rewrite msum_0, msum_of_unit; auto.
+
destruct (IHn (f n) f) as (g & H1 & H2 & H3).
*
intros; apply Hf2; lia.
*
intros; apply Hf2; lia.
*
exists (fun i => if eq_nat_dec i (f n) then 1 else g i).
split; [ | split ].
-
rewrite msum_plus1, H1; auto.
replace k with (f n + S (k - f n -1)).
2: generalize (Hf1 n); intros; lia.
rewrite msum_plus; auto; f_equal.
++
apply msum_ext.
intros i He.
destruct (eq_nat_dec i (f n)); try ring; lia.
++
rewrite msum_S, msum_of_unit; auto.
**
repeat (rewrite plus_comm; simpl).
destruct (eq_nat_dec (f n) (f n)); try ring; lia.
**
intros i Hi.
destruct (eq_nat_dec (f n+S i) (f n)); try lia.
rewrite H3; lia.
-
intros i Hi.
destruct (eq_nat_dec i (f n)); auto.
destruct (le_lt_dec (f n) i).
++
rewrite H3; lia.
++
apply H2; lia.
-
intros i Hi.
generalize (Hf1 n); intros.
destruct (eq_nat_dec i (f n)); try lia.
Admitted.

Theorem sum_sum_regroup : { g | ∑ n (fun i => ∑ i (fun j => power (f i + f j) r)) = ∑ (2*k) (fun i => g i * power i r) /\ forall i, g i <= n }.
Proof using Hf1 Hf2.
revert n f Hf1 Hf2.
induction n as [ | p IHp ]; intros f Hf1 Hf2.
+
exists (fun _ => 0); split; auto.
rewrite msum_0.
simpl; rewrite msum_of_unit; auto.
+
destruct (IHp f) as (g & H1 & H2).
*
intros; apply Hf1; lia.
*
intros; apply Hf2; lia.
*
destruct sum_regroup with (r := r) (n := p) (f := fun j => f p + f j) (k := 2*k) as (g1 & G1 & G2 & G3).
-
intros i Hi; generalize (@Hf1 p) (@Hf2 i p); intros; lia.
-
intros i j H; generalize (@Hf2 i j); intros; lia.
-
assert (forall i, g1 i <= 1) as G4.
{
intro i; destruct (le_lt_dec (2*k) i); auto; rewrite G3; lia.
}
exists (fun i => g i + g1 i); split.
++
rewrite msum_plus1; auto.
rewrite H1, G1, <- msum_sum; auto.
2: intros; ring.
apply msum_ext; intros; ring.
++
intros i.
Admitted.

Fact all_ones_equation l : 1+(r-1)*∑ l (fun i => power i r) = power l r.
Proof using Hr.
induction l as [ | l IHl ].
*
rewrite msum_0, Nat.mul_0_r, power_0; auto.
*
rewrite msum_plus1; auto.
rewrite Nat.mul_add_distr_l, power_S.
replace r with (1+(r-1)) at 4 by lia.
rewrite Nat.mul_add_distr_r.
Admitted.

Fact all_ones_dio l w : w = ∑ l (fun i => power i r) <-> 1+(r-1)*w = power l r.
Proof using Hr.
split.
+
intros; subst; apply all_ones_equation.
+
intros H.
apply equation_inj with (2 := H).
*
lia.
*
Admitted.

Let Hq : 1 <= q.
Proof.
Admitted.

Let Hq' : 0 < 4*q.
Proof.
Admitted.

Let Hr' : 4 <= r.
Proof.
Admitted.

Let Hr : 2 <= r.
Proof.
Admitted.

Fact all_ones_2_joins : 2*w = msum nat_join 0 n (fun i => 2*power i r).
Proof using Hl Hlq Hw.
rewrite Hw_1.
Admitted.

Let Hf4 : forall i j, i < m -> j < m -> f i = f j -> i = j.
Proof.
Admitted.

Fact const_u_square : u * u = u1 + u2.
Proof using Hl Hlq Hw Hu Hm.
unfold u1, u2.
rewrite Hu, square_sum; f_equal.
+
apply msum_ext; intros; rewrite <- power_plus; f_equal; lia.
+
rewrite <- sum_0n_scal_l; apply msum_ext; intros i Hi.
rewrite <- sum_0n_scal_l; apply msum_ext; intros j Hj.
Admitted.

Let Hg3 i : 2*g i < r.
Proof using Hm.
Admitted.

Let Hu2 : u2 = msum nat_join 0 (2*k) (fun i => (2*g i) * power i r).
Proof.
rewrite Hg1.
Admitted.

Let Hu1_u2_1 : u1 ⇣ u2 = 0.
Proof.
rewrite Hu1, Hu2.
apply nat_ortho_joins.
intros i j Hi Hj.
destruct (eq_nat_dec j (2*f i)) as [ H | H ].
+
unfold r; do 2 rewrite <- power_mult.
rewrite <- H.
rewrite nat_meet_mult_power2.
rewrite nat_meet_12n; auto.
+
Admitted.

Let Hu1_u2 : u*u = u1 ⇡ u2.
Proof.
rewrite const_u_square.
Admitted.

Let Hw_1 : w = msum nat_join 0 k' (fun i => 1*power i r).
Proof.
Admitted.

Let H2w_1 : 2*w = msum nat_join 0 k' (fun i => 2*power i r).
Proof.
Admitted.

Fact const_u1_prefix : { q | q <= m /\ u*u ⇣ w = ∑ q (fun i => 1*power (2*f i) r) }.
Proof using H2w_1 Hf1 Hf2 Hu1_u2.
destruct inc_seq_split_lt with (n := m) (f := fun i => 2*f i) (k := k') as (a & H1 & H2 & H3).
+
intros i j Hij; apply Hf2 in Hij; lia.
+
exists a; split; auto.
rewrite Hu1_u2, nat_meet_comm, nat_meet_join_distr_l.
do 2 rewrite (nat_meet_comm w).
rewrite Hu2_w, nat_join_n0.
rewrite Hu1, Hw_1.
replace m with (a+(m-a)) by lia.
rewrite msum_plus, nat_meet_comm, nat_meet_join_distr_l.
rewrite nat_join_comm.
rewrite (proj2 (nat_ortho_joins k' (m-a) _ _)), nat_join_0n; auto.
3: apply nat_join_monoid.
*
rewrite Hseq_u; auto.
rewrite nat_meet_comm.
apply binary_le_nat_meet.
apply nat_joins_binary_le.
intros i Hi.
exists (2*f i); split; auto.
*
intros; apply nat_meet_powers_neq with (q := 4*q); auto; try lia.
Admitted.

Fact all_ones_joins : w = msum nat_join 0 n (fun i => 1*power i r).
Proof using Hl Hlq Hw.
rewrite Hw_0.
apply sum_powers_ortho with (q := 4*q); auto; try lia.

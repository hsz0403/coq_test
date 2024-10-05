Require Import Arith Nat Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd rel_iter sums.
Set Implicit Arguments.
Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Fact sum_0n_distr_in_out n a b f : ∑ n (fun i => (a i+b i) * f i) = ∑ n (fun i => a i * f i) + ∑ n (fun i => b i * f i).
Proof.
rewrite <- msum_sum; auto.
+
apply msum_ext; intros; ring.
+
intros; ring.
Section power_decomp.
Variable (p : nat) (Hp : 2 <= p).
Let power_nzero x : power x p <> 0.
Proof.
generalize (@power_ge_1 x p); lia.
Fact power_decomp_lt n f a q : (forall i j, i < j < n -> f i < f j) -> (forall i, i < n -> f i < q) -> (forall i, i < n -> a i < p) -> ∑ n (fun i => a i * power (f i) p) < power q p.
Proof.
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
Let power_2_inj_1 i j n : j < i -> 2* power n 2 <> power i 2 + power j 2.
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
Fact power_2_inj i j : power i 2 = power j 2 -> i = j.
Proof.
intros H.
destruct (lt_eq_lt_dec i j) as [ [ C | C ] | C ]; auto; apply power_smono_l with (x := 2) in C; lia.
Let power_plus_lt a b c : a < b < c -> power a 2 + power b 2 < power c 2.
Proof.
intros [ H1 H2 ].
apply power_mono_l with (x := 2) in H2; auto.
apply power_smono_l with (x := 2) in H1; auto.
rewrite power_S in H2; lia.
Let power_inj_2 i1 j1 i2 j2 : j1 < i1 -> j2 < i2 -> power i1 2 + power j1 2 = power i2 2 + power j2 2 -> i1 = i2 /\ j1 = j2.
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

Theorem power_decomp_unique' n f a b : (forall i j, i < j < n -> f i < f j) -> (forall i, i < n -> a i < p) -> (forall i, i < n -> b i < p) -> ∑ n (fun i => a i * power (f i) p) = ∑ n (fun i => b i * power (f i) p) -> forall i, i < n -> a i = b i.
Proof.
revert f a b.
induction n as [ | n IHn ]; intros f a b Hf Ha Hb.
+
intros; lia.
+
assert (forall i, 0 < i < S n -> f 0 < f i) by (intros; apply Hf; lia).
do 2 (rewrite power_decomp_factor; auto).
intros E.
apply div_rem_uniq in E; auto.
*
destruct E as (E1 & E2).
intros [ | i ] Hi.
-
revert E2; rewrite Nat.mul_cancel_r; auto.
-
apply IHn with (4 := E1); try lia.
++
intros u j Hu; apply lt_minus_cancel; split; apply Hf; lia.
++
intros; apply Ha; lia.
++
intros; apply Hb; lia.
*
rewrite power_S.
apply Nat.mul_lt_mono_pos_r.
-
apply power_ge_1; lia.
-
apply Ha; lia.
*
rewrite power_S.
apply Nat.mul_lt_mono_pos_r.
-
apply power_ge_1; lia.
-
apply Hb; lia.

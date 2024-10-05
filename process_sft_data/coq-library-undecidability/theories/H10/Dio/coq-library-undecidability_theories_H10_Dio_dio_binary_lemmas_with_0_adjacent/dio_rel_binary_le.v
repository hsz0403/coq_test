Require Import Arith Lia List Bool Setoid.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd prime binomial sums bool_nat rel_iter.
From Undecidability.H10.ArithLibs Require Import luca.
From Undecidability.H10.Matija Require Import cipher.
From Undecidability.H10.Dio Require Import dio_logic dio_expo.
Set Implicit Arguments.
Set Default Proof Using "Type".
Local Infix "≲" := binary_le (at level 70, no associativity).
Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).
Local Infix "⇣" := nat_meet (at level 40, left associativity).
Local Infix "⇡" := nat_join (at level 50, left associativity).
Section dio_fun_binomial.
Let plus_cancel_l : forall a b c, a + b = a + c -> b = c.
Proof.
intros; lia.
Hint Resolve Nat.mul_add_distr_r : core.
Let is_binomial_eq b n k : b = binomial n k <-> exists q, q = power (1+n) 2 /\ is_digit (power n (1+q)) q k b.
Proof.
split.
+
intros ?; subst.
set (q := power (1+n) 2).
assert (Hq : q <> 0).
{
unfold q; generalize (@power_ge_1 (S n) 2); intros; simpl; lia.
}
set (c := power n (1+q)).
exists q; split; auto; split.
*
apply binomial_lt_power.
*
fold c.
destruct (le_lt_dec k n) as [ Hk | Hk ].
-
exists (∑ (n-k) (fun i => binomial n (S k+i) * power i q)), (∑ k (fun i => binomial n i * power i q)); split; auto.
2: {
apply sum_power_lt; auto; intros; apply binomial_lt_power.
}
rewrite Nat.mul_add_distr_r, <- mult_assoc, <- power_S.
rewrite <- sum_0n_distr_r with (1 := Nat_plus_monoid) (3 := Nat_mult_monoid); auto.
rewrite <- plus_assoc, (plus_comm _ (∑ _ _)).
rewrite <- msum_plus1 with (f := fun i => binomial n i * power i q); auto.
rewrite plus_comm.
unfold c.
rewrite Newton_nat_S.
replace (S n) with (S k + (n-k)) by lia.
rewrite msum_plus; auto; f_equal; apply msum_ext.
intros; rewrite power_plus; ring.
-
exists 0, c.
rewrite binomial_gt; auto.
rewrite Nat.mul_0_l; split; auto.
unfold c.
apply lt_le_trans with (power (S n) q).
++
rewrite Newton_nat_S.
apply sum_power_lt; auto.
intros; apply binomial_lt_power.
++
apply power_mono; lia.
+
intros (q & H1 & H3).
assert (Hq : q <> 0).
{
rewrite H1; generalize (@power_ge_1 (S n) 2); intros; simpl; lia.
}
rewrite Newton_nat_S in H3.
apply is_digit_fun with (1 := H3).
destruct (le_lt_dec k n) as [ Hk | Hk ].
*
red; split.
-
subst; apply binomial_lt_power.
-
exists (∑ (n-k) (fun i => binomial n (S k+i) * power i q)), (∑ k (fun i => binomial n i * power i q)); split.
2: {
apply sum_power_lt; auto; intros; subst; apply binomial_lt_power.
}
rewrite Nat.mul_add_distr_r, <- mult_assoc, <- power_S.
rewrite <- sum_0n_distr_r with (1 := Nat_plus_monoid) (3 := Nat_mult_monoid); auto.
rewrite <- plus_assoc, (plus_comm _ (∑ _ _)).
rewrite <- msum_plus1 with (f := fun i => binomial n i * power i q); auto.
rewrite plus_comm.
replace (S n) with (S k + (n-k)) by lia.
rewrite msum_plus; auto; f_equal.
apply msum_ext.
intros; rewrite power_plus; ring.
*
rewrite binomial_gt; auto.
rewrite <- Newton_nat_S.
split; try lia.
exists 0, (power n (1+q)); split; auto.
apply lt_le_trans with (power (S n) q).
-
rewrite Newton_nat_S.
apply sum_power_lt; auto.
subst; intros; apply binomial_lt_power.
-
apply power_mono; lia.

Theorem dio_rel_binary_le x y : 𝔻F x -> 𝔻F y -> 𝔻R (fun v => x v ≲ y v).
Proof.
dio by lemma (fun v => binary_le_binomial (x v) (y v)).
